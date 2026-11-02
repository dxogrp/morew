"""Check release prerequisites without changing tags, releases, or source files."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tomllib
from typing import Any


class VerificationError(Exception):
    """A prerequisite could not be established."""


def stable_version(root: Path) -> str:
    """Read the committed package version, accepting only canonical X.Y.Z."""
    with (root / "lakefile.toml").open("rb") as source:
        version = tomllib.load(source).get("version")
    if not isinstance(version, str) or re.fullmatch(
        r"(?:0|[1-9][0-9]*)\.(?:0|[1-9][0-9]*)\.(?:0|[1-9][0-9]*)", version
    ) is None:
        raise VerificationError("lakefile.toml must specify a canonical stable X.Y.Z version.")
    return version


def required_environment(name: str) -> str:
    value = os.environ.get(name, "")
    if not value:
        raise VerificationError(f"Required environment variable {name} is missing.")
    return value


def git(root: Path, *args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args], cwd=root, text=True, capture_output=True, check=False, timeout=30
    )


def resolve_commit(root: Path, ref: str) -> str:
    result = git(root, "rev-parse", "--verify", f"{ref}^{{commit}}")
    if result.returncode:
        raise VerificationError(f"Cannot resolve Git commit {ref}; check the checkout and fetch depth.")
    return result.stdout.strip()


def require_main_ancestry(root: Path, sha: str) -> None:
    main = resolve_commit(root, "refs/remotes/origin/main")
    result = git(root, "merge-base", "--is-ancestor", sha, main)
    if result.returncode == 1:
        raise VerificationError("The release tag must point to a commit contained in origin/main.")
    if result.returncode:
        raise VerificationError("Cannot verify main ancestry; fetch the full repository history.")


def fetch_workflow_runs(
    repository: str, workflow: str, sha: str, event: str
) -> list[dict[str, Any]]:
    """Fetch all matching pages, deliberately including failed and pending runs."""
    required_environment("GH_TOKEN")
    result = subprocess.run(
        [
            "gh", "api", "--hostname", "github.com", "--method", "GET",
            f"/repos/{repository}/actions/workflows/{workflow}/runs",
            "--header", "Accept: application/vnd.github+json",
            "--header", "X-GitHub-Api-Version: 2022-11-28",
            "--raw-field", "branch=main", "--raw-field", f"event={event}",
            "--raw-field", f"head_sha={sha}", "--raw-field", "per_page=100",
            "--paginate", "--slurp",
        ],
        env={**os.environ, "GH_REPO": repository},
        text=True,
        capture_output=True,
        check=False,
        timeout=120,
    )
    if result.returncode:
        # Do not echo command output: authentication errors may contain credentials.
        raise VerificationError(
            "Cannot read GitHub Actions runs; check GH_TOKEN and actions: read permission."
        )
    try:
        pages = json.loads(result.stdout)
    except json.JSONDecodeError as error:
        raise VerificationError("GitHub returned an invalid workflow-run response.") from error
    if not isinstance(pages, list):
        raise VerificationError("GitHub returned an invalid paginated workflow-run response.")
    runs = []
    for page in pages:
        if not isinstance(page, dict) or not isinstance(page.get("workflow_runs"), list):
            raise VerificationError("GitHub returned a malformed workflow-run page.")
        for run in page["workflow_runs"]:
            if not isinstance(run, dict):
                raise VerificationError("GitHub returned a malformed workflow run.")
            runs.append(run)
    return runs


def latest_successful_run(
    runs: list[dict[str, Any]], repository: str, workflow: str, sha: str, event: str
) -> str:
    """Require the latest matching run/attempt to succeed, returning its URL."""
    def same_repository(value: Any) -> bool:
        name = value.get("full_name") if isinstance(value, dict) else None
        return isinstance(name, str) and name.casefold() == repository.casefold()

    matching = []
    for run in runs:
        repo = run.get("repository")
        head_repo = run.get("head_repository")
        if (
            not same_repository(repo)
            or run.get("path") != f".github/workflows/{workflow}"
            or run.get("event") != event
            or run.get("head_branch") != "main"
            or run.get("head_sha") != sha
            or (head_repo is not None and not same_repository(head_repo))
        ):
            continue
        for key in ("id", "run_number", "run_attempt"):
            if type(run.get(key)) is not int or run[key] < 1:
                raise VerificationError(f"GitHub returned a matching run without a valid {key}.")
        matching.append(run)
    guidance = (
        "Wait for ordinary CI on main to pass at this exact commit, then rerun the candidate."
        if workflow == "ci.yml"
        else "Complete a successful main-branch release candidate at this exact commit, then rerun release verification."
    )
    if not matching:
        raise VerificationError(f"No matching {workflow} run exists for {sha}. {guidance}")
    latest = max(matching, key=lambda run: (run["run_number"], run["run_attempt"]))
    url = f"https://github.com/{repository}/actions/runs/{latest['id']}"
    if latest.get("status") != "completed" or latest.get("conclusion") != "success":
        raise VerificationError(
            f"Latest {workflow} run for {sha} is not successful "
            f"(status={latest.get('status')}, conclusion={latest.get('conclusion')}): "
            f"{url}. {guidance}"
        )
    return url


def verify(mode: str, root: Path) -> dict[str, str]:
    repository = required_environment("GITHUB_REPOSITORY")
    if re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository) is None:
        raise VerificationError("GITHUB_REPOSITORY must have the form owner/repository.")
    if mode == "candidate" and required_environment("GITHUB_REF") != "refs/heads/main":
        raise VerificationError("Release candidates must be dispatched from refs/heads/main.")
    version = stable_version(root)
    sha = resolve_commit(root, "HEAD")
    if mode == "candidate":
        if sha != required_environment("GITHUB_SHA"):
            raise VerificationError("The candidate checkout must match GITHUB_SHA exactly.")
        workflow, event = "ci.yml", "push"
    elif mode == "release":
        tag = required_environment("RELEASE_TAG")
        if tag != f"v{version}":
            raise VerificationError("The release tag must equal v plus the lakefile.toml version.")
        if resolve_commit(root, f"refs/tags/{tag}") != sha:
            raise VerificationError("The release checkout must match the tagged commit exactly.")
        require_main_ancestry(root, sha)
        workflow, event = "release-candidate.yml", "workflow_dispatch"
    else:
        raise VerificationError(f"Unknown verification mode: {mode}")
    toolchain = (root / "lean-toolchain").read_text(encoding="utf-8").strip()
    if not toolchain or len(toolchain.splitlines()) != 1:
        raise VerificationError("lean-toolchain must contain exactly one nonempty toolchain name.")
    runs = fetch_workflow_runs(repository, workflow, sha, event)
    url = latest_successful_run(runs, repository, workflow, sha, event)
    return {
        "package_version": version,
        "source_sha": sha,
        "lean_toolchain": toolchain,
        "verification_run_url": url,
    }


def report(mode: str, result: dict[str, str]) -> None:
    label = "Candidate prerequisites verified" if mode == "candidate" else "Published release verified"
    print(f"{label}: v{result['package_version']} at {result['source_sha']}.")
    print(f"Successful prerequisite: {result['verification_run_url']}")
    if output := os.environ.get("GITHUB_OUTPUT"):
        with Path(output).open("a", encoding="utf-8") as destination:
            for key, value in result.items():
                destination.write(f"{key}={value}\n")
    if summary := os.environ.get("GITHUB_STEP_SUMMARY"):
        with Path(summary).open("a", encoding="utf-8") as destination:
            destination.write(
                f"### {label}\n\n"
                f"Version: `v{result['package_version']}`\n\n"
                f"Source commit: `{result['source_sha']}`\n\n"
                f"Lean toolchain: `{result['lean_toolchain']}`\n\n"
                f"[Successful prerequisite run]({result['verification_run_url']})\n"
            )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("candidate", "release"))
    args = parser.parse_args()
    try:
        report(args.mode, verify(args.mode, Path.cwd()))
    except (VerificationError, OSError, subprocess.TimeoutExpired, tomllib.TOMLDecodeError) as error:
        print(f"Release verification failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
