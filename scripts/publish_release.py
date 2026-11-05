"""Publish a new release after the workflow's full verification job succeeds."""

from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tomllib
from typing import Any

from verify_release import VerificationError, required_environment, verify


def github_api(
    repository: str, method: str, endpoint: str,
    payload: dict[str, Any] | None = None, *, paginate: bool = False,
) -> Any:
    required_environment("GH_TOKEN")
    command = [
        "gh", "api", "--hostname", "github.com", "--method", method,
        f"/repos/{repository}/{endpoint}",
        "--header", "Accept: application/vnd.github+json",
        "--header", "X-GitHub-Api-Version: 2022-11-28",
    ]
    if payload is not None:
        command += ["--input", "-"]
    if paginate:
        command += ["--paginate", "--slurp"]
    try:
        result = subprocess.run(
            command, input=json.dumps(payload) if payload is not None else None,
            env={**os.environ, "GH_REPO": repository},
            text=True, capture_output=True, check=False, timeout=120,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise VerificationError(
            f"GitHub {method} {endpoint} could not be confirmed; inspect GitHub before retrying."
        ) from error
    if result.returncode:
        # A failed response can follow a completed write.
        # Report a fixed message to keep credentials out of logs.
        raise VerificationError(
            f"GitHub {method} {endpoint} did not succeed; check permissions and existing "
            "tags/releases before retrying."
        )
    try:
        return json.loads(result.stdout)
    except json.JSONDecodeError as error:
        raise VerificationError(
            f"GitHub {method} {endpoint} returned invalid JSON; inspect GitHub before retrying."
        ) from error


def api_post(repository: str, endpoint: str, payload: dict[str, Any]) -> dict[str, Any]:
    result = github_api(repository, "POST", endpoint, payload)
    if not isinstance(result, dict):
        raise VerificationError(f"GitHub POST {endpoint} returned an invalid response.")
    return result


def require_unused_release(repository: str, tag: str) -> None:
    # Include drafts and releases whose tags were deleted.
    pages = github_api(repository, "GET", "releases?per_page=100", paginate=True)
    if not isinstance(pages, list):
        raise VerificationError("GitHub returned an invalid release list.")
    for page in pages:
        if not isinstance(page, list):
            raise VerificationError("GitHub returned an invalid release page.")
        for existing in page:
            if not isinstance(existing, dict) or not isinstance(existing.get("tag_name"), str):
                raise VerificationError("GitHub returned a malformed release.")
            if existing["tag_name"] == tag:
                raise VerificationError(f"Release {tag} already exists; releases must not be reused.")


def publish(root: Path) -> str:
    expected_sha = required_environment("VERIFIED_SHA")
    expected_tag = required_environment("RELEASE_TAG")
    result = verify(root)
    sha, tag = result["source_sha"], result["release_tag"]
    if sha != expected_sha or tag != expected_tag:
        raise VerificationError("The publication checkout must match the verified commit and version.")
    repository = required_environment("GITHUB_REPOSITORY")
    require_unused_release(repository, tag)

    # Create the tag at the verified commit; GitHub rejects an existing tag.
    ref = api_post(repository, "git/refs", {"ref": f"refs/tags/{tag}", "sha": sha})
    target = ref.get("object")
    if (
        ref.get("ref") != f"refs/tags/{tag}"
        or not isinstance(target, dict)
        or target.get("type") != "commit"
        or target.get("sha") != sha
    ):
        raise VerificationError("Created tag identity could not be confirmed; inspect GitHub before recovery.")
    try:
        created = api_post(repository, "releases", {
            "tag_name": tag, "target_commitish": sha, "name": tag,
            "draft": False, "prerelease": False, "generate_release_notes": True,
        })
        if (
            created.get("tag_name") != tag
            or created.get("draft") is not False
            or created.get("prerelease") is not False
        ):
            raise VerificationError("GitHub returned an unexpected release identity or publication state.")
    except VerificationError as error:
        raise VerificationError(
            f"Tag {tag} was created at {sha}, but release publication could not be confirmed. "
            "Inspect the release and this run before recovery. The tag is preserved; "
            "this workflow never moves or reuses existing tags. " + str(error)
        ) from error
    return f"https://github.com/{repository}/releases/tag/{tag}"


def main() -> int:
    try:
        url = publish(Path.cwd())
        print(f"Published release: {url}")
        if summary := os.environ.get("GITHUB_STEP_SUMMARY"):
            with Path(summary).open("a", encoding="utf-8") as destination:
                destination.write(f"### Release published\n\n[View release]({url})\n")
    except (VerificationError, OSError, subprocess.TimeoutExpired, tomllib.TOMLDecodeError) as error:
        print(f"Release publication failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
