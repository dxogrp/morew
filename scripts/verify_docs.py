"""Check the selected main commit and CI run before deploying documentation."""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import subprocess
import sys

from verify_release import (
    VerificationError,
    fetch_workflow_runs,
    latest_successful_run,
    required_environment,
    resolve_commit,
)


def verify(root: Path) -> dict[str, str]:
    repository = required_environment("GITHUB_REPOSITORY")
    if re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository) is None:
        raise VerificationError("GITHUB_REPOSITORY must have the form owner/repository.")
    if required_environment("GITHUB_EVENT_NAME") != "workflow_dispatch":
        raise VerificationError("Documentation deployment requires a workflow_dispatch event.")
    if required_environment("GITHUB_REF") != "refs/heads/main":
        raise VerificationError("Documentation deployment must be dispatched from refs/heads/main.")
    sha = resolve_commit(root, "HEAD")
    if sha != required_environment("GITHUB_SHA"):
        raise VerificationError("The documentation checkout must match GITHUB_SHA exactly.")
    runs = fetch_workflow_runs(repository, "ci.yml", sha, "push")
    url = latest_successful_run(runs, repository, "ci.yml", sha, "push")
    return {"source_sha": sha, "verification_run_url": url}


def report(result: dict[str, str]) -> None:
    label = "Documentation prerequisites verified"
    print(f"{label}: {result['source_sha']}.")
    print(f"Successful prerequisite: {result['verification_run_url']}")
    if output := os.environ.get("GITHUB_OUTPUT"):
        with Path(output).open("a", encoding="utf-8") as destination:
            for key, value in result.items():
                destination.write(f"{key}={value}\n")
    if summary := os.environ.get("GITHUB_STEP_SUMMARY"):
        with Path(summary).open("a", encoding="utf-8") as destination:
            destination.write(
                f"### {label}\n\n"
                f"Source commit: `{result['source_sha']}`\n\n"
                f"[Successful prerequisite run]({result['verification_run_url']})\n"
            )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    try:
        report(verify(Path.cwd()))
    except (VerificationError, OSError, subprocess.TimeoutExpired) as error:
        print(f"Documentation verification failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
