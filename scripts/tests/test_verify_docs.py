"""Tests for the commit and CI prerequisites of documentation deployment."""

from __future__ import annotations

from contextlib import chdir, redirect_stderr, redirect_stdout
import importlib.util
import io
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch


SCRIPTS = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("verify_docs", SCRIPTS / "verify_docs.py")
assert SPEC is not None and SPEC.loader is not None
docs = importlib.util.module_from_spec(SPEC)
with patch.object(sys, "path", [str(SCRIPTS), *sys.path]):
    SPEC.loader.exec_module(docs)

REPOSITORY = "dxogrp/morew"
RUN_URL = f"https://github.com/{REPOSITORY}/actions/runs/123"


def workflow_run(sha, **changes):
    run = {
        "id": 123,
        "run_number": 10,
        "run_attempt": 1,
        "repository": {"full_name": REPOSITORY},
        "head_repository": {"full_name": REPOSITORY},
        "path": ".github/workflows/ci.yml",
        "head_sha": sha,
        "head_branch": "main",
        "event": "push",
        "status": "completed",
        "conclusion": "success",
    }
    run.update(changes)
    return run


class DocumentationGateTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.git("init", "-q", "--initial-branch=main")
        self.git("config", "user.email", "test@example.invalid")
        self.git("config", "user.name", "Documentation Test")
        (self.root / "lakefile.toml").write_text('version = "0.1.0"\n')
        self.git("add", ".")
        self.git("commit", "-qm", "Initial")
        self.sha = self.git("rev-parse", "HEAD")
        environment = patch.dict(os.environ, {
            "GITHUB_REPOSITORY": REPOSITORY,
            "GITHUB_EVENT_NAME": "workflow_dispatch",
            "GITHUB_REF": "refs/heads/main",
            "GITHUB_SHA": self.sha,
        })
        environment.start()
        self.addCleanup(environment.stop)
        api = patch.object(docs, "fetch_workflow_runs", return_value=[workflow_run(self.sha)])
        self.fetch = api.start()
        self.addCleanup(api.stop)

    def git(self, *args):
        return subprocess.run(
            ["git", *args], cwd=self.root, check=True, capture_output=True, text=True
        ).stdout.strip()

    def test_accepts_the_selected_commit_with_successful_main_push_ci(self):
        self.assertEqual(docs.verify(self.root), {
            "source_sha": self.sha,
            "verification_run_url": RUN_URL,
        })
        self.fetch.assert_called_once_with(REPOSITORY, "ci.yml", self.sha, "push")

    def test_rejects_non_main_dispatches(self):
        for ref in ("refs/heads/topic", "refs/tags/v0.1.0"):
            with self.subTest(ref=ref), patch.dict(os.environ, {"GITHUB_REF": ref}):
                with self.assertRaisesRegex(docs.VerificationError, "refs/heads/main"):
                    docs.verify(self.root)
        self.fetch.assert_not_called()

    def test_rejects_automatic_events(self):
        for event in ("push", "release", "pull_request", "workflow_run"):
            with self.subTest(event=event), patch.dict(os.environ, {"GITHUB_EVENT_NAME": event}):
                with self.assertRaisesRegex(docs.VerificationError, "workflow_dispatch"):
                    docs.verify(self.root)
        self.fetch.assert_not_called()

    def test_rejects_a_checkout_different_from_the_dispatch_commit(self):
        with patch.dict(os.environ, {"GITHUB_SHA": "b" * 40}):
            with self.assertRaisesRegex(docs.VerificationError, "match GITHUB_SHA exactly"):
                docs.verify(self.root)
        self.fetch.assert_not_called()

    def test_existing_release_tag_is_allowed_and_preserved(self):
        self.git("tag", "-a", "-m", "Version 0.1.0", "v0.1.0")
        tag_object = self.git("rev-parse", "refs/tags/v0.1.0")
        self.assertEqual(docs.verify(self.root)["source_sha"], self.sha)
        self.assertEqual(self.git("rev-parse", "refs/tags/v0.1.0"), tag_object)

    def test_package_version_is_not_a_deployment_prerequisite(self):
        (self.root / "lakefile.toml").write_text('version = "0.2.0-rc.1"\n')
        self.git("add", ".")
        self.git("commit", "-qm", "Prerelease package version")
        sha = self.git("rev-parse", "HEAD")
        self.fetch.return_value = [workflow_run(sha)]
        with patch.dict(os.environ, {"GITHUB_SHA": sha}):
            self.assertEqual(docs.verify(self.root)["source_sha"], sha)

    def test_newer_failed_or_pending_ci_cannot_reuse_an_older_success(self):
        for changes in (
            {"run_number": 11, "conclusion": "failure"},
            {"run_number": 11, "status": "in_progress", "conclusion": None},
            {"run_attempt": 2, "conclusion": "failure"},
        ):
            self.fetch.return_value = [workflow_run(self.sha), workflow_run(self.sha, **changes)]
            with self.subTest(changes=changes), self.assertRaisesRegex(
                docs.VerificationError, "Latest ci.yml run"
            ):
                docs.verify(self.root)

    def test_unrelated_ci_cannot_satisfy_the_gate(self):
        for changes in (
            {"head_sha": "b" * 40},
            {"head_branch": "topic"},
            {"event": "pull_request"},
            {"event": "workflow_dispatch"},
            {"path": ".github/workflows/docs.yml"},
        ):
            self.fetch.return_value = [workflow_run(self.sha, **changes)]
            with self.subTest(changes=changes), self.assertRaisesRegex(
                docs.VerificationError, "No matching ci.yml run"
            ):
                docs.verify(self.root)

    def test_cli_reports_the_commit_and_ci_run(self):
        output = self.root / "output"
        summary = self.root / "summary"
        with patch.dict(os.environ, {
            "GITHUB_OUTPUT": str(output), "GITHUB_STEP_SUMMARY": str(summary),
        }), patch.object(sys, "argv", ["verify_docs.py"]):
            with chdir(self.root), redirect_stdout(io.StringIO()):
                self.assertEqual(docs.main(), 0)
        metadata = dict(line.split("=", 1) for line in output.read_text().splitlines())
        self.assertEqual(metadata, {"source_sha": self.sha, "verification_run_url": RUN_URL})
        self.assertIn(self.sha, summary.read_text())
        self.assertIn(RUN_URL, summary.read_text())

    def test_cli_reports_a_failed_prerequisite(self):
        self.fetch.return_value = []
        stderr = io.StringIO()
        with patch.object(sys, "argv", ["verify_docs.py"]), chdir(self.root), redirect_stderr(stderr):
            self.assertEqual(docs.main(), 1)
        self.assertIn("Documentation verification failed", stderr.getvalue())
        self.assertIn("rerun the workflow", stderr.getvalue())


if __name__ == "__main__":
    unittest.main()
