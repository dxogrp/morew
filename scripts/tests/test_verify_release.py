"""Regression tests for release identity and exact-commit workflow gates."""

from __future__ import annotations

import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch


SPEC = importlib.util.spec_from_file_location(
    "verify_release", Path(__file__).resolve().parents[1] / "verify_release.py"
)
assert SPEC is not None and SPEC.loader is not None
release = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(release)

REPOSITORY = "dxogrp/morew"
SHA = "a" * 40


def workflow_run(**changes):
    run = {
        "id": 123,
        "run_number": 10,
        "run_attempt": 1,
        "repository": {"full_name": REPOSITORY},
        "head_repository": {"full_name": REPOSITORY},
        "path": ".github/workflows/ci.yml",
        "head_sha": SHA,
        "head_branch": "main",
        "event": "push",
        "status": "completed",
        "conclusion": "success",
    }
    run.update(changes)
    return run


class WorkflowGateTests(unittest.TestCase):
    def check(self, runs):
        return release.latest_successful_run(runs, REPOSITORY, "ci.yml", SHA, "push")

    def test_successful_latest_run(self):
        older_failure = workflow_run(run_number=9, conclusion="failure")
        self.assertEqual(
            self.check([workflow_run(), older_failure]),
            "https://github.com/dxogrp/morew/actions/runs/123",
        )

    def test_missing_run_fails(self):
        with self.assertRaisesRegex(release.VerificationError, "No matching"):
            self.check([])

    def test_newer_unsuccessful_run_cannot_reuse_older_success(self):
        for conclusion in ("failure", "cancelled", "timed_out", "neutral", "skipped"):
            with self.subTest(conclusion=conclusion), self.assertRaisesRegex(
                release.VerificationError, "not successful"
            ):
                self.check([workflow_run(), workflow_run(run_number=11, conclusion=conclusion)])

    def test_newer_pending_run_cannot_reuse_older_success(self):
        for status in ("queued", "in_progress", "waiting"):
            with self.subTest(status=status), self.assertRaisesRegex(
                release.VerificationError, "not successful"
            ):
                self.check([
                    workflow_run(),
                    workflow_run(run_number=11, status=status, conclusion=None),
                ])

    def test_latest_attempt_controls_rerun(self):
        with self.assertRaisesRegex(release.VerificationError, "not successful"):
            self.check([workflow_run(run_attempt=2, conclusion="failure"), workflow_run()])
        self.assertTrue(self.check([
            workflow_run(conclusion="failure"), workflow_run(run_attempt=2)
        ]).endswith("/123"))

    def test_unrelated_and_foreign_runs_cannot_satisfy_gate(self):
        changes = [
            {"repository": {"full_name": "someone/morew"}},
            {"repository": {"full_name": None}},
            {"repository": None},
            {"head_repository": {"full_name": "someone/morew"}},
            {"path": ".github/workflows/other.yml"},
            {"head_sha": "b" * 40},
            {"head_branch": "feature"},
            {"event": "pull_request"},
        ]
        for change in changes:
            unrelated = workflow_run(run_number=99, **change)
            with self.subTest(change=change):
                with self.assertRaisesRegex(release.VerificationError, "No matching"):
                    self.check([unrelated])
                self.assertTrue(self.check([unrelated, workflow_run()]).endswith("/123"))

    def test_malformed_ordering_cannot_hide_newer_run(self):
        for field in ("id", "run_number", "run_attempt"):
            for value in (None, "11", 0, True):
                with self.subTest(field=field, value=value), self.assertRaisesRegex(
                    release.VerificationError, "without a valid"
                ):
                    self.check([workflow_run(), workflow_run(**{field: value})])

    @patch.dict(os.environ, {"GH_TOKEN": "test-secret"})
    @patch.object(release.subprocess, "run")
    def test_fetches_every_page_without_success_filter(self, run):
        pages = [
            {"workflow_runs": [workflow_run()]},
            {"workflow_runs": [workflow_run(run_number=11, conclusion="failure")]},
        ]
        run.return_value = subprocess.CompletedProcess([], 0, json.dumps(pages), "")
        result = release.fetch_workflow_runs(REPOSITORY, "ci.yml", SHA, "push")
        self.assertEqual(len(result), 2)
        command = run.call_args.args[0]
        self.assertIn("--paginate", command)
        self.assertIn("--slurp", command)
        self.assertIn(f"head_sha={SHA}", command)
        self.assertIn("branch=main", command)
        self.assertIn("event=push", command)
        self.assertNotIn("status=success", command)
        self.assertEqual(run.call_args.kwargs["env"]["GH_REPO"], REPOSITORY)
        with self.assertRaisesRegex(release.VerificationError, "not successful"):
            self.check(result)

    @patch.dict(os.environ, {"GH_TOKEN": "test-secret"})
    @patch.object(release.subprocess, "run")
    def test_api_failure_does_not_report_credentials(self, run):
        run.return_value = subprocess.CompletedProcess([], 1, "test-secret", "test-secret")
        with self.assertRaises(release.VerificationError) as raised:
            release.fetch_workflow_runs(REPOSITORY, "ci.yml", SHA, "push")
        self.assertNotIn("test-secret", str(raised.exception))

    @patch.dict(os.environ, {"GH_TOKEN": "test-secret"})
    @patch.object(release.subprocess, "run")
    def test_malformed_api_response_fails(self, run):
        for response in ("not json", "{}", '[{}]', '[{"workflow_runs": [null]}]'):
            run.return_value = subprocess.CompletedProcess([], 0, response, "")
            with self.subTest(response=response), self.assertRaises(release.VerificationError):
                release.fetch_workflow_runs(REPOSITORY, "ci.yml", SHA, "push")


class ReleaseIdentityTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.git("init", "-q", "--initial-branch=main")
        self.git("config", "user.email", "test@example.invalid")
        self.git("config", "user.name", "Release Test")
        self.write_version("0.1.0")
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.33.0\n")
        self.git("add", ".")
        self.git("commit", "-qm", "Initial")
        self.sha = self.git("rev-parse", "HEAD")
        self.git("update-ref", "refs/remotes/origin/main", self.sha)
        environment = {
            "GITHUB_REPOSITORY": REPOSITORY,
            "GITHUB_EVENT_NAME": "workflow_dispatch",
            "GITHUB_SHA": self.sha,
            "GITHUB_REF": "refs/heads/main",
        }
        self.environment = patch.dict(os.environ, environment)
        self.environment.start()
        self.addCleanup(self.environment.stop)
        self.api = patch.object(release, "fetch_workflow_runs")
        self.fetch = self.api.start()
        self.addCleanup(self.api.stop)
        self.fetch.side_effect = lambda repo, workflow, sha, event: [
            workflow_run(path=f".github/workflows/{workflow}", head_sha=sha, event=event)
        ]

    def git(self, *args):
        return subprocess.run(
            ["git", *args], cwd=self.root, check=True, capture_output=True, text=True
        ).stdout.strip()

    def write_version(self, version):
        (self.root / "lakefile.toml").write_text(f'version = "{version}"\n')

    def test_release_checks_exact_main_push_commit_and_derives_tag(self):
        result = release.verify(self.root)
        self.assertEqual(result["source_sha"], self.sha)
        self.assertEqual(result["package_version"], "0.1.0")
        self.assertEqual(result["release_tag"], "v0.1.0")
        self.assertEqual(result["lean_toolchain"], "leanprover/lean4:v4.33.0")
        self.fetch.assert_called_once_with(REPOSITORY, "ci.yml", self.sha, "push")

    def test_release_rejects_automatic_events_before_api(self):
        for event in ("push", "release", "pull_request", "workflow_run"):
            with self.subTest(event=event), patch.dict(os.environ, {"GITHUB_EVENT_NAME": event}):
                with self.assertRaisesRegex(release.VerificationError, "workflow_dispatch"):
                    release.verify(self.root)
        self.fetch.assert_not_called()

    def test_release_rejects_non_main_ref_before_api(self):
        for ref in ("refs/heads/topic", "refs/tags/v0.1.0"):
            with self.subTest(ref=ref), patch.dict(os.environ, {"GITHUB_REF": ref}):
                with self.assertRaisesRegex(release.VerificationError, "dispatched from"):
                    release.verify(self.root)
        self.fetch.assert_not_called()

    def test_release_rejects_wrong_checkout_before_api(self):
        with patch.dict(os.environ, {"GITHUB_SHA": "b" * 40}):
            with self.assertRaisesRegex(release.VerificationError, "match GITHUB_SHA"):
                release.verify(self.root)
        self.fetch.assert_not_called()

    def test_stable_version_validation(self):
        for version in ("1.2", "v1.2.3", "01.2.3", "1.02.3", "1.2.03", "1.2.3-rc.1", "1.2.3+meta", " 1.2.3"):
            self.write_version(version)
            with self.subTest(version=version), self.assertRaisesRegex(
                release.VerificationError, "canonical stable"
            ):
                release.verify(self.root)
        self.fetch.assert_not_called()
        for version in ("0.1.0", "1.2.3", "12.20.300"):
            self.write_version(version)
            self.assertEqual(release.stable_version(self.root), version)

    def test_existing_release_tag_fails_before_ancestry_or_api(self):
        for options in ((), ("-a", "-m", "Version 0.1.0")):
            self.git("tag", *options, "v0.1.0")
            with self.subTest(options=options), patch.object(release, "require_main_ancestry") as ancestry:
                with self.assertRaisesRegex(release.VerificationError, "already exists"):
                    release.verify(self.root)
                ancestry.assert_not_called()
                self.assertEqual(self.git("rev-parse", "v0.1.0^{commit}"), self.sha)
            self.git("tag", "-d", "v0.1.0")
        self.fetch.assert_not_called()

    def test_unrelated_tag_does_not_block_release(self):
        self.git("tag", "v0.0.1")
        self.assertEqual(release.verify(self.root)["release_tag"], "v0.1.0")

    def test_tag_lookup_error_fails_closed(self):
        with patch.object(release, "git") as command:
            command.return_value = subprocess.CompletedProcess([], 128, "", "Git failure")
            with self.assertRaisesRegex(release.VerificationError, "Cannot check existing"):
                release.require_unused_tag(self.root, "v0.1.0")

    def test_release_must_be_contained_in_main(self):
        self.git("checkout", "-qb", "topic")
        self.git("commit", "--allow-empty", "-qm", "Unmerged")
        with patch.dict(os.environ, {"GITHUB_SHA": self.git("rev-parse", "HEAD")}):
            with self.assertRaisesRegex(release.VerificationError, "contained in origin/main"):
                release.verify(self.root)
        self.fetch.assert_not_called()

    def test_release_accepts_dispatch_commit_after_main_advances(self):
        self.git("commit", "--allow-empty", "-qm", "Later main commit")
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")
        self.git("checkout", "-q", self.sha)
        self.assertEqual(release.verify(self.root)["source_sha"], self.sha)

    def test_missing_main_history_fails(self):
        self.git("update-ref", "-d", "refs/remotes/origin/main")
        with self.assertRaisesRegex(release.VerificationError, "fetch depth"):
            release.verify(self.root)
        self.fetch.assert_not_called()

    def test_shallow_checkout_fails_even_when_head_is_main(self):
        with tempfile.TemporaryDirectory() as directory:
            shallow = Path(directory) / "checkout"
            subprocess.run(
                ["git", "clone", "--quiet", "--depth", "1", self.root.as_uri(), str(shallow)],
                check=True, capture_output=True, text=True,
            )
            with self.assertRaisesRegex(release.VerificationError, "full repository history"):
                release.verify(shallow)
        self.fetch.assert_not_called()

    def test_invalid_toolchain_fails_before_api(self):
        for toolchain in ("", "\n", "leanprover/lean4:v4.33.0\nother", "two names", "name\x00"):
            (self.root / "lean-toolchain").write_text(toolchain)
            with self.subTest(toolchain=toolchain), self.assertRaisesRegex(
                release.VerificationError, "lean-toolchain"
            ):
                release.verify(self.root)
        self.fetch.assert_not_called()

    def test_release_report_exports_validated_tag_without_claiming_publication(self):
        result = release.verify(self.root)
        output = self.root / "output"
        summary = self.root / "summary"
        with patch.dict(os.environ, {"GITHUB_OUTPUT": str(output), "GITHUB_STEP_SUMMARY": str(summary)}):
            with patch("builtins.print") as console:
                release.report(result)
        self.assertIn("release_tag=v0.1.0\n", output.read_text())
        self.assertIn(f"source_sha={self.sha}\n", output.read_text())
        self.assertIn("Release prerequisites verified", summary.read_text())
        self.assertIn(result["verification_run_url"], summary.read_text())
        self.assertIn(result["lean_toolchain"], summary.read_text())
        self.assertNotIn("Published", summary.read_text())
        console.assert_any_call(f"Release prerequisites verified: v0.1.0 at {self.sha}.")

    def test_cli_verifies_current_checkout_without_mode_argument(self):
        result = release.verify(self.root)
        with patch.object(release.sys, "argv", ["verify_release.py"]):
            with patch.object(release.Path, "cwd", return_value=self.root):
                with patch.object(release, "verify", return_value=result) as verify:
                    with patch.object(release, "report") as report:
                        self.assertEqual(release.main(), 0)
        verify.assert_called_once_with(self.root)
        report.assert_called_once_with(result)


if __name__ == "__main__":
    unittest.main()
