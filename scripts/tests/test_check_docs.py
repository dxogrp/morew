"""Tests for documentation publication checks."""

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
SPEC = importlib.util.spec_from_file_location("check_docs", SCRIPTS / "check_docs.py")
assert SPEC is not None and SPEC.loader is not None
docs = importlib.util.module_from_spec(SPEC)
with patch.object(sys, "path", [str(SCRIPTS), *sys.path]):
    SPEC.loader.exec_module(docs)

SHA = "a" * 40
SOURCE = f"https://github.com/dxogrp/morew/blob/{SHA}/Demo.lean"
SITE = "https://dxogrp.github.io/morew/"
REPOSITORY = "dxogrp/morew"
RUN_URL = f"https://github.com/{REPOSITORY}/actions/runs/123"


class SiteTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.site = self.root / "build/docs"
        self.write(self.root / "Demo.lean", "def answer := 42\n")
        self.write(self.site / "index.html", '<a href="guide/">Guide</a>')
        self.write(self.site / "guide/index.html", (
            '<base href="../"><link href="style.css" rel="stylesheet">'
            '<a href="api/example.html#answer">API</a>'
        ))
        self.write(self.site / "style.css", "body {}")
        self.write(self.site / "api/index.html", "API")
        self.write(self.site / "api/example.html", (
            f'<a href="{SOURCE}">View file</a><div id="answer"></div>'
            '<a href="#source">source</a>'
            '<a href="dependency.html#generated-fragment">Dependency</a>'
        ))
        self.write(self.site / "api/dependency.html", '<a href="unavailable.html">Generated reference</a>')

    def write(self, path, text):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def check(self):
        return docs.check_site(self.root, self.site, SHA)

    def test_accepts_new_pages_and_sources_without_a_fixed_inventory(self):
        self.assertGreater(self.check(), 0)
        self.write(self.root / "Extra/Notes.lean", "def other := 7\n")
        self.write(self.site / "api/new-page.html", (
            f'<a href="{SOURCE.replace("Demo.lean", "Extra/Notes.lean")}">File</a>'
            '<div id="other"></div>'
        ))
        self.write(self.site / "api/diagram.svg", '<svg xmlns="http://www.w3.org/2000/svg" id="figure"/>')
        self.write(self.site / "new-chapter.html", (
            '<a href="api/new-page.html#other">New example</a>'
            '<a href="api/diagram.svg#figure">Diagram</a>'
            '<a href="https://dxogrp.github.io/dbcp/">DBCP</a>'
            '<a href="//dxogrp.github.io/blvpy/">BLVpy</a>'
        ))
        self.check()

    def test_missing_landing_pages_and_link_targets(self):
        for name in ("index.html", "api/index.html", "guide/index.html", "api/example.html", "style.css"):
            with self.subTest(name=name):
                path = self.site / name
                content = path.read_text()
                path.unlink()
                with self.assertRaises(docs.VerificationError):
                    self.check()
                self.write(path, content)

    def test_relative_and_public_urls_check_pages_and_declaration_anchors(self):
        guide = self.site / "guide/index.html"
        for prefix in ("", "/morew/", SITE):
            with self.subTest(prefix=prefix):
                self.write(guide, f'<base href="../"><a href="{prefix}api/example.html#answer">API</a>')
                self.check()
                for target in ("api/absent.html", "api/example.html#absent"):
                    self.write(guide, f'<base href="../"><a href="{prefix}{target}">API</a>')
                    with self.assertRaises(docs.VerificationError):
                        self.check()

    def test_base_urls_and_links_remain_under_the_site_path(self):
        guide = self.site / "guide/index.html"
        self.write(guide, '<base href="/morew/"><a href="api/example.html#answer">API</a>')
        self.check()
        for content in (
            '<base href="/"><a href="style.css">Style</a>',
            '<a href="/morew/%2e%2e/style.css">Style</a>',
        ):
            self.write(guide, content)
            with self.subTest(content=content), self.assertRaises(docs.VerificationError):
                self.check()

    def test_source_links_use_the_current_commit_and_existing_paths(self):
        page = self.site / "api/example.html"
        original = page.read_text()
        for source in (SOURCE.replace(SHA, "b" * 40), SOURCE.replace("Demo.lean", "Absent.lean")):
            self.write(page, original.replace(SOURCE, source))
            with self.subTest(source=source), self.assertRaises(docs.VerificationError):
                self.check()

    def test_api_requires_a_file_source_link(self):
        page = self.site / "api/example.html"
        original = page.read_text()
        for source in ("https://github.com/dxogrp/morew", f"https://github.com/dxogrp/morew/tree/{SHA}"):
            self.write(page, original.replace(SOURCE, source))
            with self.subTest(source=source), self.assertRaises(docs.VerificationError):
                self.check()

    def test_local_source_urls_are_rejected_in_dependency_pages(self):
        for url in ("file:///tmp/source.lean", "vscode://file/tmp/source.lean", "vscode-insiders://file/tmp/source.lean"):
            self.write(self.site / "api/dependency.html", f'<a href="{url}">Source</a>')
            with self.subTest(url=url), self.assertRaises(docs.VerificationError):
                self.check()

    def test_symlinks_are_rejected(self):
        for target in (self.site / "style.css", self.site / "guide"):
            link = self.site / "linked"
            link.symlink_to(target, target_is_directory=target.is_dir())
            with self.subTest(target=target), self.assertRaises(docs.VerificationError):
                self.check()
            link.unlink()

    def test_size_limit_includes_the_boundary(self):
        size = self.check()
        with patch.object(docs, "MAX_SITE_BYTES", size):
            self.check()
        with patch.object(docs, "MAX_SITE_BYTES", size - 1):
            with self.assertRaises(docs.VerificationError):
                self.check()

    def test_site_command_reports_commit_and_size(self):
        output = io.StringIO()
        summary = self.root / "summary"
        with patch.dict(os.environ, {"GITHUB_STEP_SUMMARY": str(summary)}):
            with patch.object(docs, "resolve_commit", return_value=SHA), chdir(self.root), redirect_stdout(output):
                self.assertEqual(docs.main(["site"]), 0)
        self.assertIn(SHA, output.getvalue())
        self.assertIn("bytes", output.getvalue())
        self.assertIn(SHA, summary.read_text())


class CiTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.git("init", "-q", "--initial-branch=main")
        self.git("config", "user.email", "test@example.invalid")
        self.git("config", "user.name", "Documentation Test")
        self.git("commit", "--allow-empty", "-qm", "Initial")
        self.git("tag", "v1.2.3")
        self.sha = self.git("rev-parse", "HEAD")
        environment = patch.dict(os.environ, {
            "GITHUB_REPOSITORY": REPOSITORY,
            "GITHUB_EVENT_NAME": "workflow_dispatch",
            "GITHUB_REF": "refs/heads/main",
            "GITHUB_SHA": self.sha,
        })
        environment.start()
        self.addCleanup(environment.stop)
        api = patch.object(docs, "fetch_workflow_runs", return_value=[{
            "id": 123, "run_number": 10, "run_attempt": 1,
            "repository": {"full_name": REPOSITORY},
            "path": ".github/workflows/ci.yml", "head_sha": self.sha,
            "head_branch": "main", "event": "push",
            "status": "completed", "conclusion": "success",
        }])
        self.fetch = api.start()
        self.addCleanup(api.stop)

    def git(self, *args):
        return subprocess.run(
            ["git", *args], cwd=self.root, check=True, capture_output=True, text=True
        ).stdout.strip()

    def test_checks_the_selected_commit_without_release_requirements(self):
        self.assertEqual(docs.check_ci(self.root), {
            "source_sha": self.sha, "verification_run_url": RUN_URL,
        })
        self.fetch.assert_called_once_with(REPOSITORY, "ci.yml", self.sha, "push")
        self.assertEqual(self.git("rev-parse", "v1.2.3"), self.sha)

    def test_rejects_other_refs_events_and_checkouts_before_querying_ci(self):
        for variable, value in (
            ("GITHUB_REF", "refs/heads/topic"),
            ("GITHUB_EVENT_NAME", "push"),
            ("GITHUB_SHA", "b" * 40),
        ):
            with self.subTest(variable=variable), patch.dict(os.environ, {variable: value}):
                with self.assertRaises(docs.VerificationError):
                    docs.check_ci(self.root)
        self.fetch.assert_not_called()

    def test_ci_command_reports_metadata_and_returns_failure_when_ci_fails(self):
        output = self.root / "output"
        summary = self.root / "summary"
        with patch.dict(os.environ, {"GITHUB_OUTPUT": str(output), "GITHUB_STEP_SUMMARY": str(summary)}):
            with chdir(self.root), redirect_stdout(io.StringIO()):
                self.assertEqual(docs.main(["ci"]), 0)
        metadata = dict(line.split("=", 1) for line in output.read_text().splitlines())
        self.assertEqual(metadata, {"source_sha": self.sha, "verification_run_url": RUN_URL})
        self.assertIn(self.sha, summary.read_text())
        self.assertIn(RUN_URL, summary.read_text())
        self.fetch.return_value[0]["conclusion"] = "failure"
        with chdir(self.root), redirect_stderr(io.StringIO()):
            self.assertEqual(docs.main(["ci"]), 1)


if __name__ == "__main__":
    unittest.main()
