"""Tests for documentation pages, links, and publication limits."""

from __future__ import annotations

from contextlib import redirect_stdout
import importlib.util
import io
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch


SPEC = importlib.util.spec_from_file_location(
    "check_docs", Path(__file__).resolve().parents[1] / "check_docs.py"
)
assert SPEC is not None and SPEC.loader is not None
docs = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(docs)

SHA = "a" * 40
SOURCE = f"https://github.com/dxogrp/morew/blob/{SHA}/Morew/Core.lean"


class DocumentationTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        self.site = self.root / "build/docs"
        self.write(self.root / "Morew.lean", "import Morew.Core\n")
        self.write(self.root / "Morew/Core.lean", "namespace Morew\n")
        self.write(self.site / "index.html", '<a href="guide/">Guide</a>')
        self.write(self.site / "guide/index.html", (
            '<base href="../"><link href="style.css" rel="stylesheet">'
            '<a href="api/Morew/Core.html#Morew.value">API</a>'
        ))
        self.write(self.site / "style.css", "body {}")
        self.write(self.site / "api/index.html", "API")
        self.write(self.site / "api/Morew.html", '<a href="Morew/Core.html">Core</a>')
        self.write(self.site / "api/Morew/Core.html", (
            f'<p class="gh_nav_link"><a href="{SOURCE}">source</a></p>'
            '<div id="Morew.value"></div>'
            f'<div class="gh_link"><a href="{SOURCE}#L1-L2">source</a></div>'
            '<a href="#Morew.source">source</a>'
            '<a href="../Mathlib/Test.html#generated-fragment">Mathlib</a>'
        ))
        self.write(self.site / "api/Mathlib/Test.html", (
            '<a href="missing-dependency-page.html#missing">Generated reference</a>'
        ))

    def write(self, path, text):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def check(self):
        return docs.check_site(self.root, self.site, SHA)

    def replace(self, path, old, new):
        full_path = self.site / path
        self.write(full_path, full_path.read_text().replace(old, new))

    def test_checks_site_and_allows_empty_module_pages(self):
        result = self.check()
        self.assertEqual(result["source_sha"], SHA)
        self.assertEqual(result["modules"], 2)
        self.assertGreater(result["size_bytes"], 0)

    def test_missing_required_indexes(self):
        for index in ("index.html", "api/index.html"):
            with self.subTest(index=index):
                path = self.site / index
                text = path.read_text()
                path.unlink()
                with self.assertRaisesRegex(docs.CheckError, "Missing documentation page"):
                    self.check()
                self.write(path, text)

    def test_missing_module_page(self):
        (self.site / "api/Morew/Core.html").unlink()
        with self.assertRaisesRegex(docs.CheckError, "missing: api/Morew/Core.html"):
            self.check()

    def test_retired_module_page(self):
        self.write(self.site / "api/Morew/Old.html", "Old module")
        with self.assertRaisesRegex(docs.CheckError, "unexpected: api/Morew/Old.html"):
            self.check()

    def test_missing_local_page_and_asset(self):
        for path in ("guide/index.html", "style.css"):
            with self.subTest(path=path):
                target = self.site / path
                text = target.read_text()
                target.unlink()
                with self.assertRaisesRegex(docs.CheckError, "Missing link target"):
                    self.check()
                self.write(target, text)

    def test_missing_explicit_api_anchor(self):
        self.replace("guide/index.html", "#Morew.value", "#Morew.absent")
        with self.assertRaisesRegex(docs.CheckError, "Missing API anchor"):
            self.check()

    def test_subpath_base_url_and_absolute_links(self):
        self.replace("guide/index.html", 'href="../"', 'href="/morew/"')
        self.replace("api/Morew.html", 'href="Morew/Core.html"', 'href="/morew/api/Morew/Core.html"')
        self.check()

    def test_root_link_outside_subpath(self):
        self.replace("guide/index.html", 'href="../"', 'href="/"')
        with self.assertRaisesRegex(docs.CheckError, "leaves the /morew/ site"):
            self.check()

    def test_stale_source_commit(self):
        self.replace("api/Morew/Core.html", SHA, "b" * 40)
        with self.assertRaisesRegex(docs.CheckError, "Incorrect source commit"):
            self.check()

    def test_wrong_source_module(self):
        self.replace("api/Morew/Core.html", "/Morew/Core.lean", "/Morew.lean")
        with self.assertRaisesRegex(docs.CheckError, "Incorrect source URL"):
            self.check()

    def test_source_class_without_label(self):
        self.write(self.site / "api/Morew/Core.html", (
            f'<a class="source_link" href="{SOURCE}">View</a>'
            '<div id="Morew.value"></div>'
        ))
        self.check()

    def test_missing_source_links(self):
        self.write(self.site / "api/Morew/Core.html", '<div id="Morew.value"></div>')
        with self.assertRaisesRegex(docs.CheckError, "No Morew API source links"):
            self.check()

    def test_local_urls_in_dependency_html(self):
        for url in ("file:///tmp/source.lean", "vscode://file/tmp/source.lean"):
            with self.subTest(url=url):
                self.write(self.site / "api/Mathlib/Test.html", f'<a href="{url}">source</a>')
                with self.assertRaisesRegex(docs.CheckError, "Local source URL"):
                    self.check()

    def test_symlinks(self):
        for target in (self.site / "style.css", self.site / "guide"):
            link = self.site / "linked"
            link.symlink_to(target, target_is_directory=target.is_dir())
            with self.subTest(target=target), self.assertRaisesRegex(docs.CheckError, "Symbolic link"):
                self.check()
            link.unlink()

    def test_size_limit(self):
        size = self.check()["size_bytes"]
        with patch.object(docs, "MAX_SITE_BYTES", size):
            self.check()
        with patch.object(docs, "MAX_SITE_BYTES", size - 1):
            with self.assertRaisesRegex(docs.CheckError, "exceeds"):
                self.check()

    def test_cli_reports_commit_size_and_summary(self):
        output = io.StringIO()
        summary = self.root / "summary.txt"
        with patch.dict(os.environ, {"GITHUB_STEP_SUMMARY": str(summary)}), redirect_stdout(output):
            result = docs.main(["--root", str(self.root), "--source-sha", SHA])
        self.assertEqual(result, 0)
        self.assertIn(SHA, output.getvalue())
        self.assertIn("bytes", output.getvalue())
        self.assertEqual(summary.read_text(), output.getvalue())


if __name__ == "__main__":
    unittest.main()
