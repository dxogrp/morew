"""Check the generated documentation before publication."""

from __future__ import annotations

import argparse
from html.parser import HTMLParser
import os
from pathlib import Path
import re
import subprocess
import sys
from urllib.parse import unquote, urljoin, urlsplit


SITE_URL = "https://docs.invalid/morew/"
SOURCE_URL = "https://github.com/dxogrp/morew/"
MAX_SITE_BYTES = 1_000_000_000
VOID_TAGS = {"area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "param", "source", "track", "wbr"}


class CheckError(Exception):
    pass


class Page(HTMLParser):
    def __init__(self, path: Path, details: bool = True):
        super().__init__(convert_charrefs=True)
        self.path = path
        self.details = details
        self.base: str | None = None
        self.links: list[tuple[str, str]] = []
        self.ids: set[str] = set()
        self.source_links: list[str] = []
        self.repository_links: set[str] = set()
        self.contexts: list[tuple[str, bool]] = []

    def handle_starttag(self, tag, attrs):
        attributes = dict(attrs)
        for name, value in attrs:
            if value is None:
                continue
            if re.match(r"\s*(?:file|vscode(?:-insiders)?):", value, re.IGNORECASE):
                raise CheckError(f"Local source URL in {self.path}: {value}")
            if name in {"href", "src"} and value.startswith(SOURCE_URL):
                self.repository_links.add(value)
            if self.details and name in {"href", "src"} and tag != "base":
                self.links.append((name, value))
        if not self.details:
            return
        if tag == "base" and self.base is None:
            self.base = attributes.get("href")
        if attributes.get("id"):
            self.ids.add(attributes["id"])
        classes = set(attributes.get("class", "").split())
        source_context = bool(classes & {"gh_link", "gh_nav_link", "source_link"})
        source_context = source_context or bool(self.contexts and self.contexts[-1][1])
        if tag == "a" and attributes.get("href") and source_context:
            self.source_links.append(attributes["href"])
        if tag not in VOID_TAGS:
            self.contexts.append((tag, source_context))

    def handle_endtag(self, tag):
        for index in range(len(self.contexts) - 1, -1, -1):
            if self.contexts[index][0] == tag:
                del self.contexts[index:]
                break


def site_files(site_dir: Path) -> tuple[list[Path], int]:
    if site_dir.is_symlink():
        raise CheckError(f"Symbolic link in documentation: {site_dir}")
    if not site_dir.is_dir():
        raise CheckError(f"Documentation directory is missing: {site_dir}")
    files = []
    size = 0
    for directory, subdirs, names in os.walk(site_dir):
        for name in sorted(subdirs + names):
            path = Path(directory) / name
            if path.is_symlink():
                raise CheckError(f"Symbolic link in documentation: {path}")
        for name in sorted(names):
            path = Path(directory) / name
            size += path.stat().st_size
            files.append(path.relative_to(site_dir))
    if size > MAX_SITE_BYTES:
        raise CheckError(f"Documentation size {size:,} bytes exceeds {MAX_SITE_BYTES:,} bytes")
    return sorted(files), size


def local_target(url: str, site_dir: Path) -> tuple[Path, str] | None:
    parsed = urlsplit(url)
    if (parsed.scheme, parsed.netloc) != ("https", "docs.invalid"):
        return None
    if not parsed.path.startswith("/morew/"):
        raise CheckError(f"Link leaves the /morew/ site: {url}")
    target = site_dir / unquote(parsed.path[len("/morew/"):])
    if not target.resolve().is_relative_to(site_dir.resolve()):
        raise CheckError(f"Link leaves the documentation directory: {url}")
    if target.is_dir():
        target /= "index.html"
    return target.relative_to(site_dir), unquote(parsed.fragment)


def check_repository_link(url: str, root: Path, source_sha: str) -> None:
    parsed = urlsplit(url)
    parts = unquote(parsed.path).split("/")
    if len(parts) < 5 or parts[3] not in {"blob", "tree"}:
        return
    if parts[4] != source_sha:
        raise CheckError(f"Incorrect source commit: {url}")
    source = root.joinpath(*parts[5:])
    if not source.resolve().is_relative_to(root.resolve()) or not source.exists():
        raise CheckError(f"Source path does not exist: {url}")


def check_site(root: Path, site_dir: Path, source_sha: str) -> dict[str, str | int]:
    files, size = site_files(site_dir)
    for index in (Path("index.html"), Path("api/index.html")):
        if index not in files:
            raise CheckError(f"Missing documentation page: {index}")
    sources = {Path("Morew.lean")} | {
        path.relative_to(root) for path in (root / "Morew").rglob("*.lean")
    }
    if not (root / "Morew.lean").is_file():
        raise CheckError("Morew.lean is missing from the repository")
    expected = {Path("api") / path.with_suffix(".html"): path for path in sources}
    actual = {
        path for path in files if path == Path("api/Morew.html")
        or path.parts[:2] == ("api", "Morew") and path.suffix == ".html"
    }
    missing = sorted(expected.keys() - actual)
    extra = sorted(actual - expected.keys())
    if missing or extra:
        problems = []
        if missing:
            problems.append("missing: " + ", ".join(map(str, missing)))
        if extra:
            problems.append("unexpected: " + ", ".join(map(str, extra)))
        raise CheckError("Morew API pages do not match the source modules (" + "; ".join(problems) + ")")

    pages = {}
    for path in files:
        if path.suffix != ".html":
            continue
        details = path.parts[0] != "api" or path in expected
        page = Page(path, details)
        page.feed((site_dir / path).read_text(encoding="utf-8"))
        page.close()
        for url in page.repository_links:
            check_repository_link(url, root, source_sha)
        if details:
            pages[path] = page

    source_count = 0
    anchors = []
    for path, page in pages.items():
        page_url = urljoin(SITE_URL, path.as_posix())
        base_url = urljoin(page_url, page.base) if page.base else page_url
        if local_target(base_url, site_dir) is None:
            raise CheckError(f"External base URL in {path}: {page.base}")
        for attribute, value in page.links:
            target = local_target(urljoin(base_url, value), site_dir)
            if target is None:
                continue
            destination, fragment = target
            if not (site_dir / destination).is_file():
                raise CheckError(f"Missing link target in {path}: {value}")
            if path.parts[0] != "api" and attribute == "href" and fragment and destination.parts[0] == "api":
                anchors.append((path, destination, fragment))
        if path in expected:
            source_url = f"{SOURCE_URL}blob/{source_sha}/{expected[path].as_posix()}"
            for url in page.source_links:
                if url.split("#", 1)[0] != source_url:
                    raise CheckError(f"Incorrect source URL in {path}: {url}")
                source_count += 1
    if source_count == 0:
        raise CheckError("No Morew API source links were found")

    for origin, destination, fragment in anchors:
        if destination not in pages:
            page = Page(destination)
            page.feed((site_dir / destination).read_text(encoding="utf-8"))
            pages[destination] = page
        if fragment not in pages[destination].ids:
            raise CheckError(f"Missing API anchor from {origin}: {destination}#{fragment}")
    return {"source_sha": source_sha, "size_bytes": size, "modules": len(expected)}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--site-dir", type=Path, default=Path("build/docs"))
    parser.add_argument("--source-sha")
    args = parser.parse_args(argv)
    try:
        root = args.root.resolve()
        source_sha = args.source_sha or subprocess.run(
            ["git", "-C", str(root), "rev-parse", "HEAD"],
            check=True, capture_output=True, text=True,
        ).stdout.strip()
        if not re.fullmatch(r"[0-9a-f]{40}", source_sha):
            raise CheckError("The source commit must be a full Git commit SHA")
        result = check_site(root, root / args.site_dir, source_sha)
        message = (
            f"Documentation checked for {source_sha}: "
            f"{result['modules']} modules, {result['size_bytes']:,} bytes."
        )
        print(message)
        if summary := os.environ.get("GITHUB_STEP_SUMMARY"):
            with Path(summary).open("a", encoding="utf-8") as output:
                output.write(message + "\n")
    except (CheckError, OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"Documentation check failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
