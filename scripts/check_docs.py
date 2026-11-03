"""Check local links and assets referenced by Morew documentation pages."""

from functools import lru_cache
from html.parser import HTMLParser
from pathlib import Path
import sys
from urllib.parse import unquote, urljoin, urlsplit


class Page(HTMLParser):
    def __init__(self, path: Path):
        super().__init__(convert_charrefs=True)
        self.base = None
        self.ids = set()
        self.links = []
        self.feed(path.read_text(encoding="utf-8"))

    def handle_starttag(self, tag, attributes):
        attrs = dict(attributes)
        if "id" in attrs:
            self.ids.add(attrs["id"])
        if tag == "a" and "name" in attrs:
            self.ids.add(attrs["name"])
        if tag == "base":
            self.base = attrs.get("href")
        else:
            for name in ("href", "src"):
                if attrs.get(name):
                    self.links.append(attrs[name])


@lru_cache(maxsize=None)
def read_page(path: Path) -> Page:
    return Page(path)


def check(root: Path) -> list[str]:
    errors = []
    pages = []
    for path in root.rglob("*.html"):
        relative = path.relative_to(root)
        api_pages = {"Morew", "Morew.html", "find", "index.html", "navbar.html",
                     "search.html", "404.html", "foundational_types.html",
                     "references.html", "tactics.html"}
        if relative.parts[0] != "api" or relative.parts[1] in api_pages:
            pages.append(path)
    for path in sorted(pages):
        relative = path.relative_to(root)
        page = read_page(path)
        location = "http://docs.local/" + relative.as_posix()
        base = urljoin(location, page.base or "")
        for link in page.links:
            url = urlsplit(urljoin(base, link))
            if url.scheme not in ("http", "https") or url.netloc != "docs.local":
                continue
            target = root / unquote(url.path).lstrip("/")
            if target.is_dir():
                target /= "index.html"
            if not target.is_file():
                errors.append(f"{relative}: missing {link}")
            elif (url.fragment and unquote(url.fragment).lower() != "top"
                  and target.suffix == ".html"):
                if unquote(url.fragment) not in read_page(target).ids:
                    errors.append(f"{relative}: missing fragment in {link}")
    print(f"Checked links and assets in {len(pages)} Morew documentation pages.")
    return errors


def main() -> int:
    if len(sys.argv) != 2:
        print("Usage: python3 scripts/check_docs.py SITE_DIRECTORY", file=sys.stderr)
        return 2
    root = Path(sys.argv[1]).resolve()
    if not (root / "index.html").is_file():
        print(f"Missing documentation index: {root / 'index.html'}", file=sys.stderr)
        return 1
    errors = check(root)
    for error in errors:
        print(error, file=sys.stderr)
    return int(bool(errors))


if __name__ == "__main__":
    raise SystemExit(main())
