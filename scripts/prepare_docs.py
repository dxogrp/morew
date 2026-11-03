"""Complete page-heading anchors in Verso 4.33.0 HTML."""

from html import escape
import json
from pathlib import Path
import re
import sys

from check_docs import Page


def prepare(root: Path) -> None:
    sections = json.loads((root / "xref.json").read_text())["Verso.Genre.Manual.section"]
    pages = {}
    for entries in sections["contents"].values():
        for entry in entries:
            previous = pages.get(entry["address"])
            if previous is None or len(entry["data"]["context"]) < len(previous["data"]["context"]):
                pages[entry["address"]] = entry
    for address, entry in pages.items():
        path = root / address.lstrip("/") / "index.html"
        if entry["id"] not in Page(path).ids:
            contents = path.read_text(encoding="utf-8")
            heading = f'<h1 id="{escape(entry["id"], quote=True)}">'
            updated, count = re.subn(
                r"(<main\b[^>]*>.*?)<h1>", lambda match: match[1] + heading,
                contents, count=1, flags=re.DOTALL,
            )
            if count != 1:
                raise ValueError(f"Missing page heading: {path}")
            path.write_text(updated, encoding="utf-8")


if __name__ == "__main__":
    prepare(Path(sys.argv[1]).resolve())
