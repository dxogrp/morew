"""Complete chapter anchors and namespace breadcrumbs in Verso 4.33.0 HTML."""

from html import escape, unescape
import json
from pathlib import Path
import re
import sys
from urllib.parse import unquote

from check_docs import Page


def prepare(root: Path) -> None:
    sections = json.loads((root / "xref.json").read_text())["Verso.Genre.Manual.section"]
    for entries in sections["contents"].values():
        for entry in entries:
            if len(entry["data"]["context"]) != 2:
                continue
            path = root / entry["address"].lstrip("/") / "index.html"
            if entry["id"] not in Page(path).ids:
                contents = path.read_text(encoding="utf-8")
                heading = f'<h1 id="{escape(entry["id"], quote=True)}">'
                updated, count = re.subn(
                    r"(<main\b[^>]*>.*?)<h1>", lambda match: match[1] + heading,
                    contents, count=1, flags=re.DOTALL,
                )
                if count != 1:
                    raise ValueError(f"Missing chapter heading: {path}")
                path.write_text(updated, encoding="utf-8")

    examples = root / "examples"

    def breadcrumb(match: re.Match) -> str:
        target = examples / unquote(unescape(match[1]))
        if target.is_dir() and not (target / "index.html").is_file():
            return f"<span>{match[2]}</span>"
        return match[0]

    for path in examples.rglob("*.html"):
        contents = path.read_text(encoding="utf-8")
        updated = re.sub(
            r'<ol class="breadcrumbs"[^>]*>.*?</ol>',
            lambda match: re.sub(r'<a href="([^"]+)">(.*?)</a>', breadcrumb,
                                 match[0], flags=re.DOTALL),
            contents, flags=re.DOTALL,
        )
        if updated != contents:
            path.write_text(updated, encoding="utf-8")


if __name__ == "__main__":
    prepare(Path(sys.argv[1]).resolve())
