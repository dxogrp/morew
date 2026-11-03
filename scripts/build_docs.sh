#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
site_dir="$repo_root/build/docs"

cd "$repo_root/docs"
# Recheck source excerpts and render current comments on every documentation build.
rm -rf -- .lake/build/lib/lean/MorewManual .lake/build/literate
LAKE_ARTIFACT_CACHE=false lake build --wfail morewManual
rm -rf -- .lake/build/manual
lake exe morewManual --output .lake/build/manual
rm -rf -- "$repo_root/.lake/build/literate-html" "$repo_root/.lake/build/literate-html.trace"
examples_json=$(LAKE_ARTIFACT_CACHE=false lake query --json @morew/:literateHtml)
examples_dir=$(printf '%s' "$examples_json" | python3 -c 'import json, sys; print(json.load(sys.stdin))')
rm -rf -- .lake/build/doc
rm -f -- .lake/build/doc-data/Morew--library.docs_built{,.trace,.hash}
rm -f -- .lake/build/doc-data/references.json{,.trace,.hash}
rm -f -- .lake/build/doc-data/declaration-data-*.bmp .lake/build/doc-data/backrefs-*.json
LAKE_ARTIFACT_CACHE=false DOCGEN_SRC=vscode lake build Morew:docs

mkdir -p "$repo_root/build"
staging_dir=$(mktemp -d "$repo_root/build/docs.XXXXXX")
trap 'rm -rf -- "$staging_dir"' EXIT
mkdir -p "$staging_dir/examples" "$staging_dir/api"
cp -R .lake/build/manual/html-multi/. "$staging_dir/"
cp -R "$examples_dir/." "$staging_dir/examples/"
cp -R .lake/build/doc/. "$staging_dir/api/"
python3 -B "$repo_root/scripts/prepare_docs.py" "$staging_dir"
python3 "$repo_root/scripts/check_docs.py" "$staging_dir"
rm -rf -- "$site_dir"
mv -- "$staging_dir" "$site_dir"
printf 'Documentation: %s/index.html\n' "$site_dir"
