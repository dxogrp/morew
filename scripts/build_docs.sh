#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
site_dir="$repo_root/build/docs"

cd "$repo_root/docs"
# Recheck source excerpts and render current comments on every documentation build.
rm -rf -- .lake/build/lib/lean/MorewManual .lake/build/literate
LAKE_ARTIFACT_CACHE=false lake build --wfail Examples:literate
LAKE_ARTIFACT_CACHE=false lake build --wfail morewManual
rm -rf -- .lake/build/manual
lake exe morewManual --output .lake/build/manual
rm -rf -- .lake/build/doc
rm -f -- .lake/build/doc-data/Morew--library.docs_built{,.trace,.hash}
rm -f -- .lake/build/doc-data/references.json{,.trace,.hash}
rm -f -- .lake/build/doc-data/declaration-data-*.bmp .lake/build/doc-data/backrefs-*.json
LAKE_ARTIFACT_CACHE=false DOCGEN_SRC=vscode lake build Morew:docs

mkdir -p "$repo_root/build"
staging_dir=$(mktemp -d "$repo_root/build/docs.XXXXXX")
trap 'rm -rf -- "$staging_dir"' EXIT
mkdir -p "$staging_dir/api" "$staging_dir/source"
cp -R .lake/build/manual/html-multi/. "$staging_dir/"
cp -R .lake/build/doc/. "$staging_dir/api/"
cp -R "$repo_root/Examples" "$staging_dir/source/"
rm -rf -- "$site_dir"
mv -- "$staging_dir" "$site_dir"
printf 'Documentation: %s/index.html\n' "$site_dir"
