#!/usr/bin/env bash
set -euo pipefail

if [[ $# -gt 1 || ( $# -eq 1 && "${1:-}" != --update ) ]]; then
  printf 'Usage: %s [--update]\n' "$0" >&2
  exit 2
fi

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
site_dir="$repo_root/build/docs"

cd "$repo_root/docs"
# Recheck source excerpts and render current comments on every documentation build.
rm -rf -- .lake/build/lib/lean/MorewManual .lake/build/literate
LAKE_ARTIFACT_CACHE=false lake build --wfail Examples:literate
LAKE_ARTIFACT_CACHE=false lake build --wfail morewManual
rm -rf -- .lake/build/manual
lake exe morewManual --output .lake/build/manual
if [[ "${1:-}" == --update ]]; then
  api_dir="$site_dir/api"
else
  # Source URLs in the documentation database are not tracked by Lake.
  rm -rf -- .lake/build/doc .lake/build/doc-data
  rm -f -- .lake/build/api-docs.db .lake/build/api-docs.db-shm .lake/build/api-docs.db-wal
  LAKE_ARTIFACT_CACHE=false DOCGEN_SRC=github lake build Morew:docs
  api_dir="$repo_root/docs/.lake/build/doc"
fi

mkdir -p "$repo_root/build"
staging_dir=$(mktemp -d "$repo_root/build/docs.XXXXXX")
trap 'rm -rf -- "$staging_dir"' EXIT
mkdir -p "$staging_dir/api"
cp -R .lake/build/manual/html-multi/. "$staging_dir/"
if [[ -d "$api_dir" ]]; then
  cp -R "$api_dir/." "$staging_dir/api/"
fi
rm -rf -- "$site_dir"
mv -- "$staging_dir" "$site_dir"
printf 'Documentation: %s/index.html\n' "$site_dir"
