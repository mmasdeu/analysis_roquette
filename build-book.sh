#!/bin/bash
# Builds the Verso companion book (Book.lean, Book/*.lean) as literate Lean pages.
# View with: python3 -m http.server 8000 --directory "$(lake query :literateHtml)"
set -e -o pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
lake build Book
out="$(lake query :literateHtml | tail -n 1)"
# Lake does not track the extra assets listed in literate.toml; refresh them explicitly.
cp book-assets/* "$out"/
echo "$out"
