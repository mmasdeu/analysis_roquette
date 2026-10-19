#!/bin/bash
# Builds the Verso companion book (Book.lean, Book/*.lean) as literate Lean pages.
# View with: python3 -m http.server 8000 --directory "$(lake query :literateHtml)"
set -e -o pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
lake build Book
lake query :literateHtml
