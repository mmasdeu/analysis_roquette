#!/bin/bash
# Builds the Verso companion book (Book/*.lean) into _out/html-multi.
# View it with: python3 -m http.server 8000 --directory _out/html-multi
set -e -o pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
lake build roquette-book
rm -rf _out
.lake/build/bin/roquette-book --output _out
echo "Book written to _out/html-multi"
