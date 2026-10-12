#!/usr/bin/env bash
# Regenerates the certificate modules LiuIndex/Cert/*.lean and LiuIndex/Check/Defs.lean
# from scratch and compares them byte for byte with the committed files.
#   bash lean/generate/regenerate.sh
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LEAN="$(dirname "$HERE")"
CC="${CC:-gcc}"
PY="${PYTHON:-python3}"
command -v "$CC" >/dev/null || { echo "missing C compiler: $CC" >&2; exit 2; }
command -v "$PY" >/dev/null || { echo "missing Python: $PY" >&2; exit 2; }
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
mkdir -p "$TMP/streams"
"$CC" -O2 -fopenmp -o "$TMP/gen6" "$HERE/gen6.c"
"$TMP/gen6" "$TMP/streams"
(cd "$HERE" && "$PY" -B gen_cert.py "$TMP/streams" "$TMP/Cert")
"$PY" -B "$HERE/gen_defs.py" "$TMP/Defs.lean"
diff -r "$TMP/Cert" "$LEAN/LiuIndex/Cert"
cmp "$TMP/Defs.lean" "$LEAN/LiuIndex/Check/Defs.lean"
echo "certificate regenerated: identical to the committed files"
