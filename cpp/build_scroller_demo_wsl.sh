#!/usr/bin/env sh
set -eu

ROOT="$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
CRANE_ROOT="${CRANE_ROOT:-$ROOT/../crane}"
CXX="${CXX:-clang++}"

if [ ! -d "$CRANE_ROOT" ]; then
  echo "CRANE_ROOT does not exist: $CRANE_ROOT" >&2
  echo "Set CRANE_ROOT to your local Crane checkout path." >&2
  exit 2
fi

if [ ! -f "$ROOT/cpp/gen/jsonpath_api.cpp" ] || [ ! -f "$ROOT/cpp/gen/jsonpath_api.h" ]; then
  echo "Missing extracted API in cpp/gen/. Run cpp/build_cli_wsl.sh first." >&2
  exit 2
fi

mkdir -p "$ROOT/cpp/bin"

"$CXX" -std=c++23 -O2 -fbracket-depth=1024 \
  -I"$ROOT/cpp/gen" \
  -I"$CRANE_ROOT/theories/cpp" \
  "$ROOT/cpp/gen/jsonpath_api.cpp" \
  "$ROOT/cpp/jsonpath_scroller_demo.cpp" \
  -o "$ROOT/cpp/bin/jsonpath_scroller_demo"

echo "Built: $ROOT/cpp/bin/jsonpath_scroller_demo"
