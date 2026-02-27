#!/usr/bin/env sh
set -eu

DEMO_ROOT="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
REPO_ROOT="$(CDPATH= cd -- "$DEMO_ROOT/../.." && pwd)"
CRANE_ROOT="${CRANE_ROOT:-$REPO_ROOT/../crane}"
CXX="${CXX:-clang++}"

if [ ! -d "$CRANE_ROOT" ]; then
  echo "CRANE_ROOT does not exist: $CRANE_ROOT" >&2
  echo "Set CRANE_ROOT to your local Crane checkout path." >&2
  exit 2
fi

if [ ! -f "$DEMO_ROOT/gen/jsonpath_api.cpp" ] || [ ! -f "$DEMO_ROOT/gen/jsonpath_api.h" ]; then
  echo "Missing extracted API in demo/crane-cli/gen/. Run demo/crane-cli/build_cli_wsl.sh first." >&2
  exit 2
fi

mkdir -p "$DEMO_ROOT/bin"

"$CXX" -std=c++23 -O2 -fbracket-depth=1024 \
  -I"$DEMO_ROOT/gen" \
  -I"$DEMO_ROOT/src" \
  -I"$CRANE_ROOT/theories/cpp" \
  "$DEMO_ROOT/gen/jsonpath_api.cpp" \
  "$DEMO_ROOT/src/jsonpath_scroller_demo.cpp" \
  -o "$DEMO_ROOT/bin/jsonpath_scroller_demo"

echo "Built: $DEMO_ROOT/bin/jsonpath_scroller_demo"
