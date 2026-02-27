#!/usr/bin/env sh
set -eu

DEMO_ROOT="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
REPO_ROOT="$(CDPATH= cd -- "$DEMO_ROOT/../.." && pwd)"
TMP_BUILD="/tmp/jpv_cli_build_eval"
SWITCH="${OPAM_SWITCH:-vst216-rocq9}"
CRANE_ROOT="${CRANE_ROOT:-$REPO_ROOT/../crane}"
CXX="${CXX:-clang++}"

if [ ! -d "$CRANE_ROOT" ]; then
  echo "CRANE_ROOT does not exist: $CRANE_ROOT" >&2
  echo "Set CRANE_ROOT to your local Crane checkout path." >&2
  exit 2
fi

rm -rf "$TMP_BUILD"
mkdir -p "$TMP_BUILD/theories" "$TMP_BUILD/extraction" "$TMP_BUILD/demo/crane-cli/gen"
cp "$REPO_ROOT/theories/"*.v "$TMP_BUILD/theories/"
cp "$DEMO_ROOT/extraction/jpv_crane_extract_eval.v" "$TMP_BUILD/extraction/"

cd "$TMP_BUILD"
opam exec --switch="$SWITCH" -- coqc -q -Q theories '' theories/JPV_Core.v
opam exec --switch="$SWITCH" -- coqc -q -Q theories '' theories/JPV_Formalization.v
opam exec --switch="$SWITCH" -- coqc -q -Q theories '' theories/JPV_Extensions.v
opam exec --switch="$SWITCH" -- coqc -q -Q theories '' theories/JPV_API_Extraction.v
opam exec --switch="$SWITCH" -- env OCAMLPATH="$CRANE_ROOT/_build/install/default/lib" \
  coqc -q -Q theories '' -R "$CRANE_ROOT/_build/default/theories" Crane \
  extraction/jpv_crane_extract_eval.v

mkdir -p "$DEMO_ROOT/gen" "$DEMO_ROOT/bin"
cp "$TMP_BUILD/demo/crane-cli/gen/jsonpath_api.h" "$DEMO_ROOT/gen/jsonpath_api.h"
cp "$TMP_BUILD/demo/crane-cli/gen/jsonpath_api.cpp" "$DEMO_ROOT/gen/jsonpath_api.cpp"

"$CXX" -std=c++23 -O2 -fbracket-depth=1024 \
  -I"$DEMO_ROOT/gen" \
  -I"$DEMO_ROOT/src" \
  -I"$CRANE_ROOT/theories/cpp" \
  "$DEMO_ROOT/gen/jsonpath_api.cpp" \
  "$DEMO_ROOT/src/jsonpath_bridge.cpp" \
  "$DEMO_ROOT/src/jsonpath_cli.cpp" \
  -o "$DEMO_ROOT/bin/jsonpath_cli"

echo "Built: $DEMO_ROOT/bin/jsonpath_cli"
