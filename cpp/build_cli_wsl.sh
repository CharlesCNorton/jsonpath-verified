#!/usr/bin/env sh
set -eu

ROOT="$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
TMP_BUILD="/tmp/jpv_cli_build_eval"
SWITCH="${OPAM_SWITCH:-vst216-rocq9}"
CRANE_ROOT="${CRANE_ROOT:-$ROOT/../crane}"
CXX="${CXX:-clang++}"

if [ ! -d "$CRANE_ROOT" ]; then
  echo "CRANE_ROOT does not exist: $CRANE_ROOT" >&2
  echo "Set CRANE_ROOT to your local Crane checkout path." >&2
  exit 2
fi

rm -rf "$TMP_BUILD"
mkdir -p "$TMP_BUILD/theories" "$TMP_BUILD/scripts" "$TMP_BUILD/cpp/gen"
cp "$ROOT/theories/"*.v "$TMP_BUILD/theories/"
cp "$ROOT/scripts/jpv_crane_extract_eval.v" "$TMP_BUILD/scripts/"

cd "$TMP_BUILD"
opam exec --switch="$SWITCH" -- coqc -q -Q theories '' theories/JPV_Core.v
opam exec --switch="$SWITCH" -- coqc -q -Q theories '' theories/JPV_Formalization.v
opam exec --switch="$SWITCH" -- coqc -q -Q theories '' theories/JPV_Extensions.v
opam exec --switch="$SWITCH" -- coqc -q -Q theories '' theories/JPV_API_Extraction.v
opam exec --switch="$SWITCH" -- env OCAMLPATH="$CRANE_ROOT/_build/install/default/lib" \
  coqc -q -Q theories '' -R "$CRANE_ROOT/_build/default/theories" Crane \
  scripts/jpv_crane_extract_eval.v

mkdir -p "$ROOT/cpp/gen" "$ROOT/cpp/bin"
cp "$TMP_BUILD/cpp/gen/jsonpath_api.h" "$ROOT/cpp/gen/jsonpath_api.h"
cp "$TMP_BUILD/cpp/gen/jsonpath_api.cpp" "$ROOT/cpp/gen/jsonpath_api.cpp"

"$CXX" -std=c++23 -O2 -fbracket-depth=1024 \
  -I"$ROOT/cpp/gen" \
  -I"$CRANE_ROOT/theories/cpp" \
  "$ROOT/cpp/gen/jsonpath_api.cpp" \
  "$ROOT/cpp/jsonpath_bridge.cpp" \
  "$ROOT/cpp/jsonpath_cli.cpp" \
  -o "$ROOT/cpp/bin/jsonpath_cli"

echo "Built: $ROOT/cpp/bin/jsonpath_cli"
