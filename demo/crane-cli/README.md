# Crane C++ Demo

This demo is the most practical end-to-end runnable path for this project with the current Crane extraction toolchain.

## What it includes

- extraction directives in `demo/crane-cli/extraction/`
- extracted API output in `demo/crane-cli/gen/` (`jsonpath_api.h`, `jsonpath_api.cpp`)
- bridge layer in `demo/crane-cli/src/jsonpath_bridge.{h,cpp}`
- CLI entrypoint in `demo/crane-cli/src/jsonpath_cli.cpp`
- optional terminal scroller demo in `demo/crane-cli/src/jsonpath_scroller_demo.cpp`

## Prerequisites

- a local Crane checkout with its Rocq plugin built
- Rocq 9 toolchain available in an opam switch (default: `vst216-rocq9`)
- C++23 compiler (`clang++` by default in the scripts)

## Build the CLI

From repository root:

```bash
CRANE_ROOT=/path/to/crane demo/crane-cli/build_cli_wsl.sh
```

Output:

- `demo/crane-cli/gen/jsonpath_api.h`
- `demo/crane-cli/gen/jsonpath_api.cpp`
- `demo/crane-cli/bin/jsonpath_cli`

## Run the CLI

Inline JSON:

```bash
./demo/crane-cli/bin/jsonpath_cli --query '$.store.book[*].title' --json '{"store":{"book":[{"title":"A"},{"title":"B"}]}}'
```

From file:

```bash
./demo/crane-cli/bin/jsonpath_cli --query '$.store.book[0].title' --json-file sample.json
```

The CLI prints a JSON array of matched values.

## Build the scroller demo

```bash
CRANE_ROOT=/path/to/crane demo/crane-cli/build_scroller_demo_wsl.sh
./demo/crane-cli/bin/jsonpath_scroller_demo
```

## Notes

- The query parser adapter currently covers common child/name/index/wildcard forms.
- Paths are intentionally parameterized via env vars to avoid machine-local path leakage.
