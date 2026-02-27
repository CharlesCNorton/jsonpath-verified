# Crane C++ Demo

This demo is the most practical end-to-end runnable path for this project with the current Crane extraction toolchain.

## What it includes

- extracted API output in `cpp/gen/` (`jsonpath_api.h`, `jsonpath_api.cpp`)
- bridge layer in `cpp/jsonpath_bridge.{h,cpp}`
- CLI entrypoint in `cpp/jsonpath_cli.cpp`
- optional terminal scroller demo in `cpp/jsonpath_scroller_demo.cpp`

## Prerequisites

- a local Crane checkout with its Rocq plugin built
- Rocq 9 toolchain available in an opam switch (default: `vst216-rocq9`)
- C++23 compiler (`clang++` by default in the scripts)

## Build the CLI

From repository root:

```bash
CRANE_ROOT=/path/to/crane cpp/build_cli_wsl.sh
```

Output:

- `cpp/gen/jsonpath_api.h`
- `cpp/gen/jsonpath_api.cpp`
- `cpp/bin/jsonpath_cli`

## Run the CLI

Inline JSON:

```bash
./cpp/bin/jsonpath_cli --query '$.store.book[*].title' --json '{"store":{"book":[{"title":"A"},{"title":"B"}]}}'
```

From file:

```bash
./cpp/bin/jsonpath_cli --query '$.store.book[0].title' --json-file sample.json
```

The CLI prints a JSON array of matched values.

## Build the scroller demo

```bash
CRANE_ROOT=/path/to/crane cpp/build_scroller_demo_wsl.sh
./cpp/bin/jsonpath_scroller_demo
```

## Notes

- The query parser adapter currently covers common child/name/index/wildcard forms.
- Paths are intentionally parameterized via env vars to avoid machine-local path leakage.
