# jsonpath-verified

Mechanized JSONPath (RFC 9535) semantics in Coq/Rocq, with executable evaluators, parser and lexer layers, Unicode support, proof correspondence results, and OCaml extraction.

## Repository layout

- `JPV_Core.v`: base data model, JSONPath AST, slice/index machinery, regex engine, relational semantics, executable semantics, and core soundness/completeness bridges.
- `JPV_Formalization.v`: higher-level equivalence and closure theorems, unrestricted direct reflection modules, typing layers (`Typing`, `TypingPrecise`), and extensive semantic invariants/regressions.
- `JPV_Extensions.v`: Unicode model and conversion lemmas, ABNF relations and parsers (token-level and concrete surface), lexer, parser correctness theorems, and property suites.
- `JPV_API_Extraction.v`: user-facing API modules (`API`, `UnicodeAPI`) plus extraction directives.
- `jsonpath_verified.v`: facade that re-exports all modules above.
- `quickchick_run.v`: QuickChick entry file.
- `proof_hygiene.py`: guard that rejects `Admitted` and `Axiom`.
- `_CoqProject`, `Makefile`: build configuration.

## What is formalized

### JSON and JSONPath core

`JPV_Core.v` defines:

- JSON values: null, bool, rational numbers (`Q`), strings, arrays, objects.
- Paths and nodes (`path * value`) with normalized step/path predicates.
- JSONPath syntax: selectors, segments (`Child`, `Desc`), queries, arithmetic/filter expressions, and regex syntax.
- Slice normalization and index handling over `Z`, including negative indices and signed steps.

### Regex engine

`Regex` is a total derivative-based matcher (Brzozowski derivatives with simplification), with:

- `regex_match` and `regex_search`.
- semantic language relation `lang`.
- soundness/completeness/correctness theorems for matching.

### Relational semantics

Core relations include:

- `eval_selector`
- `visit_order`
- `eval_seg`
- `eval`
- `aeval_rel`
- `holds`

These encode permutation-aware object behavior and ordered array behavior aligned with RFC-level intent.

### Executable semantics

`Exec` defines total evaluators:

- filter-free path: `sel_exec_nf`, `eval_exec_nf`
- full path with filters: `sel_exec`, `eval_exec`
- arithmetic/filter evaluators: `aeval`, `holds_b`

Relational wrappers and bridges are provided via:

- `eval_exec_rel`, `aeval_rel_exec`, `holds_exec`
- reflection/equivalence theorems in both core and formalization layers.

## Proof landscape

`JPV_Formalization.v` provides:

- full query/segment/selector executable-relational correspondence theorems.
- order and permutation transfer theorems over unrestricted and child-only fragments.
- direct unrestricted reflection module (`DirectUnrestricted`) for `eval`, `aeval_rel`, and `holds`.
- linear-fragment exactness/arity properties and closure lemmas used by API contracts.
- typing safety layers:
  - `Typing`: coarse predicate family.
  - `TypingPrecise`: discriminating well-formedness checks for filters/regex/slices with proved properties.

## Unicode, grammar, and concrete parsing

`JPV_Extensions.v` adds:

- Unicode model (`codepoint`, `ustring`) and validity predicates.
- Unicode JSON/JSONPath/Regex/Exec layers.
- total partial-conversion API (`*_opt`) with round-trip/simulation theorems.
- ABNF relations and parsers:
  - token-level core and full grammars (`abnf_query`, `abnf_full_query`, etc.).
- concrete lexer/parser pipeline from raw Unicode strings:
  - `lex_surface`
  - `parse_surface_query_string`
  - soundness/completeness/correctness theorems (`*_sound`, `*_complete`, `*_correct`).

## API surface

`JPV_API_Extraction.v` exports:

- `API` (ASCII JSONPath/JSON):
  - `eval_checked`
  - `eval_nf_checked`
  - `eval_one_linear`
  - typed error model (`E_NotWF`, `E_NotChildOnly`, `E_NotLinear`, `E_NotFound`, `E_Multiple`)
  - path/value projections (`paths_of`, `values_of`)
- `UnicodeAPI` equivalents for Unicode query/value domains.
- theorem-level correspondence between API errors and decision procedures (`*_iff` and exactness lemmas).

## Property suites

`PropertySuite` (in `JPV_Extensions.v`) includes:

- core invariants for linearity, wildcard cardinality, and descendant superset behavior.
- regex `search`/`match` consistency checks.
- concrete parse+eval vectors and AST differential vectors.
- parse-error vector checks.
- aggregate suite theorem `quickchick_extended_suite_passes`.

## Build

Prerequisites:

- Rocq/Coq toolchain (8.20-class environment).
- Standard library dependencies used in the files (`List`, `String`, `ZArith`, `QArith`, `Permutation`, etc.).
- Optional: QuickChick for randomized property runs.
- Optional: OCaml toolchain for extracted artifacts.

Build with make:

```bash
make regen
make
```

Run proof hygiene:

```bash
make proof-hygiene
```

Raw compilation order (no filtering):

```bash
coqc -q JPV_Core.v
coqc -q JPV_Formalization.v
coqc -q JPV_Extensions.v
coqc -q JPV_API_Extraction.v
coqc -q jsonpath_verified.v
```

## Extraction

Compiling `JPV_API_Extraction.v` runs extraction directives and emits OCaml modules for:

- `JSON`
- `JSONPath`
- `Regex`
- `Exec`
- `Typing`
- Unicode and Unicode API layers
- example documents (`company_json`, `acme_db_json`)

Extraction is configured for exact arithmetic and total evaluator paths.
