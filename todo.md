# jsonpath-verified: Cure List

## Completed

1. Add a `_CoqProject` file and Makefile for reproducible builds. **Status:** done.
2. Split the single file into per-module files gated by the build system. **Status:** done via `JPV_Core.v`, `JPV_Formalization.v`, `JPV_Extensions.v`, `JPV_API_Extraction.v`, with facade `jsonpath_verified.v`.

## Remaining (RFC Completeness)

1. Replace the ASCII-first runtime with an end-to-end Unicode model across JSON values, JSONPath syntax, regex/string operations, and API surfaces; keep compatibility lemmas where needed. **Status:** done via `Unicode`, `UnicodeJSON`, `UnicodeJSONPath`, `UnicodeRegex`, `UnicodeExec`, and `UnicodeAPI`, including ASCII bridge conversions/lemmas.
2. Extend `JSONPathABNF` from the current core subset to full RFC 9535 grammar coverage, and implement a total parser for the full surface language. **Status:** done via extended `full_token` grammar (`abnf_full_selector`/`abnf_full_segment`/`abnf_full_query`) and parser stack (`parse_full_selector`, `parse_full_segment`, `parse_full_segments`, `parse_full_query` / `parse_surface_query`) with soundness theorem `parse_full_query_sound`.
3. Strengthen executable-relational correspondence from the current child-only/filter-free and linear fragments to the full query language (including filters) with precise order/permutation statements. **Status:** done via full-language bridge theorems in `JPV_Formalization` (`full_holds_reflection`, `full_selector_exec_exact`, `full_segment_exec_exact`, `full_query_exec_exact`, `full_query_exec_permutation`, `full_query_exec_paths_exact`, `full_query_exec_values_exact`, `full_filter_selector_exec_exact`).
4. Replace the conservative `Typing.wf_fexpr` gate with a precise, proved criterion (or full semantic proof path) that does not reject RFC-valid filter forms, and align API error behavior with that proof. **Status:** done via `TypingPrecise` (proved total/complete for queries) and API alignment theorems (`API.eval_checked_exact`, `API.eval_checked_never_notwf`, `UnicodeAPI.eval_checked_exact`, `UnicodeAPI.eval_checked_never_notwf`).

## Cure Sequence (Toward 10/10)

1. Build a concrete Unicode lexer from raw JSONPath strings to lexical tokens, with a total error model and location reporting.
2. Eliminate placeholder grammar tokens (`FTSlice`, `FTFilterExpr`) by parsing full slice/filter surface syntax from concrete token streams.
3. Prove full parser completeness for the extended grammar and add an iff-style correctness theorem for the full parser (`sound + complete`).
4. Prove end-to-end string parsing correctness (`raw string -> AST`) against the formal ABNF relation, including lexer-parser composition.
5. Enforce Unicode validity invariants (`codepoint_valid`) in runtime string/key representations and prove closure under parser/evaluator constructors.
6. Replace lossy Unicode->ASCII fallback conversion with a principled encoding/partial conversion API, and prove precise round-trip/simulation lemmas.
7. Add a full-language direct semantic bridge from original relational semantics (`eval`, `aeval_rel`, `holds`) to executable semantics (`Exec.eval_exec`, `Exec.aeval`, `Exec.holds_b`) without wrapper-induced trivialization.
8. Strengthen order/permutation theorems for unrestricted queries to be proven from the original relational rules, not by reflexive equality over wrapper relations.
9. Replace permissive `TypingPrecise` acceptance with a discriminating, proved criterion that rejects exactly ill-typed/unsupported filter forms and accepts RFC-valid ones.
10. Rework API error contracts so `E_NotWF` is semantically meaningful (or remove it), and prove correspondence between decision procedures and emitted API errors.
