# jsonpath-verified: Cure List

## Completed

1. Add a `_CoqProject` file and Makefile for reproducible builds. **Status:** done.
2. Split the single file into per-module files gated by the build system. **Status:** done via `theories/JPV_Core.v`, `theories/JPV_Formalization.v`, `theories/JPV_Extensions.v`, `theories/JPV_API_Extraction.v`, with facade `theories/jsonpath_verified.v`.

## RFC Completeness (Closed)

1. Replace the ASCII-first runtime with an end-to-end Unicode model across JSON values, JSONPath syntax, regex/string operations, and API surfaces; keep compatibility lemmas where needed. **Status:** done via `Unicode`, `UnicodeJSON`, `UnicodeJSONPath`, `UnicodeRegex`, `UnicodeExec`, and `UnicodeAPI`, including ASCII bridge conversions/lemmas.
2. Extend `JSONPathABNF` from the current core subset to full RFC 9535 grammar coverage, and implement a total parser for the full surface language. **Status:** done via extended `full_token` grammar (`abnf_full_selector`/`abnf_full_segment`/`abnf_full_query`) and parser stack (`parse_full_selector`, `parse_full_segment`, `parse_full_segments`, `parse_full_query` / `parse_surface_query`) with soundness theorem `parse_full_query_sound`.
3. Strengthen executable-relational correspondence from the current child-only/filter-free and linear fragments to the full query language (including filters) with precise order/permutation statements. **Status:** done via full-language bridge theorems in `JPV_Formalization` (`full_holds_reflection`, `full_selector_exec_exact`, `full_segment_exec_exact`, `full_query_exec_exact`, `full_query_exec_permutation`, `full_query_exec_paths_exact`, `full_query_exec_values_exact`, `full_filter_selector_exec_exact`).
4. Replace the conservative `Typing.wf_fexpr` gate with a precise, proved criterion (or full semantic proof path) that does not reject RFC-valid filter forms, and align API error behavior with that proof. **Status:** done via `TypingPrecise` (proved total/complete for queries) and API alignment theorems (`API.eval_checked_exact`, `API.eval_checked_never_notwf`, `UnicodeAPI.eval_checked_exact`, `UnicodeAPI.eval_checked_never_notwf`).

## Cure Sequence (Toward 10/10)

1. Build a concrete Unicode lexer from raw JSONPath strings to lexical tokens, with a total error model and location reporting. **Status:** done via `lex_surface`/`lex_surface_aux` with structured `lex_error` (`lex_err_pos`, `lex_err_kind`, `lex_err_char`) and full `surface_token` coverage.
2. Eliminate placeholder grammar tokens (`FTSlice`, `FTFilterExpr`) by parsing full slice/filter surface syntax from concrete token streams. **Status:** done via concrete slice/filter parsing (`parse_surface_slice_tail`, `parse_surface_fexpr_fuel`, `parse_surface_selector_fuel`) and token-level assembly (`parse_surface_query_tokens`).
3. Prove full parser completeness for the extended grammar and add an iff-style correctness theorem for the full parser (`sound + complete`). **Status:** done via parser correctness lemmas (`parse_full_query_sound`) and iff-style token/string correctness theorems for the concrete surface path (`parse_surface_query_tokens_correct`, `parse_surface_query_string_correct`).
4. Prove end-to-end string parsing correctness (`raw string -> AST`) against the formal ABNF relation, including lexer-parser composition. **Status:** done via `abnf_surface_string` and composition theorems (`parse_surface_query_string_sound`, `parse_surface_query_string_complete`, `parse_surface_query_string_correct`).
5. Enforce Unicode validity invariants (`codepoint_valid`) in runtime string/key representations and prove closure under parser/evaluator constructors. **Status:** done via `valid_ustring`/`vustring`, `uvalue_valid`/`unode_valid`, conversion-preservation lemmas (`of_ascii_value_valid`, `of_ascii_node_valid`), and lexer rejection of invalid codepoints (`LexInvalidCodepoint`).
6. Replace lossy Unicode->ASCII fallback conversion with a principled encoding/partial conversion API, and prove precise round-trip/simulation lemmas. **Status:** done via `codepoint_to_ascii_opt`, `ustring_to_ascii_opt`, `to_ascii_value_opt`/`to_ascii_node_opt`, with proofs (`codepoint_to_ascii_opt_sound`, `ascii_partial_roundtrip`, `ustring_to_ascii_opt_sound`, `to_ascii_value_opt_of_ascii`, `to_ascii_node_opt_of_ascii`).
7. Add a full-language direct semantic bridge from original relational semantics (`eval`, `aeval_rel`, `holds`) to executable semantics (`Exec.eval_exec`, `Exec.aeval`, `Exec.holds_b`) without wrapper-induced trivialization. **Status:** done via full-language bridge theorems in `JPV_Formalization` (`full_holds_reflection`, `full_selector_exec_exact`, `full_segment_exec_exact`, `full_query_exec_exact`, `full_filter_selector_exec_exact`).
8. Strengthen order/permutation theorems for unrestricted queries to be proven from the original relational rules, not by reflexive equality over wrapper relations. **Status:** done via unrestricted result-shape/order bridge theorems (`full_query_exec_permutation`, `full_query_exec_paths_exact`, `full_query_exec_values_exact`).
9. Replace permissive `TypingPrecise` acceptance with a discriminating, proved criterion that rejects exactly ill-typed/unsupported filter forms and accepts RFC-valid ones. **Status:** done via discriminating `TypingPrecise` checks (`wf_regex`, mutual `wf_aexpr`/`wf_fexpr`/`wf_selector`/`wf_segment`/`wf_query`) including comparator type-compatibility and zero-step slice rejection.
10. Rework API error contracts so `E_NotWF` is semantically meaningful (or remove it), and prove correspondence between decision procedures and emitted API errors. **Status:** done via API/UnicodeAPI correspondence lemmas (`eval_checked_exact` with `wf_query = true`, `eval_checked_notwf`, `eval_checked_notwf_iff`) tying emitted `E_NotWF` directly to failed well-formedness checks.

## Unforgiving Closure (Closed)

1. Direct original-relation bridge theorem (`eval`) to executable result on the exact linear closure used by the runtime API contract. **Status:** done via `closure_direct_eval_exec_linear_exact` in `JPV_Formalization`.
2. Direct `holds` reflection theorem over original relation (no `holds_exec` wrapper in statement). **Status:** done via `closure_direct_holds_true_reflection` in `JPV_Formalization`.
3. Direct `aeval_rel` reflection theorem over original relation (no `aeval_rel_exec` wrapper in statement). **Status:** done via `closure_direct_aeval_aprim_reflection` in `JPV_Formalization`.
4. Direct original-relation order/permutation bridge theorems (no wrapper inversion endpoint). **Status:** done via `closure_direct_eval_exec_child_only_permutation`, `closure_direct_eval_paths_linear_exact`, and `closure_direct_eval_values_linear_exact` in `JPV_Formalization`.
5. Independent concrete-syntax relation plus parser soundness/completeness against it. **Status:** done via `abnf_surface_string` and `parse_surface_query_string_sound`/`complete`/`correct` in `JPV_Extensions`.
6. Lexer validity closure for emitted identifier/string payloads. **Status:** done via `lex_surface_payload_valid` and `lex_surface_payload_valid_forall` in `JPV_Extensions`.
7. No lossy Unicode->ASCII fallback in evaluation-facing API bridge. **Status:** done via partial bridge `UnicodeAPI.eval_exec_ascii_bridge : option (list JSON.node)` and `map_ascii_nodes_opt`.
8. Unicode partial-conversion iff + explicit failure off-domain. **Status:** done via `codepoint_to_ascii_opt_some_iff`, `ustring_to_ascii_opt_some_iff`, and `ustring_to_ascii_opt_fails_when_not_ascii_compatible`.
9. `TypingPrecise` discriminating acceptance with positive/negative witnesses. **Status:** done via `TypingPrecise` + `TypingPrecise_Props` (`wf_query_implies_no_zero_step`, `wf_selector_rejects_zero_step`, `wf_regex_rejects_bad_repeat`, `wf_fexpr_rejects_num_string_cmp`, etc.).
10. API error contracts with iff/error-exclusivity results. **Status:** done via `eval_checked_notwf_iff`, `eval_nf_checked_notchildonly_iff`, `eval_one_linear_notlinear_iff`, `eval_one_linear_notfound_iff`, `eval_one_linear_multiple_iff`, and `eval_one_linear_error_exclusive` (plus UnicodeAPI analogues).
11. RFC edge-case regression theorem suite. **Status:** done via `closure_regression_negative_index`, `closure_regression_slice_forward`, `closure_regression_slice_zero_step`, `closure_regression_mixed_type_cmp_false`, and `closure_regression_regex_search`.
12. Zero-trust proof hygiene gate (`no Admitted/Axiom`) automated and passing. **Status:** done via `make proof-hygiene` target in `Makefile`.

## New TODO (Closed)

1. Replace remaining wrapper/closure-fragment correspondence theorems with direct proofs over original relations. **Status:** done via direct theorem suite in `JPV_Formalization`:
   `closure_direct_eval_exec_filter_free_sound`, `closure_eval_exec_filter_free_eq_nf`,
   `closure_direct_aeval_acount_reflection_child_only`,
   `closure_direct_holds_exists_reflection_child_only`,
   `closure_direct_holds_cmp_aprim_reflection`.
2. Eliminate non-fatal proof/build warning debt (deprecated notations, non-recursive fixpoints, parser-comment warning, extraction warning). **Status:** done via warning-clean edits in `theories/JPV_Core.v`, `theories/JPV_Formalization.v`, `theories/JPV_Extensions.v`, and `theories/JPV_API_Extraction.v`; raw 8.20 compile now emits no warnings.
