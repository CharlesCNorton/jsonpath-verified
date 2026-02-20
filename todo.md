# jsonpath-verified: Cure List

1. Fix the `holds_b_simple` bug at line 814: change second `aeval_func a v` to `aeval_func b v`.
2. Remove `visit_df_value_deterministic`, `visit_arr_aux_det`, `visit_obj_aux_det` (reflexivity-only "proofs").
3. Remove the Totality section's trivial `exists res, f x = res` theorems and the trivial determinism lemmas (`sel_exec_deterministic`, `holds_b_deterministic`, `aeval_deterministic`).
4. Change `is_prefix_of` from a `Lemma`/`Defined` to a `Definition`.
5. Eliminate the duplicated `prim_of_value` — remove the top-level copy (line 791), import from `JSONPath`.
6. Factor `prim_eq`, `prim_lt`, `cmp_prim` into a single shared definition; have `Exec` reuse it.
7. Eliminate the `Regex` module duplication — define module functions in terms of the top-level originals, or delete the top-level originals and use only the module.
8. Reshape `wf_fmatch_type_safe` and `wf_fsearch_type_safe` return types so `reassoc_match_type` and `reassoc_search_type` become unnecessary; delete them.
9. Make `comparable` perform actual type discrimination instead of returning `true` unconditionally.
10. Define a denotational semantics for regular languages and prove `regex_match` correct against it.
11. Prove `nullable` correct (accepts empty string iff language contains epsilon).
12. Prove `deriv` correct (Brzozowski derivative computes the derivative of the denoted language).
13. Prove `rsimpl` preserves language equivalence.
14. Prove soundness of `holds_b` against the relational `holds` for all filter expressions.
15. Prove completeness of `holds_b` against `holds` for all filter expressions.
16. Prove soundness of `sel_exec` (full, with filters) against `eval_selector`.
17. Prove completeness of `sel_exec` against `eval_selector`.
18. Prove end-to-end equivalence for `Desc` segments through the full query engine.
19. Prove end-to-end equivalence for the full `eval_exec` (with filters and descendants) against the relational `eval`.
20. Prove `FMatch`/`FSearch` completeness in the relational direction (if `regex_match r s = true` then `holds (FMatch ...) n`).
21. Extend string representation from ASCII to Unicode (replace `Coq.String.Ascii` with a UTF-8 or codepoint model).
22. Formalize the RFC 9535 ABNF grammar as an inductive or parser type.
23. Implement a JSONPath string parser producing the existing AST.
24. Prove the parser correct against the ABNF grammar.
25. Run the QuickChick properties and record passing results in the artifact.
26. Add a `_CoqProject` file and Makefile for reproducible builds.
27. Split the single file into per-module files gated by the build system.
