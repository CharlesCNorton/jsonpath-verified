# jsonpath-verified: Cure List

1. Eliminate the duplicated `prim_of_value` — remove the top-level copy, import from `JSONPath`.
2. Factor `prim_eq`, `prim_lt`, `cmp_prim` into a single shared definition; have `Exec` reuse it.
3. Eliminate the `Regex` module duplication — define module functions in terms of the top-level originals, or delete the top-level originals and use only the module.
4. Reshape `wf_fmatch_type_safe` and `wf_fsearch_type_safe` return types so `reassoc_match_type` and `reassoc_search_type` become unnecessary; delete them.
5. Make `comparable` perform actual type discrimination instead of returning `true` unconditionally.
6. Define a denotational semantics for regular languages and prove `regex_match` correct against it.
7. Prove `nullable` correct (accepts empty string iff language contains epsilon).
8. Prove `deriv` correct (Brzozowski derivative computes the derivative of the denoted language).
9. Prove `rsimpl` preserves language equivalence.
10. Prove soundness of `holds_b` against the relational `holds` for all filter expressions.
11. Prove completeness of `holds_b` against `holds` for all filter expressions.
12. Prove soundness of `sel_exec` (full, with filters) against `eval_selector`.
13. Prove completeness of `sel_exec` against `eval_selector`.
14. Prove end-to-end equivalence for `Desc` segments through the full query engine.
15. Prove end-to-end equivalence for the full `eval_exec` (with filters and descendants) against the relational `eval`.
16. Prove `FMatch`/`FSearch` completeness in the relational direction (if `regex_match r s = true` then `holds (FMatch ...) n`).
17. Extend string representation from ASCII to Unicode (replace `Coq.String.Ascii` with a UTF-8 or codepoint model).
18. Formalize the RFC 9535 ABNF grammar as an inductive or parser type.
19. Implement a JSONPath string parser producing the existing AST.
20. Prove the parser correct against the ABNF grammar.
21. Run the QuickChick properties and record passing results in the artifact.
22. Add a `_CoqProject` file and Makefile for reproducible builds.
23. Split the single file into per-module files gated by the build system.
