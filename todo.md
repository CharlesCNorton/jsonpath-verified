# jsonpath-verified: Cure List

1. Prove soundness of `holds_b` against the relational `holds` for all filter expressions.
2. Prove completeness of `holds_b` against `holds` for all filter expressions.
3. Prove soundness of `sel_exec` (full, with filters) against `eval_selector`.
4. Prove completeness of `sel_exec` against `eval_selector`.
5. Prove end-to-end equivalence for `Desc` segments through the full query engine.
6. Prove end-to-end equivalence for the full `eval_exec` (with filters and descendants) against the relational `eval`.
7. Prove `FMatch`/`FSearch` completeness in the relational direction (if `regex_match r s = true` then `holds (FMatch ...) n`).
8. Extend string representation from ASCII to Unicode (replace `Coq.String.Ascii` with a UTF-8 or codepoint model).
9. Formalize the RFC 9535 ABNF grammar as an inductive or parser type.
10. Implement a JSONPath string parser producing the existing AST.
11. Prove the parser correct against the ABNF grammar.
12. Run the QuickChick properties and record passing results in the artifact.
13. Add a `_CoqProject` file and Makefile for reproducible builds.
14. Split the single file into per-module files gated by the build system.
