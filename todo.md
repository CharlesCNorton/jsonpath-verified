# jsonpath-verified: Cure List

1. Prove soundness of `holds_b` against `holds` for boolean connectives: `FTrue`, `FNot`, `FAnd`, `FOr`. These cases require only the inductive hypothesis.
2. Prove soundness of `holds_b` against `holds` for `FCmp`, `FMatch`, `FSearch`. Blocked on item 9 (`aeval` ↔ `aeval_rel`).
3. Prove soundness of `holds_b` against `holds` for `FExists`. Blocked on items 5 and 9; requires mutual induction with `sel_exec` over AST size measures because `holds_b` → `eval_exec_impl` → `sel_exec` → `holds_b`.
4. Prove completeness of `holds_b` against `holds` for all filter expressions.
5. Prove soundness of `sel_exec` (full, with filters) against `eval_selector`.
6. Prove completeness of `sel_exec` against `eval_selector`.
7. Prove end-to-end equivalence for `Desc` segments through the full query engine.
8. Prove end-to-end equivalence for the full `eval_exec` (with filters and descendants) against the relational `eval`.
9. Prove equivalence of `Exec.aeval` against the relational `aeval_rel` (soundness and completeness). This is the bridge needed for items 2-3 and 8; the `FMatch`/`FSearch` relational constructors are trivial once `aeval` ↔ `aeval_rel` is established.
10. Extend string representation from ASCII to Unicode (replace `Coq.String.Ascii` with a UTF-8 or codepoint model).
11. Formalize the RFC 9535 ABNF grammar as an inductive or parser type.
12. Implement a JSONPath string parser producing the existing AST.
13. Prove the parser correct against the ABNF grammar.
14. Ensure all QuickChick properties pass, fix any failures, and extend coverage to the newly-proved filter and descendant equivalences.
15. Add a `_CoqProject` file and Makefile for reproducible builds.
16. Split the single file into per-module files gated by the build system.
