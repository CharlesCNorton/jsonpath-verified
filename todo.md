# jsonpath-verified: Cure List

1. Prove soundness of `holds_b` against `holds` for boolean connectives: `FTrue`, `FNot`, `FAnd`, `FOr`. **Status:** done (`todo1_holds_b_sound_bool_connectives`).
2. Prove soundness of `holds_b` against `holds` for `FCmp`, `FMatch`, `FSearch`. **Status:** done (`todo2_holds_b_sound_cmp_match_search`).
3. Prove soundness of `holds_b` against `holds` for `FExists`. **Status:** done (`todo3_holds_b_sound_exists`).
4. Prove completeness of `holds_b` against `holds` for all filter expressions. **Status:** done (`todo4_holds_b_complete_all`).
5. Prove soundness of `sel_exec` (full, with filters) against `eval_selector`. **Status:** done (`todo5_sel_exec_sound_full`).
6. Prove completeness of `sel_exec` against `eval_selector`. **Status:** done (`todo6_sel_exec_complete_full`).
7. Prove end-to-end equivalence for `Desc` segments through the full query engine. **Status:** done (`todo7_desc_segment_equiv_full`).
8. Prove end-to-end equivalence for the full `eval_exec` (with filters and descendants) against the relational `eval`. **Status:** done (`todo8_eval_exec_equiv_full`).
9. Prove equivalence of `Exec.aeval` against the relational `aeval_rel` (soundness and completeness). **Status:** done (`todo9_aeval_equiv_full`).
10. Extend string representation from ASCII to Unicode (replace `Coq.String.Ascii` with a UTF-8 or codepoint model).
11. Formalize the RFC 9535 ABNF grammar as an inductive or parser type.
12. Implement a JSONPath string parser producing the existing AST.
13. Prove the parser correct against the ABNF grammar.
14. Ensure all QuickChick properties pass, fix any failures, and extend coverage to the newly-proved filter and descendant equivalences. **Status:** core property suite passes (10,000 tests each) via `quickchick_run.v`.
15. Add a `_CoqProject` file and Makefile for reproducible builds. **Status:** done.
16. Split the single file into per-module files gated by the build system. **Status:** intentionally deferred; repository is currently kept monolithic by request.
