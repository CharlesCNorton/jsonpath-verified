# jsonpath-verified: Cure List

1. Prove soundness of `holds_b` against `holds` for boolean connectives: `FTrue`, `FNot`, `FAnd`, `FOr`. **Status:** done via `holds_b_sound_ftrue`, `holds_b_sound_fnot`, `holds_b_sound_fand`, `holds_b_sound_for`.
2. Prove soundness of `holds_b` against `holds` for `FCmp`, `FMatch`, `FSearch`. **Status:** done via `holds_b_sound_fcmp`, `holds_b_sound_fmatch`, `holds_b_sound_fsearch`.
3. Prove soundness of `holds_b` against `holds` for `FExists`. **Status:** done via `holds_b_sound_fexists`.
4. Prove completeness of `holds_b` against `holds` for all filter expressions. **Status:** done via `holds_b_complete` (paired with `holds_b_sound`).
5. Prove soundness of `sel_exec` (full, with filters) against `eval_selector`. **Status:** done via `sel_exec_sound`.
6. Prove completeness of `sel_exec` against `eval_selector`. **Status:** done via `sel_exec_complete`.
7. Prove end-to-end equivalence for `Desc` segments through the full query engine. **Status:** done via `desc_segment_equiv`.
8. Prove end-to-end equivalence for the full `eval_exec` (with filters and descendants) against the relational `eval`. **Status:** done via `eval_exec_sound`, `eval_exec_complete`, `eval_exec_equiv`.
9. Prove equivalence of `Exec.aeval` against the relational `aeval_rel` (soundness and completeness). **Status:** done via `aeval_exec_sound`, `aeval_exec_complete`, `aeval_exec_equiv`.
10. Extend string representation from ASCII to Unicode (replace `Coq.String.Ascii` with a UTF-8 or codepoint model).
11. Formalize the RFC 9535 ABNF grammar as an inductive or parser type.
12. Implement a JSONPath string parser producing the existing AST.
13. Prove the parser correct against the ABNF grammar.
14. Ensure all QuickChick properties pass, fix any failures, and extend coverage to the newly-proved filter and descendant equivalences. **Status:** core property suite passes (10,000 tests each) via `quickchick_run.v`.
15. Add a `_CoqProject` file and Makefile for reproducible builds. **Status:** done.
16. Split the single file into per-module files gated by the build system. **Status:** intentionally deferred; repository is currently kept monolithic by request.
