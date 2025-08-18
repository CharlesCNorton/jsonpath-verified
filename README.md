# JSONPath (RFC 9535) — A Coq Formalization with Executable Semantics and Extraction

A mechanically verified development of JSONPath that provides (i) a declarative, permutation‑aware relational semantics matching RFC 9535, (ii) a total, executable interpreter, and (iii) machine‑checked correspondence theorems, together with extraction to a compact OCaml library.

---

## Abstract

This repository contains a comprehensive formalization of JSONPath in the Coq proof assistant. The development presents two complementary views: a relational semantics that captures the meaning of JSONPath expressions as inductively defined judgments, and an executable semantics that computes query results by structural recursion. Arrays are handled in document order as mandated by the standard; object members are handled modulo permutation at the specification level—precisely where the standard leaves order unstipulated—while the interpreter fixes a deterministic visitation order for executability. The two semantics are connected by correctness theorems: for the filter‑free fragment (child and descendant segments with name, index, wildcard, and slice selectors) the interpreter is sound and complete up to permutation with respect to the relational rules; for linear paths of singleton child steps, the interpreter coincides exactly and is arity‑bounded by one. The development includes a small, total regular‑expression engine based on Brzozowski derivatives, executable checks for filter expressions, a library of structural lemmas for slicing and indexing, an extensive suite of examples and property‑based tests, and an extraction pipeline that yields an OCaml implementation with exact arithmetic and no partial functions.

---

## Introduction

JSONPath is a widely used selection language for JSON documents. RFC 9535 standardizes the core language while intentionally admitting latitude in object‑member order and some host‑dependent extensions. The formalization offered here is designed to mirror that standard faithfully and at the right level of abstraction. The specification layer treats object‑member order as intentionally unspecified and therefore expresses results modulo permutation whenever objects are traversed; the interpreter layer imposes a concrete, consistent order in order to produce executable code. The correctness results are calibrated to this split: arrays are preserved in order, nodes are reported before their descendants, and permutations appear only in the places where the RFC does not stipulate an order.

The artifact aims to be useful along two axes. As a formal model, it provides a precise foundation for reasoning about JSONPath programs and for validating implementations. As executable code, it offers a small, self‑contained library that can be embedded in applications and tested using the included examples and generators.

---

## Overview of the Formal Development

The development is structured as a collection of small, compositional modules.

The **JSON** module defines the value domain (null, booleans, rationals, strings, arrays, and objects), explicit **paths** as lists of steps (either `SName s` or `SIndex i`), and **nodes** as path–value pairs. Utilities instantiate equality and orderings on strings via ASCII codes and exact arithmetic on rationals (`Q`), together with list combinators for indexing and slicing; the latter normalize negative indices and negative steps in a Python‑style fashion.

The **JSONPath** module defines the abstract syntax of queries. Selectors include exact names, integer indices (with negative indices interpreted from the end), wildcards over arrays and objects, and slices with optional bounds and arbitrary steps. Segments are either `Child` or `Desc` (descendant), and queries are lists of segments. Filter expressions include primitive constants, numeric and lexicographic comparisons, existential tests (`exists q`), the `value`/`count`/`length` family over embedded queries, and string predicates (`match`, `search`) whose semantics are provided by the regex engine below.

The **Regex** module implements a total regular‑expression engine based on Brzozowski derivatives with simplification. Matching is defined by repeated derivation followed by nullability; search is defined as matching `.* r .*`. All constructions are total and purely functional.

The **relational semantics** is given by three inductive relations. `eval_selector` specifies the behavior of a single selector on a single node, including in‑bounds arithmetic for indices and normalized positions for slices, and it returns either a singleton node list or the empty list. Wildcards over objects produce a multiset of child nodes, abstracted up to permutation; wildcards over arrays preserve index order. `visit_order` defines admissible document‑order traversals: a node appears before all of its descendants, arrays are visited in increasing index order, and objects may be visited in any order. `eval_seg` lifts selectors to segments (`Child` or `Desc`) using `visit_order`, and `eval` composes segments left‑to‑right by concatenating per‑node results.

The **executable semantics** mirrors the above. A depth‑first, pre‑order visitor enumerates nodes with the same structural constraints the relational semantics requires; the per‑segment executor either applies selectors at the current frontier (`Child`) or applies them at every visited node (`Desc`). The interpreter is parameterized by a selector implementation, yielding a filter‑free instance and a full instance with filters enabled. Filters are guarded by an executable well‑formedness predicate to rule out obvious type mismatches at run time; the Boolean evaluator for filters calls back into the interpreter for the `value`/`count`/`length` family.

An **API** layer packages the evaluators in a small, extraction‑friendly result type and provides conveniences such as projecting values and paths from result sets and a one‑result interface for linear paths.

---

## Relational Semantics

Selector evaluation proceeds by structural cases. A name selector succeeds with a singleton if the object has a field with the indicated key and fails otherwise. An index selector first reduces negative indices by adding the array length, then succeeds with a singleton if the resulting index is in `[0, len)`. A wildcard over an object yields the set of its children, treated modulo permutation; over an array it yields the children in index order. A slice is reduced by normalizing its bounds and step to a finite list of positions, from which a list of singleton selections is formed. The empty list signifies absence of a match.

Segments compose selector behavior. A child segment applies its selectors at the current node. A descendant segment first visits the current node and all of its descendants according to `visit_order` and then applies its selectors at each visited node. This captures the RFC requirement that nodes precede their descendants and that arrays be traversed in order while leaving the relative order of object members free.

Queries are lists of segments. The relational evaluation of a query threads a multiset of nodes through the list, applying each segment to each node from the previous stage and concatenating the results.

---

## Executable Semantics

The interpreter adopts the same granularity as the relational semantics. The visiting function performs a depth‑first, pre‑order traversal. Arrays are always visited in increasing index order; objects are visited in the list order in which their fields are stored in the value. Selector execution is a direct functional counterpart of the relational rules: name lookup by `find`, index lookup with explicit in‑bounds arithmetic, wildcard by mapping over object fields or array elements, and slices by computing normalized positions and selecting exactly those elements.

Segments are interpreted as functions from lists of nodes to lists of nodes. A child segment maps the selector executor over the frontier and concatenates the results. A descendant segment first computes the visitation list via the visitor and then maps the child‑level executor over that list. The query executor is the left‑fold of segment executors starting from the singleton list containing the root node.

Filter evaluation is a total Boolean function that interprets comparison operators over primitive values (null, booleans, rationals, strings), evaluates `exists` by checking whether a sub‑query returns a non‑empty list, interprets `value`/`count`/`length` by delegating to the interpreter on the current node’s value, and interprets `match`/`search` using the regex engine.

---

## Correctness Theorems

Three families of theorems connect the two semantics.

1. **Selector‑level equivalence in the child case.** For each filter‑free selector, the relational rules and the executable implementation agree. On objects, agreement is stated up to permutation to reflect intentional order agnosticism in the standard; on arrays and scalars, agreement is exact. These results are proved both as soundness (the interpreter only produces relational results) and completeness (every relational result appears in the interpreter’s output, modulo permutation where applicable).

2. **Segment‑ and query‑level equivalence for the filter‑free fragment including `Desc`.** The executable depth‑first visit order is admissible in the relational system, and any relational visit order is a permutation of the executable one. Lifting selector‑level agreement pointwise and propagating permutations through concatenation yields end‑to‑end equivalence up to permutation for entire queries whose segments are `Child` or `Desc` and whose selectors are name/index/wildcard/slice. Because arrays are ordered in both semantics, permutations arise only from object‑member reordering.

3. **Linear‑path exactness and arity.** For queries that are chains of singleton child steps by name or by index, the interpreter returns either the empty list or a singleton, and in the singleton case the result is exactly equal to the relational outcome. An explicit arity bound of at most one follows, and a convenience function returns a single node or a small error drawn from a fixed set.

These results are accompanied by structural invariants used pervasively in proofs and by clients: cardinality of wildcard results on arrays and objects, arity bounds for name and index selection, stability of path extension (every result path is formed by appending exactly one step for a single selector), preservation of array order, and the identity establishing `search r` as `match (.* r .*)` at the Boolean level.

---

## Regular Expressions

Regular‑expression matching is realized by Brzozowski derivatives with a simplifier that collapses neutral and absorbing forms. Matching is the repeated derivation of the regular expression over the characters of the input followed by a nullability check. Searching is defined as matching `.* r .*`. The engine operates over ASCII characters and is completely total. It is integrated into filter evaluation in two forms: full‑string match and substring search.

---

## Slicing and Indexing

Slices are interpreted by first normalizing `(start, end, step)` into a bounded arithmetic progression in `ℤ` and then filtering it to `[0, len)` using an in‑bounds check. Negative indices are translated by adding the array length; negative steps enumerate positions in descending order. Normalization is used uniformly in both the relational and executable accounts, and the normalized positions drive the exact selection of array elements. Auxiliary lemmas characterize bounds, monotonicity with respect to step sign, and the cardinality of resulting positions.

---

## Property‑Based Validation

Alongside the machine‑checked theorems, the development includes a QuickChick test suite. Generators produce compact, human‑readable JSON values (lower‑case ASCII keys and strings, small rationals) and deduplicate object fields to maintain canonical structure. Properties validate the arity bound for linear paths, the cardinality of wildcards, the inclusion of child paths within descendant paths under projection, and the equivalence of `search` with `match` under dot‑star padding. Because all functions are pure and total, the properties reduce to Boolean checks inside Coq and serve as executable regression tests.

Representative invocations:

```coq
QuickChick test_suite_with_stats.
QuickChick stress_test_edge_cases.
QuickChick performance_test.
```

---

## Extraction and Executable API

The interpreter is designed for extraction. Extraction directives preserve singleton types, map machine integers to Zarith big integers, and emit compact OCaml modules corresponding to the Coq modules (`JSON`, `JSONPath`, `Regex`, `Exec`, `Typing`, and the API). The resulting library exposes two principal evaluators: a filter‑free evaluator targeted by the strongest correspondence theorems and a full evaluator that admits filters under an executable well‑formedness guard. Helper functions project values and paths from results and provide a one‑result interface for linear queries. The extracted code contains no partial functions; all in‑bounds checks, normalizations, and arithmetic are explicit.

---

## Datasets and Examples

Two illustrative JSON documents are included: a compact “company” example and a richer “acme\_db” record that exercises arrays of objects, nested objects, numeric fields, time‑stamp strings, and text fields. Example queries demonstrate child and descendant traversal, negative indices, descending slices, wildcard enumeration, filter‑style counting and existence tests, and string matching and searching. These examples serve both as executable documentation and as anchors for proofs and properties.

---

## Building and Running

The development compiles with recent versions of Coq. The test suite requires QuickChick. Extraction targets OCaml and uses Coq’s standard extraction support for strings, characters, big integers, and rationals. A typical build loads the main Coq file, checks all proofs, and produces the extracted modules. The QuickChick properties may be executed interactively from within Coq.

---

## License and Citation

MIT License.
When citing, refer to this repository as a Coq formalization of JSONPath (RFC 9535) providing a relational semantics, a total interpreter, machine‑checked correspondence theorems (including descendant traversal in the filter‑free fragment), a derivative‑based regex engine, and extraction to OCaml.

---

## Acknowledgments

The development relies on the Coq standard library and QuickChick. The RFC 9535 specification informed the semantics and invariants and provided the basis for the permutation‑aware modeling of object‑member order.
