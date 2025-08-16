# JSONPath RFC 9535 Formalization in Coq

A mechanically verified implementation of JSONPath query expressions with complete formal semantics, providing both relational specifications and executable algorithms extracted to OCaml.

## Abstract

This development presents a comprehensive formalization of JSONPath (RFC 9535) in the Coq proof assistant. We provide both a relational semantics capturing the mathematical specification of the standard and an executable implementation with mechanically verified correctness proofs. The formalization addresses a critical gap in the JSONPath ecosystem, where implementation divergence has persisted despite recent standardization efforts. Our work employs only the Coq standard library, achieving complete verification without axioms or admitted lemmas.

## Contributions

This formalization makes the following technical contributions:

- **Formal semantics**: Complete inductive definitions for JSONPath evaluation according to RFC 9535
- **Verified implementation**: Executable semantics with formal proofs of correspondence to the specification
- **Regex formalization**: A total regex engine based on Brzozowski derivatives with simplification
- **Rational arithmetic**: Extension of JSON numbers to exact rational arithmetic, eliminating floating-point ambiguity
- **Static analysis**: A conservative type system for filter expressions with soundness guarantees
- **Extraction framework**: Certified extraction to OCaml producing an executable reference implementation

## Technical Approach

The formalization stratifies the development into three principal components:

1. **Specification layer**: Inductive relations defining the denotational semantics of JSONPath queries
2. **Implementation layer**: Recursive functions computing query results with verified totality
3. **Correspondence proofs**: Formal verification establishing semantic equivalence between layers

The development leverages Coq's inductive types to model JSON values, paths, and query expressions. Evaluation semantics are specified through inference rules in the relational style, while the executable semantics employ structural recursion with careful treatment of descendant selectors and filter expressions.

## Formalized Components

### Core Language Features
- Child and descendant selectors with proper document order
- Array slicing with negative indices and arbitrary step values
- Filter expressions including existential quantification and comparisons
- Wildcard selectors for object and array traversal
- Regular expression matching via I-Regexp (RFC 9485)

### Semantic Properties
- Determinism of evaluation (modulo object member ordering)
- Totality of the executable implementation
- Preservation of document structure in result paths
- Well-formedness conditions for valid queries

## Validation

The formalization includes:
- Formal proofs of over 50 theorems establishing correctness properties
- Systematic testing against examples from RFC 9535
- Complex integration tests on naturalistic datasets
- Extraction validation through execution trace comparison

## Requirements

The development requires:
- Coq 8.16 or later (earlier versions untested)
- OCaml 4.14 or later for extraction
- Standard ML basis for rational arithmetic
- Python 3.8+ with standard library for test harness

## Significance

This represents the first formal treatment of JSONPath RFC 9535 in any proof assistant. The work establishes:
- Mathematical foundations for JSONPath implementations
- A reference semantics for validation of existing implementations  
- Infrastructure for verified JSON processing tools
- Basis for further formal work on query languages

## Repository Structure

- `jsonpath_rfc9535.v`: Complete Coq formalization
- `runner.py`: Test harness with GUI for interactive evaluation
- Extraction produces `jsonpath_exec.ml` for integration

## License

MIT License

## Acknowledgments

This work was enabled by the Coq development team's proof assistant infrastructure and the IETF JSONPath Working Group's standardization efforts.
