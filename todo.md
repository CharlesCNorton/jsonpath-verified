# jsonpath-verified: Cure List

1. Add a `_CoqProject` file and Makefile for reproducible builds. **Status:** done.
2. Split the single file into per-module files gated by the build system. **Status:** done via `JPV_Core.v`, `JPV_Formalization.v`, `JPV_Extensions.v`, `JPV_API_Extraction.v`, with facade `jsonpath_verified.v`.
