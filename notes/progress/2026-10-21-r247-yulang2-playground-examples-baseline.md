# R247 — Yulang2 playground sample baseline

R247 records the first ordinary-test and exact-sample evidence after the active goal was restated as unchanged Yulang2 playground compatibility plus implementation and proof.

The six `.yu` examples currently checked into `web/playground/examples/` have passing CLI regression coverage: identity (1), ordinary islands (6), type/provenance diagnostics (1), repeated choice (1), and polymorphic escaping closure (1), for 10 test cases total across two focused invocations.

The unchanged R149 Types source stops at `candidate lowering unavailable: StructuralProjection`, because current LocalSource rejects comma-delimited parenthesized forms. The unchanged Console source stops at a structural `ErrorGroup` on root `say: 1 + 2`, because the colon-application parser is disabled in `MlMode::None`. Neither sample reaches imported library resolution or the expected type/output behavior. These are reproduced current failures, not source-language counterexamples.

R149 remains the compatibility authority and R168's exhaustive tuple matrix remains a useful owner map. No source or test was edited. The next useful work is an exact implementation contract against the unchanged R149 end state; the existing checked-in demo tests are only baseline evidence. Web/WASM and the broader Yulang2 catalog remain unverified. No theorem or production gate closes here.
