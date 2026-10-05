# Parsed scoped source/core execution bridge

Date: 2026-10-05
Status: finite test-only characterization; no production or inference authority
Scope: actual parsed `call` and `compose` declarations through the existing scoped candidate and synthesized core
Governing sources: [typed computation core](../design/2026-10-02-typed-computation-core-elaboration.md) §§3,6; [ordinary computation semantics](../design/2026-10-02-ordinary-computation-semantics-package.md) §§3–4; charter §§17,21
Review: compiler_referee found no blocking, major, or minor findings in the formatted test

The test `research_parsed_scoped_call_compose_execution_bridge` in
[`crates/yu-hir/src/lib.rs`](../../crates/yu-hir/src/lib.rs#L1582) starts from
the actual parsed declarations `my call f x = f x` and
`my compose f g x = f (g x)`. It feeds each `BindingStatement` through the
existing research association, candidate name/binder resolution, and
`research_synthesize_scoped` typed-core skeleton. It then compares a recursive
scoped-expression evaluator with an explicit-stack evaluator of the synthesized
core. This closes a bounded parsed-source → scoped-candidate → core-execution
characterization that the standalone Python probe did not cover.

The supplied environment gives `f` and `g` finite `Int -> Int` primitive
relations, and supplies the entry binders rather than executing their lambda
construction. The finite search covers 128 configurations across two source
declarations, binary values/states/responses, two `f` behaviors, and the
optional `g` request behavior. The compose request occurs in the nested
argument; its snapshot preserves the outer call suffix, and its resumed state
is observed by the outer call. The two evaluators agree on result, final
state, event trace, and pending suffix across all configurations. Mutants that
force before receipt or reuse the pre-resumption state are killed; their
reported witnesses are the first cases under the test's lexicographic order.

Verification:

```text
RUSTC_WRAPPER= cargo test -p yu-hir research_parsed_scoped_call_compose_execution_bridge
  1 passed; 0 failed
rustfmt --edition 2024 --check crates/yu-hir/src/lib.rs
  passed
git diff --check
  passed
```

This does not execute the generated lambda binders, construct production HIR,
infer types, or model typed receipt/activation identity, handler dispatch,
capture incidence, adapters, actual `(nu,K,D)`, detached continuation
resumption, native operation result consumers, Function membership, or
principality. The primitives and request are supplied by the test. It is
finite characterization of source shape and scheduled Value-entry behavior,
not a source-to-endpoint adequacy theorem. The complete
comparison-independent Function membership/admission interpretation and
actual-to-checked containment remain open.
