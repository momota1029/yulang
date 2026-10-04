# Production HIR boundary for the source-generated callback core

Date: 2026-10-04
Status: read-only source bridge audit; no implementation authority
Scope: correspondence between Theorem C's typed source core and current
`yu-hir` lowering
Depends on: [source-generated theorem package](../design/2026-10-04-source-generated-callback-structural-theorems.md)

## Finding

Theorem C defines a source-core generator for lambdas, calls, bind, reify,
explicit computation elimination, operations, and their typed source
derivations. The current `yu-hir` production path does not emit that graph.
This is a concrete boundary in addition to the separate gap between an
operational graph and a finite inference endpoint.

In `crates/yu-hir/src/module.rs`, `ResolvedExpr` currently has only
`Lambda`, `Integer`, `Name`, and `Error` variants (lines 425–449). In
`crates/yu-hir/src/lib.rs`, the separate pre-HIR `HirExpr` can preserve an
associated operator `Apply` (lines 48–69), but `lower_simple_chain` accepts
only a leaf `Value` with no children; a non-leaf associated expression returns
`Unsupported` (module.rs lines 1402–1423). Its supported leaf cases are
integer literals and identifier expressions. The resolved expression shown
here has no call/application, record, operation/request, handler, or explicit
computation-consumer constructor.

Therefore Theorem C's finite-generation induction is a theorem for its
mathematical typed-core derivation graph, not a theorem that the current
production HIR constructs such graphs from raw Yulang input. The new finding
does not refute Theorem C, change accepted Yulang programs, or authorize
compiler edits.

## Exact next bridge

To claim raw/production correspondence for the callback fragment, a later
implementation/design gate must first identify the source forms admitted by
that fragment and map their resolved HIR nodes to Theorem C's derivation
constructors. For the currently represented simple forms, this includes
proving that lambda/name/integer occurrences preserve binder identity and
source provenance. Callback applications, effectful argument carriers,
requests, and their `d⁻`/`d⁺`/`b⁺`, receipt, profile, and `K,D` evidence need
production HIR constructors and a lowering theorem before they can be checked
against the theorem generator. This is not yet evidence that a new runtime or
solver carrier is needed; it is a source-shape gap in the HIR boundary.

No compiler code or tests changed/run. `git diff --check` is the only check
required for this record-only update.
