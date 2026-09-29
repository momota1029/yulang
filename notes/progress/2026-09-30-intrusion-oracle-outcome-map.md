# Oracle staged outcome map

Date: 2026-09-30
Oracle: frozen Yulang2 `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Classification: read-only source map; not a selected diagnostic contract

## Entry-point-dependent lowering outcomes

`lower_loaded_files_with_consumer_once` propagates CST indexing, module-map,
and missing-module-path failures, while terminal proof-kernel failure becomes
`LoadedFilesError::ProofKernelFailed` (`crates/infer/src/lowering/body/mod.rs`
roughly lines 670–679, 725–745, 791–796). These route as hard `RouteError::Lower`
failures in `crates/yulang/src/source/mod.rs`.

Expression/body/binding/root errors can instead accumulate in
`BodyLowering.errors`; binding errors skip `finish_binding`, root errors are
recorded without pushing a runtime root, and `finish` adds analysis
diagnostics before returning a `BuildPolyOutput` that retains errors
(`lowering/body/mod.rs:2125–2147, 2327–2364, 1653–1708`). The public operation
then matters: check/analyze routes can return `SourceDiagnostic`, while runtime
readiness rejects lowering diagnostics before specialization
(`infer/check.rs:168–197`, `source/mod.rs:1973–1976, 2293–2300,
2738–2781, 4451–4509, 5462–5470`). The same source therefore needs an
entrypoint parameter in any contextual parity relation.

## Inference and cast outcomes

Fixed cross-kind constructor/Function shapes can generate
`UnsatisfiedSubtypeShape` (`constraints/machine/propagate.rs:194–207,
337–398`) and are routed/deduplicated as diagnostics with optional complete
provenance context (`analysis/session/subtype_diagnostic.rs:16–49`).

Different nominal constructor paths generate `NominalCastNeeded`
(`propagate.rs:272–292`). The session deduplicates the producer, retains a
pending cast, and eagerly adds candidate constraints
(`analysis/session/lifecycle.rs:478–497`,
`analysis/session/generalize.rs:897–938`). After inference quiescence,
source-boundary eligibility is classified and only proven source boundaries
are activated (`lowering/body/mod.rs:1653–1658`,
`analysis/session/lifecycle.rs:520–540`, `analysis/session/ocast_activation.rs`).
For eligible boundaries, no implicit cast yields `MissingImplicitCast`, one
cast yields no cast diagnostic, and multiple casts yield
`AmbiguousImplicitCast`; internal/incomplete routes do not emit that public
cast diagnostic. A later specialization cast failure is a distinct route.
Thus `NominalCastNeeded` is an intermediate route with eager solver effects,
not a direct public mismatch.

Weighted `Pos::Var <: Neg::Row` constraints enter
`add_effect_row_upper_bound` (`constraints/row_effect.rs:88–234`). Depending on
weights and row shape, the solver can reduce against existing lowers, filter
items by stack weights, derive a source-to-tail obligation, or introduce/reuse
a residual variable and derive both source/residual obligations. An
`EffectFilterViolation` is a deduplicated analysis event
(`row_effect.rs:903–913, 988–1002`), later routed to `AnalysisDiagnostic`; it
can lack a primary definition source range. This failure event is distinct
from the weighted row residual state that may continue inference.

## Specialization failures

Tuple inference descends only for equal arity; unequal arity has no infer
shape event and is rejected by specialization as `UnsatisfiedSubtype`
(`constraints/machine/propagate.rs:317–329`,
`specialize2/type_graph.rs:731–759`). Missing required record fields likewise
can be deferred until specialization (`type_graph.rs:760–796`). A contextual
source diagnostic is attached only when provenance or a selection ID provides
the needed source context; otherwise the route remains a bare
`RouteError::Specialize` (`source/mod.rs:1979–2083`). Record literals also
have a `MissingRecordField` origin in `specialize/task_solver.rs:732–747`.

## Limits

These tags are source-map evidence for the candidate staged interface, not an
exhaustive enumeration of all Oracle failures and not an approved public
compatibility policy. The final observation contract must verify which routes,
payload fields, source spans, and entrypoints belong to the supported envelope.
No paired intrusion run, tests, Python, or measurements were performed.
