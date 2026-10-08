# Current annotation syntax is not a production Direct caller

Status: bounded source-path audit; exact-path review passed; research-only
Baseline: `eee675680`
Scope: whether existing Yulang annotation syntax reaches a production
source-checking/Direct caller

## Finding

No production annotation caller exists in the inspected default syntax → HIR →
solver path. The parser accepts expression and pattern type-annotation forms,
but production HIR does not lower them into a typed check/view constructor.
They therefore cannot currently supply the selected `view(h,q,V)` semantic
caller without a new source/compiler contract.

## Expression annotation path

For `1 as Int`, syntax parsing emits `TypeAnnotationTail` and parses the full
RHS type (`crates/yu-syntax/src/expression/tails/type_annotation.rs:17–37`).
HIR association preserves it as generic `HirExpr::Value` structure with
`TypeAnnotationTail` (`crates/yu-hir/src/lib.rs:315,468`). This is a syntax
association, not a typed annotation judgment.

Production `lower_simple_chain` accepts only a direct integer/name atom with
an associated leaf and no children (`crates/yu-hir/src/module.rs:1940`). An
annotated expression fails that shape, and root/binding lowering emits
`ResolvedExpr::Error` with `UnsupportedExpression` (`:1361,1548`).
`ResolvedExpr` has no annotation, check, or type-view variant (`:443`), so
`ConstraintBatch::collect` has no annotation inequality or Direct proof to
consume (`crates/yu-solver/src/lib.rs:855,1096`).

## Pattern annotation path

The parser emits `PatternTypeAnnotation` and delegates its RHS to Type parsing
(`crates/yu-syntax/src/pattern/mod.rs:1075,1294`). Production
`plain_binding_header` admits a plain identifier or one plain identifier
parameter (`crates/yu-hir/src/module.rs:2025`); annotation children instead
reach `UnsupportedTarget` (`:1193`). The fixture `my apply (f: T) x = f x`
in `crates/yu-hir/src/tests/shadow_annotation_positions.rs:224` exercises the
shadow skeleton, not production inference.

## Shadow and historical boundaries

Shadow annotation inventory is feature/test-gated and every occurrence remains
`PendingTypedPortAndProfile` (`crates/yu-hir/src/lib.rs:9`,
`crates/yu-hir/src/shadow.rs:998,1076`). Its
`ParameterAnnotationIncidence` supplies no typed port or permission (`:1096`).
The optional core source crosswalk joins syntax and occurrence identities but
leaves annotation port/profile, applicability and permission unresolved
(`crates/yu-core/src/lib.rs:27`,
`crates/yu-core/src/shadow_source_annotation_crosswalk.rs:11,69,95`). It is not
consumed by default solving (`tasks/current.md:629`). The frozen legacy
annotation audit is likewise not a current successor caller.

## Consequence for the caller decision

The source rule `view(h,q,V)` remains a selected semantic model boundary, but
mapping it to existing `as` syntax is not already authorized by production
behavior. Choosing that route requires a source/compiler contract for the
annotation's checked port, applicability and permission, plus the authentic
root and local-law suppliers. An internal checker boundary avoids changing
source syntax, but by itself supplies no source caller and does not replace
F5. No API or semantics are selected here.

This separation is also explicit in authoritative FVIEW §1.1: a written source
annotation, inferred public scheme, and internal evidence-rich view are
different layers. The current `as Type` parse tree therefore cannot be treated
as an internal Direct view without an additional selected bridge.

Review: read-only bounded audit by an `explorer`; an independent
`regression_auditor` found no substantive issue and noted one non-blocking
function-level citation that was refined to the exact rejection branch.
`git diff --check` passed. No code, tests, builds, benchmarks, or measurements
were performed.
