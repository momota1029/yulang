# R151 implementation-owner handoff

Status: `NO_SAFE_CODE_SLICE`.

## Pinned owner evidence

The five named Y3 owner blobs match the R151 contract pins in the current
workspace. `crates/yu-hir/src/module.rs` defines `HirItem` as `Binding`,
`Expression`, or `Error`. A binding owns an artifact-branded
`DefinitionRootId`, `DefId`, visibility, parameters, value, and optional
`EvaluationClass`; its classifier derives `FetchValue` from selected resolved
value shapes. `SemanticImports` carries at most opaque caller evidence tied to
one declaration in the parsed input. That evidence is explicitly not semantic
certification and is not an imported declaration or initializer record.

`crates/yu-solver/src/candidate_source.rs` stores definition schedules in a
map keyed by local `DefinitionRootId`; a `Schedule::Root` selects the matching
local definition position and executes that root's source actions. This
provides local source-root ownership, but no imported initializer identity,
classification, publication result, or cross-module order carrier appears in
this owner.

`tools/inference-playground/src/runtime/program.rs` walks `hir.items()` in
source order. For each binding/expression it requires a local source for its
root, emits runtime code, indexes definitions by `DefId`, and records
computation definitions or expressions in `source_schedule`. Definition
computation is classified from emitted instruction shape; bare value
definitions are materialized on demand. `ExecutionRoot::Definition` carries
only a `DefId`; `ExecutionRoot::Expression` carries an authenticated
expression-root/code join. The machine resolves definition roots through its
`definition_indices`, rejects absent or repeated definitions/order entries,
and executes selected source-order roots, while value-definition reads use the
definition cache. No imported declaration-qualified record is consumed here.

## Missing carrier / implementation boundary

The first visible obstruction in these pinned owners is the HIR boundary:
there is no imported declaration item/source-root representation to join an
imported declaration identity to its initializer body and source position.
Consequently the local candidate schedule cannot publish an authenticated
import initializer classification or its source-order slot, and
`RuntimeProgram` cannot build/validate such an imported root for its runtime
consumer. The permitted evidence does not identify the first concrete Y2
ordinary imported constructor, prove that either sample reaches it, or establish
what initializer classes/order those samples require. Do not add a carrier or
change runtime classification on this evidence alone.

Any later approved implementation slice needs an independently reviewed
source result identifying the exact ordinary/imported constructor and its
declaration-qualified body; a reviewed R150 rev2 correction; and an authorized
lease for the end-to-end carrier joins. Those joins must authenticate source
declaration identity and artifact ownership, distinguish ordinary bindings
from header-argument, pattern/destructured, `OpDef`, method, and generated
routes, retain the correct body/publication classification and source order
through HIR and candidate scheduling, and let runtime validate the same
declaration-to-emitted-body/order mapping before selecting or materializing an
initializer. Keep exact sample reachability, final ordering, and semantics
unclaimed until the source/proof lane and both independent reviews close their
premises.

## Gate and evidence limits

`NO_SAFE_CODE_SLICE` remains in force until the R150 rev2 correction and the
R151 source result each receive CLEAN independent review. This is a read-only
owner handoff, not review or theorem closure. No code, tests, builds, or
executions were changed or run. No scratch paths were created.
