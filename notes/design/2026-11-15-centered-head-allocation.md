# Clause-aware child-output allocation

Status: additive proof record, astra2-centered-29, 2026-11-15.

The successor repairs the representation without restricting source programs.
The original collision fixture now performs an actual installation that
generates both children and leaves an inhabited journal. Twelve operational
and order bridges transfer unconditionally. General selected-child production
remains conditional on the three explicitly scoped completion obligations below.

## Representation and operational integration

The supervisor's decision for this turn is to retain clause-local equation
IDs and repair purpose-5 allocation. The new private output origin is

```text
(invocation, declaration.id, 5, pair(clause.id, equation.id), 0)
```

`GeneralNominalIdentities.pair` is injective. Using it inside the existing
origin representation keys the allocation by both source identities. It does
not require equation IDs to be globally unique.

`GeneralNominalCenteredHeadAllocEncoding.registry` compiles the internal
allocation view of each declaration:

- Every clause output equation ID becomes `pair(clause.id, equation.id)`.
- Every output-binder producer reference receives the same transformation.
- Clause IDs, declaration IDs, binder names, type patterns, associated bodies,
  catalogue and role declarations are retained.

The two identity consumers are migrated together: `Produced` still locates
the same producing equation, while purpose-5 reservation and consumption use
the paired key. Purpose-2 shared binder allocation is unchanged. This respects
§6.5's requirement that repeated uses of an implementation variable name the
same actual argument: 「同じ型変数を使い回すと同じ実際の引数を指す」.
The distinction between independent output equations and deliberately shared
output binders is preserved.

The direct successor allocation is in
`GeneralNominalCenteredHeadAllocAllocation`. Its exact bridges are:

| Theorem | Conclusion |
| --- | --- |
| `keys_exact`, `reserved_exact` | The direct successor reservations are exactly the existing kernel's reservations over the compiled registry. |
| `output_identity` | Two private outputs agree precisely when both clause IDs and equation IDs agree. |
| `output_reserved` | Every visible clause output's repaired target is reserved. |
| `capture_unchanged` | Compilation preserves the input/output capture function. |
| `compiled_output_target` | The actual compiled output consumer equals the direct successor allocator. |
| `shared_binder_unchanged` | A named output-variable producer continues to use its purpose-2 capture. |
| `child_demand` | The compiled kernel emits the direct successor child demand, including all named output targets. |

The successor is operationally defined by

```lean
GeneralNominalCenteredHeadAllocBoundary.Step r =
  GeneralNominalCenteredHeadMatStepKernel.Step
    (GeneralNominalCenteredHeadAllocEncoding.registry r)
```

Its state is the existing total-materialization journal state. The entire
kernel consumes the compiled registry: stored packets, plans, total output
schemas, centered child schemas, class effects, live effects, full journal
models and the trusted observation ledger use that same allocation view.
Local's registry-dependent predicates, OutputConflict and Evidence also use
it. There is no side channel that feeds an uncompiled declaration to an
installation. Refresh and reobservation retain their existing justified-model
certificates and transition rules.

The new boundary's `Checked` and `Initial` are exactly the original source
predicates. `Encoding.declaration_checked`, `registry_checked`, `coverage`
and `initial_source` establish their compiled counterparts. They do not add
a uniqueness, source-form or model-existence requirement. All source paths
map directly to old kernel paths over the compiled registry by
`Boundary.reachable_compiled`; this is definitional transport of the whole
successor relation, with no restricted-step premise.

## Closed laws and executor

The executor runs the previous canonical executor on the compiled registry.
`Encoding.declaration_reorders` and `registry_reorders` cover declaration
and requirement reordering, including transformed producer references.
The existing journal/effect/trusted-ledger permutation simulation therefore
applies to the compiled registry in both directions.

`GeneralNominalCenteredHeadAllocComposition.twelveLaws roles` packages these
twelve bridges with their reachable-state quantifiers:

| Field | Exact proving theorem, with prefix `GeneralNominalCenteredHeadAlloc` |
| --- | --- |
| progress | `Executor.progress` |
| execution | `Executor.execution` |
| halted | `Executor.halted` |
| closure | `Boundary.closure` |
| stepModels | `Boundary.stepModels` |
| frontierLocal | `Executor.frontierLocal` |
| localIdentity | `Executor.localIdentity` |
| whereAccessible | `Boundary.whereAccessible` |
| treeExecution | `Executor.treeExecution` |
| canonicalLocalOrder | `Executor.canonicalLocalOrder` |
| dictionaryRefl | `Boundary.dictionaryRefl` |
| initialReorders | `Boundary.initialReorders` |

The Local fields use V6 Local, including OutputConflict; they are not silently
identified with V5 Local. The source-domain Checked/Initial premises remain
unchanged. `Executor.canonical_exit_lifting` closes the corresponding successor
exit-lifting predicate. `Executor.exact`, `saturationTotal` and `orderIndependent`
prove the named V6 target clauses with no completion assumptions. The package
does not claim the full `B4TargetV6.Statement`.

## Actual repaired collision trace

The original source registry, initial context and root are reused literally.
Its schematic source is

```yulang
impl P int:
    where R(out = int), S(out = :tick int)
```

The two clauses still have IDs 42 and 44, and both locally use equation ID 43.
`GeneralNominalCenteredHeadAllocCollision.schema_exact` computes the actual
compiled output schema as

```text
t(pair(42,43)) = int
t(pair(44,43)) = :tick int
```

`CollisionSource.targets_distinct` proves that the targets differ. The final
model assigns the second target `:tick int`, retaining the original model on
every source identity. `Collision.packet_models` proves the complete corrected
packet meaning, and `installation_models` also proves all live ledger clauses.
`installable` and `novel` feed the real install constructor in `Collision.step`.

`GeneralNominalCenteredHeadAllocCollision.collision_repaired` is closed and
asserts: original Checked, original Initial, successor V6 selected, one real
successor Step, inhabited final Models, two emitted children, and both children
in Generated. It asserts generation of the two demands, not installation or
resolution of their own implementations; the fixture has only P registered.

## General completion: proved part and remaining hypotheses

`GeneralNominalCenteredHeadAllocOutputModels.target_injective` proves that
distinct checked source producers have distinct private targets.
`fill_value` constructs arbitrary independent values at all those targets.
`fill_other_purpose` preserves every source origin whose purpose differs from
5, in particular every purpose-2 shared binder. `source_extension` extends any
model of an InitialSource while preserving every original source identity and
all purpose-2 identities. Its premises are an InitialSource, its model, a
declaration's existing Identified judgment, and the desired producer values.
No extra source restriction is introduced.

This is a concrete part of PacketAssembly: the old cross-clause equation
collision no longer forces unrelated outputs equal. It does not yet establish
that arbitrary new assignments preserve every previously installed packet or
that their values satisfy all input/center schemas in the same journal model.

All remaining completion predicates live in
`GeneralNominalCenteredHeadAllocCompletion`; they quantify over the original
source registry and reachable states of the repaired Step. Effects carry
`effect.registry = Encoding.registry sourceRegistry` and
`effect.snapshot = state.core`.

1. `HeadBaseline roles`: each reachable selected demand has one current journal
   model satisfying its `ChosenHead`, including a recorded Frame, readiness of requested role effects,
   and centered head equations.
2. `PacketAssembly roles`: a common current journal/chosen-effect model extends
   to a model also satisfying the entire corrected packet, with the chosen
   effect retained. This includes input support, materialized child endpoints
   and centers, existing ownership/revisits and historical journal constraints.
3. `ChoiceFromCommon roles`: for a reachable selected plan with that common
   model, every previously installed packet in its alias class has the same
   declaration key.

None of these three predicates is proved in general here. They are not imported
as universal claims about uncompiled registries, where the previous negative
theorem still applies. `extension_iff` and `selected_installable_iff` retain
the exact current/common-model and choice requirements. `selectedCompletion`
derives the repaired completion predicate from the three named hypotheses;
`generatedSelectedChildren` then proves V6-selected child production.
`Composition.withProduction` packages precisely that conditional result.

The production interface requires V6 Local selected, and therefore absence
of OutputConflict. No proof of the stronger conflict-insensitive V5 production
field is claimed. The remaining EvidenceNode obligation for dot has exact type

```lean
B4SkeletonV5.EvidenceNode
  (B4TargetV6.prior (GeneralNominalCenteredHeadAllocBoundary.boundary roles))
```

There is no new certified counterexample or owner question in this turn.
The full common-model/choice proof and exhaustive K2 projections remain open.

## Validation

The direct derivation was constructed by the primary, with fresh independent
read-only review of the operational integration, concrete regression, output
model extension, completion predicates, twelve-law package and full audit. No
configured or callable `prover` role was available. Final commands and their
exit codes are recorded after execution below.


All commands ran from the repository root:

| Exact command | Exit code |
| --- | --- |
| `cd lean && lake build --wfail Yulang.GeneralNominalCenteredHeadAllocComposition Yulang.GeneralNominalCenteredHeadAllocCollision` | 0 |
| `cd lean && lake build --wfail Yulang` | 0 |
| `cd lean && lake build --wfail` | 0 |
| `cd lean && lake env lean Audit/GeneralNominalCenteredHeadAlloc.lean` | 0 |
| `git diff --check` | 0 |

The audit covers 107 new public theorems; its dependency set is exactly
`propext`, `Classical.choice`, `Quot.sound`. Scope checks confirm ten new
modules, an import for every one, and only appended root imports and an index
entry among existing files. HEAD remains
`39b4a94d08c4cac8b07447ac003feb7ef14983c4` on `astra2/centered`.
