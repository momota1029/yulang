# General B4 source boundary: inventory and blockers

Status: Draft implementation inventory, 2026-11-11. This records the authorized
partial-structure fallback, not a general instance or a new language decision.

## Result and authority

There is no `generalVocabulary`, `generalBoundary`, or `generalExecutor` in this
change. The surveyed modules do not supply a faithful general registry, the
connection between ordinary constraints and role inspection, or general
post-propagation survivors. Filling those holes requires more than assembling
existing definitions. `Yulang.GeneralSourceBoundary.DefinedFields` and its
concrete value `definedFields` inventory the usable components without providing
parameters for the missing fields. No fragment is promoted to a general boundary.

Authority:

- [Approved B4 draft, including the 2026-11-11 addendum](2026-11-08-b4-main-statement-draft.md):
  vocabulary, independent classification, the five theorem clauses, pending
  priority, and lossless diagnostic trees.
- [Roles specification](../../spec/06-roles.md), §§6.2–6.5 and its final K2
  decisions subsection (2026-11-07/08): caller-visible
  implementations, shared associated equalities, lower-head deferral, normalized
  declaration descent, K2 before ambiguity, and conjunction of where siblings.
- [Skeleton design](2026-11-11-cycle112-b4-skeleton.md),
  [gap analysis](2026-11-11-b4-gap-analysis.md), and
  [Lean module guide](../../lean/README.md) guided the survey; their descriptions
  were checked against the relevant definitions and module scope statements.

All names below are under `Yulang`. A module name is also its file basename
under `lean/Yulang/`, except `B4Target`, which is in `lean/Main.lean`.
“Independent” means independent of an executor's returned classification, not
that a missing source bridge has been established.

## Field-by-field mapping

### Vocabulary and execution

| Field | Status and concrete definition | Fidelity, missing piece, and independence |
| --- | --- | --- |
| `Vocabulary.Registry` | **MISSING**. Closest: `Roles.AssocEnv` / `Roles.AssocImpl` in `RolesAssoc`; `CommonRoleHeadDetermination.Declaration`; `CommonRoleStablePaterson.Declaration`; `CommonRoleSettledFrontier.Registry`. | Draft vocabulary and §6.3 require where children with associated equations, explicit declaration identity, head normalization, and declaration checks. `Roles.Impl.constraints : List Roles.Goal` cannot hold a child's associated equations. `AssocImpl.assoc` only annotates the parent. `HeadDetermination` has a restricted record grammar; `StablePaterson` uses int/pair/join/tick Forms; `SettledFrontier` is unary/settled. Smallest prerequisite: an integrated declaration/where-equation carrier with scope and normalized check judgments. No registry is chosen. Independent of execution. |
| `Vocabulary.State` | **MISSING**. Defined component: `GeneralSourceBoundary.OrdinaryState α := List (PresenceNormalForm.Atom α)`. Shared equation graph: `CommonPresenceConstraintGraph.Compiled n`. Separate inspection graph: `CommonRoleRegularGraph.Graph n`. | Draft state and §6.3 require one shared constraint state with associated updates, lower/upper endpoints, and graph identities. `CommonRoleSettledConstraints.State n` contains ordinary atoms and grammar proofs; the settled resolver keeps its type graph in a separate namespace. Merely pairing arbitrary atoms with an arbitrary inspection graph permits disagreement. Smallest prerequisite: source identities and a proved correspondence from reconciled ordinary bounds to the inspection graph, retained across allocation and updates. Independent. |
| `Vocabulary.Demand` | **MISSING**. Defined interval component: `GeneralSourceBoundary.Argument α := CommonRoleIntervalGeneration.Argument α`, namely two `TyTerm α` endpoints. | Draft demand requires multiple normalized role arguments and the associated output obligations from §6.3. `CommonRoleIntervalPaterson.Goal` is a fixed Form grammar; `CommonRoleOpenProducer.Request` is unary; `CommonRoleSettledFrontier.Request` forces equal endpoints when known. Existing `TyTerm` covers all current finite ordinary constructors, but has no explicit nominal constructor or recursive binder; variable interpretations can still be arbitrary Common types. Smallest prerequisite: a full normalized source demand linked to state identities and associated outputs. Independent. |
| `Vocabulary.Model` | **DEFINED COMPONENT**: `GeneralSourceBoundary.Model α := α → Core.PresenceGeneration.Comp Common.model`. | Draft's Common assignments, retaining type and row components and using one assignment across all sibling constraints (§6.3). This is usable independently of a solver. It is not a claim that the source nominal carrier has been connected: `CommonNominalFullCarrier.model` in `CommonNominalFullModel` is a separate, richer carrier with its own integration obligations. The full vocabulary remains unavailable. |
| `Executor.run` | **MISSING**, also blocked by the frozen result type. Closest general outer combinator: `CommonRoleOutermostResolver.resolve`; actual restricted drivers: `CommonRoleOpenRecursivePass.run`, `CommonRoleStructuralAssociatedClosure.saturate`, `CommonRoleStructuralAssociatedReplay.run`. | Draft (1),(2), addendum (2): saturation must regenerate siblings/parents and return a lossless tree. The outer combinator requires frontier exactness and accessibility and does not update sibling state. The open pass uses unary dual inspection and external allocation; the structural closure uses fixed occurrences and scalar associated outputs. Smallest prerequisites: general independent update rules, dynamic child/allocation closure, their termination argument, and a tree-valued target interface. This is the only execution-side row. |

### Every `SourceBoundary` field

| Field | Status and concrete definition | Fidelity, missing piece, and independence |
| --- | --- | --- |
| `Checked` | **MISSING**; existing checks are **fragment-only**: `CheckedRoles.checkImpl`, `CommonRoleNormalizedDeclarations.checkImpl`, `CommonRoleStablePaterson.check`, `CommonRoleHeadDetermination.Declaration.check`. | Draft vocabulary; §6.3 requires hidden-field removal, same-tag merging before counting, rejection of first merges after capture, and associated determination. Raw `Roles.Impl.WellFormed` measures raw first-order terms. The normalized checker covers a restricted pattern language; the stable checker covers Forms; neither supplies the full declaration judgment. Need the integrated normalized registry check, independently of resolution. |
| `Models` | **MISSING for full State**; **DEFINED ordinary/graph components**: `GeneralSourceBoundary.Models`, `CommonPresenceConstraintGraph.Compiled.Models`, packaged as `definedFields.ordinaryModels` and `.equationModels`. | Draft state and (1),(4): satisfaction is at a specified Common assignment, not the proposition that some model exists. `reconcile_graph_models` connects these actual components and preserves original type/row readback. Need the remaining state/inspection/associated-update correspondence. Both predicates are independent of execution. |
| `Step` | **MISSING**; closest actual transition relation: `CommonRoleStructuralHornSchedules.Step` and `.Execution` (**finite fixed-clause fragment**). | Draft (1), §6.3 sibling regeneration: these rules add seeds, structural decompositions, transitive consequences, and fixed Horn conclusions. They do not generate general where invocations or implement full role/ordinary feedback. Need an integrated causal state transition over the general carrier. Not replaced by list append, an arbitrary rank, or a supplied trace. Existing relation is independent. |
| `Stable` | **MISSING**; closest `CommonRoleStructuralHornSchedules.Closed` (**same fragment**). | Draft (1), §6.3: final stability includes all generated demands and the end-of-file context. Closure under a fixed finite rule set does not establish that no later sibling or associated update changes the frontier. Need closure of the general transitions and demand regeneration, with finalization at file end. Not defined as equality with a returned state. |
| `Generated` | **MISSING**; `CommonRoleOpenFiniteClosure.Reach`, `CommonRoleGeneratedWhereClosure.Reach`, and `CommonRoleIntervalWorkClosure.Reach` are **restricted child closures**. | Draft selected/where rule and (1): every instantiated where child must retain shared repeated-variable endpoints and associated output equations. The unary/first-order/Form closures do not generate the missing general declaration carrier. Need a source-identified child-generation relation and its dynamic closure. No reachability from an executor return is substituted. |
| `RootPending` | **MISSING for source**; **DEFINED graph component**: `GeneralSourceBoundary.GraphUnresolved graph lower`, the node equality `graph lower = .unresolved`. | Draft pending, addendum (1), §§6.3–6.4: wait for the lower head; an upper bound or a singleton registry must not select it. `CommonRoleGraphDemandSnapshots.lowerHeads` explicitly omits unresolved seeds, so empty/nonempty alone is insufficient. Need reconciled source lower-head observation, including multiargument demands. The graph component is independent and is not called full `RootPending`. |
| `RootK2` | **MISSING for source**; **DEFINED graph component**: `GeneralSourceBoundary.GraphK2 := CommonRoleGraphBisimulation.RegularAt`. | Draft rejection (i), spec K2 decisions (2026-11-07/08): detect anonymous cycles and finite unrollings, keep nominal bodies opaque. This graph predicate is more general than the settled unary encoding, but its connection to the full Common/source carrier is explicitly open. Need the same source/inspection bridge as `RootPending`. Independent, with graph-local exclusion proved. |
| `CandidateK2` | **MISSING**. `CommonRoleGraphInspection.inspectAll` retains `.cycle` observations; complete classification exists only in **settled/unary fragments**. | Draft rejection (ii), spec K2 decisions (2026-11-07/08): a cycle encounter matters only in a surviving applicable candidate and precedes ambiguity. An observation before interval propagation is insufficient. Need applicability and K2 jointly linked to general propagated candidates. Cannot set this to “any inspection encountered a cycle.” Inspection itself does not use the outer executor. |
| `InspectionPending` | **MISSING**. `.unresolved` observations in `CommonRoleGraphInspection`; deferred trials in `CommonRoleOpenProducer` / `CommonRoleSettledFrontier` are **fragment-only**. | Draft safe selected/ambiguous rules and §6.3 deferral: preserve unfinished inspection through propagation and sibling updates. Need the general inspected-candidate relation and its lossless pending representation. Independent observations alone do not establish the field. |
| `Survivor` | **MISSING**. General ordinary pieces: `CommonRoleCandidateConstraints.generate` / `.Compatible`, `CommonRoleSourceIntervalBatches.cross`; candidate selection is **fragment-only**: `CommonRoleIntervalCandidateFrontier.Fits`, `CommonRoleIntervalCandidates.Accepts`, `CommonRoleSettledFrontier.TrialRule`. | Draft reconciliation and selected rules: self/cross interval checks and ordinary propagation, repeated-variable merging, all substituted where children; alternatives remain separate. The interval frontier checks scalar heads, Form capture excludes repeated-variable and join heads, settled trials cannot represent general narrowing. Need their integrated general capture/propagation/child judgment. `GeneralSourceBoundary.Compatible` proves only one candidate's captured interval checks, with no substitution search and no executor dependence. |
| `Evidence` | **MISSING**. Closest: `RoleDictionaries.Dictionary`, `CommonRoleIntervalDictionaries.Dictionary`, `CommonRoleScalarDictionaryModels.Implements`. | Draft (4), §§6.2–6.3: evidence must agree with the real head, every where child, and associated equations under the same arbitrary final model. First-order dictionaries do not have that general model interpretation; interval dictionaries use restricted Forms and still emit ordinary obligations; scalar model evidence is unary with no where children. Need a source-indexed dictionary relation including captures and associated equalities. Existing proof objects are not promoted to this field. |
| `Reorders` | **MISSING**. Closest: `List.Perm` over settled declarations and `CommonRoleSourceEnvironmentCongruence.Same` (**scalar/rigid pipeline**). | Draft (3), §§6.2–6.3: change visible enumeration and where order while preserving actual declaration/obligation identities and equations. Membership equivalence is useful for repeated enumeration, but does not construct permutations of general where clauses. Need the full registry plus a relation retaining obligation identities through permutations. Independent of output. |
| `DictionaryEquivalent` | **MISSING**. `CommonRoleDiagnosticOrder.Equivalent` is diagnostic-tree equivalence in a **rigid fragment**; it only permutes overlap heads and preserves selected child positions. | Draft (3), §6.3 sibling conjunction, skeleton's source-obligation canonicalization direction: compare dictionaries by the same source obligations, preserving multiplicity and identities. Need obligation-indexed evidence and a canonical comparison/readback. Literal child-list equality and a multiset of implementation keys are insufficient. No universal relation or output equality is used as a replacement. |

## Why the frozen target cannot be the faithful final interface

Two approved corrections have not reached `Main.lean`:

1. `B4Target.RejectReason` still contains unguarded
   `∀ key children, ¬ Survivor ... key children`. With an unresolved lower head
   and no visible implementation, both legacy pending and rejected hold.
   `GeneralSourceBoundary.ResolvedEmpty` records the addendum's guarded reason
   (iii), and `pending_excludes_resolvedEmpty` proves its exclusion. This is a
   check of the guard for arbitrary boundaries, not a general source instance.
   `legacy_frontier_obstruction` proves a stronger interface-local consequence:
   at such a snapshot, **no** protocol with the legacy `B4Skeleton.Local` can
   satisfy `FrontierExact`, even before choosing an executor or final state.
2. `B4Target.Executor.run` returns `State × Result`, and `Exact` requires total
   four-way classification. Addendum (2) requires `State × Tree` with
   `Resolves Local` exactness; `B4Skeleton.Completed` only reads completed trees.
   A selected parent containing a failed child must remain that parent tree.
   `B4Skeleton.rejected_child_has_no_completed_readback` already demonstrates
   this obstruction. Reusing `CommonRoleOutermostResolver.combine` to fold
   child failure would violate the approved boundary.

There is a related representation gap: `InspectionPending` prevents `SafeKnown`,
but the current `Classify.pending` and `B4Skeleton.Local.pending` constructors
accept only `RootPending`. A general lossless local interface must express an
unfinished nested inspection without silently claiming that the root head is
unknown. No additional classification rule is introduced here.

The task freezes those existing files. An eventual approved-interface successor
can be added in a new module, but doing so alone would not fill the source holes.
This change leaves the old target intact and proves no `B4Bridges` field for a
general boundary.

## Lean deliverable and exact scope of the proofs

New module: [GeneralSourceBoundary.lean](../../lean/Yulang/GeneralSourceBoundary.lean).
`DefinedFields` has concrete signatures for ordinary model satisfaction,
captured interval compatibility/generation, ordinary graph compilation and
models, graph-local unresolvedness, and graph-local K2. `definedFields` supplies
existing definitions or the explicit independent predicates above. It has no
missing-registry/solver fields to fill by arbitrary propositions later.

Five public theorems, all in `Yulang.GeneralSourceBoundary`:

- `reconcile_models`: for every `α : Type`, old ordinary state, finite capture
  list and assignment, the reconciled constraints hold iff the old constraints
  and every same-name self/cross comparison hold at that same assignment.
- `reconcile_graph_models`: for every finite slot count and those same inputs,
  models of the actual compiled reconciled graph with exact original assignment
  readback exist iff the old constraints and captured comparisons hold. This
  composes the real graph compiler's model correspondence, not a candidate
  solver or an existential implementation-substitution search.
- `unresolved_excludes_graphK2`: for every finite inspection graph and node,
  an unresolved node does not satisfy `RegularAt`. This establishes only a
  graph-local property until the source observation bridge exists.
- `pending_excludes_resolvedEmpty`: for every target vocabulary, boundary,
  registry, state and demand, `RootPending` excludes the addendum-guarded
  empty-survivor reason. This checks a proposed guard, not the frozen target.
- `legacy_frontier_obstruction`: for every target vocabulary, boundary,
  registry, state and demand with root pending and no survivors, any protocol
  whose `Local` equals the legacy local judgment fails `FrontierExact`.

The full quantified Lean statements are in that module and each public theorem
has an appended audit command. No general correctness, termination, dictionary
soundness, or bridge closure is claimed.

## Requested examples remain unproved

These are acceptance obligations for the future general instance, not new
fragment examples counted as completion:

1. §6.3's declaration `impl Display (list 'a): where 'a: Display`, at
   `Display (list int)` with a visible `Display int` leaf, should retain the
   selected list implementation and its selected `Display int` where child.
   The spec explicitly describes the descent `list (list int) → list int → int`.
   A general proof needs the list's invariant interval encoding, checked
   declaration, capture/propagation, and instantiated child relation. Existing
   `Roles` or settled proofs of a similarly shaped term would not prove this
   source-boundary obligation.
2. §6.3's `my z = default ()`, before its result lower head is known, should
   remain pending even with one visible `Default` implementation; with zero
   implementations, addendum (1) still requires pending. No implementation may
   be selected from its uniqueness or from an upper bound. At file end this
   becomes final pending only after stability. `GraphUnresolved` alone does
   not prove these source judgments.

Consequently step 4(a) has only a parametric guarded-reason sanity lemma and a
graph-local K2 exclusion. Step 4(b)'s two **general** classifications and step
5's general bridge remain open. This is the reason for using the explicit
step-3 fallback, not a claim that those checks were completed indirectly.

## Assessment of the existing proof direction

Some components are converging: centerless self/cross checks preserve arbitrary
Common assignments; `CommonPresenceConstraintGraph.compile_atoms_exact`
connects them to the real shared graph; the outer `Tree`/`Resolves` protocol
retains children; finite mixed Horn closure has an actual causal schedule.
These are reusable, independently stated results.

The fragment sequence is not yet converging to a **single general instance**.
`CommonRoleSettledSyntax` explicitly excludes multiple arguments, open record
tails, associated updates, and non-singleton intervals. The more recent scalar
registries still use distinct classification definitions and lack where
children. Their saturated entry keeps the visible scalar entries separate from
the associated environment. The first-order registry still cannot store the
where equations in §6.3's `Wrap` example. None of those limitations is removed
by another scalar exactness or dictionary theorem.

The older gap analysis is partly stale: ordinary materialization is no longer
int-only. `CommonRoleStructuralOrdinaryMaterialization.decode` handles closed
int/pair/union/tick Forms. It still requires one distinct syntactic paired
payload, does not cover arbitrary source forms or recursive graphs, and is
explicitly incomplete for semantic entailment. Likewise
`CommonRoleStructuralAssociatedClosure` supplies actual alternating closure,
but on finite occurrence templates and scalar associated outputs.

The next prerequisite is the declaration/where-equation carrier and its
normalized checks, followed by the state-to-inspection correspondence and the
general propagated survivor judgment. Those prerequisites should precede another
fragment being counted toward B4 closure. No numerical completion estimate is
justified by this survey.

## Verification and review

Commands run from `lean/`:

| Command | Exit code | Result |
| --- | --- | --- |
| `lake build Yulang.GeneralSourceBoundary` (first run) | 1 | A missing unfolding in the new graph exclusion proof; repaired in the new file. |
| `lake build Yulang.GeneralSourceBoundary` (after repair) | 0 | Module and dependencies built, 402 jobs. |
| `lake build Yulang` | 0 | New import and umbrella built, 1323 jobs. |
| `lake env lean Audit.lean > /tmp/astra-general-boundary-audit.log 2>&1` | 0 | Full audit including all five appended entries. |

The audit dependency whitelist check accepts only `propext`, `Classical.choice`,
and `Quot.sound`; the full audit reported no other dependencies. The first two
new theorems use `propext` and `Quot.sound`, the graph exclusion uses all three,
and the two interface checks use none. Original bytes of `lean/Audit.lean` and `lean/Yulang.lean` were verified
as unchanged prefixes; only the permitted appended lines were added.

An independent read-only reviewer checked the missing general definitions, the
partial fallback, and the new proof statements against their proofs. The review
found no proof/scope defect; its corrections to the K2 citation, state/graph
description, and exact names were incorporated. No registered `prover` role was available in the host
schema; the skill's repository `.codex/config.toml` and prover role file were
absent. The primary constructed this bounded derivation directly; no prover
agent ran. Review does not certify the unconstructed general instance.

No spec, plan, lake configuration, existing theorem body, or git reference is
changed. Existing Lean changes are the new umbrella import and appended audit
commands only. No parser lowering, method execution, full source model adequacy,
general saturation, or the two source classifications was verified.

## Open representation question — defer before choosing

For a multiargument role, which lower-head observations constitute root readiness,
and which remaining unknown arguments are pending inspections? For example:

```yulang
role Index 'container 'key:
    type value
    our container.index: 'key -> value

impl Index str int:
    type value = char

my lookup(c, k) = c.index k
// At a call, c is known to be str while k still has no lower head.
```

1. Keep the goal deferred until the observations needed for applicability are
   available; represent unresolved argument inspections explicitly and do not
   infer `k = int` from the lone implementation. This is the recommended
   conservative continuation of the approved wait-for-known policy.
2. Inspect the known receiver immediately while retaining a separate pending
   argument-inspection obligation; finalization must still wait for stabilization.

These options may be operationally equivalent after the missing graph/inspection
rules are specified. This change keeps the distinction open: it defines no
multiargument `RootPending`, readiness test, or executable classification. The
approved deferral and end-of-file rules remain constraints on either choice.
