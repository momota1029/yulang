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

## Item 2

Status: **partial implementation, 2026-11-12**. The owner selected option 1
above, recorded as addendum 3 of the approved draft. The implementation follows
whole-demand deferral. This section supersedes the earlier open question; it
does not reopen the owner's choice.

New modules:
[GeneralSourceState](../../lean/Yulang/GeneralSourceState.lean) and
[GeneralSourceStateExamples](../../lean/Yulang/GeneralSourceStateExamples.lean).
No registry carrier or declaration checker was added. Existing `Roles.RoleDecls`
supplies arity and associated-output names. Item 1 remains with its other owner.

### Shared state and its invariant

`GeneralSourceState.State` is a checked snapshot with a finite slot count,
arbitrary existing ordinary type/row atoms, source type-node IDs, independent row
IDs, centerless endpoint pairs, and typed inspection-head descriptions.
`State.graph` computes the existing inspection graph from those descriptions;
there is no independent arbitrary graph field. Scalar codes use the existing
injective scalar encoding. Structural codes index an injective table of typed
signatures, including arrow-row syntax and exact child arity.

`HeadModels` has a concrete definition: each recorded scalar/constructor gives
an equation, up to `Common.Equivalent`, between its original ordinary slot and
the constructor applied to its original child slots. An unresolved observation
asserts no equation. The state requires a proof that **every ordinary model**
satisfies these equations and every registered interval's lower/upper comparison.
Those conditions are not imposed by silently narrowing the ordinary model set.
`models_ordinary` proves that the full snapshot `Models` is exactly ordinary
satisfaction. `models_compiled` connects it to the real shared equation-graph
compiler and exact original type/row readback. `recorded_head_sound` exposes the
per-node consequence to later work.

The source ID map is injective: repeated references to the same ID denote the
same slot and graph node (`shared_source_node`). Row IDs are separate; matching
type-node identity does not impose an equality between unrelated effect rows.
This does not yet canonicalize **different** source names equated by ordinary
constraints. `Models` uses a global `Nat → Comp Common.model` assignment, so
different finite snapshots can be compared without changing the model carrier.

This is not a general materializer or proof of source reachability. In
particular, all-model implication can hold vacuously on inconsistent ordinary
constraints, and an unresolved observation can conservatively remain even when
the constraints entail more information. It does not certify that the recorded
interval is the fully propagated source bound. These limits prevent claiming a
complete source-state/normalized-inspection correspondence.

### Demand and deferral

`Demand roles` stores a role, exactly `roles role |>.arity` source endpoint pairs,
and the complete supplied list of named associated-output obligations. Each
output name must be declared by the role; its target is an ordinary source
variable. No output RHS or default is selected in this layer. Repeated output
obligations are retained. `Linked state demand` proves that every argument pair
occurs in the state and that every output target has a source slot.

This represents endpoints by source IDs; it does **not** normalize arbitrary
source type expressions or establish all same-head interval simplifications.
The fully normalized demand requested in item 2 remains missing.

`Needed demand` is the permitted abstract applicability-argument set, a predicate
on the finite positional argument indices. Item 3 must produce that set from
the applicability rules. This layer makes no receiver-only, all-arguments, or
singleton-implementation choice. The `Index` example supplies both positional
arguments explicitly. Associated outputs are not silently treated as positional
inputs.

`RootPending state demand needed` holds exactly when a needed argument lacks a
recorded lower head. On linked demands, `pending_graph_iff` identifies this with
an actual lower source node satisfying `GeneralSourceBoundary.GraphUnresolved`.
Only the lower endpoint is queried. An unlinked reference conservatively lacks
a known head; the graph equivalence theorem explicitly requires `Linked`.
The final end-of-file/stability policy is unchanged and is not implemented here.

`Refines before after` is a contract for future updates, not the language `Step`:
it supplies a source- and row-ID-preserving slot embedding, inclusion of renamed
old atoms, preservation of recorded knownness, and retained interval pairs.
It proves model decrease, retained linkage, and pending antitonicity for the
**same** demand and fixed `Needed` set. Mere atom inclusion is not claimed to
refresh observations or imply this contract. The `Index` example provides a
concrete instance after an explicit ordinary equality for the key is added.

“No retroactive rejection” is deliberately snapshot-specific:
`pending_defers_decisions` excludes the gated graph-cycle observation and guarded
empty-survivor reason at the old pending snapshot. Resolving a head may legitimately
expose a cycle or no candidates in a new snapshot. No theorem says rejection
can never occur later.

### Why source RootK2 remains missing

The initial all-model equation invariant was challenged by independent review.
The following raw self-tail equation is satisfied by a finite type:

```text
x ≈ { L: int, ..x }
x = { L: int }
```

`Common.common_shadowed_head_equivalent` proves this after hidden-field removal.
A raw graph for the equation nevertheless has a self-cycle through the tail.
`shadow_cycle_counterexample` now constructs that graph inside a checked,
model-inhabited `State`, links its demand, and proves both the graph-cycle flag
and the literal finite lower type. Thus the issue is a concrete false-positive
family, not just an absent proof.

The code therefore defines **`ObservedRootK2`**, not source `RootK2`. It preserves
`RootCycleObserved` but gates actionable observation on `¬ RootPending`, as
required for whole-demand deferral. `pending_excludes_observedK2` proves that
exclusion. Neither predicate may be used as the general source K2 field.

A general normalized projection also has to reconcile equivalent row syntax
in arrow tags, required fields versus record-with-empty-tail presentations, and
ordinary aliases of different unresolved source IDs. The injective signature
table prevents accidental tag collisions; it does not prove semantic
canonicalization. `Common.model` still lacks the separate nominal carrier's
constructor. The current head vocabulary has selected Common constructors, not
all ordinary syntax. Unsupported observations must remain deferred until a
justified view is available; they must not become rejection.

The next missing piece is an independently defined source normalization and
inspection correspondence that excludes the hidden-tail counterexample and
handles these canonicalization cases. A free `Normalized : Prop` assumption
would only conceal this gap. No such field was added. This is an implementation
gap under the existing owner decisions, not a new language-semantics question.

### Current field status

Here `S` means `GeneralSourceState`. “Component” is not a completed B4 field.

| Requested item-2 row | Status after this change |
| --- | --- |
| `Vocabulary.State` | **DEFINED checked Common snapshot component:** `S.State`, `S.State.graph`. **MISSING** general normalized source observation and materialization correspondence, alias canonicalization, and nominal integration. |
| `Vocabulary.Demand` | **DEFINED carrier:** `S.Demand`, `S.Linked`, positional arity and associated-output targets. **MISSING** general source-type/same-head normalization. |
| `Models` | **DEFINED for this full checked snapshot:** `S.Models`; exact ordinary and compiled-graph agreement proved. No unrestricted source-state adequacy claim. |
| `RootPending` | **DEFINED for linked snapshots and supplied applicability indices:** `S.RootPending`, `S.pending_graph_iff`. Derivation of `Needed`, complete source observation, and finalization remain missing. |
| `RootK2` | **MISSING** for normalized source semantics. `S.RootCycleObserved` and `S.ObservedRootK2` are graph components only; a concrete counterexample prevents promoting them. |

All 13 boundary fields, as required by I-18:

| Field | Current status |
| --- | --- |
| `Checked` | **MISSING in this work**; item 1 belongs to the other owner. |
| `Models` | **DEFINED checked-snapshot component**, `S.Models`. |
| `Step` | **MISSING**; `S.Refines` is an update contract, not saturation. |
| `Stable` | **MISSING**. |
| `Generated` | **MISSING**. |
| `RootPending` | **DEFINED snapshot component**, `S.RootPending`, conditional on the applicability set and linked source observations as above. |
| `RootK2` | **MISSING**; only graph observation is supplied. |
| `CandidateK2` | **MISSING**; item 3. |
| `InspectionPending` | **MISSING**; item 3. |
| `Survivor` | **MISSING**; item 3. |
| `Evidence` | **MISSING**. |
| `Reorders` | **MISSING**. |
| `DictionaryEquivalent` | **MISSING**. |

`generalVocabulary`, `generalBoundary`, and an executor remain unconstructed.
Item 2 is not closed. The earlier assessment of fragment convergence is unchanged:
this work adds shared interfaces and a falsifier for a proposed bridge, rather
than another fragment-specific `Classify` theorem.

### Examples and handoff to item 3

- `index_example`: the two-argument Index demand is linked, all Common key types
  still model its ordinary state, and the demand is pending. Adding an explicit
  `key = int` equation gives an actual `Refines` witness and removes pending.
  No implementation is supplied or allowed to infer that equation.
- `recursive_example`: a linked unary demand has a real Common regular model
  `μ ≈ {7: μ}`, a graph-cycle observation, and no pending argument. This is
  **not** a general source `RootK2` theorem.
- `shadow_cycle_counterexample`: the raw record-tail graph flags a cycle while
  the lower endpoint is the finite type `{7: int}` in an ordinary model. A
  normalized source K2 implementation must exclude this case.

Item 3 can consume:

1. `Demand.arguments`, `Demand.outputs`, and `Linked`, retaining all endpoint
   and associated-output source identities. Capture invocations still need
   their own identities; they must not be identified merely by type equality.
2. `State.assignment`, `Models`, `models_ordinary`, `models_compiled`, and
   `recorded_head_sound` for a single type/row assignment across propagation.
3. `State.graph` and typed `Head`/`Shape` information as **checked raw views**,
   with an additional normalized source correspondence still required before K2.
4. `Needed` and `RootPending`: item 3 must derive the applicability set and retain
   pending for unresolved required inputs without fixing them from candidates.
5. `Refines` and its theorems as obligations on proposed updates. Changes to the
   applicability set or source normalization are not covered by the fixed-set
   pending monotonicity theorem.

Item 3 must still supply candidate-local capture/reconciliation, repeated-variable
merging, survivor filtering, every where/associated child, and inspection deferral.
It must not reuse `ObservedRootK2` as `CandidateK2` or source `RootK2`. No registry,
candidate, or dictionary carrier was built here.

### Item-2 checks

Final commands, run from `lean/`:

| Command | Exit code | Result |
| --- | --- | --- |
| `lake build Yulang.GeneralSourceState Yulang.GeneralSourceStateExamples > /tmp/astra-state-demand-build.log 2>&1` | 0 | Both modules, 421 jobs. |
| `lake build Yulang > /tmp/astra-state-demand-umbrella.log 2>&1` | 0 | Umbrella import, 1325 jobs. |
| `lake env lean Audit.lean > /tmp/astra-state-demand-audit.log 2>&1` | 0 | Full audit, all 16 new public theorem entries present. |

The full audit reports only `propext`, `Classical.choice`, and `Quot.sound`;
the whitelist check passed. The new files contain none of the excluded tokens.
The old contents of `Audit.lean` and `Yulang.lean` are unchanged byte prefixes.
`git diff --check`, audit-entry coverage, and design-note links passed.

Intermediate focused builds exited 1 on elaboration/reducibility and a tuple proof;
those errors were fixed only in the new files. No existing Lean theorem body
was edited. The skill's registered prover launch surface remains unavailable;
the primary constructed the bounded proofs and a separate read-only reviewer
challenged the design and reviewed the revised claims.

### Item-2 theorem statements

These are the complete public theorem signatures from the new modules.
Implicit parameters are universally quantified: slot counts are naturals,
`roles` is `Roles.RoleDecls`, and `before`/`after` are `State`. Names use the
respective module namespace and its opened namespaces, as in the source.

`Yulang.GeneralSourceState`:

```lean
theorem equationAtoms_exact (slot : Fin slots) (term : TyTerm (Fin slots))
    (assignment : Fin slots → Comp Common.model) :
    All Common.model assignment (equationAtoms slot term) ↔
      Common.Equivalent (assignment slot).1 (term.eval Common.model assignment)

theorem models_ordinary (state : State) (model : Assignment) :
    Models state model ↔ state.OrdinaryModels model

theorem models_compiled (state : State) (model : Assignment) :
    Models state model ↔
      ∃ values : Fin (CommonPresenceConstraintGraph.compile state.ordinary).size → Common.Ty,
        (CommonPresenceConstraintGraph.compile state.ordinary).Models
          (fun slot => (state.assignment model slot).2) values ∧
        (CommonPresenceConstraintGraph.compile state.ordinary).readback
          (fun slot => (state.assignment model slot).2) values = state.assignment model

theorem recorded_head_sound (state : State) (model : Assignment) (models : Models state model)
    (slot : Fin state.slots) (term : TyTerm (Fin state.slots))
    (recorded : (state.heads slot).equation = some term) :
    Common.Equivalent (model (state.source slot)).1
      (term.eval Common.model (state.assignment model))

theorem shared_source_node (state : State) (left right : Fin state.slots)
    (same : state.source left = state.source right) :
    left = right ∧ state.graph left = state.graph right

theorem pending_graph_iff (state : State) (demand : Demand roles) (linked : Linked state demand)
    (needed : Needed demand) :
    RootPending state demand needed ↔
      ∃ argument slot, needed argument ∧ state.source slot = (demand.arguments argument).1 ∧
        GeneralSourceBoundary.GraphUnresolved state.graph slot

theorem pending_excludes_observedK2 (state : State) (demand : Demand roles) (needed : Needed demand)
    (pending : RootPending state demand needed) : ¬ ObservedRootK2 state demand needed

theorem observedK2_graph_iff (state : State) (demand : Demand roles) (needed : Needed demand) :
    ObservedRootK2 state demand needed ↔
      ¬ RootPending state demand needed ∧
        ∃ argument slot, state.source slot = (demand.arguments argument).1 ∧
          GeneralSourceBoundary.GraphK2 state.graph slot

theorem refinement_models (refinement : Refines before after) (model : Assignment)
    (models : Models after model) : Models before model

theorem refinement_linked (refinement : Refines before after) (demand : Demand roles)
    (linked : Linked before demand) : Linked after demand

theorem refinement_known (refinement : Refines before after) (source : Nat)
    (known : Known before source) : Known after source

theorem refinement_pending (refinement : Refines before after) (demand : Demand roles)
    (needed : Needed demand) (pending : RootPending after demand needed) :
    RootPending before demand needed

theorem pending_defers_decisions (state : State) (demand : Demand roles) (needed : Needed demand)
    (pending : RootPending state demand needed) (survivor : Nat → Prop) :
    ¬ ObservedRootK2 state demand needed ∧ ¬ ResolvedEmpty state demand needed survivor
```

`Yulang.GeneralSourceStateExamples`:

```lean
theorem index_example :
    Linked indexState indexDemand ∧ (∀ key, Models indexState (indexModel key)) ∧
      RootPending indexState indexDemand indexNeeded ∧
      Nonempty (Refines indexState indexAfter) ∧
      ¬ RootPending indexAfter indexDemand indexNeeded

theorem recursive_example :
    Linked loopState loopDemand ∧ Models loopState loopModel ∧
      ObservedRootK2 loopState loopDemand loopNeeded ∧
      ¬ RootPending loopState loopDemand loopNeeded ∧
      Common.Equivalent loopType (Common.required 7 loopType)

theorem shadow_cycle_counterexample :
    Linked shadowState loopDemand ∧ Models shadowState shadowModel ∧
      ObservedRootK2 shadowState loopDemand loopNeeded ∧
      (shadowModel 0).1 = Common.required 7 (.base .int)
```


## Item 2b

2026-11-12, normalized source observation and root K2. This section supersedes
Item 2's raw-cycle status for **separately checked normalized snapshots**. It
does not claim a total materializer, complete language classification, or a
finished `generalBoundary`.

The new modules are:

- [GeneralNormalizedObservation.lean](../../lean/Yulang/GeneralNormalizedObservation.lean),
  namespace `Yulang.GeneralNormalizedObservation` (`N` below).
- [GeneralSourceK2.lean](../../lean/Yulang/GeneralSourceK2.lean), namespace
  `Yulang.GeneralSourceK2` (`K` below).
- [GeneralSourceK2Examples.lean](../../lean/Yulang/GeneralSourceK2Examples.lean),
  namespace `Yulang.GeneralSourceK2Examples`.

All are imported by `Yulang.lean`. The original state, demand, ordinary atoms,
interval endpoints, row identities, and associated-output links are unchanged.
There is no registry carrier, candidate choice, or executor in these modules.

### What the snapshot checks

`N.Rewrites state first last` is a finite, independent normalization derivation.
Its source steps use either an actual recorded head equation or both directions
of an equation occurring in `state.ordinary`. Its other steps are constructor
congruence, required-field expansion, hidden-field removal, swapping distinct
record fields, same-tag merging, and union idempotence. They reuse
`Common.common_shadowed_head_equivalent`,
`CommonPatternConcreteRecordTypes.record_swap`,
`CommonCanonicalShapes.variant_union_group`, and the existing Common constructor
congruences. This is a certificate calculus, **not an executable general
normalization algorithm**. No caller may replace a missing derivation by an
assertion that an inspection succeeded.

`rewrites_sound` quantifies every original Common assignment satisfying the full
shared state. `Snapshot.checked` requires such a derivation from the original
slot for every stored term. `observation_models` and `models_preserved` prove
that adding the checked observations discards no ordinary model. This is exact
preservation of Models, not completeness or uniqueness of the observations.
There is no claim that every Common-equivalent presentation has the same
certificate or the same K2 outcome. Inconsistent ordinary states still make the
old State's semantic head invariant vacuous; no consistency theorem or automatic
source materialization is supplied here.

Complete record signatures store **all** visible labels in strictly increasing
order, with one child per payload. Required fields and records with an
`emptyRecord` tail use the same signature (`required_record_same`). Distinct
signatures have distinct table indices, enforced by `shapes_injective`.
Consequently `{L: y, M: int}` cannot be mistaken for `{L: y}` merely because
its first field agrees. Payload edges reset field visibility; there is no raw
record-tail edge in the normalized graph.

A residual observation stores a visible prefix and the original tail term.
The prefix labels are the hidden-label context for that tail. A residual has
no complete graph head: `Head.node` gives `.unresolved`. The shadow fixture
unfolds `x` once under its record tail, exposes a duplicate `L`, removes it
using `Rewrites.shadow`, and retains the original residual reference. It does
**not** turn the equation `x ≈ {L: int, ..x}` into `x ≈ {L: int}`. The separate
`shadow_residual_model` theorem exhibits a model with another visible field.
The unknown residual is a normalization limitation, not a new rejection rule.
This snapshot does not decide that the shadow demand is finally accepted or
finally fails at end of file.

The new observation language accepts arbitrary finite arities, arbitrary labels,
pairs, complete records, variants, all scalar bases, and exact-empty heads.
The ordinary state and Common model carrier remain unrestricted. Unsupported
heads retain their terms as deferred observations. This is a partial interface
on the general state, not a scalar/settled/unary replacement for that state,
and there is no new fragment-specific `Classify`.

### Independent root criterion and why it is not nonfiniteness

The K2 decisions at the end of [spec/06-roles.md](../../spec/06-roles.md) explicitly
say that the root of `Check {box: μ}`, with `μ = {tick: μ}`, is not recursive.
A constructor-inspecting candidate can still trigger **candidate** K2 at `μ`.
Similarly, `Len (list μ)` without a where child passes the root rule. The whole
denotation of such a wrapper can require a recursive description. Therefore
“in every model no finite equivalent type exists” would reject too much;
changing “every” to “some” does not repair the root/descendant distinction.
It would also confuse an unknown residual's possible model with a known source
observation. No choice between those two proposed denotational criteria is made.

Instead `K.Child`, `K.Path`, `K.Cycle`, `K.read`, and `K.RecursAt` define an
independent normalized-observation criterion. A root either lies on a nonempty
visible payload path returning to itself, or its observations at **every finite
depth** agree with a root on such a cycle. A descendant's cycle alone is
insufficient. This accounts for finite unrollings without imposing a depth
cutoff. These definitions do not call the graph detector, a resolver, or an
executor. Signature indices refer to the snapshot's injective canonical table.

`child_graph_iff`, `path_graph_iff`, `cycle_graph_iff`, and `read_graph` prove the
actual correspondence with the existing graph. `graphK2_sound` proves soundness
against `RecursAt`; `graphK2_exact` proves the converse on a fully determined
snapshot using the existing finite-observation/bisimulation theorem. The
closed-view premise prevents distinct unresolved identities from becoming equal
merely because both read as unknown.

`K.RootPending` is defined from normalized lower-head knowledge and the supplied
`Needed` applicability-index set. The derivation of that set still belongs to
item 3. It replaces, for this snapshot, the earlier raw-head observation; the old
module remains unchanged. `pending_graph_iff` connects it to `.unresolved` at
the linked lower endpoint.

`K.Complete` requires every node reachable from an endpoint to have a normalized
head. `RootInspectionUnknown` records that some demand argument lacks such a
complete cone. It is distinct from lower-head pending: a known pair can have an
unsupported descendant. It ignores unrelated associated-output nodes.
`RootK2` requires a linked demand, no lower-head pending, no inspection unknown,
and a complete lower endpoint with graph K2. The extra inspection gate is
**conservative partial-normalizer deferral**, not a newly approved language
restriction. It may delay a cycle already visible on one branch while another
branch remains unsupported. It must not be finalized as rejection merely because
our materializer is incomplete.

`rootK2_sound` retains those gates and proves independent normalized recurrence.
`rootK2_exact` gives an iff for linked, ready, fully determined snapshots.
`rootK2_observation_sound` additionally identifies a normalized term for the
rejected lower endpoint and proves it equivalent to that endpoint in **every
original model**. It does not claim that the model itself has no finite
equivalent presentation. All public signatures are reproduced below.

### Canonicalization coverage and deferral

| Case | Implemented correspondence | Remaining work / required behavior |
| --- | --- | --- |
| Hidden same-name fields | `Rewrites.shadow`, congruence, and distinct-field swaps; full sorted signatures | Derivations must be supplied; no total source traversal or completeness theorem. |
| Raw self-tail `x ≈ {L: int, ..x}` | Explicit unfold/remove-duplicate derivation; original tail retained in `Deferred.residual` | Root stays unknown in this snapshot, never a graph cycle or K2 rejection. No empty-tail substitution. |
| Genuine `μ ≈ {L: μ}` | Required-field normalization retains the payload edge | The linked loop example is RootK2 and not RootPending. |
| Same-tag variants | `Rewrites.merge` for arbitrary payload terms; `duplicate_tag` and `duplicate_tag_source` contract repeated payloads | Unequal merged payloads need a materialized union child identity and a checked fold/readback bridge. Without it, keep `Deferred.unsupported`; no full variant-row normalizer is claimed. |
| Required field vs record with empty tail | `required_record_same`, one `Shape.record [label]` | Handled for this equivalence. |
| Arrow row-expression equivalence | Arrows are retained as unsupported terms, never complete signatures | No comparison of raw row expressions or row-slot IDs is used to reject. Canonical row observations remain missing. |
| Aliases with different unresolved source IDs | Literal source identities are retained; incomplete cones defer | No general alias quotient. Explicit ordinary equalities can be unfolded by certificates, but unknowns are not equated. |
| Nominals, defaults, other Common normalization | Retain unsupported terms | Nominal integration and additional canonical observations remain missing. Named bodies must remain opaque. |

`unknown_path_defers_rootK2` proves that any unresolved node on a normalized
argument path prevents this RootK2 reason. `pending_excludes_rootK2` and
`unknown_excludes_rootK2` state both exclusion gates explicitly. In particular,
`¬RootK2` alone is **not** permission to select, declare ambiguity, or issue an
empty-survivor rejection. There is still no full classification judgment here.

### Field table after Item 2b

`S` means `Yulang.GeneralSourceState`; all defined rows below are independent of
any executor. References to draft items mean the approved
[main draft and addenda](2026-11-08-b4-main-statement-draft.md).

| Requested row | Status and Lean name | Faithfulness / remaining obligation |
| --- | --- | --- |
| `Vocabulary.State` | **DEFINED checked component:** `S.State` with `N.Snapshot state` | Shared identities/ordinary bounds retained. Snapshot checks finite normalization certificates. Full materializer, nominal integration and normalization completeness **MISSING**. Draft assumptions and spec 6.3. |
| `Vocabulary.Demand` | **DEFINED carrier:** `S.Demand`, `S.Linked` | Existing Roles arity and associated names, centerless interval endpoints, outputs retain original identities. Deriving source demands/applicability set **MISSING**. Spec 6.2–6.3, addendum 3. |
| `Vocabulary.Registry` | **MISSING in this lane** | Item 1 remains owned by the other prover; no registry carrier added. |
| `Vocabulary.Model` | **DEFINED Common assignment carrier:** `S.Assignment` | One assignment supplies type and row components for all source identities; nominal integration remains missing. |
| `Models` | **DEFINED checked-snapshot component:** `S.Models`, `N.ObservationModels`, `N.models_preserved` | Every old ordinary model is retained; no model is selected to decide K2. Draft assumptions and model preservation. |
| `RootPending` | **DEFINED partial normalized snapshot predicate:** `K.RootPending`, `K.pending_graph_iff` | Whole demand waits for the supplied needed lower heads, including normalization-unknown heads. Final EOF handling and derivation of `Needed` **MISSING**. Addenda 1/3; spec 6.3. |
| `RootK2` | **DEFINED on checked partial normalized snapshots:** `K.RootK2` | Sound for independent `K.RecursAt`, exact on fully determined views. General Common-equivalence adequacy/total observation coverage **MISSING**. Draft local rejected case; spec K2 root-position decision. |
| `Checked` | **MISSING in this lane** | Item 1; snapshot checking is not impl declaration checking. |
| `Step` | **MISSING** | Existing `S.Refines` remains an update contract, not a source saturation step. |
| `Stable` | **MISSING** | No stable EOF or sibling-fixpoint driver. |
| `Generated` | **MISSING** | No source-to-demand or where-child producer. |
| `Survivor` | **MISSING** | Item 3 must integrate capture and interval propagation. |
| `InspectionPending` | **MISSING as a complete boundary field** | `K.RootInspectionUnknown` is a defined normalization-deferral component, not complete candidate inspection. |
| `CandidateK2` | **MISSING** | Must be based on actual surviving candidate inspections, not any recursive descendant. |
| `Evidence` | **MISSING** | General dictionary/model correctness remains open. |
| `Reorders` | **MISSING** | No general sibling/candidate order relation supplied. |
| `DictionaryEquivalent` | **MISSING** | General dictionary observation relation remains open. |
| `Executor.run` | **MISSING** | No executor introduced or used to define any field. |

No row is filled by a scalar, settled or unary fragment. Existing narrow
normalizers were surveyed but not adopted as general definitions.
`generalVocabulary` and `generalBoundary` are still unconstructed.

### Handoff to item 3 and remaining verification

Item 3 can use the original `S.Demand`/`Linked`/`Models` and the new
`N.Snapshot.checked`, `rewrites_sound`, `observation_models`, normalized graph,
`K.Child`/`Path`, and the two distinct deferral predicates. It must:

1. Derive the applicability argument set without allowing a singleton impl to
   fix an unknown argument. Keep output obligations separate from input heads.
2. Materialize merged payloads and record residuals with actual shared source
   identities and checked normalization evidence; keep unsupported observations
   deferred and revalidate snapshots after updates.
3. Prove survivor/capture/propagation correspondence, preserve every where child,
   and trigger candidate K2 only when a surviving candidate inspects a recursive
   constructor. Neither raw graph cycles nor arbitrary descendant cycles suffice.
4. Carry `RootInspectionUnknown` into inspection deferral. A negative RootK2 result
   is insufficient evidence for any other classification.

Not verified: automatic snapshot construction, unique/canonical outcomes across
all equivalent presentations, source expression reachability, arbitrary Common
nonfiniteness, nominal or arrow coverage, merged-child materialization, general
alias canonicalization, new-snapshot monotonicity, saturation termination,
finalization, candidate correctness, or any B4 bridge field. The older raw-state
refinement theorem does not automatically transport these normalized snapshots.

Assessment of convergence: this work makes concrete progress toward the general
instance because it connects existing arbitrary-Common normalization laws to the
shared state and original demand identities, with model-preservation and explicit
unknown gates. The old scalar/settled/unary classification theorems still do not
instantiate the general boundary. Their existence alone is not evidence that
B4 is nearly complete; the table still has substantial empty fields. The useful
reused results here are Common congruences, record/tag equivalences, finite graph
paths, and graph bisimulation, rather than fragment-specific classifier outputs.

### Semantic questions

No new language decision is required for the implemented partial snapshot.
Deferral follows the approved owner decisions; it is not a choice to reject
unsupported types. For example `impl R {L: int, ..a} where a: R` with a goal
whose residual has not been materialized keeps waiting. Arrow and unresolved
alias examples likewise remain unknown. Whether a particular solver update can
materialize a complete view is an open **proof/implementation obligation**, not
a request to choose new language semantics. No final EOF classification for an
implementation-unsupported observation is inferred here.

### Item-2b theorem statements

These are the full public signatures, copied from the source. Implicit `state`,
`roles`, source terms, and counts are universally quantified with their inferred
types; names resolve in each module's namespace and opened namespaces.

`Yulang.GeneralNormalizedObservation`:

```lean
theorem rewrites_sound (derivation : Rewrites state first last) (model : Assignment)
    (models : Models state model) :
    Common.Equivalent (first.eval Common.model (state.assignment model))
      (last.eval Common.model (state.assignment model))

theorem observation_models (view : Snapshot state) (model : Assignment)
    (models : Models state model) : ObservationModels view model

theorem models_preserved (view : Snapshot state) (model : Assignment) :
    Models state model ∧ ObservationModels view model ↔ Models state model

theorem deferred_graph (view : Snapshot state) (slot : Fin state.slots)
    (reason : Deferred state.slots) (deferred : view.heads slot = .deferred reason) :
    GeneralSourceBoundary.GraphUnresolved view.graph slot

theorem duplicate_tag (state : State) (tag : Nat) (payload : TyTerm (Fin state.slots)) :
    Rewrites state (.union (.variant tag payload) (.variant tag payload)) (.variant tag payload)

theorem duplicate_tag_source (state : State) (slot : Fin state.slots) (tag : Nat)
    (payload : TyTerm (Fin state.slots))
    (forward : Atom.tyLe (.var slot) (.union (.variant tag payload) (.variant tag payload)) ∈ state.ordinary)
    (backward : Atom.tyLe (.union (.variant tag payload) (.variant tag payload)) (.var slot) ∈ state.ordinary) :
    Rewrites state (.var slot) (.variant tag payload)

theorem required_record_same (state : State) (label : Nat) (payload : Fin state.slots) :
    Rewrites state (.required label (.var payload)) ((Shape.record [label]).term (fun _ => payload)) ∧
      Rewrites state (.record label (.var payload) .emptyRecord)
        ((Shape.record [label]).term (fun _ => payload))
```

`Yulang.GeneralSourceK2`:

```lean
theorem child_graph_iff (view : Snapshot state) (source target : Fin state.slots) :
    Child view source target ↔ target ∈ successors view.graph source

theorem path_graph_iff (view : Snapshot state) (first last : Fin state.slots) :
    Path view first last ↔ FiniteWorklist.Path (successors view.graph) first last

theorem cycle_graph_iff (view : Snapshot state) (root : Fin state.slots) :
    Cycle view root ↔ StructuralCycleAt view.graph root

theorem read_graph (view : Snapshot state) (depth : Nat) (slot : Fin state.slots) :
    read view depth slot = CommonRoleGraphBisimulation.observe view.graph depth slot

theorem graphK2_sound (view : Snapshot state) (root : Fin state.slots)
    (recursive : GeneralSourceBoundary.GraphK2 view.graph root) : RecursAt view root

theorem graphK2_exact (view : Snapshot state)
    (closed : ∀ slot, view.graph slot ≠ .unresolved) (root : Fin state.slots) :
    GeneralSourceBoundary.GraphK2 view.graph root ↔ RecursAt view root

theorem pending_graph_iff (view : Snapshot state) (demand : Demand roles)
    (linked : Linked state demand) (needed : Needed demand) :
    RootPending view demand needed ↔ ∃ argument slot, needed argument ∧
      state.source slot = (demand.arguments argument).1 ∧
      GeneralSourceBoundary.GraphUnresolved view.graph slot

theorem pending_excludes_rootK2 (view : Snapshot state) (demand : Demand roles)
    (needed : Needed demand) (pending : RootPending view demand needed) :
    ¬ RootK2 view demand needed

theorem unknown_excludes_rootK2 (view : Snapshot state) (demand : Demand roles)
    (needed : Needed demand) (unknown : RootInspectionUnknown view demand) :
    ¬ RootK2 view demand needed

theorem incomplete_defers (view : Snapshot state) (root slot : Fin state.slots)
    (path : Path view root slot) (unknown : view.graph slot = .unresolved) :
    ¬ Complete view root

theorem unknown_path_defers_rootK2 (view : Snapshot state) (demand : Demand roles)
    (needed : Needed demand) (argument : Fin (roles demand.role).arity)
    (root slot : Fin state.slots) (source : state.source root = (demand.arguments argument).1)
    (path : Path view root slot) (unknown : view.graph slot = .unresolved) :
    ¬ RootK2 view demand needed

theorem rootK2_sound (view : Snapshot state) (demand : Demand roles) (needed : Needed demand)
    (rejected : RootK2 view demand needed) :
    Linked state demand ∧ ¬ RootPending view demand needed ∧ ¬ RootInspectionUnknown view demand ∧
      ∃ argument slot, state.source slot = (demand.arguments argument).1 ∧
        Complete view slot ∧ RecursAt view slot

theorem rootK2_exact (view : Snapshot state) (demand : Demand roles) (needed : Needed demand)
    (linked : Linked state demand) (ready : ¬ RootPending view demand needed)
    (closed : ∀ slot, view.graph slot ≠ .unresolved) :
    RootK2 view demand needed ↔
      ∃ argument slot, state.source slot = (demand.arguments argument).1 ∧ RecursAt view slot

theorem rootK2_observation_sound (view : Snapshot state) (demand : Demand roles) (needed : Needed demand)
    (rejected : RootK2 view demand needed) :
    ∃ argument slot term, state.source slot = (demand.arguments argument).1 ∧
      (view.heads slot).term = some term ∧ RecursAt view slot ∧
      ∀ model, GeneralSourceState.Models state model →
        Common.Equivalent (model (demand.arguments argument).1).1
          (term.eval Common.model (state.assignment model))
```

`Yulang.GeneralSourceK2Examples`:

```lean
theorem shadow_normalization :
    Rewrites shadowState (.var 0) (.record 7 (.var 1) (.var 0)) ∧
      Rewrites shadowState (.record 7 (.var 1) (.record 7 (.var 1) (.var 0)))
        (.record 7 (.var 1) (.var 0))

theorem index_pending_not_rootK2 :
    GeneralSourceState.Linked indexState indexDemand ∧
      (∀ key, GeneralSourceState.Models indexState (indexModel key)) ∧
      RootPending indexView indexDemand indexNeeded ∧ ¬ RootK2 indexView indexDemand indexNeeded

theorem loop_rootK2 :
    GeneralSourceState.Linked loopState loopDemand ∧
      GeneralSourceState.Models loopState loopModel ∧
      RootK2 loopView loopDemand loopNeeded ∧ ¬ RootPending loopView loopDemand loopNeeded ∧
      RecursAt loopView 0

theorem shadow_not_rootK2 :
    GeneralSourceState.Linked shadowState loopDemand ∧
      GeneralSourceState.Models shadowState shadowModel ∧
      RootPending shadowView loopDemand loopNeeded ∧ ¬ RootK2 shadowView loopDemand loopNeeded ∧
      ¬ GeneralSourceBoundary.GraphK2 shadowView.graph 0 ∧
      (shadowModel 0).1 = Common.required 7 (.base .int)

theorem shadow_residual_model :
    GeneralSourceState.Models shadowState shadowWiderModel ∧
      ObservationModels shadowView shadowWiderModel ∧
      (shadowWiderModel 0).1 = Common.record 7 (.base .int) (Common.required 9 (.base .str))
```


### Item-2b checks

Final commands, run from `lean/`:

| Exact command | Exit code |
| --- | --- |
| `lake build Yulang.GeneralNormalizedObservation Yulang.GeneralSourceK2 Yulang.GeneralSourceK2Examples > /tmp/astra-normalized-k2-focused.log 2>&1` | 0 |
| `lake build Yulang > /tmp/astra-normalized-k2-umbrella.log 2>&1` | 0 |
| `lake env lean Audit.lean > /tmp/astra-normalized-k2-audit.log 2>&1` | 0 |

The focused build completed 425 jobs; the umbrella build completed 1328 jobs.
All 26 new public theorems have audit entries and full statements above.
The full audit dependency whitelist contains only `propext`, `Classical.choice`,
and `Quot.sound`. New modules contain none of the excluded tokens. Existing
`Audit.lean` and `Yulang.lean` contents remain exact byte prefixes. Local links
and `git diff --check` pass. No existing theorem body, specification, plan,
lake configuration, or git reference was changed.

Early focused builds exited 1 while fixing dependent constructor equality,
finite-index elaboration and a lemma namespace; only the new files were edited.
A preliminary audit-coverage script was run before the audit process finished
and correctly reported missing trailing output; it passed after process exit.
No failing proof or audit entry remains.

The `yulang-proofs` skill was applied. Its referenced repository orchestration
files and configured prover launch role were unavailable in this checkout; the
primary constructed the bounded derivations. A separate read-only reviewer
challenged the semantics and reviewed the final gate changes and this note.
No prover agent ran. The reviewer ran `git diff --check`, not independent Lean
builds; the build and audit results above are the primary's checks.


## Item 1

2026-11-12, declaration carrier, declaration-only certification, and child demand
emission. The owner reassigned this lane in I-18. During this task the owner
resolved the generated-binder question: generated associated binders are
**output-only**, and only unnamed child arguments enter the Paterson conditions.
That decision is implemented concretely, with no remaining sugar-accounting
parameter.

Authority: [spec section 6.3](../../spec/06-roles.md), the
[approved draft and addenda](2026-11-08-b4-main-statement-draft.md), and the new
“回答” section of
[the associated-sugar question](../questions/2026-11-10-cycle70-associated-sugar-checking.md).
The worktree's older spec/question text was not edited. The updated answer was
read with the read-only command
`git -C /home/momota1029/rust/yulang show origin/integration/m1-final:notes/questions/2026-11-10-cycle70-associated-sugar-checking.md`;
the owner identified its integration commit as `400cb091a`. No fetch or ref update
was performed. The earlier note's open sugar-accounting status is superseded by
this decision.

### Delivered interface and its limits

New modules:

- [GeneralDeclarationPatterns.lean](../../lean/Yulang/GeneralDeclarationPatterns.lean)
  (`P`): resolved finite pattern trees, normalization, counts, and capture stability.
- [GeneralDeclarations.lean](../../lean/Yulang/GeneralDeclarations.lean) (`D`): full
  declaration/registry carriers, `DeclarationChecked`, `Checked`, output-only
  checks, and capture-relative associated determination.
- [GeneralDeclarationDemands.lean](../../lean/Yulang/GeneralDeclarationDemands.lean)
  (`G`): interval captures, explicit allocations/materialization requests, and
  lossless child `GeneralSourceState.Demand` emission.
- [GeneralDeclarationExamples.lean](../../lean/Yulang/GeneralDeclarationExamples.lean):
  accepted/rejected spec examples using these same carriers.

`D.Registry` contains a constructor catalogue, the existing `Roles.RoleDecls`,
and the complete declaration list. `D.CheckedRegistry` packages it with a proof
of `D.Checked`. This is a concrete declaration **certificate component**, not
a complete executable source validator and not a completed B4 boundary field.
In particular, full source/Common normalization adequacy and the link from
source matching to associated determination remain unproved. No fragment's
classifier or scalar registry is substituted for those obligations.

`P.Pattern` has variables, arbitrary-arity resolved constructor applications,
record fields/tails, variants, and joins. The constructor catalogue retains
name and type/row/lower/upper parameter layout, so nominal and interval shapes
are not erased into unary placeholders. Constructor validation currently checks
arity, not all type/row/variance kinds. Parsing, elaboration, nominal variance
checking, and the interpretation of catalogue names remain separate obligations.
Applications do not unfold named bodies.

A `D.Declaration` keeps its source identity, role, original head patterns, all
where clauses, own associated definitions, and generated-binder provenance.
`normalHead` exposes the computed normalized head while keeping the original
spelling for provenance and lexical scope checks. Every `D.Clause` keeps its
own identity, role, complete unnamed arguments, and complete list of named
`D.Equation`s. Equations have their own identities and arbitrary pattern RHSs.
Identical clause contents are not deduplicated. Registry declaration identities,
clause identities within a declaration, and equation identities within their
owner must be distinct. This is a storage invariant, not global role coherence.
Repeated imports/visibility still need an adapter to this definition registry.

### Rules checked, with authority

| Rule | Concrete definition / evidence | Authority and scope |
| --- | --- | --- |
| Normalize invisible fields before counting | `P.normalize`, `P.hide`, `hidden_field_removed` | Spec 6.3 hidden-field paragraph; visibility resets inside payloads and unknown tail variables remain. |
| Group same tags before counting | `P.variantRow`, `P.merge`, existing `Variants.Merged.normalize`, sorted tag reconstruction, `duplicate_variant_removed`, `nonadjacent_tag_grouped` | Spec 6.3 same-tag paragraph, also the existing tag-unique row operation. Whole rows are grouped, including separated tag occurrences. |
| Smaller children and occurrence bounds | `P.Smaller`, `P.checkSmaller`, `checkSmaller_exact`; `DeclarationChecked.paterson` | Spec 6.3 numbered conditions. Both sides are normalized first. Only `Clause.arguments` enters the child count. Uses `CheckedRoles.checkCondition_exact` directly. |
| Preserve descent after capture | `P.StableSmaller`; `DeclarationChecked.captureStable`; `late_merge_rejected` | Spec 6.3 paragraph rejecting capture-induced loss of strict descent. Quantifies every finite capture; no resolver success is assumed. |
| Avoid inflated partial counts | `CountsCovered`, `ConservativeSmaller`, `NormalizationDeferred` | Conservative implementation coverage. Residual joins defer certification; the head lower bound does not count an arbitrary record tail as guaranteed structure. These extra gates are not new language rejection reasons. |
| Generated binders are output-only | `Declaration.OutputOnly`, `output_input_rejected` | Owner answer of 2026-11-12. Generated names cannot occur in the impl's unnamed head or any child's unnamed input, even in syntactically hidden fields. They may occur in own associated RHSs and child named equations. |
| Generated variables have a producer | `Declaration.Produced` | Each binder points to a real clause/equation whose RHS is that variable. Merely listing an arbitrary output name cannot make it determined. |
| Variables are scoped | `Declaration.Scoped` | Normalized child input variables come from normalized head captures; own associated RHSs and named equations may additionally use the produced output-only binders. Ordinary where-only variables remain excluded. |
| Associated names and defaults | `Declaration.Signature`, `Clause.Signature` | Existing `Roles.RoleDecls`: correct unnamed arity, every supplied name declared, every own required name explicitly defined or defaulted. Merely validating supplied names is not completeness. |
| Associated determination through children | `SatisfiesOutputs`, `outputs_determined`, `capture_determines_associated` | Spec 6.3 named outputs are determined from unnamed inputs. The theorem is relative to actual captured-binding agreement and a fixed functional local output interpretation; source/dictionary discharge is still missing. |

The output-only decision counts neither own associated definitions nor child
named equations in the Paterson comparison. It does not assign generated
variables artificial size zero: their allowed occurrences live outside the
unnamed argument lists that are counted. Every child, including one introduced
by associated-RHS sugar, still has a strictly smaller unnamed input list.
The same output binder can be shared by several child named equations, which
remain simultaneous constraints.

`StableSmaller` is an independent mathematical requirement, not a finite
procedure for arbitrary patterns. `CheckedRoles` supplies the exact finite
size/occurrence subcheck. `CommonRoleStablePaterson.check_sound` was surveyed;
its Form grammar is int/pair/tick/join, so it was not installed as the general
check. Likewise `CommonRoleNormalizedDeclarations` and
`CommonRoleHeadDetermination` are restricted record-pattern components. Their
contracts informed the separation here, but their restricted checkers do not
validate arbitrary constructor applications. `unary_descent` proves a general
constructor schema directly, for every finite captured payload.

### Normalization coverage is not full semantic adequacy

The new pattern pass removes record shadows and groups complete variant rows.
It contracts equal payloads; remaining unequal payload joins retain their
structure. It does not invent pair/nominal variance coalescing or claim complete
Common equivalence. A residual join makes `CountsCovered` false. Consequently a
multi-tag row may be represented and normalized while declaration certification
still waits for broader count coverage.

`ConservativeSmaller` additionally replaces residual joins and record tails in
its head lower bound by a one-node constant. It can decline valid declarations:
for example a known multi-field record may have a useful tail that this bound
discards. `deferred_not_certified` records that such a declaration is not yet
certified. Neither this theorem nor generic `¬DeclarationChecked` alone says
that the language rejects it. The rejected examples below have the specific
approved output-only or nondecrease reason.

A general theorem connecting these bounds to **all** Common canonicalization
is not proved. Nor is there a full interpretation theorem for arbitrary
constructor-catalogue applications. This is why the field table labels Checked
a certificate component with source/Common adequacy still missing. An accepted
certificate is not yet a whole-language soundness theorem.

The first version of the local merge draft only grouped immediate variant
operands. Independent review found the separated-tag counterexample
`(tick int | other str) | tick int`. The implementation now flattens and groups
the whole row with the existing operation; `nonadjacent_tag_grouped` proves that
regression. This was corrected before final checks.

### Associated determination and its remaining bridge

`CapturesAgree d first last` says that two actual captures agree on every
surviving head variable. It does **not** quantify arbitrary substitutions merely
making the head Common-equivalent. This matters for the approved merged-variable
rule: the whole merged payload is captured into both variables, rather than
split into arbitrary preimages.

`Associated` is a fixed local interpretation of role input lists and named
outputs. `SatisfiesOutputs` requires every child named equation to hold in that
interpretation. If two captures agree on the head bindings, `Scoped` makes all
child input lists equal. A produced output-only binder then receives equal
values from its producing child equation. `outputs_determined` proves that step;
`capture_determines_associated` extends it to every own normalized associated RHS
using structural substitution congruence.

This is **capture-relative determination**. It does not prove the source
matcher's binding agreement from equal input intervals, prove functionality of
selected child dictionaries, or impose global coherence on visible impls.
The later source/dictionary model must discharge those premises. Defaults are
retained in `Roles.RoleDecls`; this module validates their availability but does
not build default dictionaries or instantiate their bodies into source state.

### Child demands and identity preservation

`G.Capture.inputs` supplies centerless lower/upper source pairs. Its `outputs`
map supplies ordinary identities reserved for generated output binders; no
freshness or injectivity is silently assumed. `G.Allocation` supplies identities
for compound input and output expressions.

`childDemand` substitutes a directly captured input variable's interval without
choosing either endpoint as a centre. A generated variable in a named equation
uses its reserved ordinary output identity. Other RHSs receive an allocated
materialization target; neither lower nor upper endpoint is
arbitrarily selected as that target.

`emit` retains the capture, invocation/declaration/clause identities, the actual
item-2 `Demand`, every input materialization request, and every named equation's
identity/RHS/target. `emitAll` produces one emission per original clause,
including bare clauses with zero equations. `emitAll_identities` proves exact
list preservation of qualified identities, and `emitAll_length` proves no
clause disappears. `child_outputs_exact` proves exact named-obligation membership.
`child_linked` proves linkage to an existing state when the emitted identities
are present there.

Identity linkage alone is not materialization correctness. The retained input
and output requests must be realized as ordinary/interval constraints by item 3.
No general `Pattern`-to-Common/nominal materializer, fresh-source allocator, or
candidate filtering is supplied here. In particular, allocating a compound
pattern's endpoints is not evidence that those endpoints denote the pattern.

### Spec examples proved

- `display_checked`: `impl Display (list 'a) where Display 'a` is certified.
  The size/occurrence and capture-stability proof uses `unary_descent`, quantified
  over every finite captured payload.
- `wrap_checked`: the approved Wrap/Container declaration is certified
  **unconditionally**, after the owner's output-only decision.
- `registry_checked`: the actual registry containing Display and Wrap is Checked.
- `wrap_child_keeps_item`: invocation 9 of declaration 2 emits clause 20 as
  Container, preserves captured input interval `(100,101)`, and emits the item
  output target 200 with equation identity 21 and RHS binder 1. The allocated
  fallback target 400 and argument `(300,301)` do not replace those captures.
- `output_used_as_input_rejected`: `Show (box 'a)` with `Container('a,item='b)`
  followed by unnamed `Show 'b` is not Checked specifically because binder `'b`
  is output-only.
- `hidden_padding_rejected`: duplicating a hidden record field does not make an
  equal normalized child smaller.
- `capture_merge_rejected`: the spec's pair-payload late-merge example loses
  strict decrease at the explicit `a := int` capture and is not Checked.
  `capture_merge_signature` confirms its two-argument role signature is valid;
  rejection is not explained by an unrelated arity error.
- `nonadjacent_tag_grouped`: separated duplicate tags normalize to the same row.

### Field table after Item 1

`D`, `P`, and `G` are the module aliases above; `S` is `GeneralSourceState` and
`K` is `GeneralSourceK2`. All new checking and emission definitions are independent
of resolution and executor output.

| Field | Status / concrete definition | Remaining obligation |
| --- | --- | --- |
| `Vocabulary.Registry` | **DEFINED general finite carrier:** `D.Registry`, `D.CheckedRegistry` | Parser/elaborator/visibility production, catalogue interpretation, and complete checking remain open. |
| `Vocabulary.State` | **DEFINED checked component:** `S.State`, `GeneralNormalizedObservation.Snapshot` | Full source materialization/normalization and nominal integration remain missing. |
| `Vocabulary.Demand` | **DEFINED:** `S.Demand`; `G.childDemand`, `G.emitAll` supply where children | Realize retained materialization requests before classification. |
| `Vocabulary.Model` | **DEFINED Common component:** `S.Assignment` | General nominal/source interpretation remains missing. |
| `Checked` | **DEFINED declaration certificate component:** `D.Checked`, `D.DeclarationChecked` | Full source/Common adequacy, general bound soundness, finite complete validation, and dictionary-relative determination discharge **MISSING**. |
| `Models` | **DEFINED checked-state component:** `S.Models` | No complete registry/dictionary model supplied. |
| `Step` | **MISSING** | No saturation transition. |
| `Stable` | **MISSING** | No sibling/EOF fixpoint judgment. |
| `Generated` | **MISSING as the full boundary field** | `G.emitAll` is a defined where-emission component; selected candidate provenance and ordinary realization remain item 3/4. |
| `RootPending` | **DEFINED partial snapshot component:** `K.RootPending` | `G.needed` supplies conservative all-input deferral, not a proved minimal applicability set. |
| `RootK2` | **DEFINED partial normalized component:** `K.RootK2` | Earlier normalization/source adequacy gaps remain. |
| `CandidateK2` | **MISSING** | Actual surviving candidate inspections must produce it. |
| `InspectionPending` | **MISSING as a complete field** | `K.RootInspectionUnknown` and `D.NormalizationDeferred` are distinct partial deferral conditions. |
| `Survivor` | **MISSING** | No candidate matching or interval filtering. |
| `Evidence` | **MISSING** | No source-indexed general dictionary model. |
| `Reorders` | **MISSING** | Identities are retained for this future relation; no full relation defined here. |
| `DictionaryEquivalent` | **MISSING** | No general dictionary observation equivalence. |
| `Executor.run` | **MISSING** | No executor introduced. |

No field is silently filled by a scalar, settled or unary classifier. This work
provides useful concrete carriers and certificates for item 3, but it does not
close Item 1's full source-adequacy obligations or instantiate `generalBoundary`.
No B4 bridge field is claimed complete.

### Needed: lazy implementation and remaining owner question

The draft's addendum 3 fixes Index with a rigid second argument: it waits rather
than inferring that argument from a lone implementation. Heads alone do not yet
specify a unique minimal applicability set in every case. Taking only the union
of rigid head positions would also produce an empty set for an empty registry,
incorrectly allowing unresolved goals past the pending-priority gate.

`G.needed` currently includes **every unnamed role argument**, derived from
`Roles.RoleDecls.arity`, regardless of candidate count. `every_input_needed` and
`unknown_input_pending` prove that an unresolved input remains pending. Named
associated outputs are not added to that set. This is the conservative deferred
implementation, not a claim that every input is semantically necessary.

Question, lazy option first:

```yulang
impl Keep int 'a:
    // no where clauses
my use(k) = 1.keep k
// receiver is int; k's lower head is unresolved
```

1. Continue waiting for all unnamed lower heads, including the unconstrained
   nonreceiver wildcard position. This is the implementation retained here.
2. Permit inspection when a proved applicability dependency analysis says that
   wildcard position can be captured without inspecting its head. Receiver
   readiness, repeated-variable interval constraints, and empty registries must
   still obey the approved pending rules.

The example is schematic, not a parser fixture. No owner choice between these
acceptance scopes is inferred here; the conservative pending result keeps it
open. A minimal head-derived Needed set and its sufficiency proof remain missing.
The generated-binder policy, in contrast, is settled and has no such parameter.

### Handoff and assessment

Item 3 can now consume declaration/obligation/equation IDs, full named and
unnamed clause data, generated-binder producers, `normalHead`, the certified
Paterson and output-only facts, and `emitAll` with its exact identity/obligation
preservation theorems. It must provide actual capture from the shared interval
graph, materialization of all retained requests, source linkage/freshness,
survivor propagation, and candidate inspection. Dictionary work must supply the
local functionality used by `Associated`, without introducing global coherence.

Not verified: parser production, type/row kind correctness, full normalization
meaning/minimality, nominal variance coalescing, full Common lower-bound
soundness, complete finite declaration validation, source head-equivalence
recovery, actual dictionary functionality, default-body materialization,
minimal Needed, fresh allocation, survivor correctness, saturation, or B4.

Assessment: the concrete registry and child interface now share item-2 demand
identities and preserve all associated equations. This is progress toward one
general instance. The old fragment theorems alone still do not supply that
instance. The remaining source/Common adequacy gaps are substantive; naming a
certificate `Checked` does not turn them into completed proofs.

### Item-1 theorem statements

The following are the full public signatures from the four modules. Implicit
parameters are universally quantified with the types inferred in the source;
namespace openings are as in each module. The private Wrap signature helper is
not a separate public theorem.

`Yulang.GeneralDeclarationPatterns`:

```lean
theorem checkSmaller_exact (head child : List Pattern) :
    checkSmaller head child = true ↔ Smaller head child

theorem subst_congr (pattern : Pattern) (first last : Nat → Pattern)
      (agree : ∀ name ∈ pattern.variables, first name = last name) :
      pattern.subst first = pattern.subst last

theorem substArgs_congr (arguments : List Pattern) (first last : Nat → Pattern)
      (agree : ∀ name ∈ variablesArgs arguments, first name = last name) :
      substArgs first arguments = substArgs last arguments

theorem hide_idempotent (label : Nat) (pattern : Pattern) :
    hide label (hide label pattern) = hide label pattern

theorem hidden_field_removed (label : Nat) (payload hidden tail : Pattern) :
    normalize (.record label payload (.record label hidden tail)) =
      normalize (.record label payload tail)

theorem duplicate_variant_removed (tag : Nat) (payload : Pattern) :
    normalize (.join (.variant tag payload) (.variant tag payload)) = normalize (.variant tag payload)

theorem unary_descent (constructor name : Nat) :
    StableSmaller [.app constructor [.var name]] [.var name]
```

`Yulang.GeneralDeclarations`:

```lean
theorem deferred_not_certified (declaration : Declaration) (deferred : NormalizationDeferred declaration) :
    ¬ DeclarationChecked constructors roles declaration

theorem checked_child_descent (checked : DeclarationChecked constructors roles declaration)
    (clause : Clause) (present : clause ∈ declaration.requirements) (capture : Nat → Pattern) :
    Smaller (substArgs capture declaration.head) (substArgs capture clause.arguments)

theorem output_input_rejected (declaration : Declaration) (clause : Clause)
    (present : clause ∈ declaration.requirements) (name : Nat)
    (output : name ∈ declaration.outputNames) (input : name ∈ variablesArgs clause.arguments) :
    ¬ DeclarationChecked constructors roles declaration

theorem late_merge_rejected (declaration : Declaration) (clause : Clause)
    (present : clause ∈ declaration.requirements) (capture : Nat → Pattern)
    (noDecrease : ¬ Roles.argsSize (counted (substArgs capture clause.arguments)) <
      Roles.argsSize (counted (substArgs capture declaration.head))) :
    ¬ DeclarationChecked constructors roles declaration

theorem outputs_determined (checked : DeclarationChecked constructors roles declaration)
    (associated : Associated) (first last : Nat → Pattern)
    (head : CapturesAgree declaration first last)
    (firstOutputs : SatisfiesOutputs associated declaration first)
    (lastOutputs : SatisfiesOutputs associated declaration last) :
    ∀ name ∈ declaration.outputNames, first name = last name

theorem capture_determines_associated (checked : DeclarationChecked constructors roles declaration)
    (associated : Associated) (first last : Nat → Pattern)
    (head : CapturesAgree declaration first last)
    (firstOutputs : SatisfiesOutputs associated declaration first)
    (lastOutputs : SatisfiesOutputs associated declaration last)
    (equation : Equation) (present : equation ∈ declaration.associated) :
    (normalize equation.rhs).subst first = (normalize equation.rhs).subst last
```

`Yulang.GeneralDeclarationDemands`:

```lean
theorem emitAll_identities (invocation : Nat) (declaration : Declaration)
    (valid : declaration.Signature roles) (capture : Capture)
    (allocate : (clause : Clause) → Allocation roles clause) :
    (emitAll invocation declaration valid capture allocate).map
      (fun result => (result.invocation, result.declaration, result.clause)) =
        declaration.requirements.map (fun clause => (invocation, declaration.id, clause.id))

theorem emitAll_length (invocation : Nat) (declaration : Declaration)
    (valid : declaration.Signature roles) (capture : Capture)
    (allocate : (clause : Clause) → Allocation roles clause) :
    (emitAll invocation declaration valid capture allocate).length = declaration.requirements.length

theorem child_outputs_exact (declaration : Declaration) (clause : Clause)
    (valid : clause.Signature roles) (capture : Capture) (allocation : Allocation roles clause)
    (output : Output) :
    output ∈ (childDemand declaration clause valid capture allocation).outputs ↔
      ∃ equation ∈ clause.outputs, output =
        ⟨equation.name, outputTarget declaration capture allocation.outputs equation⟩

theorem generated_output_target (declaration : Declaration) (capture : Capture) (allocate : Nat → Nat)
    (equation : Equation) (name : Nat) (generated : name ∈ declaration.outputNames)
    (rhs : equation.rhs = .var name) :
    outputTarget declaration capture allocate equation = capture.outputs name

theorem child_linked (state : GeneralSourceState.State) (declaration : Declaration) (clause : Clause)
    (valid : clause.Signature roles) (capture : Capture) (allocation : Allocation roles clause)
    (arguments : ∀ index, ∃ pair ∈ state.intervals,
      (state.source pair.1, state.source pair.2) =
        (childDemand declaration clause valid capture allocation).arguments index)
    (outputs : ∀ equation ∈ clause.outputs, ∃ slot,
      state.source slot = outputTarget declaration capture allocation.outputs equation) :
    GeneralSourceState.Linked state (childDemand declaration clause valid capture allocation)

theorem every_input_needed (demand : Demand roles) (index : Fin (roles demand.role).arity) :
    needed roles demand index

theorem unknown_input_pending (state : GeneralSourceState.State) (demand : Demand roles)
    (index : Fin (roles demand.role).arity)
    (unknown : ¬ GeneralSourceState.Known state (demand.arguments index).1) :
    GeneralSourceState.RootPending state demand (needed roles demand)
```

`Yulang.GeneralDeclarationExamples`:

```lean
theorem display_checked : DeclarationChecked constructors roles display

theorem wrap_checked : DeclarationChecked constructors roles wrap

theorem registry_checked : Checked registry

theorem output_used_as_input_rejected :
    ¬ DeclarationChecked constructors roles showOutput

theorem hidden_padding_rejected :
    ¬ DeclarationChecked constructors roles shadowDeclaration

theorem capture_merge_signature : lateDeclaration.Signature roles

theorem capture_merge_rejected :
    ¬ DeclarationChecked constructors roles lateDeclaration

theorem wrap_child_keeps_item :
    let child := emit 9 wrap containerChild (wrap_checked.signature.2.2.2 containerChild (by simp))
      wrapCapture wrapAllocation
    child.invocation = 9 ∧ child.declaration = 2 ∧ child.clause = 20 ∧
      child.demand.role = 2 ∧
      child.demand.arguments ⟨0, by simp [child, emit, childDemand, roles, outputRole]⟩ = (100, 101) ∧
      child.demand.outputs = [⟨1, 200⟩] ∧
      child.outputs = [⟨21, 1, .var 1, 200⟩]

theorem nonadjacent_tag_grouped :
    normalize (.join (.join (.variant 7 (.app 2 [])) (.variant 8 (.app 3 [])))
      (.variant 7 (.app 2 []))) =
    normalize (.join (.variant 7 (.app 2 [])) (.variant 8 (.app 3 [])))
```


### Item-1 checks

Final commands, run from `lean/`:

| Exact command | Exit code |
| --- | --- |
| `lake build Yulang.GeneralDeclarationPatterns Yulang.GeneralDeclarations Yulang.GeneralDeclarationDemands Yulang.GeneralDeclarationExamples > /tmp/astra-declarations-focused.log 2>&1` | 0 |
| `lake build Yulang > /tmp/astra-declarations-umbrella.log 2>&1` | 0 |
| `lake env lean Audit.lean > /tmp/astra-declarations-audit.log 2>&1` | 0 |

The focused build completed 426 jobs; the umbrella build completed 1332 jobs.
All 29 public theorem entries are present in the completed audit. The full
dependency whitelist contains only `propext`, `Classical.choice`, and `Quot.sound`.
The new modules contain none of the excluded tokens. Existing `Yulang.lean` and
`Audit.lean` contents are unchanged byte prefixes; only four imports and 29 audit
lines were appended. `git diff --check`, local note links, and audit/signature
coverage checks pass. No spec, plan, lake configuration, existing theorem body,
or git reference was modified.

Early focused builds exited 1 while resolving nested-tree equality, reserved
identifiers, finite-index elaboration and proof simplification. The separated-tag
regression initially exposed row ordering; the final grouping sorts tags and its
proof uses the library's sort simplification lemmas. These changes were confined
to the new files. A temporary executable probe was used only to inspect the row
values; the final regression is proved by Lean simplification and audited.

The `yulang-proofs` skill was applied. No configured prover role/launch surface
was available; the primary constructed these bounded derivations and a separate
read-only reviewer checked the design, implementation and final note. The
reviewer ran `git diff --check`, not independent Lean builds. No prover agent ran.
The review's two final documentation corrections (a let-containing theorem
signature and an overstated allocation-distinctness phrase) were applied before
completion.

### Owner answer to the Item 1 `Needed` question (2026-11-12)

Option 1. Every unnamed role argument is needed: the demand stays pending until every unnamed argument's lower head is known, even at a position every candidate captures with a bare variable. Named associated outputs are not needed. Recorded as addendum 4 of the approved B4 draft. `G.needed` (all unnamed inputs) is therefore the intended definition, not merely a conservative placeholder.

## Item 3 — candidate inspection and private interval propagation (2026-11-12)

Status: **partial, not a completed general source boundary**. The source task is
not closed. Five new modules connect existing general carriers, checked normalized
observations, the actual ordinary solver, and complete canonical child plans.
They do not supply the missing nominal/Common interpretation or the source
allocator. In particular the requested positive `Display (list int)` and
`Wrap (list 'a)` survivor examples are **not proved**. Keeping these obligations
visible is necessary: interpreting `list` as an arbitrary record/graph tag would
change the language.

The authority is the approved [draft and addenda 1–4](2026-11-08-b4-main-statement-draft.md),
[spec 6.3–6.4](../../spec/06-roles.md), and the current
[V3 target](../../lean/Yulang/B4TargetV3.lean). The former Item 1 `Needed` question
is settled: every unnamed argument is needed, including a plain-variable
position; named associated outputs are excluded. No minimal-needed analysis is
introduced.

### Components and exact scope

Abbreviations below are `I = Yulang.GeneralCandidateIntervals`,
`Q = Yulang.GeneralCandidateInspection`, and
`B = Yulang.GeneralCandidateBoundaryParts`.

- [GeneralCandidateIntervals](../../lean/Yulang/GeneralCandidateIntervals.lean)
  uses `CommonRoleCandidateConstraints.generate/solve`, not a head-substitution
  search. Every occurrence of a captured variable is retained, including both
  self comparisons and both repeated-variable cross directions. `I.propagate`
  uses the existing `GeneralDictionaryEquationRecording.append`; each candidate
  has its own ordinary extension. `propagate_models` is an exact equivalence at
  the same original source assignment. `survives_iff_model` connects the actual
  ordinary solver to existence of an actual source model, under `Covered`.
  `MergeLinked` checks both source endpoints against union-of-lowers and
  intersection-of-uppers. `MergeRecorded` is a finite storage condition implying
  it. No centre is allocated.
- `Covered` contains the existing child/width/row grammar certificates and
  injectivity of `State.rowSource`. The last condition is required by the present assignment-lifting proof:
  the reused solver gives independent parameters to local row slots. Shared row
  aliases otherwise need equality atoms before solving. `row_alias_defers`
  enforces this coverage limit; it is not a language rejection rule. The
  underlying general State has not been restricted or changed. The ordinary
  grammar also excludes some exact endpoint equations, including upper variant,
  union and intersection expressions; their general solver/materialization
  bridge is still missing. Thus repeated-capture coalescing is defined generally
  but arbitrary coalesced endpoints are not automatically within `Covered`.
- [GeneralCandidateInspection](../../lean/Yulang/GeneralCandidateInspection.lean)
  traverses a finite normalized pattern and both interval endpoints. All sibling
  captures, inspected positions, blockers, conflicts and arity problems survive
  concatenation. Traversal is bounded by the pattern structure, not an imposed
  resolution-depth limit. It can traverse an observed cycle mathematically to
  determine a finite candidate footprint; K2 separately records the constructor
  inspections in that footprint. A variable captures its interval without
  inspecting the constructor. Merged plain variables each capture the complete
  merged payload, as required by spec 6.3.
- The partial translator first uses `Declaration.normalHead` and its existing
  hidden-field/same-tag normalization. It supports explicit ordinary primitive
  annotations, closed record spines sorted together with their payload queries,
  and variants. `PrimitivesCompatible` checks annotated constructor arity and
  parameter kinds against the declaration catalogue. **The annotation table is
  an extra input, not a proved extraction from the source catalogue.** Nominal
  applications, arrow forms, open record tails and other untranslated forms are
  retained as deferred patterns. No annotation for `list` is supplied. Canonical
  source/Common adequacy for all constructor names is still MISSING.
- [GeneralCandidateBoundaryParts](../../lean/Yulang/GeneralCandidateBoundaryParts.lean)
  uses actual source-ID lookup from `GeneralDictionaryBinderLocations.sourceSlot`.
  `HeadReady` requires complete inspection plus a positive ordinary pass.
  `Prepared` additionally checks captured interval materialization, the actual
  root linkage, primitive metadata, and the supported child-emission requests.
  Its root named-output list must currently be empty. Child inputs must be
  normalized plain variables actually present in the computed captures; their
  endpoints must equal the frame's captured endpoints. Supported child named
  outputs must be output-only binders. Compound input/output materialization
  remains deferred. **No child's resolution is checked here.**
- `B.Survivor` is a partial, fixed-frame candidate relation. Its children are
  exactly `GeneralDictionaryEmissionPlans.children`, built from all canonical
  `GeneralDeclarationDemands` emissions. Where clauses are not filtered or
  resolved. The frame's captured input endpoints are checked, but its output
  allocation, invocation identity map, freshness and source provenance are
  **not** derived. Different caller-supplied output IDs or a noninjective
  invocation map are therefore not certified as faithful source allocation.
  These are remaining premises of the partial interface, not completed fields.
- `B.InspectionPending` retains a visible, checked, same-role declaration that
  has not independently failed but lacks a preparation certificate. This includes
  unresolved needed descendants and unimplemented materialization/interpretation.
  `Failed` requires compatible primitive metadata and a genuine scalar conflict
  or a covered empty ordinary solver result. Unsupported coverage is never
  converted into interval failure. This is a conservative partial observation
  relation, not a proof that the final source normalizer eventually handles
  every language case.
- `B.CandidateK2` requires an applicable finite head footprint with feasible
  interval constraints, root linkage, compatible primitive annotations, no
  demanded root associated outputs, and a normalized recurrence at a constructor
  the candidate actually inspected. It uses `Complete` and normalized `GraphK2`,
  then `GeneralSourceK2.graphK2_sound` to obtain the independent `RecursAt` fact.
  It does not use raw graph-cycle flags or the absence of `InspectionPending`.
  Child emission/materialization and child resolution are not prerequisites to
  this K2 check. Unknown aliases are not equated merely because both display an
  unknown observation token.
- `B.RootK2` adapts the previous normalized root predicate to V3: after all
  unnamed root lower heads are known, a complete recurrent lower endpoint is
  sufficient. An unrelated incomplete descendant in another argument does not
  suppress that root reason. The old module is unchanged. This respects the
  owner's reached-root reading rather than whole-denotation nonfiniteness.

All candidate definitions are independent of the executor. The only execution
used in their definitions is the existing **ordinary constraint solver**, after
capture has already been computed. No candidate type-substitution enumeration is
introduced.

### Models and the requested universal soundness claim

The proved exact law is, for every assignment `m`,

```text
Models (I.propagate s captures) m
  ↔ Models s m ∧ CommonRoleCandidateConstraints.Compatible captures (s.assignment m).
```

Thus every model of the private propagated candidate state satisfies all its
captured constraints, and every such model preserves the original state.
`survivor_interval_sound` states this with the actual declaration and computed
capture report, retaining all quantifiers. `survives_has_model` proves these
claims need not be vacuous merely because the ordinary solver returned a
nonempty list: a shared-source model really exists within the stated coverage.

This is **not** the stronger claim that feasibility of each alternative makes
its extra constraints true in *every model of the unextended shared state*.
That claim does not follow from feasibility. `recorded_capture_sound` proves the
shared-state universal version with an explicit ordinary-storage premise, which
is the connection needed after actual recording. `two_alternatives_models`
shows that appending both alternatives' checks conjoins them; the implementation
never silently performs that conjunction as candidate selection.

### Vocabulary and all thirteen fields

`B.vocabulary roles` fixes the role-declaration environment as a parameter; the
registry itself remains `GeneralDeclarations.Registry`. `B.availableFields`
packages only the six independently available fields below. It is **not** a
`SourceBoundary`, and no absent field receives a placeholder value.

| Vocabulary entry | Definition and status | Authority / limit |
| --- | --- | --- |
| Registry | `GeneralDeclarations.Registry` | Draft registry; existing checked declaration carrier, including every child equation. |
| State | `B.Context roles` containing the unchanged `GeneralSourceState.State`, checked normalized snapshot, partial primitive annotations, fixed frames and merged endpoint locations | Draft shared state; view and frame production remain external. |
| Demand | `GeneralSourceDictionaries.Occurrence roles`, containing `GeneralSourceState.Demand roles` | All unnamed centerless interval arguments and associated targets, with the existing occurrence carrier. Source freshness is not proved by the Nat identity. |
| Model | `GeneralSourceState.Assignment` | Actual Common source assignments, separate type/row identities. No nominal carrier is smuggled in. |
| Executor.run | **MISSING** | No general saturation or stable-file driver is defined. |

| SourceBoundary field | Current definition/status | Why faithful; remaining limit |
| --- | --- | --- |
| Checked | **DEFINED on the carrier:** `B.RegistryChecked` = matching role environment and `GeneralDeclarations.Checked` | Spec 6.3, including output-only binders. Existing certificate checker adequacy limits remain. |
| Models | **DEFINED on the carrier:** `B.StateModels` = `GeneralSourceState.Models` | Draft Common assignments and shared ordinary/graph correspondence. No general nominal model bridge. |
| Step | **MISSING** | `I.propagate` is a private ordinary append, not source saturation or sibling regeneration. |
| Stable | **MISSING** | No source sibling/EOF fixpoint definition or proof. |
| Generated | **MISSING as a full field**; `emitAll`, `canonicalEmit`, and partial `B.Survivor` children are connected components | Draft all-where conjunction and addendum 2; actual source allocation/materialization remains external. |
| RootPending | **DEFINED on checked snapshots:** `B.RootPending` using `GeneralSourceK2.RootPending` and `GeneralDeclarationDemands.needed` | Addenda 1, 3, 4: wait for every unnamed lower head, never for named outputs. Partial source normalization retains unknowns. |
| RootK2 | **DEFINED on checked snapshots:** `B.RootK2` | Draft rejection (i), spec K2 reached-root rule; no global inspection-pending gate. Complete normalized cone required at the witnessed endpoint. |
| CandidateK2 | **PARTIAL; full field MISSING:** `B.CandidateK2` | Draft rejection (ii) and V3 priority; normalized inspected recurrence and actual interval propagation. General source interpretation, root named-output materialization and solver coverage remain open. |
| InspectionPending | **PARTIAL; full field MISSING:** `B.InspectionPending` | V3 unfinished inspection plus conservative implementation deferral. Full source production/progress remains open. |
| Survivor | **PARTIAL; full field MISSING:** `B.Survivor` | Draft centerless self/cross propagation and exact all-child emission. Fixed-frame provenance, nominal/full constructor interpretation, general outputs and materialization remain open. |
| Evidence | **MISSING as a full field**; existing dictionary/transaction/binder-location modules reused | Spec 6.4 and draft dictionary soundness still need actual general declaration-instance meaning and selected source frames. |
| Reorders | **DEFINED:** `GeneralRegistryReordering.Reorders` | Spec sibling/visible order independence at the registry carrier. Final candidate/state order invariance is not claimed. |
| DictionaryEquivalent | **DEFINED structurally:** `GeneralDictionaryPayloadOrder.Equivalent` (source counterpart remains `GeneralSourceDictionaries.DictionaryEquivalent`) | Addendum 2 and dictionary modules preserve payload structure/multiplicity. General semantic Evidence remains open. |

None of the twelve concrete general-source `B4SkeletonV3.B4Bridges` obligations is reported
closed. `survivor_children_functional` proves the actual same-key coherence of
this fixed-frame partial relation. `local_total_of_extension` applies the V3
local-totality theorem to **any future full boundary agreeing with this relation**;
it does not construct such a boundary or prove general saturation.

### Regression coverage and unfulfilled requested examples

[GeneralCandidateExamples](../../lean/Yulang/GeneralCandidateExamples.lean)
uses a real normalized record state and a satisfying regular Common model.
The source pattern is `{8: {7: 'a}}`; the demand lower endpoint denotes
`{8: μ}`, with `μ ≈ {7: μ}`. The declaration is checked, survives the private
interval pass, emits no children, and triggers candidate K2 at μ.
`reached_constructor_not_root` proves the outer demand is not root K2.
`K2_with_other_inspection_pending` proves candidate K2 and another candidate's
inspection-pending coexist. This is a record example, **not an encoding of list**.
With the inner source head unresolved, `inspection_pending_example` proves
actual inspection-pending and retains the unknown position.

[GeneralCandidateConflictExamples](../../lean/Yulang/GeneralCandidateConflictExamples.lean)
uses the existing general `indexAfter` state, with a real str/int source model,
and a checked binary head `R 'a 'a`. Both root lower heads are known and both
individual intervals are valid. The computed repeated capture creates the
cross str ≤ int check, the ordinary solver eliminates the candidate, and
`known_all_candidates_fail` proves there are no survivors and no inspection
pending. The corresponding unresolved second input stays root-pending even
though both head positions are plain variables. This checks addendum 4.

Requested but **not completed**:

1. `Display (list int)` with the list impl and `Display int` visible, exactly one
   survivor and the child `[Display int]`. `display_application_deferred`
   instead records the actual current limitation: the genuine list application
   has no translation into this Common state. No fragment result is substituted.
2. A Wrap/list survivor with the Container child and item equation. The existing
   `GeneralDeclarationExamples.wrap_child_keeps_item` still proves exact emission
   of that source equation under its supplied capture; it is not a survivor
   theorem. `wrap_application_deferred` exposes the missing nominal head bridge.
3. The literal all-model shared-state survivor claim without an added recording
   premise; the private-extension and explicit-recording theorems are stated above.

No parser/source reachability, source-frame allocator, nominal/Common adapter,
complete normalization, complete ordinary propagation, root associated-RHS
materialization, saturation, or final EOF classification has been verified.

### What the next general integration needs

- A source constructor interpretation and a nominal-aware state/model bridge.
  `CommonNominalFullCarrier` and related modules provide a dedicated nominal
  carrier, but are not the Common assignments used by the current State. The
  primitive annotations here expose, rather than solve, that mismatch.
- Exact general capture coalescing/materialization, including states whose row
  source IDs alias. Equality atoms and a source-assignment correspondence can
  remove the explicit row-injectivity coverage restriction.
- A source-derived invocation frame: merged endpoint locations, independent
  output-only binder variables, and preserved/fresh obligation identities.
  Existing dictionary `Frame`, `Plan`, canonical emissions and binder-location
  functions can consume it. No arbitrary frame should be promoted to a proved
  source-generated frame.
- General root associated-output and compound child RHS lowering, retaining
  every named equation and never selecting one interval endpoint as its centre.
- Actual candidate/private-state recording and regeneration in a shared Step,
  then stable sibling/EOF handling. The new fixed-frame child coherence supplies
  the V3 local-totality premise once the full source field is implemented.

My assessment: this work is closer to the general instance than another fragment
classifier: it imports the actual registry, state, demand, normalized observation,
ordinary solver, source-ID lookup and complete dictionary-emission machinery.
However, the main convergence bottleneck remains unchanged. The raw declaration
catalogue has names/arity/kinds but no general type interpretation; State still
uses Common without nominal layers; fixed frames still come from the caller.
The list/Wrap positive examples cannot yet cross those interfaces. Further
fragment classification results would not close these missing bridges.

### Scope question kept open

The user-facing soundness wording needs a precise state boundary; no language
choice is made here. Consider a known pair receiver with the source head
`impl Same ('a, 'a)`, where one component has type `int` and the other retains
an interval with multiple possible models. A candidate's cross constraints can
be consistent while excluding some models of the original state.

1. **Defer the unextended shared-state assertion**: use the explicitly named
   private propagated candidate state for survivor soundness, and require
   ordinary recording before the final shared-state all-model theorem.
2. Use the name `Survivor` only after the candidate's actual constraints are
   recorded in the state argument; keep a distinct potential-candidate relation
   before that point. This needs an explicit source Step/selection contract.

Both avoid conjoining all alternative candidates' constraints. The implementation
proves the private-state law and the separate recorded-state law; it does not
assert that these two state stages are the same. An asynchronous clarification
was sent during the task; no answer has been assumed.

### Full theorem statements

The following inventory is generated by Lean with `#check @...` for every new
public theorem, including implicit parameters. Module qualifications are retained.

```lean
Yulang.GeneralCandidateIntervals.propagate_models : ∀ (state : Yulang.GeneralSourceState.State)
  (bindings : Yulang.GeneralCandidateIntervals.Bindings state) (model : Yulang.GeneralSourceState.Assignment),
  Yulang.GeneralSourceState.Models (Yulang.GeneralCandidateIntervals.propagate state bindings) model ↔
    Yulang.GeneralSourceState.Models state model ∧
      Yulang.CommonRoleCandidateConstraints.Compatible bindings (state.assignment model)
Yulang.GeneralCandidateIntervals.propagated_capture_sound : ∀ (state : Yulang.GeneralSourceState.State)
  (bindings : Yulang.GeneralCandidateIntervals.Bindings state) (model : Yulang.GeneralSourceState.Assignment),
  Yulang.GeneralSourceState.Models (Yulang.GeneralCandidateIntervals.propagate state bindings) model →
    Yulang.CommonRoleCandidateConstraints.Compatible bindings (state.assignment model)
Yulang.GeneralCandidateIntervals.propagated_original : ∀ (state : Yulang.GeneralSourceState.State)
  (bindings : Yulang.GeneralCandidateIntervals.Bindings state) (model : Yulang.GeneralSourceState.Assignment),
  Yulang.GeneralSourceState.Models (Yulang.GeneralCandidateIntervals.propagate state bindings) model →
    Yulang.GeneralSourceState.Models state model
Yulang.GeneralCandidateIntervals.recorded_capture_sound : ∀ (state : Yulang.GeneralSourceState.State)
  (bindings : Yulang.GeneralCandidateIntervals.Bindings state),
  (∀ (atom : Yulang.PresenceNormalForm.Atom (Fin state.slots)),
      atom ∈ Yulang.CommonRoleCandidateConstraints.generate bindings → atom ∈ state.ordinary) →
    ∀ (model : Yulang.GeneralSourceState.Assignment),
      Yulang.GeneralSourceState.Models state model →
        Yulang.CommonRoleCandidateConstraints.Compatible bindings (state.assignment model)
Yulang.GeneralCandidateIntervals.eliminated_no_model : ∀ (state : Yulang.GeneralSourceState.State)
  (bindings : Yulang.GeneralCandidateIntervals.Bindings state),
  Yulang.GeneralCandidateIntervals.Eliminated state bindings →
    ¬∃ model, Yulang.GeneralSourceState.Models (Yulang.GeneralCandidateIntervals.propagate state bindings) model
Yulang.GeneralCandidateIntervals.model_survives : ∀ (state : Yulang.GeneralSourceState.State)
  (bindings : Yulang.GeneralCandidateIntervals.Bindings state),
  Yulang.GeneralCandidateIntervals.Covered state →
    ∀ (model : Yulang.GeneralSourceState.Assignment),
      Yulang.GeneralSourceState.Models (Yulang.GeneralCandidateIntervals.propagate state bindings) model →
        Yulang.GeneralCandidateIntervals.Survives state bindings
Yulang.GeneralCandidateIntervals.uncovered_defers : ∀ (state : Yulang.GeneralSourceState.State)
  (bindings : Yulang.GeneralCandidateIntervals.Bindings state),
  ¬Yulang.GeneralCandidateIntervals.Covered state →
    ¬Yulang.GeneralCandidateIntervals.Survives state bindings ∧
      ¬Yulang.GeneralCandidateIntervals.Eliminated state bindings
Yulang.GeneralCandidateIntervals.row_alias_defers : ∀ (state : Yulang.GeneralSourceState.State)
  (bindings : Yulang.GeneralCandidateIntervals.Bindings state) (first last : Fin state.slots),
  first ≠ last →
    state.rowSource first = state.rowSource last →
      ¬Yulang.GeneralCandidateIntervals.Survives state bindings ∧
        ¬Yulang.GeneralCandidateIntervals.Eliminated state bindings
Yulang.GeneralCandidateIntervals.survives_excludes_eliminated : ∀ (state : Yulang.GeneralSourceState.State)
  (bindings : Yulang.GeneralCandidateIntervals.Bindings state),
  Yulang.GeneralCandidateIntervals.Survives state bindings → ¬Yulang.GeneralCandidateIntervals.Eliminated state bindings
Yulang.GeneralCandidateIntervals.survives_has_model : ∀ (state : Yulang.GeneralSourceState.State)
  (bindings : Yulang.GeneralCandidateIntervals.Bindings state),
  Yulang.GeneralCandidateIntervals.Survives state bindings →
    ∃ model, Yulang.GeneralSourceState.Models (Yulang.GeneralCandidateIntervals.propagate state bindings) model
Yulang.GeneralCandidateIntervals.survives_iff_model : ∀ (state : Yulang.GeneralSourceState.State)
  (bindings : Yulang.GeneralCandidateIntervals.Bindings state),
  Yulang.GeneralCandidateIntervals.Covered state →
    (Yulang.GeneralCandidateIntervals.Survives state bindings ↔
      ∃ model, Yulang.GeneralSourceState.Models (Yulang.GeneralCandidateIntervals.propagate state bindings) model)
Yulang.GeneralCandidateIntervals.merge_recorded_linked : ∀ (state : Yulang.GeneralSourceState.State)
  (bindings : Yulang.GeneralCandidateIntervals.Bindings state) (locations : Nat → Fin state.slots × Fin state.slots),
  Yulang.GeneralCandidateIntervals.MergeRecorded state bindings locations →
    Yulang.GeneralCandidateIntervals.MergeLinked state bindings locations
Yulang.GeneralCandidateIntervals.singleton_merge_linked : ∀ (state : Yulang.GeneralSourceState.State) (name : Nat)
  (bounds : Fin state.slots × Fin state.slots),
  Yulang.GeneralCandidateIntervals.MergeLinked state [(name, bounds)] fun x => bounds
Yulang.GeneralCandidateIntervals.two_alternatives_models : ∀ (state : Yulang.GeneralSourceState.State)
  (first last : Yulang.GeneralCandidateIntervals.Bindings state) (model : Yulang.GeneralSourceState.Assignment),
  Yulang.GeneralSourceState.Models
      (Yulang.GeneralDictionaryEquationRecording.append state
        (Yulang.CommonRoleCandidateConstraints.generate first ++ Yulang.CommonRoleCandidateConstraints.generate last))
      model ↔
    Yulang.GeneralSourceState.Models state model ∧
      Yulang.CommonRoleCandidateConstraints.Compatible first (state.assignment model) ∧
        Yulang.CommonRoleCandidateConstraints.Compatible last (state.assignment model)
@Yulang.GeneralCandidateInspection.inspection_recurrence : ∀ {state : Yulang.GeneralSourceState.State}
  (view : Yulang.GeneralNormalizedObservation.Snapshot state) (report : Yulang.GeneralCandidateInspection.Report state),
  Yulang.GeneralCandidateInspection.NeedsK2 view report →
    ∃ visit,
      visit ∈ report.inspected ∧
        Yulang.GeneralSourceK2.Complete view visit.bounds.fst ∧ Yulang.GeneralSourceK2.RecursAt view visit.bounds.fst
@Yulang.GeneralCandidateInspection.append_preserves_inspections : ∀ {state : Yulang.GeneralSourceState.State}
  (first last : Yulang.GeneralCandidateInspection.Report state) (visit : Yulang.GeneralCandidateInspection.Visit state),
  visit ∈ (first.append last).inspected ↔ visit ∈ first.inspected ∨ visit ∈ last.inspected
@Yulang.GeneralCandidateInspection.append_preserves_blockers : ∀ {state : Yulang.GeneralSourceState.State}
  (first last : Yulang.GeneralCandidateInspection.Report state)
  (issue : Yulang.GeneralCandidateInspection.Visit state × Yulang.GeneralCandidateInspection.Reason),
  issue ∈ (first.append last).blocked ↔ issue ∈ first.blocked ∨ issue ∈ last.blocked
@Yulang.GeneralCandidateInspection.variable_does_not_inspect : ∀ {state : Yulang.GeneralSourceState.State}
  (view : Yulang.GeneralNormalizedObservation.Snapshot state) (names : List Nat)
  (bounds : Yulang.GeneralCandidateInspection.Bounds state),
  (Yulang.GeneralCandidateInspection.inspect view (Yulang.GeneralCandidateInspection.Query.variables names)
          bounds).inspected =
      [] ∧
    (Yulang.GeneralCandidateInspection.inspect view (Yulang.GeneralCandidateInspection.Query.variables names)
          bounds).captures =
      List.map (fun name => (name, bounds)) names
@Yulang.GeneralCandidateInspection.unresolved_constructor_defers : ∀ {state : Yulang.GeneralSourceState.State}
  (view : Yulang.GeneralNormalizedObservation.Snapshot state) (shape : Yulang.GeneralNormalizedObservation.Shape)
  (children : List Yulang.GeneralCandidateInspection.Query) (bounds : Yulang.GeneralCandidateInspection.Bounds state)
  (reason : Yulang.GeneralNormalizedObservation.Deferred state.slots),
  view.heads bounds.fst = Yulang.GeneralNormalizedObservation.Head.deferred reason →
    (Yulang.GeneralCandidateInspection.inspect view (Yulang.GeneralCandidateInspection.Query.node shape children)
          bounds).blocked ≠
      []
@Yulang.GeneralCandidateInspection.untranslated_application_defers : ∀ {state : Yulang.GeneralSourceState.State}
  (view : Yulang.GeneralNormalizedObservation.Snapshot state)
  (primitives : Yulang.GeneralCandidateInspection.Primitives) (constructor : Nat)
  (arguments : List Yulang.GeneralDeclarationPatterns.Pattern)
  (bounds : Yulang.GeneralCandidateInspection.Bounds state),
  primitives constructor = none →
    (Yulang.GeneralCandidateInspection.inspect view
          (Yulang.GeneralCandidateInspection.translate primitives
            (Yulang.GeneralDeclarationPatterns.Pattern.app constructor arguments))
          bounds).blocked ≠
      []
Yulang.GeneralCandidateInspection.merged_plain_payload : ∀ (primitives : Yulang.GeneralCandidateInspection.Primitives)
  (first last tag : Nat),
  Yulang.GeneralCandidateInspection.translate primitives
      (Yulang.GeneralDeclarationPatterns.Pattern.variant tag
        ((Yulang.GeneralDeclarationPatterns.Pattern.var first).join
          (Yulang.GeneralDeclarationPatterns.Pattern.var last))) =
    Yulang.GeneralCandidateInspection.Query.node (Yulang.GeneralNormalizedObservation.Shape.variant tag)
      [Yulang.GeneralCandidateInspection.Query.variables [first, last]]
@Yulang.GeneralCandidateBoundaryParts.pending_excludes_rootK2 : ∀ {roles : Yulang.Roles.RoleDecls}
  (context : Yulang.GeneralCandidateBoundaryParts.Context roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralCandidateBoundaryParts.RootPending context root →
    ¬Yulang.GeneralCandidateBoundaryParts.RootK2 context root
@Yulang.GeneralCandidateBoundaryParts.pending_excludes_candidateK2 : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralCandidateBoundaryParts.Context roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralCandidateBoundaryParts.RootPending context root →
    ¬Yulang.GeneralCandidateBoundaryParts.CandidateK2 registry context root
@Yulang.GeneralCandidateBoundaryParts.rootK2_recurrence : ∀ {roles : Yulang.Roles.RoleDecls}
  (context : Yulang.GeneralCandidateBoundaryParts.Context roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralCandidateBoundaryParts.RootK2 context root →
    ∃ argument slot,
      context.state.source slot = (root.demand.arguments argument).fst ∧
        Yulang.GeneralSourceK2.RecursAt context.view slot
@Yulang.GeneralCandidateBoundaryParts.prepared_headReady : ∀ {roles : Yulang.Roles.RoleDecls}
  {constructors : Yulang.GeneralDeclarationPatterns.Constructors}
  (context : Yulang.GeneralCandidateBoundaryParts.Context roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked constructors roles declaration),
  Yulang.GeneralCandidateBoundaryParts.Prepared context root declaration checked →
    Yulang.GeneralCandidateBoundaryParts.HeadReady context root declaration
@Yulang.GeneralCandidateBoundaryParts.headReady_not_failed : ∀ {roles : Yulang.Roles.RoleDecls}
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors)
  (context : Yulang.GeneralCandidateBoundaryParts.Context roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration),
  Yulang.GeneralCandidateBoundaryParts.HeadReady context root declaration →
    ¬Yulang.GeneralCandidateBoundaryParts.Failed constructors context root declaration
@Yulang.GeneralCandidateBoundaryParts.conservative_deferral : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralCandidateBoundaryParts.Context roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  ¬Yulang.GeneralCandidateBoundaryParts.RootPending context root →
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration),
      declaration ∈ registry.declarations →
        ∀ (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration),
          declaration.role = root.demand.role →
            ¬Yulang.GeneralCandidateBoundaryParts.Failed registry.constructors context root declaration →
              ¬Yulang.GeneralCandidateBoundaryParts.Prepared context root declaration checked →
                Yulang.GeneralCandidateBoundaryParts.InspectionPending registry context root
@Yulang.GeneralCandidateBoundaryParts.blocked_unprepared : ∀ {roles : Yulang.Roles.RoleDecls}
  {constructors : Yulang.GeneralDeclarationPatterns.Constructors}
  (context : Yulang.GeneralCandidateBoundaryParts.Context roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked constructors roles declaration)
  (bounds : List (Yulang.GeneralCandidateInspection.Bounds context.state)),
  Yulang.GeneralCandidateBoundaryParts.arguments context root = some bounds →
    (Yulang.GeneralCandidateBoundaryParts.report context root declaration bounds).blocked ≠ [] →
      ¬Yulang.GeneralCandidateBoundaryParts.Prepared context root declaration checked
@Yulang.GeneralCandidateBoundaryParts.private_model_not_failed : ∀ {roles : Yulang.Roles.RoleDecls}
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors)
  (context : Yulang.GeneralCandidateBoundaryParts.Context roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (bounds : List (Yulang.GeneralCandidateInspection.Bounds context.state)),
  Yulang.GeneralCandidateBoundaryParts.arguments context root = some bounds →
    (Yulang.GeneralCandidateBoundaryParts.report context root declaration bounds).conflicts = [] →
      ∀ (model : Yulang.GeneralSourceState.Assignment),
        Yulang.GeneralSourceState.Models
            (Yulang.GeneralCandidateIntervals.propagate context.state
              (Yulang.GeneralCandidateBoundaryParts.report context root declaration bounds).captures)
            model →
          ¬Yulang.GeneralCandidateBoundaryParts.Failed constructors context root declaration
@Yulang.GeneralCandidateBoundaryParts.all_failed_no_survivors : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralCandidateBoundaryParts.Context roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  (∀ (declaration : Yulang.GeneralDeclarations.Declaration),
      declaration ∈ registry.declarations →
        declaration.role = root.demand.role →
          Yulang.GeneralCandidateBoundaryParts.Failed registry.constructors context root declaration) →
    (∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
        ¬Yulang.GeneralCandidateBoundaryParts.Survivor registry context root key children) ∧
      ¬Yulang.GeneralCandidateBoundaryParts.InspectionPending registry context root
@Yulang.GeneralCandidateBoundaryParts.survivor_children_functional : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry),
  Yulang.GeneralDeclarations.Checked registry →
    ∀ (context : Yulang.GeneralCandidateBoundaryParts.Context roles)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
      (first last : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
      Yulang.GeneralCandidateBoundaryParts.Survivor registry context root key first →
        Yulang.GeneralCandidateBoundaryParts.Survivor registry context root key last → first = last
@Yulang.GeneralCandidateBoundaryParts.survivor_interval_sound : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralCandidateBoundaryParts.Context roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
  (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
  Yulang.GeneralCandidateBoundaryParts.Survivor registry context root key children →
    ∃ declaration,
      declaration ∈ registry.declarations ∧
        declaration.id = key ∧
          ∃ bounds,
            Yulang.GeneralCandidateBoundaryParts.arguments context root = some bounds ∧
              ∀ (model : Yulang.GeneralSourceState.Assignment),
                Yulang.GeneralSourceState.Models
                    (Yulang.GeneralCandidateIntervals.propagate context.state
                      (Yulang.GeneralCandidateBoundaryParts.report context root declaration bounds).captures)
                    model →
                  Yulang.GeneralSourceState.Models context.state model ∧
                    Yulang.CommonRoleCandidateConstraints.Compatible
                      (Yulang.GeneralCandidateBoundaryParts.report context root declaration bounds).captures
                      (context.state.assignment model)
@Yulang.GeneralCandidateBoundaryParts.candidateK2_inspected_recurrence : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralCandidateBoundaryParts.Context roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralCandidateBoundaryParts.CandidateK2 registry context root →
    ∃ declaration,
      declaration ∈ registry.declarations ∧
        ∃ bounds,
          Yulang.GeneralCandidateBoundaryParts.arguments context root = some bounds ∧
            ∃ visit,
              visit ∈ (Yulang.GeneralCandidateBoundaryParts.report context root declaration bounds).inspected ∧
                Yulang.GeneralSourceK2.Complete context.view visit.bounds.fst ∧
                  Yulang.GeneralSourceK2.RecursAt context.view visit.bounds.fst
Yulang.GeneralCandidateBoundaryParts.local_total_of_extension : ∀ (roles : Yulang.Roles.RoleDecls)
  (boundary : Yulang.B4Target.SourceBoundary (Yulang.GeneralCandidateBoundaryParts.vocabulary roles))
  (registry : Yulang.GeneralDeclarations.Registry),
  Yulang.GeneralDeclarations.Checked registry →
    ∀ (context : Yulang.GeneralCandidateBoundaryParts.Context roles)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      (∀ (key : Nat) (children : List (Yulang.GeneralCandidateBoundaryParts.vocabulary roles).Demand),
          boundary.Survivor registry context root key children ↔
            Yulang.GeneralCandidateBoundaryParts.Survivor registry context root key children) →
        ∃ frontier, Yulang.B4TargetV3.Local boundary registry context root frontier
Yulang.GeneralCandidateExamples.recursive_head_checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralCandidateExamples.constructors Yulang.GeneralCandidateExamples.roles
  Yulang.GeneralCandidateExamples.recursiveHead
Yulang.GeneralCandidateExamples.root_arguments : ∀ (resolved : Bool),
  Yulang.GeneralCandidateBoundaryParts.arguments (Yulang.GeneralCandidateExamples.context resolved)
      Yulang.GeneralCandidateExamples.root =
    some [(0, 0)]
Yulang.GeneralCandidateExamples.translated_record : Yulang.GeneralCandidateInspection.headQueries
    Yulang.GeneralCandidateExamples.primitives Yulang.GeneralCandidateExamples.recursiveHead =
  [Yulang.GeneralCandidateInspection.Query.node (Yulang.GeneralNormalizedObservation.Shape.record [8])
      [Yulang.GeneralCandidateInspection.Query.node (Yulang.GeneralNormalizedObservation.Shape.record [7])
          [Yulang.GeneralCandidateInspection.Query.variables [0]]]]
Yulang.GeneralCandidateExamples.recursive_captures : (Yulang.GeneralCandidateBoundaryParts.report
      (Yulang.GeneralCandidateExamples.context true) Yulang.GeneralCandidateExamples.root
      Yulang.GeneralCandidateExamples.recursiveHead [(0, 0)]).captures =
  [(0, 1, 1)]
Yulang.GeneralCandidateExamples.recursive_state_model : Yulang.GeneralSourceState.Models
  (Yulang.GeneralCandidateExamples.recordState true) Yulang.GeneralCandidateExamples.recordModel
Yulang.GeneralCandidateExamples.recursive_private_model : Yulang.GeneralSourceState.Models
  (Yulang.GeneralCandidateIntervals.propagate (Yulang.GeneralCandidateExamples.recordState true)
    (Yulang.GeneralCandidateBoundaryParts.report (Yulang.GeneralCandidateExamples.context true)
        Yulang.GeneralCandidateExamples.root Yulang.GeneralCandidateExamples.recursiveHead [(0, 0)]).captures)
  Yulang.GeneralCandidateExamples.recordModel
Yulang.GeneralCandidateExamples.recursive_head_ready : Yulang.GeneralCandidateBoundaryParts.HeadReady
  (Yulang.GeneralCandidateExamples.context true) Yulang.GeneralCandidateExamples.root
  Yulang.GeneralCandidateExamples.recursiveHead
Yulang.GeneralCandidateExamples.recursive_inspection_K2 : Yulang.GeneralCandidateInspection.NeedsK2
  (Yulang.GeneralCandidateExamples.recordView true)
  (Yulang.GeneralCandidateBoundaryParts.report (Yulang.GeneralCandidateExamples.context true)
    Yulang.GeneralCandidateExamples.root Yulang.GeneralCandidateExamples.recursiveHead [(0, 0)])
Yulang.GeneralCandidateExamples.candidate_K2_example : Yulang.GeneralCandidateBoundaryParts.CandidateK2
  Yulang.GeneralCandidateExamples.registry (Yulang.GeneralCandidateExamples.context true)
  Yulang.GeneralCandidateExamples.root
Yulang.GeneralCandidateExamples.reached_constructor_not_root : ¬Yulang.GeneralCandidateBoundaryParts.RootK2
    (Yulang.GeneralCandidateExamples.context true) Yulang.GeneralCandidateExamples.root
Yulang.GeneralCandidateExamples.descendant_inspection_deferred : (Yulang.GeneralCandidateBoundaryParts.report
      (Yulang.GeneralCandidateExamples.context false) Yulang.GeneralCandidateExamples.root
      Yulang.GeneralCandidateExamples.recursiveHead [(0, 0)]).blocked ≠
  []
Yulang.GeneralCandidateExamples.inspection_pending_example : Yulang.GeneralCandidateBoundaryParts.InspectionPending
  Yulang.GeneralCandidateExamples.registry (Yulang.GeneralCandidateExamples.context false)
  Yulang.GeneralCandidateExamples.root
Yulang.GeneralCandidateExamples.recursive_survivor : Yulang.GeneralCandidateBoundaryParts.Survivor
  Yulang.GeneralCandidateExamples.registry (Yulang.GeneralCandidateExamples.context true)
  Yulang.GeneralCandidateExamples.root 40 []
Yulang.GeneralCandidateExamples.display_application_deferred : ∀ (resolved : Bool),
  (Yulang.GeneralCandidateBoundaryParts.report (Yulang.GeneralCandidateExamples.context resolved)
        Yulang.GeneralCandidateExamples.root Yulang.GeneralDeclarationExamples.display [(0, 0)]).blocked ≠
    []
Yulang.GeneralCandidateExamples.wrap_application_deferred : ∀ (resolved : Bool),
  (Yulang.GeneralCandidateBoundaryParts.report (Yulang.GeneralCandidateExamples.context resolved)
        Yulang.GeneralCandidateExamples.root Yulang.GeneralDeclarationExamples.wrap [(0, 0)]).blocked ≠
    []
Yulang.GeneralCandidateExamples.K2_with_other_inspection_pending : Yulang.GeneralCandidateBoundaryParts.CandidateK2
    Yulang.GeneralCandidateExamples.mixedRegistry (Yulang.GeneralCandidateExamples.context true)
    Yulang.GeneralCandidateExamples.root ∧
  Yulang.GeneralCandidateBoundaryParts.InspectionPending Yulang.GeneralCandidateExamples.mixedRegistry
    (Yulang.GeneralCandidateExamples.context true) Yulang.GeneralCandidateExamples.root
Yulang.GeneralCandidateConflictExamples.repeated_checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralCandidateExamples.constructors Yulang.GeneralCandidateExamples.roles
  Yulang.GeneralCandidateConflictExamples.repeated
Yulang.GeneralCandidateConflictExamples.repeated_capture : (Yulang.GeneralCandidateBoundaryParts.report
      Yulang.GeneralCandidateConflictExamples.context Yulang.GeneralCandidateConflictExamples.root
      Yulang.GeneralCandidateConflictExamples.repeated [(0, 0), (1, 1)]).captures =
  Yulang.GeneralCandidateConflictExamples.bindings
Yulang.GeneralCandidateConflictExamples.known_arguments : Yulang.GeneralCandidateBoundaryParts.arguments
    Yulang.GeneralCandidateConflictExamples.context Yulang.GeneralCandidateConflictExamples.root =
  some [(0, 0), (1, 1)]
Yulang.GeneralCandidateConflictExamples.known_lower_heads : ¬Yulang.GeneralCandidateBoundaryParts.RootPending
    Yulang.GeneralCandidateConflictExamples.context Yulang.GeneralCandidateConflictExamples.root
Yulang.GeneralCandidateConflictExamples.original_has_model : Yulang.GeneralSourceState.Models
  Yulang.GeneralSourceStateExamples.indexAfter
  (Yulang.GeneralSourceStateExamples.indexModel (Yulang.CommonSyntax.Layer.base Yulang.Inference.Base.int))
Yulang.GeneralCandidateConflictExamples.cross_constraints_eliminate : Yulang.GeneralCandidateIntervals.Eliminated
  Yulang.GeneralSourceStateExamples.indexAfter Yulang.GeneralCandidateConflictExamples.bindings
Yulang.GeneralCandidateConflictExamples.known_all_candidates_fail : (∀ (key : Nat)
    (children : List (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralCandidateExamples.roles)),
    ¬Yulang.GeneralCandidateBoundaryParts.Survivor Yulang.GeneralCandidateConflictExamples.registry
        Yulang.GeneralCandidateConflictExamples.context Yulang.GeneralCandidateConflictExamples.root key children) ∧
  ¬Yulang.GeneralCandidateBoundaryParts.InspectionPending Yulang.GeneralCandidateConflictExamples.registry
      Yulang.GeneralCandidateConflictExamples.context Yulang.GeneralCandidateConflictExamples.root
Yulang.GeneralCandidateConflictExamples.unresolved_second_input_pending : Yulang.GeneralCandidateBoundaryParts.RootPending
    Yulang.GeneralCandidateConflictExamples.before Yulang.GeneralCandidateConflictExamples.root ∧
  ¬Yulang.GeneralCandidateBoundaryParts.RootK2 Yulang.GeneralCandidateConflictExamples.before
        Yulang.GeneralCandidateConflictExamples.root ∧
    ¬Yulang.GeneralCandidateBoundaryParts.CandidateK2 Yulang.GeneralCandidateConflictExamples.registry
        Yulang.GeneralCandidateConflictExamples.before Yulang.GeneralCandidateConflictExamples.root
```

### Verification and review for Item 3

Final commands, each run from `lean/`:

| Exact command | Exit code |
| --- | --- |
| `lake build Yulang.GeneralCandidateIntervals Yulang.GeneralCandidateInspection Yulang.GeneralCandidateBoundaryParts Yulang.GeneralCandidateExamples Yulang.GeneralCandidateConflictExamples > /tmp/astra-candidates-focused.log 2>&1` | 0 |
| `lake build Yulang > /tmp/astra-candidates-umbrella.log 2>&1` | 0 |
| `lake env lean Audit.lean > /tmp/astra-candidates-audit.log 2>&1` | 0 |
| `lake env lean /tmp/astra-candidates-signatures.lean > /tmp/astra-candidates-signatures.txt 2>&1` | 0 |

The focused build completed 542 jobs; the umbrella build completed 1382 jobs.
The full audit contained 8705 dependency reports, including all 58 new public
theorems. Its complete dependency whitelist was exactly `propext`,
`Classical.choice`, and `Quot.sound`. The report count includes existing entries
and is not a count of new independent results.

Append-only checks confirmed that existing `Yulang.lean` and `Audit.lean` bytes
remain unchanged prefixes. Only five imports and 58 audit entries were added.
New-file token/whitespace checks, theorem/signature/audit coverage, allowed-path
checks, and `git diff --check` passed. No existing implementation module, spec,
plan, lake configuration, commit, push, or git reference was changed.

Earlier focused elaboration attempts failed while resolving dependent finite
indices, recursive-function rewriting, and proof simplification. Those failures
were corrected only in new modules. The initial signature harness used an
unsupported pretty-printer option; removing it produced the recorded exit-0
inventory. No failed command is counted as a successful final check.

The `yulang-proofs` skill was applied. No registered prover role or launch
configuration was available, so the primary constructed the bounded derivations;
no prover agent ran. A separate read-only reviewer examined all five modules,
source limitations, the final Item 3 table and all 58 signatures. The reviewer
found no blocking defect in the stated partial claims, checked the append-only
and inventory restrictions, and requested a wording correction clarifying that
row injectivity is required by the current lifting proof, not inherently by the
language. That correction is incorporated. The reviewer did not independently
run Lean builds. Neither review nor these checks certify completion of Item 3,
a full SourceBoundary, or any concrete general B4 bridge.

## Item 3b — nominal/Common correspondence and derived invocation frames (2026-11-12)

This increment connects the shared source identities and ordinary terms to
`CommonNominalFullCarrier`, and proves the positive Display and Wrap examples
with genuine nominal values. It does **not** finish general Item 3. The model
represents arbitrary invariant type/row interval descriptors, but the supported
nominal inspection range currently requires existing identical endpoint IDs,
complete reachable observations, and no explicit nominal-argument recurrence.
Other observations defer. No complete `SourceBoundary` or executor is defined.

### Carrier and model correspondence

`GeneralNominalCommonBridge.lift` uses
`CommonNominalFullModelMap.value`, which preserves constructors and preserves
and reflects Common subtyping. `row_eval`, `type_eval`, `atom_exact`, and
`atoms_exact` transport the existing ordinary terms and constraints. The source
and independent row identity maps are unchanged. `models_exact` proves exact
agreement with old `GeneralSourceState.Models` **on lifted Common assignments**.
It does not apply a Common-only certificate or the nominal retraction to an
arbitrary full-carrier assignment.

For arbitrary full assignments, the interpretation explicitly retains the
recorded source-head equations and interval inequalities in addition to the
ordinary atoms. Their redundancy is proved on lifted old assignments; no
universal full-carrier `Models ↔ original ordinary atoms alone` theorem is
claimed. Automatic production of these full source equations is still part of
the source-generation/Step bridge. The examples here give the equations
explicitly and construct actual full models satisfying them.

`GeneralNominalState.State` extends this same finite source snapshot and its
normalized view. A nominal descriptor carries a catalogue key, the resolved
`Constructor.name`, its checked parameter layout, and references to the same
source endpoint slots. `Denotes` says that the root is equivalent to a genuine
`CommonNominalFullCarrier.nominal` value whose semantic arguments satisfy those
intervals. These mathematical model witnesses are **not** allocated source
centres and are never searched as candidate substitutions. Type and row
parameters are represented independently. Nominal bodies are absent.

The existing normalization derivations are replayed against arbitrary full
assignments by `GeneralNominalCommonBridge.rewrites_sound`: hidden-field
removal, distinct-field reordering, required-field/empty-tail equality, and
same-tag merging all hold with nominal children. The full finite observation
proofs reuse the existing Common normalization argument and full nominal
constructor/probe laws. `normalization_preserves` proves that the normalized
observations add no restriction to this full interpretation. K2 still uses the
existing normalized structural recurrence definition, not raw graph flags;
`embed_pending`, `embed_K2`, `atK2_recurrence`, and the regression theorems make
that preservation explicit. Mixed nominal/structural K2 is not claimed.

This implements the opacity and invariant-argument decisions of spec §6.3–6.4,
while retaining the root-recurrence reading of draft rejection (i). It does not
reinterpret `list` as a record or variant. Source metadata distinguishes
primitive names from invariant nominal applications; inspection compares
resolved `.name`, not catalogue indices. Catalogue-to-front-end provenance and
unsupported variance/layout interpretations remain open bridges.

### Why broad nominal observations still defer

Interval membership by itself is insufficient as an exact inspection view.
For example, consider two inputs fixed by ordinary equations to `list int`
and `list str`, both recorded with coarse parameter bounds `(bottom, top)`.
For the head `R(list 'a, list 'a)`, intersecting those coarse bounds would
succeed despite the already fixed invariant parameters being incompatible.
The missing piece is propagation from arbitrary nominal equations back into
precise interval observations, preserving all original model constraints.
This is a proof/representation gap, not a new owner semantic question.

Accordingly, `typeArguments` accepts only existing identical type endpoint IDs.
`fits_existing_endpoint` and `denotes_singleton_exact` prove the resulting
actual-nominal correspondence. This is an explicit restricted inspection range,
not a general interval implementation disguised as a completed field. Broad
intervals remain representable by `Descriptor`/`Denotes` and are blocked, never
turned into an interval failure. Different but provably equal IDs also defer
until that normalization bridge is supplied. No new midpoint is introduced.

There is a second coverage guard. A source equation such as `x ≈ list x` is
recursion through an **explicit argument**, unlike a named declaration's opaque
recursive body. `explicitSuccessors` follows normalized structural children
and existing point parameter references, without body edges. `NominalSupported`
requires all reached observations to be known and forbids cycles through any
reached nominal parameter position. This also blocks a hidden cycle through
an unresolved alias. It permits an acyclic nominal wrapper pointing to a known
pure structural cycle; inspecting that structural position uses the existing
K2 theorem. These are conservative coverage conditions, not a newly decided
rejection rule. Every unnamed root position is included in the report, so a
bare-variable implementation cannot bypass this coverage check. General mixed
recurrence normalization remains MISSING.

Arrow-row normalization, non-point nominal interval propagation, row-pattern
inspection, lower/upper parameter layouts, covariance outside an invariant
context, and alias canonicalization have not been implemented by this increment.
Their observations stay deferred. The current catalogue lacks general variance
metadata; `Interpretation.invariantNominal` explicitly identifies the supported
source interpretation instead of asserting all constructors are invariant.

### Allocation and candidate lifecycle

`GeneralNominalIdentities.encode` injectively encodes invocation, declaration,
purpose, clause/binder, and position. The source snapshot retains a seed and
allocated origins. Its numeric IDs are independent of registry enumeration and
remain identical after private reservation/propagation. Distinct invocations
have distinct generated IDs even from the same snapshot. The finite requested
origin list is derived from the actual declarations and clauses; it is not an
externally supplied frame.

`GeneralNominalAllocation.capture`, `allocation`, and `frame` derive capture and
child identities. A single captured occurrence retains its original interval;
repeated occurrences obtain separate union-of-lowers and intersection-of-uppers
identities. `cross` generates every self and repeated-variable cross inequality.
`propagate` reserves the generated identities, records their ownership, and
adds these ordinary constraints to a candidate-private extension. Output-only
binders receive fresh ordinary identities, without a value equation until the
appropriate associated result is supplied. All ordinary free type and row IDs
are included in `sources`, so freshness does not ignore an existing constraint
simply because its ID is absent from the old inspection graph.

`Fresh` allows an origin's revisit and blocks collisions with unrelated state
sources. Both preparation and interval-failure classification require freshness;
`allocation_collision_defers` prevents an accidental generated collision from
becoming an empty-candidate rejection. `source_registry_independent` and
`propagated_source_preserved` prove the relevant identity properties. Allocation
under future Step updates must retain the seed and ownership records. This is
not a proof of a source invocation-tree producer or a complete reordering bridge.

`Survivor` takes registry, context, root, key, and children. It takes **no supplied
frame or merged-slot map**. Children are exactly the existing canonical emitter's
whole clause list, including named equations and obligation identities. Their
source support is checked in the private extension. Child success is not a
survivor premise; the where list remains a conjunction and candidates remain
separate alternatives. `Consistent` is mathematical satisfiability of propagated
full-state equations, independent of an executor. It is not an effective
complete full-carrier solver or a substitution enumeration.

`survivor_interval_sound` quantifies over **every model of that candidate's
private propagated state**, and recovers the original state model plus all
captured self/cross inequalities. It does not say that all models of the
unextended state already satisfy every alternative's constraints. A general
fresh-model extension/completeness theorem and an effective solver remain open.
The same-key child-functionality proof gives V3 local totality only conditionally
for a future complete boundary extending this exact relation.

Associated RHS materialization is still restricted. The positive Wrap demand is
`Wrap (list int)` with no requested root output; its implementation retains
`out = list 'b` and its emitted Container child carries `item = 'b` at a computed,
fresh, reserved target. The theorem does not execute Container, construct the
root `out` value, or select a dictionary. Compound child input/output RHS requests
and requested root outputs remain deferred. The where child itself is emitted
before its resolution, as the draft's lossless-tree requirement demands.

The new owner rule merging equal-input demands belongs to Item 4 and is not
implemented here. Fresh identity inequalities never imply unequal denotations:
`Models` permits equal values at different IDs. Item 4 can therefore add output
equalities for same-role demands with equal unnamed inputs, while preserving
obligation provenance and allocation ownership.

### Vocabulary, executor, and all thirteen boundary fields

All definitions below are independent of an executor result. “Partial” means
that the general carrier exists but a complete faithful field is still MISSING;
it must not be silently installed as a finished general boundary.

| Component | Concrete definition / status | Faithfulness and remaining boundary |
| --- | --- | --- |
| Vocabulary.Registry | **Defined:** `GeneralDeclarations.Registry` | Full checked declarations, where equations, output-only binders and source IDs; spec §6.3. |
| Vocabulary.State | **Defined extension:** `GeneralNominalCandidates.Context`, containing `GeneralNominalState.State` | Shared old source/row maps, full ordinary equations, nominal interval descriptors, normalized view, reservation and ownership. Snapshot construction is not source reachability. |
| Vocabulary.Demand | **Defined:** `GeneralSourceDictionaries.Occurrence roles` / `GeneralSourceState.Demand roles` | Same role-arity-indexed unnamed intervals and named output obligations; addenda 3–4. |
| Vocabulary.Model | **Defined:** `GeneralNominalCommonBridge.Assignment` | `Nat → Comp CommonNominalFullCarrier.model`; exact old Common lifting, genuine opaque nominal constructors. |
| Checked | **Defined:** `GeneralDeclarations.Checked`; future adapter also requires `registry.roles = roles` | Existing general declaration rules, including output-only checking; no resolution dependence. |
| Models | **Defined:** `GeneralNominalState.Models` | General full-carrier equations plus nominal descriptor meaning. Exact old correspondence is on lifted assignments, as stated above. |
| Step | **MISSING** | No complete shared full-state saturation, nominal equation-to-interval propagation, materialization, or equal-input demand merging. |
| Stable | **MISSING** | No general fixed-point/end-of-file stability predicate tied to that Step. |
| Generated | **MISSING** | No general source producer for full checked snapshots, occurrence identities and all obligations. |
| RootPending | **Defined on the snapshot:** `GeneralNominalState.RootPending` | Every unnamed lower root must have a normalized ordinary or nominal observation; named outputs are excluded, addenda 3–4. |
| RootK2 | **Partial:** `GeneralNominalState.RootK2` / `AtK2` | Gated by absence of RootPending; sound against normalized structural `RecursAt`. General mixed nominal recurrence classification is **MISSING**; incomplete observations defer through coverage when candidates are inspected. |
| CandidateK2 | **Partial:** `GeneralNominalCandidates.CandidateK2` | Uses inspected normalized structural recurrence, never raw cycles; independent of absence of InspectionPending. Mixed nominal recurrence remains **MISSING**. |
| InspectionPending | **Partial:** `GeneralNominalCandidates.InspectionPending` | Retains visible checked candidates blocked by observation, freshness or materialization; `coverage_defers` and `allocation_collision_defers` prove conservative deferral. Complete general normalization/applicability remains **MISSING**. |
| Survivor | **Partial:** `GeneralNominalCandidates.Survivor` | Genuine nominal positive examples and derived frames now work. Non-point nominal inspection, general materialization and a complete full solver bridge remain **MISSING**. This support restriction is explicit; it is not an int/str replacement for the model. |
| Evidence | **MISSING for this full-state boundary** | Existing `GeneralSourceDictionaries*` / `GeneralDictionary*` carriers and transaction proofs are reused for emission, but full nominal RHS/selection soundness and feedback are not connected here. |
| Reorders | **Defined carrier relation:** `GeneralRegistryReordering.Reorders` | Existing declaration/obligation IDs preserved, where order irrelevant. Allocated source IDs now ignore enumeration; full classifier/evidence reordering is unproved. |
| DictionaryEquivalent | **Defined carrier relation:** `GeneralDictionaryPayloadOrder.Equivalent` | Existing dictionary payload/order equivalence; connection to full-model Evidence remains open. |
| Executor.run | **MISSING** | No concrete general executor over this full state, Step and lossless diagnostic tree. |

Consequently no `generalBoundary : SourceBoundary ...` is fabricated. The
conditional `local_total_of_extension` is a representation result for future
integration, not completion of a general B4 theorem or a V3 bridge instance.

### Examples and convergence assessment

`display_exactly_one` proves for **every** key and child list that the survivor
relation for the checked registry containing `Display int`, the list Display
implementation, and Wrap holds exactly for key 1 and `[displayChild]`.
`displayChild` is the computed occurrence of `Display int` at the existing
parameter endpoints. `wrap_survivor`, `wrap_children`, `wrap_item_equation`, and
`item_target_fresh` prove the actual Container child and fresh item-equation
identity. `state_models` constructs genuine `nominal 0 [int]` models.

The extended regressions prove Index pending with every lifted Common key
assignment still possible; no RootK2 at Index or the shadow example; RootK2 and
a model for the genuine structural loop; unresolved nominal payload inspection
pending; different parameter endpoint IDs deferred; and no survivors for the
known str/int repeated-capture conflict in the full model. Existing Item 3
CandidateK2, mixed-pending, and negative regressions remain included in the
umbrella build and full audit.

This is measurable convergence: the general source identities, ordinary atoms,
normalized proofs, declaration emitter, actual nominal carrier, and derived
frames now participate in the same positive survivor theorems. The older narrow
solvers still do not provide the general nominal interval propagation theorem.
The broad-descriptor counterexample explains concretely why more isolated
scalar/settled lemmas alone cannot close that remaining gap. Current status is
a proved correspondence and supported candidate slice, not completed Item 3.

There is no new owner semantic question in this increment. All remaining cases
above are deferred implementation/proof gaps under the existing decisions.

### Full public theorem statements for Item 3b

The following inventory is the Lean-generated type of every new public theorem
(84 declarations). Private proof helpers are not claimed separately.

```lean
Yulang.GeneralNominalIdentities.pair_injective : Function.Injective fun p =>
  Yulang.GeneralNominalIdentities.pair p.fst p.snd
Yulang.GeneralNominalIdentities.encode_injective : Function.Injective Yulang.GeneralNominalIdentities.encode
Yulang.GeneralNominalIdentities.invocation_le : ∀ (key : Yulang.GeneralNominalIdentities.Origin),
  key.fst ≤ Yulang.GeneralNominalIdentities.encode key
Yulang.GeneralNominalIdentities.source_identity : ∀ (seed : Nat) (first last : Yulang.GeneralNominalIdentities.Origin),
  Yulang.GeneralNominalIdentities.source seed first = Yulang.GeneralNominalIdentities.source seed last ↔ first = last
Yulang.GeneralNominalIdentities.source_above_seed : ∀ (seed : Nat) (key : Yulang.GeneralNominalIdentities.Origin),
  seed < Yulang.GeneralNominalIdentities.source seed key
Yulang.GeneralNominalIdentities.source_above_invocation : ∀ (seed : Nat) (key : Yulang.GeneralNominalIdentities.Origin),
  key.fst < Yulang.GeneralNominalIdentities.source seed key
@Yulang.GeneralNominalCommonBridge.row_eval : ∀ {α : Type}
  (assignment : α → Yulang.Core.PresenceGeneration.Comp Yulang.Common.model)
  (term : Yulang.Core.PresenceGeneration.RowTerm α),
  Yulang.Core.PresenceGeneration.RowTerm.eval Yulang.CommonNominalFullCarrier.model
      (Yulang.GeneralNominalCommonBridge.lift assignment) term =
    Yulang.Core.PresenceGeneration.RowTerm.eval Yulang.Common.model assignment term
@Yulang.GeneralNominalCommonBridge.type_eval : ∀ {α : Type}
  (assignment : α → Yulang.Core.PresenceGeneration.Comp Yulang.Common.model)
  (term : Yulang.Core.PresenceGeneration.TyTerm α),
  Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.CommonNominalFullCarrier.model
      (Yulang.GeneralNominalCommonBridge.lift assignment) term =
    Yulang.CommonNominalFullModelMap.value
      (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.Common.model assignment term)
@Yulang.GeneralNominalCommonBridge.atom_exact : ∀ {α : Type}
  (assignment : α → Yulang.Core.PresenceGeneration.Comp Yulang.Common.model) (atom : Yulang.PresenceNormalForm.Atom α),
  Yulang.PresenceNormalForm.Atom.Holds Yulang.CommonNominalFullCarrier.model
      (Yulang.GeneralNominalCommonBridge.lift assignment) atom ↔
    Yulang.PresenceNormalForm.Atom.Holds Yulang.Common.model assignment atom
@Yulang.GeneralNominalCommonBridge.atoms_exact : ∀ {α : Type}
  (assignment : α → Yulang.Core.PresenceGeneration.Comp Yulang.Common.model)
  (atoms : List (Yulang.PresenceNormalForm.Atom α)),
  Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model
      (Yulang.GeneralNominalCommonBridge.lift assignment) atoms ↔
    Yulang.PresenceNormalForm.All Yulang.Common.model assignment atoms
Yulang.GeneralNominalCommonBridge.assignment_lift : ∀ (state : Yulang.GeneralSourceState.State)
  (model : Yulang.GeneralSourceState.Assignment),
  Yulang.GeneralNominalCommonBridge.assignment state (Yulang.GeneralNominalCommonBridge.lift model) =
    Yulang.GeneralNominalCommonBridge.lift (state.assignment model)
Yulang.GeneralNominalCommonBridge.models_exact : ∀ (state : Yulang.GeneralSourceState.State)
  (model : Yulang.GeneralSourceState.Assignment),
  Yulang.GeneralNominalCommonBridge.Models state (Yulang.GeneralNominalCommonBridge.lift model) ↔
    Yulang.GeneralSourceState.Models state model
Yulang.GeneralNominalCommonBridge.finite_shadow : ∀ (label : Nat)
  (a b tail : Yulang.CommonNominalFullDemand.Ty Yulang.CommonNominalFullCarrier.Row),
  Yulang.CommonNominalFullDemand.ProducerEq Yulang.Common.rowLe
    (Yulang.CommonNominalFinite.Ty.record label a (Yulang.CommonNominalFinite.Ty.record label b tail))
    (Yulang.CommonNominalFinite.Ty.record label a tail)
Yulang.GeneralNominalCommonBridge.finite_swap : ∀ (first last : Nat),
  first ≠ last →
    ∀ (a b tail : Yulang.CommonNominalFullDemand.Ty Yulang.CommonNominalFullCarrier.Row),
      Yulang.CommonNominalFullDemand.ProducerEq Yulang.Common.rowLe
        (Yulang.CommonNominalFinite.Ty.record first a (Yulang.CommonNominalFinite.Ty.record last b tail))
        (Yulang.CommonNominalFinite.Ty.record last b (Yulang.CommonNominalFinite.Ty.record first a tail))
Yulang.GeneralNominalCommonBridge.shadow : ∀ (label : Nat) (a b tail : Yulang.CommonNominalFullCarrier.Ty),
  Yulang.CommonNominalFullCarrier.Equivalent
    (Yulang.CommonNominalFullCarrier.record label a (Yulang.CommonNominalFullCarrier.record label b tail))
    (Yulang.CommonNominalFullCarrier.record label a tail)
Yulang.GeneralNominalCommonBridge.swap : ∀ (first last : Nat),
  first ≠ last →
    ∀ (a b tail : Yulang.CommonNominalFullCarrier.Ty),
      Yulang.CommonNominalFullCarrier.Equivalent
        (Yulang.CommonNominalFullCarrier.record first a (Yulang.CommonNominalFullCarrier.record last b tail))
        (Yulang.CommonNominalFullCarrier.record last b (Yulang.CommonNominalFullCarrier.record first a tail))
Yulang.GeneralNominalCommonBridge.variant_merge : ∀ (tag : Nat) (a b : Yulang.CommonNominalFullCarrier.Ty),
  Yulang.CommonNominalFullCarrier.Equivalent
    (Yulang.CommonNominalSyntax.Layer.union (Yulang.CommonNominalFullCarrier.variant tag a)
      (Yulang.CommonNominalFullCarrier.variant tag b))
    (Yulang.CommonNominalFullCarrier.variant tag (Yulang.CommonNominalSyntax.Layer.union a b))
@Yulang.GeneralNominalCommonBridge.rewrites_sound : ∀ {state : Yulang.GeneralSourceState.State}
  {first last : Yulang.Core.PresenceGeneration.TyTerm (Fin state.slots)},
  Yulang.GeneralNormalizedObservation.Rewrites state first last →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalCommonBridge.Models state model →
        Yulang.CommonNominalFullCarrier.Equivalent
          (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.CommonNominalFullCarrier.model
            (Yulang.GeneralNominalCommonBridge.assignment state model) first)
          (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.CommonNominalFullCarrier.model
            (Yulang.GeneralNominalCommonBridge.assignment state model) last)
@Yulang.GeneralNominalCommonBridge.observation_models : ∀ {state : Yulang.GeneralSourceState.State}
  (view : Yulang.GeneralNormalizedObservation.Snapshot state) (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalCommonBridge.Models state model → Yulang.GeneralNominalCommonBridge.ObservationModels view model
@Yulang.GeneralNominalCommonBridge.normalization_preserves : ∀ {state : Yulang.GeneralSourceState.State}
  (view : Yulang.GeneralNormalizedObservation.Snapshot state) (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalCommonBridge.Models state model ∧
      Yulang.GeneralNominalCommonBridge.ObservationModels view model ↔
    Yulang.GeneralNominalCommonBridge.Models state model
Yulang.GeneralNominalState.embed_models : ∀ (base : Yulang.GeneralSourceState.State)
  (view : Yulang.GeneralNormalizedObservation.Snapshot base)
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (model : Yulang.GeneralSourceState.Assignment),
  Yulang.GeneralNominalState.Models (Yulang.GeneralNominalState.embed base view constructors)
      (Yulang.GeneralNominalCommonBridge.lift model) ↔
    Yulang.GeneralSourceState.Models base model
Yulang.GeneralNominalState.normalized_models : ∀ (state : Yulang.GeneralNominalState.State)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models state model → Yulang.GeneralNominalCommonBridge.ObservationModels state.view model
Yulang.GeneralNominalState.nominal_models : ∀ (state : Yulang.GeneralNominalState.State)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models state model →
    ∀ (slot : Fin state.base.slots) (descriptor : Yulang.GeneralNominalState.Descriptor state.base.slots),
      state.nominals slot = some descriptor → Yulang.GeneralNominalState.Denotes state.base model slot descriptor
Yulang.GeneralNominalState.atK2_recurrence : ∀ (state : Yulang.GeneralNominalState.State) (slot : Fin state.base.slots),
  Yulang.GeneralNominalState.AtK2 state slot → Yulang.GeneralSourceK2.RecursAt state.view slot
@Yulang.GeneralNominalState.pending_excludes_K2 : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalState.State) (demand : Yulang.GeneralSourceState.Demand roles),
  Yulang.GeneralNominalState.RootPending state demand → ¬Yulang.GeneralNominalState.RootK2 state demand
@Yulang.GeneralNominalState.linked_embed : ∀ {roles : Yulang.Roles.RoleDecls} (base : Yulang.GeneralSourceState.State)
  (view : Yulang.GeneralNormalizedObservation.Snapshot base)
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (demand : Yulang.GeneralSourceState.Demand roles),
  Yulang.GeneralSourceState.Linked base demand →
    Yulang.GeneralNominalState.Linked (Yulang.GeneralNominalState.embed base view constructors) demand
@Yulang.GeneralNominalState.embed_pending : ∀ {roles : Yulang.Roles.RoleDecls} (base : Yulang.GeneralSourceState.State)
  (view : Yulang.GeneralNormalizedObservation.Snapshot base)
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (demand : Yulang.GeneralSourceState.Demand roles),
  Yulang.GeneralNominalState.RootPending (Yulang.GeneralNominalState.embed base view constructors) demand ↔
    Yulang.GeneralSourceK2.RootPending view demand (Yulang.GeneralDeclarationDemands.needed roles demand)
Yulang.GeneralNominalState.embed_K2 : ∀ (base : Yulang.GeneralSourceState.State)
  (view : Yulang.GeneralNormalizedObservation.Snapshot base)
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors) (slot : Fin base.slots),
  Yulang.GeneralNominalState.AtK2 (Yulang.GeneralNominalState.embed base view constructors) slot ↔
    Yulang.GeneralSourceK2.Complete view slot ∧ Yulang.GeneralSourceBoundary.GraphK2 view.graph slot
Yulang.GeneralNominalState.extend_models : ∀ (state : Yulang.GeneralNominalState.State) (reserved : List Nat)
  (atoms : List (Yulang.PresenceNormalForm.Atom Nat)) (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models (Yulang.GeneralNominalState.extend state reserved atoms) model ↔
    Yulang.GeneralNominalState.Models state model ∧
      Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model atoms
@Yulang.GeneralNominalState.extend_pending : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalState.State) (reserved : List Nat) (atoms : List (Yulang.PresenceNormalForm.Atom Nat))
  (demand : Yulang.GeneralSourceState.Demand roles),
  Yulang.GeneralNominalState.RootPending (Yulang.GeneralNominalState.extend state reserved atoms) demand ↔
    Yulang.GeneralNominalState.RootPending state demand
Yulang.GeneralNominalState.fits_existing_endpoint : ∀ (state : Yulang.GeneralSourceState.State)
  (model : Yulang.GeneralNominalCommonBridge.Assignment) (slot : Fin state.slots)
  (value : Yulang.CommonNominalFullCarrier.Ty),
  Yulang.GeneralNominalState.Fits state model (Yulang.GeneralNominalState.Parameter.type (slot, slot)) (Sum.inl value) →
    Yulang.CommonNominalFullCarrier.Equivalent value (model (state.source slot)).fst
Yulang.GeneralNominalState.singleton_nominal_congr : ∀ (name : Nat) (first last : Yulang.CommonNominalFullCarrier.Ty),
  Yulang.CommonNominalFullCarrier.Equivalent first last →
    Yulang.CommonNominalFullCarrier.Equivalent (Yulang.CommonNominalFullCarrier.nominal name [Sum.inl first])
      (Yulang.CommonNominalFullCarrier.nominal name [Sum.inl last])
Yulang.GeneralNominalState.denotes_singleton_exact : ∀ (state : Yulang.GeneralSourceState.State)
  (model : Yulang.GeneralNominalCommonBridge.Assignment) (root endpoint : Fin state.slots)
  (descriptor : Yulang.GeneralNominalState.Descriptor state.slots),
  descriptor.arguments = [Yulang.GeneralNominalState.Parameter.type (endpoint, endpoint)] →
    (Yulang.GeneralNominalState.Denotes state model root descriptor ↔
      Yulang.CommonNominalFullCarrier.Equivalent (model (state.source root)).fst
        (Yulang.CommonNominalFullCarrier.nominal descriptor.declaration.name
          [Sum.inl (model (state.source endpoint)).fst]))
Yulang.GeneralNominalAllocation.member_le_max : ∀ (values : List Nat) (value : Nat),
  value ∈ values → value ≤ List.foldr max 0 values
Yulang.GeneralNominalAllocation.source_initial_fresh : ∀ (state : Yulang.GeneralNominalState.State)
  (registry : Yulang.GeneralDeclarations.Registry) (root : Nat) (key : Yulang.GeneralNominalAllocation.Origin)
  (old : Nat), old ≤ state.seed → Yulang.GeneralNominalAllocation.source state registry root key ≠ old
Yulang.GeneralNominalAllocation.source_fresh : ∀ (state : Yulang.GeneralNominalState.State)
  (registry : Yulang.GeneralDeclarations.Registry) (root : Nat),
  Yulang.GeneralNominalAllocation.Fresh state registry root →
    ∀ (key : Yulang.GeneralNominalAllocation.Origin),
      key ∈ Yulang.GeneralNominalAllocation.keys registry root →
        ¬key ∈ state.allocated →
          ¬Yulang.GeneralNominalAllocation.source state registry root key ∈ Yulang.GeneralNominalState.sources state
Yulang.GeneralNominalAllocation.source_identity : ∀ (state : Yulang.GeneralNominalState.State)
  (registry : Yulang.GeneralDeclarations.Registry) (root : Nat) (first last : Yulang.GeneralNominalAllocation.Origin),
  Yulang.GeneralNominalAllocation.source state registry root first =
      Yulang.GeneralNominalAllocation.source state registry root last ↔
    first = last
Yulang.GeneralNominalAllocation.source_preserved : ∀ (state : Yulang.GeneralNominalState.State)
  (registry : Yulang.GeneralDeclarations.Registry) (root : Nat) (reserved : List Nat)
  (atoms : List (Yulang.PresenceNormalForm.Atom Nat)) (key : Yulang.GeneralNominalAllocation.Origin),
  Yulang.GeneralNominalAllocation.source (Yulang.GeneralNominalState.extend state reserved atoms) registry root key =
    Yulang.GeneralNominalAllocation.source state registry root key
Yulang.GeneralNominalAllocation.distinct_invocations : ∀ (state : Yulang.GeneralNominalState.State)
  (registry : Yulang.GeneralDeclarations.Registry) (first last key purpose owner position : Nat),
  first ≠ last →
    Yulang.GeneralNominalAllocation.source state registry first
        (Yulang.GeneralNominalAllocation.origin first key purpose owner position) ≠
      Yulang.GeneralNominalAllocation.source state registry last
        (Yulang.GeneralNominalAllocation.origin last key purpose owner position)
Yulang.GeneralNominalAllocation.later_fresh : ∀ (state : Yulang.GeneralNominalState.State)
  (registry : Yulang.GeneralDeclarations.Registry) (first next : Nat)
  (old new : Yulang.GeneralNominalAllocation.Origin),
  old ≠ new →
    Yulang.GeneralNominalAllocation.source
        (Yulang.GeneralNominalState.extend state (Yulang.GeneralNominalAllocation.reserved state registry first) [])
        registry next new ≠
      Yulang.GeneralNominalAllocation.source state registry first old
Yulang.GeneralNominalAllocation.source_registry_independent : ∀ (state : Yulang.GeneralNominalState.State)
  (first last : Yulang.GeneralDeclarations.Registry) (invocation : Nat) (key : Yulang.GeneralNominalAllocation.Origin),
  Yulang.GeneralNominalAllocation.source state first invocation key =
    Yulang.GeneralNominalAllocation.source state last invocation key
Yulang.GeneralNominalAllocation.cross_exact : ∀ (bindings : Yulang.GeneralNominalAllocation.Bindings)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
      (Yulang.GeneralNominalAllocation.cross bindings) ↔
    Yulang.GeneralNominalAllocation.Compatible bindings model
Yulang.GeneralNominalAllocation.propagate_models : ∀ (state : Yulang.GeneralNominalState.State)
  (registry : Yulang.GeneralDeclarations.Registry) (root : Nat) (declaration : Yulang.GeneralDeclarations.Declaration)
  (bindings : Yulang.GeneralNominalAllocation.Bindings) (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models (Yulang.GeneralNominalAllocation.propagate state registry root declaration bindings)
      model ↔
    Yulang.GeneralNominalState.Models state model ∧
      Yulang.GeneralNominalAllocation.Compatible bindings model ∧
        Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
          (Yulang.GeneralNominalAllocation.merges state registry root declaration bindings)
Yulang.GeneralNominalAllocation.propagated_source_preserved : ∀ (state : Yulang.GeneralNominalState.State)
  (registry : Yulang.GeneralDeclarations.Registry) (root : Nat) (declaration : Yulang.GeneralDeclarations.Declaration)
  (bindings : Yulang.GeneralNominalAllocation.Bindings) (key : Yulang.GeneralNominalAllocation.Origin),
  Yulang.GeneralNominalAllocation.source
      (Yulang.GeneralNominalAllocation.propagate state registry root declaration bindings) registry root key =
    Yulang.GeneralNominalAllocation.source state registry root key
Yulang.GeneralNominalInspection.inspected_recurrence : ∀ (state : Yulang.GeneralNominalState.State)
  (report : Yulang.GeneralNominalInspection.Report state),
  Yulang.GeneralNominalInspection.NeedsK2 state report →
    ∃ bounds, bounds ∈ report.inspected ∧ Yulang.GeneralSourceK2.RecursAt state.view bounds.fst
Yulang.GeneralNominalInspection.variables_capture_intervals : ∀ (state : Yulang.GeneralNominalState.State)
  (names : List Nat) (bounds : Yulang.GeneralNominalInspection.Bounds state),
  Yulang.GeneralNominalInspection.inspect state (Yulang.GeneralNominalInspection.Query.variables names) bounds =
    { captures := List.map (fun name => (name, bounds)) names }
Yulang.GeneralNominalInspection.unknown_defers : ∀ (state : Yulang.GeneralNominalState.State) (name : Nat)
  (patterns : List Yulang.GeneralNominalInspection.Query) (bounds : Yulang.GeneralNominalInspection.Bounds state),
  state.nominals bounds.fst = none →
    state.view.heads bounds.fst =
        Yulang.GeneralNormalizedObservation.Head.deferred Yulang.GeneralNormalizedObservation.Deferred.unresolved →
      (Yulang.GeneralNominalInspection.inspect state (Yulang.GeneralNominalInspection.Query.nominal name patterns)
            bounds).blocked ≠
        []
Yulang.GeneralNominalInspection.nominal_bodies_opaque : ∀ (state : Yulang.GeneralNominalState.State) (expected : Nat)
  (patterns : List Yulang.GeneralNominalInspection.Query) (slot : Fin state.base.slots)
  (descriptor : Yulang.GeneralNominalState.Descriptor state.base.slots),
  state.nominals slot = some descriptor →
    descriptor.declaration.name = expected →
      ∀ (arguments : List (Yulang.GeneralNominalInspection.Bounds state)),
        Yulang.GeneralNominalInspection.typeArguments descriptor.arguments = some arguments →
          Yulang.GeneralNominalInspection.inspect state
              (Yulang.GeneralNominalInspection.Query.nominal expected patterns) (slot, slot) =
            Yulang.GeneralNominalInspection.Report.visit (slot, slot)
              (Yulang.GeneralNominalInspection.inspectMany state patterns arguments)
@Yulang.GeneralNominalCandidates.survivor_interval_sound : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
  (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
  Yulang.GeneralNominalCandidates.Survivor registry context root key children →
    ∃ declaration,
      declaration ∈ registry.declarations ∧
        declaration.id = key ∧
          ∃ bounds,
            Yulang.GeneralNominalCandidates.arguments context root = some bounds ∧
              ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                Yulang.GeneralNominalState.Models
                    (Yulang.GeneralNominalCandidates.privateState registry context root declaration bounds) model →
                  Yulang.GeneralNominalState.Models context.state model ∧
                    Yulang.GeneralNominalAllocation.Compatible
                      (Yulang.GeneralNominalInspection.bindings context.state
                        (Yulang.GeneralNominalCandidates.report context declaration bounds))
                      model
@Yulang.GeneralNominalCandidates.survivor_children_functional : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry),
  Yulang.GeneralDeclarations.Checked registry →
    ∀ (context : Yulang.GeneralNominalCandidates.Context) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
      (key : Nat) (first last : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
      Yulang.GeneralNominalCandidates.Survivor registry context root key first →
        Yulang.GeneralNominalCandidates.Survivor registry context root key last → first = last
@Yulang.GeneralNominalCandidates.pending_excludes_candidateK2 : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralNominalState.RootPending context.state root.demand →
    ¬Yulang.GeneralNominalCandidates.CandidateK2 registry context root
@Yulang.GeneralNominalCandidates.candidateK2_recurrence : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralNominalCandidates.CandidateK2 registry context root →
    ∃ declaration,
      declaration ∈ registry.declarations ∧
        ∃ bounds,
          Yulang.GeneralNominalCandidates.arguments context root = some bounds ∧
            ∃ visited,
              visited ∈ (Yulang.GeneralNominalCandidates.report context declaration bounds).inspected ∧
                Yulang.GeneralSourceK2.RecursAt context.state.view visited.fst
@Yulang.GeneralNominalCandidates.conservative_deferral : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  ¬Yulang.GeneralNominalState.RootPending context.state root.demand →
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration),
      declaration ∈ registry.declarations →
        ∀ (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration),
          declaration.role = root.demand.role →
            ¬Yulang.GeneralNominalCandidates.Failed registry context root declaration →
              ¬Yulang.GeneralNominalCandidates.Prepared registry context root declaration checked →
                Yulang.GeneralNominalCandidates.InspectionPending registry context root
@Yulang.GeneralNominalCandidates.allocation_collision_defers : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  ¬Yulang.GeneralNominalState.RootPending context.state root.demand →
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration),
      declaration ∈ registry.declarations →
        Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration →
          declaration.role = root.demand.role →
            ¬Yulang.GeneralNominalAllocation.Fresh context.state registry root.identity →
              Yulang.GeneralNominalCandidates.InspectionPending registry context root
@Yulang.GeneralNominalCandidates.coverage_defers : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  ¬Yulang.GeneralNominalState.RootPending context.state root.demand →
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration),
      declaration ∈ registry.declarations →
        Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration →
          declaration.role = root.demand.role →
            ∀ (bounds : List (Yulang.GeneralNominalInspection.Bounds context.state)),
              Yulang.GeneralNominalCandidates.arguments context root = some bounds →
                ¬Yulang.GeneralNominalInspection.Covered context.state
                      (Yulang.GeneralNominalCandidates.report context declaration bounds) →
                  Yulang.GeneralNominalCandidates.InspectionPending registry context root
Yulang.GeneralNominalCandidates.local_total_of_extension : ∀ (roles : Yulang.Roles.RoleDecls)
  (boundary : Yulang.B4Target.SourceBoundary (Yulang.GeneralNominalCandidates.vocabulary roles))
  (registry : Yulang.GeneralDeclarations.Registry),
  Yulang.GeneralDeclarations.Checked registry →
    ∀ (context : Yulang.GeneralNominalCandidates.Context) (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      (∀ (key : Nat) (children : List (Yulang.GeneralNominalCandidates.vocabulary roles).Demand),
          boundary.Survivor registry context root key children ↔
            Yulang.GeneralNominalCandidates.Survivor registry context root key children) →
        ∃ frontier, Yulang.B4TargetV3.Local boundary registry context root frontier
Yulang.GeneralNominalExamples.int_display_checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDeclarationExamples.roles
  Yulang.GeneralNominalExamples.intDisplay
Yulang.GeneralNominalExamples.registry_checked : Yulang.GeneralDeclarations.Checked
  Yulang.GeneralNominalExamples.registry
Yulang.GeneralNominalExamples.state_models : ∀ (known : Bool),
  Yulang.GeneralNominalState.Models (Yulang.GeneralNominalExamples.state known) Yulang.GeneralNominalExamples.model
Yulang.GeneralNominalExamples.display_report : ∀ (known : Bool),
  Yulang.GeneralNominalCandidates.report (Yulang.GeneralNominalExamples.context known)
      Yulang.GeneralDeclarationExamples.display [(0, 0)] =
    { captures := [(0, 1, 1)], inspected := [(0, 0), (0, 0)] }
Yulang.GeneralNominalExamples.wrap_report : ∀ (known : Bool),
  Yulang.GeneralNominalCandidates.report (Yulang.GeneralNominalExamples.context known)
      Yulang.GeneralDeclarationExamples.wrap [(0, 0)] =
    { captures := [(0, 1, 1)], inspected := [(0, 0), (0, 0)] }
Yulang.GeneralNominalExamples.int_report : ∀ (known : Bool),
  Yulang.GeneralNominalCandidates.report (Yulang.GeneralNominalExamples.context known)
      Yulang.GeneralNominalExamples.intDisplay [(0, 0)] =
    { inspected := [(0, 0), (0, 0)], conflicts := [(0, 0)] }
Yulang.GeneralNominalExamples.display_children : Yulang.GeneralNominalAllocation.children
    (Yulang.GeneralNominalExamples.state true) Yulang.GeneralNominalExamples.registry
    Yulang.GeneralNominalExamples.displayRoot Yulang.GeneralDeclarationExamples.display
    Yulang.GeneralDeclarationExamples.display_checked Yulang.GeneralNominalExamples.captured =
  [Yulang.GeneralNominalExamples.displayChild]
Yulang.GeneralNominalExamples.wrap_children : Yulang.GeneralNominalAllocation.children
    (Yulang.GeneralNominalExamples.state true) Yulang.GeneralNominalExamples.registry
    Yulang.GeneralNominalExamples.wrapRoot Yulang.GeneralDeclarationExamples.wrap
    Yulang.GeneralDeclarationExamples.wrap_checked Yulang.GeneralNominalExamples.captured =
  [Yulang.GeneralNominalExamples.wrapChild]
Yulang.GeneralNominalExamples.wrap_item_equation : Yulang.GeneralNominalExamples.wrapChild.demand.outputs =
  [{ name := 1, target := Yulang.GeneralNominalExamples.itemTarget }]
Yulang.GeneralNominalExamples.item_target_fresh : ¬Yulang.GeneralNominalExamples.itemTarget ∈
    Yulang.GeneralNominalState.sources (Yulang.GeneralNominalExamples.state true)
Yulang.GeneralNominalExamples.display_survivor : Yulang.GeneralNominalCandidates.Survivor
  Yulang.GeneralNominalExamples.registry (Yulang.GeneralNominalExamples.context true)
  Yulang.GeneralNominalExamples.displayRoot 1 [Yulang.GeneralNominalExamples.displayChild]
Yulang.GeneralNominalExamples.wrap_survivor : Yulang.GeneralNominalCandidates.Survivor
  Yulang.GeneralNominalExamples.registry (Yulang.GeneralNominalExamples.context true)
  Yulang.GeneralNominalExamples.wrapRoot 2 [Yulang.GeneralNominalExamples.wrapChild]
Yulang.GeneralNominalExamples.display_exactly_one : ∀ (key : Nat)
  (children : List (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)),
  Yulang.GeneralNominalCandidates.Survivor Yulang.GeneralNominalExamples.registry
      (Yulang.GeneralNominalExamples.context true) Yulang.GeneralNominalExamples.displayRoot key children ↔
    key = 1 ∧ children = [Yulang.GeneralNominalExamples.displayChild]
Yulang.GeneralNominalRegressions.index_pending : Yulang.GeneralNominalState.RootPending
  Yulang.GeneralNominalRegressions.indexState' Yulang.GeneralSourceStateExamples.indexDemand
Yulang.GeneralNominalRegressions.index_not_K2 : ¬Yulang.GeneralNominalState.RootK2
    Yulang.GeneralNominalRegressions.indexState' Yulang.GeneralSourceStateExamples.indexDemand
Yulang.GeneralNominalRegressions.index_all_common_assignments : ∀ (key : Yulang.Common.Ty),
  Yulang.GeneralNominalState.Models Yulang.GeneralNominalRegressions.indexState'
    (Yulang.GeneralNominalCommonBridge.lift (Yulang.GeneralSourceStateExamples.indexModel key))
Yulang.GeneralNominalRegressions.shadow_pending : Yulang.GeneralNominalState.RootPending
  Yulang.GeneralNominalRegressions.shadowState' Yulang.GeneralSourceStateExamples.loopDemand
Yulang.GeneralNominalRegressions.shadow_not_K2 : ¬Yulang.GeneralNominalState.RootK2
    Yulang.GeneralNominalRegressions.shadowState' Yulang.GeneralSourceStateExamples.loopDemand
Yulang.GeneralNominalRegressions.loop_K2 : Yulang.GeneralNominalState.RootK2 Yulang.GeneralNominalRegressions.loopState'
  Yulang.GeneralSourceStateExamples.loopDemand
Yulang.GeneralNominalRegressions.loop_model : Yulang.GeneralNominalState.Models
  Yulang.GeneralNominalRegressions.loopState'
  (Yulang.GeneralNominalCommonBridge.lift Yulang.GeneralSourceStateExamples.loopModel)
Yulang.GeneralNominalRegressions.shadow_normalization_full : ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models Yulang.GeneralNominalRegressions.shadowState' model →
    Yulang.GeneralNominalCommonBridge.ObservationModels Yulang.GeneralSourceK2Examples.shadowView model
Yulang.GeneralNominalRegressions.concrete_checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralNominalRegressions.constructors Yulang.GeneralDeclarationExamples.roles
  Yulang.GeneralNominalRegressions.concreteList
Yulang.GeneralNominalRegressions.unresolved_payload_report : Yulang.GeneralNominalCandidates.report
    (Yulang.GeneralNominalExamples.context false) Yulang.GeneralNominalRegressions.concreteList [(0, 0)] =
  { inspected := [(0, 0), (0, 0), (1, 1)], blocked := [(1, 1)] }
Yulang.GeneralNominalRegressions.inspection_pending : Yulang.GeneralNominalCandidates.InspectionPending
  Yulang.GeneralNominalRegressions.concreteRegistry (Yulang.GeneralNominalExamples.context false)
  Yulang.GeneralNominalExamples.displayRoot
@Yulang.GeneralNominalRegressions.different_parameter_endpoints_defer : ∀ {slots : Nat} (first last : Fin slots),
  first ≠ last →
    Yulang.GeneralNominalInspection.typeArguments [Yulang.GeneralNominalState.Parameter.type (first, last)] = none
Yulang.GeneralNominalRegressions.cross_conflict : ¬∃ model,
    Yulang.GeneralNominalState.Models Yulang.GeneralNominalRegressions.conflictState model ∧
      Yulang.GeneralNominalAllocation.Compatible Yulang.GeneralNominalRegressions.conflicting model
Yulang.GeneralNominalRegressions.repeated_captures : Yulang.GeneralNominalInspection.bindings
    Yulang.GeneralNominalRegressions.conflictState
    (Yulang.GeneralNominalCandidates.report Yulang.GeneralNominalRegressions.conflictContext
      Yulang.GeneralCandidateConflictExamples.repeated [(0, 0), (1, 1)]) =
  Yulang.GeneralNominalRegressions.conflicting
Yulang.GeneralNominalRegressions.no_conflict_survivors : ∀ (key : Nat)
  (children : List (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)),
  ¬Yulang.GeneralNominalCandidates.Survivor Yulang.GeneralCandidateConflictExamples.registry
      Yulang.GeneralNominalRegressions.conflictContext Yulang.GeneralCandidateConflictExamples.root key children
```

### Verification and independent review for Item 3b

Final commands, run from `lean/`:

| Exact command | Exit code |
| --- | --- |
| `lake build Yulang.GeneralNominalIdentities Yulang.GeneralNominalCommonBridge Yulang.GeneralNominalState Yulang.GeneralNominalAllocation Yulang.GeneralNominalInspection Yulang.GeneralNominalCandidates Yulang.GeneralNominalExamples Yulang.GeneralNominalRegressions > /tmp/astra-nominal-focused.log 2>&1` | 0 |
| `lake build Yulang > /tmp/astra-nominal-umbrella.log 2>&1` | 0 |
| `lake env lean Audit.lean > /tmp/astra-nominal-audit.log 2>&1` | 0 |
| `lake env lean /tmp/astra-nominal-signatures.lean > /tmp/astra-nominal-signatures.txt 2>&1` | 0 |

The focused build completed 562 jobs and the umbrella build completed 1407 jobs.
The full audit printed 8898 dependency reports, including all 84 new public
theorems exactly once. The complete dependency set was `propext`,
`Classical.choice`, and `Quot.sound`. These counts include older reports and do
not assert 8898 new or independent results.

Append-only byte-prefix checks passed for `Yulang.lean` and `Audit.lean`.
The change adds eight imports and 84 audit entries. New-module token/docstring
checks, theorem-to-signature-to-audit coverage, allowed-path checks, and
`git diff --check` all passed. No existing implementation module, specification,
plan, lake configuration, commit, push, or git reference was changed.
Earlier elaboration failures were corrected in the new files. The first
signature harness used an unavailable pretty-printer option; removing the
option produced the recorded exit-0 inventory. Earlier failures are not counted
as successful final checks.

The `yulang-proofs` workflow was applied. No registered `prover` role or launch
configuration was available, so the primary constructed these bounded results;
no prover agent ran. A separate read-only reviewer checked all eight modules,
the final examples, table, quantifiers, and the 84-statement inventory. Review
exposed and led to corrections for origin persistence, same-snapshot invocation
collisions, free-source support, broad descriptor precision, collision-induced
false rejection, and explicit nominal recurrence/alias coverage. The final
review found no blocking defect in the stated **partial** claims. Its independent
restriction/inventory and whitespace checks exited 0. The reviewer did not
independently rerun the final Lean builds or complete audit.

Not verified: a complete source generator; arbitrary full-carrier equivalence
between ordinary atoms alone and recorded graph equations; general non-point
nominal applicability; general model-extension/completeness of candidate
propagation; mixed nominal K2 classification; all layout/variance/alias cases;
compound child or root associated RHS materialization; source Step/stability;
equal-input demand merging; evidence soundness for the new full state; or a
concrete complete B4/V3 boundary, executor, or unconditional bridge. No parser,
runtime, or frontend execution claim is made by this increment.


## Item 3c — interval sharing, K2 coverage, and the local boundary (2026-11-12)

**Status: Item 3c is not complete.** This increment proves full-carrier interval
laws, source projection uniqueness, finite ordinary propagation for extracted
captures, and retention of child provenance. It does **not** yet connect those
captures to the general recursive pattern inspector or replace the existing
`GeneralNominalCandidates.Survivor`. In particular, the old
`different_parameter_endpoints_defer` regression is still true of that inspector.
Calling the new algebra a completed non-point Survivor would be incorrect.

All seven new modules are additive. The existing cycle-127 recipe,
`EmissionsReady`, frame, child-demand, dictionary, and candidate interfaces are
unchanged. This increment neither implements nor constrains the later Step
rule that merges equal-input demands.

### What the interval proofs establish

`GeneralNominalIntervalLaws` uses **the same**
`CommonNominalFullCarrier.Ty`, `Subtype`, and `GeneralNominalState.Models` as
Item 3b. It does not encode nominal names as records or introduce a second
semantic carrier. The central rules are spec §6.4's centreless interval rules:
self checks, both cross checks, union of lowers, intersection of uppers, and
recursive ordinary subtyping of endpoints. `merge_holds` and
`merge_consistent` are exact on arbitrary full-carrier endpoints; they do not
require point bounds, scalar endpoints, or bounded nesting depth.

`checks` emits `tyLe` for type parameters and `rowLe` for row parameters, keeping
all four original/cross comparisons. `checks_exact` proves the meaning of the
actual generated atoms. `nominal_endpoint_checks` obtains argument sharing
from **actual nominal endpoint subtyping**, using
`CommonNominalFullCarrier.nominal_regular_invariant_exact`. It does not infer
sharing merely because two intervals overlap. `nominal_subtype_equivalent`
and `nominal_sandwich` prove that a value between comparable invariant nominal
endpoints is equivalent to those endpoints. `pair_interval` and
`variant_interval` prove component laws when the actual value has the stated
constructor; they do not claim a general factorization theorem for arbitrary
values bounded by structural constructors.

These nominal theorems apply to the full carrier's invariant nominal operation.
They do not supply general declaration variance metadata, reinterpret a
covariant `box` at top level as invariant, or prove the entire catalogue has
that interpretation. Spec §6.4 permits invariant treatment inside an invariant
argument; installing that interpretation recursively remains a source compiler
obligation.

The decisive provenance condition is represented by
`GeneralNominalProjections.Ref`: a source identity followed by resolved nominal
argument positions. `Observes` decomposes the denotation of that source in a
given existing model. It adds no fresh type variable, selected midpoint, or
substitution enumeration. Model witnesses are constructor observations, and
`observation_unique` proves they are unique up to the carrier's argument
equivalence. Rows use row equality. `Compatible` requires both interval
membership and equality of actual observations for a repeated binder.

`GeneralNominalProjections.Models` is an explicit **restriction** of the original
shared Models by those conditions. `models_source`, `models_normalized`, and
`empty_extension` give the exact preservation statements. There is no claim
that adding a conflicting candidate's equalities conserves every source model.
`GeneralNominalProjectionPropagation.compile` is a finite source-driven
compiler for all same-name self/cross pairs, including rows. `propagation_exact`
proves that appending its ordinary atoms preserves exactly the models already
satisfying the projection conditions; projection equalities are retained.

`extract` accepts arbitrary endpoint pairs and ordered type/row parameters for
variable argument patterns. `extract_valid` covers arbitrary arity, offset,
and name lists, using the actual checked descriptor and its model. This is not
a recursive constructor-pattern compiler. The new example has descriptor
bounds `(source 2, source 3)` with denotations `(bottom, top)`, so the endpoints
have distinct identities **and** distinct denotations. Both `list int` and
`list str` satisfy the one-capture model. Extraction and ordinary propagation
are proved; general Survivor classification is not.

The conflict regression uses two actual nominal occurrences, `list int` and
`list str`, both described by the same coarse `(bottom, top)` bounds. Every
ordinary self/cross check passes (`coarse_checks_pass`), but sharing their
captured binder is impossible (`coarse_actual_conflict`). This is a concrete
reason that removing the old endpoint-identity guard without adding provenance
would be unsound.

### Emission and future equal-input merging

`GeneralNominalEmissionOrigins` adds a sidecar to the **existing** emissions.
An entry retains allocated child occurrence, unnamed argument position,
endpoint pair, and nominal observation path. Its key is not an endpoint pair:
two actual inputs can share a coarse pair without denoting the same thing.
The occurrence identity uses the same invocation/declaration/clause allocation
as `GeneralNominalAllocation`, and is independent of registry order.
`annotation_erases` preserves the complete original emission, including every
named associated equation.

`emitted_input_origin` proves syntactic retention for a variable where input.
`origin_has_observation` proves existence of its model observation, but by itself
does **not** connect an arbitrary supplied Capture's endpoints to that value.
The additional `single_capture_child_bounds` uses the actual computed singleton
capture/allocation and proves the projected actual lies in the emitted child's
interval. Repeated captures still need a theorem connecting the computed
union/intersection endpoints to all originating actuals. Compound input/RHS
materialization and a deterministic producer of this sidecar for every
inspection result remain open. This distinction matters even before item 4.

### K2 and conservative deferral

Spec §6.3's K2 decisions reject a reached anonymous recursive structural head,
or inspection of such a constructor by a nonvariable head pattern. Named
bodies remain opaque; merely capturing a deep recursive argument does not
inspect it. Draft addenda 1 and 3 require the root-pending gate, and V3 gives
both K2 reasons priority over inspection pending.

`GeneralNominalK2Coverage.AtK2` adds a direct normalized structural cycle to the
previous complete-cone K2 relation. A known cycle does not need an unrelated
unknown descendant to resolve. `direct_cycle_with_unresolved_descendant`
expresses precisely that change; `atK2_recurrence` proves soundness against the
already documented independent `GeneralSourceK2.RecursAt`. On a closed normalized
view, `atK2_exact_closed` gives equivalence. This remains a source-observation
characterization, not a theorem about all equivalent full-carrier presentations
or the absence of a finite denotation.

The new RootK2 preserves Linked and not-RootPending. Existing loop, shadow, and
Index regressions are re-proved against it. The new CandidateK2 removes the old
whole-cone Covered premise while retaining successful pattern inspection and
consistent propagated intervals. Thus direct K2 can be known despite an
unrelated unresolved cone. A blocker **within the same candidate's actual
inspection** still prevents Finished; no completeness claim is made for that
case. Old CandidateK2 implies the new CandidateK2.

`ExplicitCycle` follows normalized structural edges and explicit **point**
nominal parameter edges, never a nominal body. Non-point interval endpoints
are not actual argument edges: following an upper endpoint as if it were an
actual could manufacture a cycle. `MixedUnknown` retains explicit cycles not
covered by AtK2. `nominal_cycle_not_supported` and `nominal_cycle_defers` show
that an inspected nominal explicit cycle blocks applicability and remains
inspection pending, rather than becoming an empty-candidate rejection.
This is deliberate deferral, not a completed mixed-cycle K2 classification.

### Layout and normalization coverage

| Case | Current support and remaining limit |
| --- | --- |
| Invariant type intervals | Full-carrier laws, actual projection sharing, arbitrary non-point variable-argument extraction, and ordinary propagation are proved. Recursive pattern inspection and Survivor integration remain missing. |
| Row intervals | Four `rowLe` checks and their meaning, actual row projection equality, and variable-argument extraction are proved. Existing declaration-to-query translation and where-input capture still lack a row-kind bridge, so source applicability defers. |
| Catalogue `lower` / `upper` entries | Existing `GeneralNominalState.Parameter` has only type and row cases. There is no faithful adapter for these entries, including their layout/variance meaning. `unsupported_layout_deferred` proves current translation keeps them deferred. No interpretation is invented. |
| Other variance layouts | Full declaration variance results exist separately, but are not connected to this source catalogue/inspector. Current `Interpretation` remains explicit; missing metadata does not justify rejection. |
| Same-head nested constructors | Nominal sandwich and pair/variant interval laws are available. A recursive source inspection compiler that retains actual origins through structural positions is still missing. |
| Arrow rows, open records, unresolved aliases | Existing conservative normalized observation limits remain. New interval algebra does not silently resolve these cases. |
| Mixed structural/nominal recurrence | Explicit point-argument cycles are recognized as unsupported observations and deferred; general non-point actual recurrence needs the projection-to-observation bridge and the owner answer below. |

`blocked_defers` and `unsupported_layout_deferred` make the conservative policy
explicit. Some blockers are missing implementation/normalization support, not
genuinely unresolved language heads. Therefore InspectionPending here is still
a conservative partial source definition and must not be called the completed
specification-level predicate.

### The thirteen fields and four remaining record slots

All definitions below are independent of an executor. No fragment-specific
classifier replaces a general field.

| SourceBoundary field | Status and Lean definition | Faithfulness / remaining obligation |
| --- | --- | --- |
| Checked | DEFINED: `GeneralNominalLocalBoundary.generalFields.Checked`, using `GeneralDeclarations.Checked` plus registry-role equality | §6.3 declaration checks and the output-only owner rule; unchanged. |
| Models | DEFINED: `GeneralNominalState.Models` in `generalFields`; optional projection extension `GeneralNominalProjections.Models` | Same full carrier and shared ordinary/normalized state. The projection extension is not yet installed in the candidate state flow. |
| Step | MISSING | General source propagation, regeneration, same-input merge, and projection provenance persistence are not implemented. |
| Stable | MISSING | Requires the actual complete saturation/progress relation and stable end-of-file handling. |
| Generated | MISSING | Requires general source materialization/closure for all child demands and their provenance. The sidecar is only a proved subpart. |
| RootPending | DEFINED: `GeneralNominalState.RootPending` | Every unnamed lower head is needed (addenda 3–4); named outputs are excluded. Existing normalization deferral remains visible. |
| RootK2 | PARTIAL: `GeneralNominalK2Coverage.RootK2` | Direct normalized structural recurrence plus previous complete alias recurrence; pending gate preserved. Mixed/unsupported normalized observations defer. |
| CandidateK2 | PARTIAL: `GeneralNominalK2Coverage.CandidateK2` | Stronger direct-cycle coverage; old pattern inspection and Finished/Consistent premises remain. General non-point/mixed inspection is not connected. |
| InspectionPending | PARTIAL: `GeneralNominalCandidates.InspectionPending` | Lossless conservative deferral, still including implementation coverage gaps. Not restricted to genuinely unknown heads yet. |
| Survivor | PARTIAL: `GeneralNominalCandidates.Survivor` | Existing point-nominal/general-carrier candidate predicate is unchanged. Projection-aware recursive capture and general materialization remain missing. No non-point Survivor theorem is claimed. |
| Evidence | MISSING | Cycle-127 source recipes are preserved; no full projection-state/all-layout evidence equivalence is installed. |
| Reorders | DEFINED: `GeneralRegistryReordering.Reorders` | Actual visible-declaration and where-clause reorder relation, retaining identities. |
| DictionaryEquivalent | DEFINED: `GeneralDictionaryPayloadOrder.Equivalent` | Existing dictionary observation relation. Its full source evidence bridge remains an Evidence obligation. |

`GeneralNominalLocalBoundary.Fields` packages these nine available record slots.
Four of the nine still have the explicit partial status above. `Remaining`
contains exactly Step, Stable, Generated, and Evidence, with their original
SourceBoundary types. `complete fields remaining` assembles a SourceBoundary
**only from supplied remaining fields**; it asserts neither their faithfulness
nor any B4 obligation. No closed `generalBoundary` or executor is introduced.
Vocabulary remains `GeneralNominalCandidates.vocabulary`: general Registry,
Context with shared nominal state, source Occurrence demands, and full-carrier
assignments. This package does not change cycle-127's interfaces.

### Local functionality and totality

The raw Survivor, InspectionPending, and CandidateK2 predicates are not
pairwise exclusive: different alternatives may survive, block, or require K2
at once, and K2 can also accompany a surviving alternative. Proving pairwise
exclusivity would contradict V3's priority rules. The new package instead proves:

- root pending excludes all three predicates and RootK2;
- a candidate cannot be both Failed and Prepared;
- a visible checked candidate is Failed, Prepared, or contributes inspection
  pending (classically);
- guarded Local outcomes are functional;
- Local is total when survivor children are functional, with either explicit
  decision instances (`local_total_decidable`) or classical reasoning;
- the concrete checked registry supplies survivor-child functionality and
  hence classical local totality (`general_local_total`);
- `local_extension` identifies this local relation exactly with V3.Local for
  any supplied four-field completion.

None of these statements supplies decidability for full-carrier consistency,
a runnable executor, source inspection completeness, where-tree accessibility,
Step stabilization, or B4 exactness. Local totality of conservative predicates
can return pending because an implementation bridge is absent. It is not a
proof that language-level applicability is complete.

### Open owner question: mixed explicit recurrence (lazy option first)

The question was presented during this task; no answer has been incorporated.
The existing decisions clearly distinguish deep anonymous recurrence from
reaching its structural head, and exempt named bodies. They do not explicitly
say whether an explicit cycle that passes through nominal **arguments** makes
the nominal-headed node itself a K2 root.

For example, consider an inferred anonymous type `μ = {next: list μ}`:

```yulang
impl Len (list 'a)       // no where child
impl Show (list 'a) where Show 'a
// A value r has the inferred anonymous type μ = {next: list μ}.
len [r]
show [r]
```

1. **Lazy / opaque nominal head:** `Len (list μ)` may pass without inspecting
   μ. Reject when a reached anonymous structural recursive head (or a demanded
   nonvariable inspection of it) is established, including whether μ's cycle
   through its explicit list argument qualifies. Named bodies stay opaque.
2. Treat every reached node on an explicit argument cycle, including a nominal
   root such as `list μ`, as recursive for K2 and reject there.

No choice is installed here. Mixed observations outside the proved normalized
structural relation stay unknown/pending. This question is not permission to
unfold a nominal body. A future answer also needs a checked source projection
observation bridge; arbitrary bounds cannot serve as actual recurrence edges.

### Assessment and remaining work

The work is converging at the shared-state/model interface: the interval and
projection theorems use the actual nominal carrier, prove ordinary constraint
meaning, expose a concrete false-positive capture, and preserve the real child
emission interface. The old fragment-only classifiers do not discharge the
missing source compiler merely by building. In particular, the unchanged
point-only inspector theorem is direct evidence that Item 3 is still open.

The next implementation must carry projection origins and all contributing
intervals through finite pattern recursion, retain them through capture merges
and child emission, and connect that result to candidate-private Models and
Survivor. It also needs kind-aware row captures, catalogue lower/upper/variance
interpretation, full compound input/associated RHS materialization, and the
mixed-recurrence decision. These are source-generation and correctness
obligations, not assumptions to hide in a Checked or successful-result field.

No complete general non-point Survivor, unrestricted local applicability
coverage, general model-extension theorem, mixed-cycle K2 characterization,
all-layout/variance/alias normalization, repeated-capture child provenance
correspondence, Step/stability/equal-input merging, full source Evidence, B4
bridge, or executor was verified. No parser, frontend, or runtime test was run.

### Full public theorem statements for Item 3c

The following is Lean's `#check @...` output for all 76 new public theorems,
including implicit parameters. Private proof helpers are covered transitively
by the dependency audit. No proof precondition has been removed from this list.

```lean
Yulang.GeneralNominalIntervalLaws.merge_holds : ∀ (first last : Yulang.GeneralNominalIntervalLaws.Bounds)
  (value : Yulang.CommonNominalFullCarrier.Ty),
  Yulang.GeneralNominalIntervalLaws.Holds (Yulang.GeneralNominalIntervalLaws.merge first last) value ↔
    Yulang.GeneralNominalIntervalLaws.Holds first value ∧ Yulang.GeneralNominalIntervalLaws.Holds last value
Yulang.GeneralNominalIntervalLaws.merge_consistent : ∀ (first last : Yulang.GeneralNominalIntervalLaws.Bounds),
  Yulang.CommonNominalFullCarrier.Subtype (Yulang.GeneralNominalIntervalLaws.merge first last).fst
      (Yulang.GeneralNominalIntervalLaws.merge first last).snd ↔
    Yulang.GeneralNominalIntervalLaws.Checks first last
Yulang.GeneralNominalIntervalLaws.shared_value_checks : ∀ (first last : Yulang.GeneralNominalIntervalLaws.Bounds)
  (value : Yulang.CommonNominalFullCarrier.Ty),
  Yulang.GeneralNominalIntervalLaws.Holds first value →
    Yulang.GeneralNominalIntervalLaws.Holds last value → Yulang.GeneralNominalIntervalLaws.Checks first last
Yulang.GeneralNominalIntervalLaws.checks_exact : ∀ (state : Yulang.GeneralSourceState.State)
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (first last : Yulang.GeneralNominalState.Parameter state.slots),
  (∃ atoms,
      Yulang.GeneralNominalIntervalLaws.checks state first last = Option.some atoms ∧
        Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model atoms) ↔
    Yulang.GeneralNominalIntervalLaws.ParameterChecks state model first last
Yulang.GeneralNominalIntervalLaws.fits_equivalent : ∀ (state : Yulang.GeneralSourceState.State)
  (model : Yulang.GeneralNominalCommonBridge.Assignment) (bounds : Yulang.GeneralNominalState.Parameter state.slots)
  (first last : Yulang.CommonNominalFullCarrier.Argument),
  Yulang.CommonNominalFullCarrier.ArgumentEquivalent first last →
    (Yulang.GeneralNominalState.Fits state model bounds first ↔ Yulang.GeneralNominalState.Fits state model bounds last)
Yulang.GeneralNominalIntervalLaws.fits_checks : ∀ (state : Yulang.GeneralSourceState.State)
  (model : Yulang.GeneralNominalCommonBridge.Assignment) (first last : Yulang.GeneralNominalState.Parameter state.slots)
  (value : Yulang.CommonNominalFullCarrier.Argument),
  Yulang.GeneralNominalState.Fits state model first value →
    Yulang.GeneralNominalState.Fits state model last value →
      Yulang.GeneralNominalIntervalLaws.ParameterChecks state model first last
Yulang.GeneralNominalIntervalLaws.fitsAll_at : ∀ (state : Yulang.GeneralSourceState.State)
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (bounds : List (Yulang.GeneralNominalState.Parameter state.slots))
  (values : List Yulang.CommonNominalFullCarrier.Argument),
  Yulang.GeneralNominalState.FitsAll state model bounds values →
    ∀ (index : Nat) (parameter : Yulang.GeneralNominalState.Parameter state.slots),
      bounds[index]? = Option.some parameter →
        ∃ value, values[index]? = Option.some value ∧ Yulang.GeneralNominalState.Fits state model parameter value
Yulang.GeneralNominalIntervalLaws.nominal_endpoint_checks : ∀ (state : Yulang.GeneralNominalState.State)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models state model →
    ∀ (lower upper : Fin state.base.slots) (left right : Yulang.GeneralNominalState.Descriptor state.base.slots),
      state.nominals lower = Option.some left →
        state.nominals upper = Option.some right →
          Yulang.CommonNominalFullCarrier.Subtype (model (state.base.source lower)).fst
              (model (state.base.source upper)).fst →
            left.declaration.name = right.declaration.name ∧
              ∀ (index : Nat) (a b : Yulang.GeneralNominalState.Parameter state.base.slots),
                left.arguments[index]? = Option.some a →
                  right.arguments[index]? = Option.some b →
                    Yulang.GeneralNominalIntervalLaws.ParameterChecks state.base model a b
Yulang.GeneralNominalIntervalLaws.nominal_subtype_equivalent : ∀ (name other : Nat)
  (first last : List Yulang.CommonNominalFullCarrier.Argument),
  Yulang.CommonNominalFullCarrier.Subtype (Yulang.CommonNominalFullCarrier.nominal name first)
      (Yulang.CommonNominalFullCarrier.nominal other last) →
    Yulang.CommonNominalFullCarrier.Equivalent (Yulang.CommonNominalFullCarrier.nominal name first)
      (Yulang.CommonNominalFullCarrier.nominal other last)
Yulang.GeneralNominalIntervalLaws.nominal_sandwich : ∀ (name other : Nat)
  (first last : List Yulang.CommonNominalFullCarrier.Argument) (value : Yulang.CommonNominalFullCarrier.Ty),
  Yulang.CommonNominalFullCarrier.Subtype (Yulang.CommonNominalFullCarrier.nominal name first) value →
    Yulang.CommonNominalFullCarrier.Subtype value (Yulang.CommonNominalFullCarrier.nominal other last) →
      Yulang.CommonNominalFullCarrier.Equivalent value (Yulang.CommonNominalFullCarrier.nominal name first) ∧
        Yulang.CommonNominalFullCarrier.Equivalent value (Yulang.CommonNominalFullCarrier.nominal other last)
Yulang.GeneralNominalIntervalLaws.pair_interval : ∀ (first last : Yulang.GeneralNominalIntervalLaws.Bounds)
  (a b : Yulang.CommonNominalFullCarrier.Ty),
  Yulang.GeneralNominalIntervalLaws.Holds
      (Yulang.CommonNominalFullCarrier.pair first.fst last.fst, Yulang.CommonNominalFullCarrier.pair first.snd last.snd)
      (Yulang.CommonNominalFullCarrier.pair a b) ↔
    Yulang.GeneralNominalIntervalLaws.Holds first a ∧ Yulang.GeneralNominalIntervalLaws.Holds last b
Yulang.GeneralNominalIntervalLaws.variant_interval : ∀ (tag : Nat) (bounds : Yulang.GeneralNominalIntervalLaws.Bounds)
  (value : Yulang.CommonNominalFullCarrier.Ty),
  Yulang.GeneralNominalIntervalLaws.Holds
      (Yulang.CommonNominalFullCarrier.variant tag bounds.fst, Yulang.CommonNominalFullCarrier.variant tag bounds.snd)
      (Yulang.CommonNominalFullCarrier.variant tag value) ↔
    Yulang.GeneralNominalIntervalLaws.Holds bounds value
Yulang.GeneralNominalProjections.observation_unique : ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (ref : Yulang.GeneralNominalProjections.Ref) (first last : Yulang.CommonNominalFullCarrier.Argument),
  Yulang.GeneralNominalProjections.Observes model ref first →
    Yulang.GeneralNominalProjections.Observes model ref last →
      Yulang.CommonNominalFullCarrier.ArgumentEquivalent first last
Yulang.GeneralNominalProjections.equal_all_observations : ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (first last : Yulang.GeneralNominalProjections.Ref),
  Yulang.GeneralNominalProjections.Equal model first last →
    ∀ (a b : Yulang.CommonNominalFullCarrier.Argument),
      Yulang.GeneralNominalProjections.Observes model first a →
        Yulang.GeneralNominalProjections.Observes model last b → Yulang.CommonNominalFullCarrier.ArgumentEquivalent a b
Yulang.GeneralNominalProjections.compatible_cross : ∀ (state : Yulang.GeneralNominalState.State)
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (bindings : List (Yulang.GeneralNominalProjections.Binding state)),
  Yulang.GeneralNominalProjections.Compatible state model bindings →
    ∀ (first last : Yulang.GeneralNominalProjections.Binding state),
      first ∈ bindings →
        last ∈ bindings →
          first.name = last.name →
            Yulang.GeneralNominalIntervalLaws.ParameterChecks state.base model first.bounds last.bounds
Yulang.GeneralNominalProjections.parameter_binding_valid : ∀ (state : Yulang.GeneralNominalState.State)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models state model →
    ∀ (slot : Fin state.base.slots) (descriptor : Yulang.GeneralNominalState.Descriptor state.base.slots),
      state.nominals slot = Option.some descriptor →
        ∀ (index name : Nat) (bounds : Yulang.GeneralNominalState.Parameter state.base.slots),
          descriptor.arguments[index]? = Option.some bounds →
            Yulang.GeneralNominalProjections.Binding.Valid state model
              (Yulang.GeneralNominalProjections.parameterBinding state slot descriptor index name bounds)
Yulang.GeneralNominalProjections.models_source : ∀ (state : Yulang.GeneralNominalProjections.State)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalProjections.Models state model → Yulang.GeneralNominalState.Models state.source model
Yulang.GeneralNominalProjections.models_normalized : ∀ (state : Yulang.GeneralNominalProjections.State)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalProjections.Models state model →
    Yulang.GeneralNominalCommonBridge.ObservationModels state.source.view model
Yulang.GeneralNominalProjections.models_cross : ∀ (state : Yulang.GeneralNominalProjections.State)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalProjections.Models state model →
    ∀ (first last : Yulang.GeneralNominalProjections.Binding state.source),
      first ∈ state.bindings →
        last ∈ state.bindings →
          first.name = last.name →
            Yulang.GeneralNominalIntervalLaws.ParameterChecks state.source.base model first.bounds last.bounds
Yulang.GeneralNominalProjections.empty_extension : ∀ (source : Yulang.GeneralNominalState.State)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalProjections.Models { source := source, bindings := [] } model ↔
    Yulang.GeneralNominalState.Models source model
Yulang.GeneralNominalProjections.incompatible_occurrences_excluded : ∀ (state : Yulang.GeneralNominalProjections.State)
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (first last : Yulang.GeneralNominalProjections.Binding state.source),
  first ∈ state.bindings →
    last ∈ state.bindings →
      first.name = last.name →
        ∀ (a b : Yulang.CommonNominalFullCarrier.Argument),
          Yulang.GeneralNominalProjections.Observes model first.origin a →
            Yulang.GeneralNominalProjections.Observes model last.origin b →
              ¬Yulang.CommonNominalFullCarrier.ArgumentEquivalent a b →
                ¬Yulang.GeneralNominalProjections.Models state model
@Yulang.GeneralNominalProjectionPropagation.mem_pairs : ∀ {state : Yulang.GeneralNominalState.State}
  (bindings : List (Yulang.GeneralNominalProjections.Binding state))
  (first last : Yulang.GeneralNominalProjections.Binding state),
  (first, last) ∈ Yulang.GeneralNominalProjectionPropagation.pairs bindings ↔
    first ∈ bindings ∧ last ∈ bindings ∧ first.name = last.name
Yulang.GeneralNominalProjectionPropagation.compilePairs_exact : ∀ (state : Yulang.GeneralNominalState.State)
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (items : List (Yulang.GeneralNominalProjections.Binding state × Yulang.GeneralNominalProjections.Binding state)),
  (∃ atoms,
      Yulang.GeneralNominalProjectionPropagation.compilePairs state items = Option.some atoms ∧
        Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model atoms) ↔
    ∀ (pair : Yulang.GeneralNominalProjections.Binding state × Yulang.GeneralNominalProjections.Binding state),
      pair ∈ items → Yulang.GeneralNominalIntervalLaws.ParameterChecks state.base model pair.fst.bounds pair.snd.bounds
Yulang.GeneralNominalProjectionPropagation.compile_exact : ∀ (state : Yulang.GeneralNominalState.State)
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (bindings : List (Yulang.GeneralNominalProjections.Binding state)),
  (∃ atoms,
      Yulang.GeneralNominalProjectionPropagation.compile state bindings = Option.some atoms ∧
        Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model atoms) ↔
    ∀ (first : Yulang.GeneralNominalProjections.Binding state),
      first ∈ bindings →
        ∀ (last : Yulang.GeneralNominalProjections.Binding state),
          last ∈ bindings →
            first.name = last.name →
              Yulang.GeneralNominalIntervalLaws.ParameterChecks state.base model first.bounds last.bounds
Yulang.GeneralNominalProjectionPropagation.compile_sound : ∀ (state : Yulang.GeneralNominalState.State)
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (bindings : List (Yulang.GeneralNominalProjections.Binding state)),
  Yulang.GeneralNominalProjections.Compatible state model bindings →
    ∃ atoms,
      Yulang.GeneralNominalProjectionPropagation.compile state bindings = Option.some atoms ∧
        Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model atoms
Yulang.GeneralNominalProjectionPropagation.propagation_exact : ∀ (state : Yulang.GeneralNominalState.State)
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (bindings : List (Yulang.GeneralNominalProjections.Binding state))
  (atoms : List (Yulang.PresenceNormalForm.Atom Nat)),
  Yulang.GeneralNominalProjectionPropagation.compile state bindings = Option.some atoms →
    (Yulang.GeneralNominalState.Models (Yulang.GeneralNominalState.extend state [] atoms) model ∧
        Yulang.GeneralNominalProjections.Compatible state model bindings ↔
      Yulang.GeneralNominalProjections.Models { source := state, bindings := bindings } model)
Yulang.GeneralNominalProjectionPropagation.extract_one : ∀ (state : Yulang.GeneralNominalState.State)
  (slot : Fin state.base.slots) (descriptor : Yulang.GeneralNominalState.Descriptor state.base.slots) (name : Nat)
  (bounds : Yulang.GeneralNominalState.Parameter state.base.slots),
  Yulang.GeneralNominalProjectionPropagation.extract state slot descriptor 0 [[name]] [bounds] =
    Option.some [Yulang.GeneralNominalProjections.parameterBinding state slot descriptor 0 name bounds]
Yulang.GeneralNominalProjectionPropagation.extract_valid : ∀ (state : Yulang.GeneralNominalState.State)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models state model →
    ∀ (slot : Fin state.base.slots) (descriptor : Yulang.GeneralNominalState.Descriptor state.base.slots),
      state.nominals slot = Option.some descriptor →
        ∀ (offset : Nat) (names : List (List Nat))
          (parameters : List (Yulang.GeneralNominalState.Parameter state.base.slots)),
          (∀ (index : Nat) (parameter : Yulang.GeneralNominalState.Parameter state.base.slots),
              parameters[index]? = Option.some parameter →
                descriptor.arguments[offset + index]? = Option.some parameter) →
            ∀ (bindings : List (Yulang.GeneralNominalProjections.Binding state)),
              Yulang.GeneralNominalProjectionPropagation.extract state slot descriptor offset names parameters =
                  Option.some bindings →
                ∀ (binding : Yulang.GeneralNominalProjections.Binding state),
                  binding ∈ bindings → Yulang.GeneralNominalProjections.Binding.Valid state model binding
Yulang.GeneralNominalProjectionPropagation.single_capture_compatible : ∀ (state : Yulang.GeneralNominalState.State)
  (model : Yulang.GeneralNominalCommonBridge.Assignment) (binding : Yulang.GeneralNominalProjections.Binding state),
  Yulang.GeneralNominalProjections.Binding.Valid state model binding →
    Yulang.GeneralNominalProjections.Compatible state model [binding]
Yulang.GeneralNominalK2Coverage.old_atK2 : ∀ (state : Yulang.GeneralNominalState.State) (slot : Fin state.base.slots),
  Yulang.GeneralNominalState.AtK2 state slot → Yulang.GeneralNominalK2Coverage.AtK2 state slot
@Yulang.GeneralNominalK2Coverage.old_rootK2 : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalState.State) (demand : Yulang.GeneralSourceState.Demand roles),
  Yulang.GeneralNominalState.RootK2 state demand → Yulang.GeneralNominalK2Coverage.RootK2 state demand
Yulang.GeneralNominalK2Coverage.atK2_recurrence : ∀ (state : Yulang.GeneralNominalState.State)
  (slot : Fin state.base.slots),
  Yulang.GeneralNominalK2Coverage.AtK2 state slot → Yulang.GeneralSourceK2.RecursAt state.view slot
@Yulang.GeneralNominalK2Coverage.pending_excludes_K2 : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalState.State) (demand : Yulang.GeneralSourceState.Demand roles),
  Yulang.GeneralNominalState.RootPending state demand → ¬Yulang.GeneralNominalK2Coverage.RootK2 state demand
@Yulang.GeneralNominalK2Coverage.direct_cycle_rejects : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalState.State) (demand : Yulang.GeneralSourceState.Demand roles),
  Yulang.GeneralNominalState.Linked state demand →
    ¬Yulang.GeneralNominalState.RootPending state demand →
      ∀ (index : Fin (roles demand.role).arity) (slot : Fin state.base.slots),
        state.base.source slot = (demand.arguments index).fst →
          Yulang.GeneralSourceK2.Cycle state.view slot → Yulang.GeneralNominalK2Coverage.RootK2 state demand
Yulang.GeneralNominalK2Coverage.direct_cycle_with_unresolved_descendant : ∀ (state : Yulang.GeneralNominalState.State)
  (root child : Fin state.base.slots),
  Yulang.GeneralSourceK2.Cycle state.view root →
    Yulang.GeneralSourceK2.Path state.view root child →
      state.view.graph child = Yulang.CommonRoleRegularGraph.Node.unresolved →
        Yulang.GeneralNominalK2Coverage.AtK2 state root ∧ ¬Yulang.GeneralSourceK2.Complete state.view root
Yulang.GeneralNominalK2Coverage.mixed_unknown_not_K2 : ∀ (state : Yulang.GeneralNominalState.State)
  (root : Fin state.base.slots),
  Yulang.GeneralNominalK2Coverage.MixedUnknown state root → ¬Yulang.GeneralNominalK2Coverage.AtK2 state root
Yulang.GeneralNominalK2Coverage.nominal_not_atK2 : ∀ (state : Yulang.GeneralNominalState.State)
  (root : Fin state.base.slots) (descriptor : Yulang.GeneralNominalState.Descriptor state.base.slots),
  state.nominals root = Option.some descriptor → ¬Yulang.GeneralNominalK2Coverage.AtK2 state root
Yulang.GeneralNominalK2Coverage.nominal_cycle_not_supported : ∀ (state : Yulang.GeneralNominalState.State)
  (root : Fin state.base.slots) (descriptor : Yulang.GeneralNominalState.Descriptor state.base.slots),
  state.nominals root = Option.some descriptor →
    Yulang.GeneralNominalK2Coverage.ExplicitCycle state root →
      ¬Yulang.GeneralNominalInspection.NominalSupported state root
@Yulang.GeneralNominalK2Coverage.nominal_cycle_defers : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  ¬Yulang.GeneralNominalState.RootPending context.state root.demand →
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration),
      declaration ∈ registry.declarations →
        Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration →
          declaration.role = root.demand.role →
            ∀ (bounds : List (Yulang.GeneralNominalInspection.Bounds context.state)),
              Yulang.GeneralNominalCandidates.arguments context root = Option.some bounds →
                ∀ (visited : Yulang.GeneralNominalInspection.Bounds context.state),
                  visited ∈ (Yulang.GeneralNominalCandidates.report context declaration bounds).inspected →
                    ∀ (descriptor : Yulang.GeneralNominalState.Descriptor context.state.base.slots),
                      context.state.nominals visited.fst = Option.some descriptor →
                        Yulang.GeneralNominalK2Coverage.ExplicitCycle context.state visited.fst →
                          Yulang.GeneralNominalCandidates.InspectionPending registry context root
Yulang.GeneralNominalK2Coverage.atK2_exact_closed : ∀ (state : Yulang.GeneralNominalState.State),
  (∀ (slot : Fin state.base.slots), state.view.graph slot ≠ Yulang.CommonRoleRegularGraph.Node.unresolved) →
    ∀ (root : Fin state.base.slots),
      Yulang.GeneralNominalK2Coverage.AtK2 state root ↔ Yulang.GeneralSourceK2.RecursAt state.view root
@Yulang.GeneralNominalK2Coverage.old_candidateK2 : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralNominalCandidates.CandidateK2 registry context root →
    Yulang.GeneralNominalK2Coverage.CandidateK2 registry context root
@Yulang.GeneralNominalK2Coverage.candidate_recurrence : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralNominalK2Coverage.CandidateK2 registry context root →
    ∃ declaration,
      declaration ∈ registry.declarations ∧
        ∃ bounds,
          Yulang.GeneralNominalCandidates.arguments context root = Option.some bounds ∧
            ∃ visited,
              visited ∈ (Yulang.GeneralNominalCandidates.report context declaration bounds).inspected ∧
                Yulang.GeneralSourceK2.RecursAt context.state.view visited.fst
@Yulang.GeneralNominalK2Coverage.pending_excludes_candidateK2 : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralNominalState.RootPending context.state root.demand →
    ¬Yulang.GeneralNominalK2Coverage.CandidateK2 registry context root
@Yulang.GeneralNominalLocalBoundary.rejection_not_pending : ∀ {v : Yulang.B4Target.Vocabulary}
  {b : Yulang.GeneralNominalLocalBoundary.Fields v} {r : v.Registry} {s : v.State} {d : v.Demand},
  Yulang.GeneralNominalLocalBoundary.RejectReason b r s d → ¬b.RootPending r s d
@Yulang.GeneralNominalLocalBoundary.safe_survivor_not_rejected : ∀ {v : Yulang.B4Target.Vocabulary}
  {b : Yulang.GeneralNominalLocalBoundary.Fields v} {r : v.Registry} {s : v.State} {d : v.Demand} {key : Nat}
  {children : List v.Demand},
  Yulang.GeneralNominalLocalBoundary.SafeKnown b r s d →
    b.Survivor r s d key children → ¬Yulang.GeneralNominalLocalBoundary.RejectReason b r s d
@Yulang.GeneralNominalLocalBoundary.unique_not_ambiguous : ∀ {v : Yulang.B4Target.Vocabulary}
  {b : Yulang.GeneralNominalLocalBoundary.Fields v} {r : v.Registry} {s : v.State} {d : v.Demand} {key : Nat}
  {children : List v.Demand} {key₁ : Nat} {cs₁ : List v.Demand} {key₂ : Nat} {cs₂ : List v.Demand},
  Yulang.GeneralNominalLocalBoundary.Unique b r s d key children →
    b.Survivor r s d key₁ cs₁ → b.Survivor r s d key₂ cs₂ → key₁ ≠ key₂ → False
@Yulang.GeneralNominalLocalBoundary.inspection_not_rejected : ∀ {v : Yulang.B4Target.Vocabulary}
  {b : Yulang.GeneralNominalLocalBoundary.Fields v} {r : v.Registry} {s : v.State} {d : v.Demand},
  b.InspectionPending r s d →
    ¬b.RootK2 r s d → ¬b.CandidateK2 r s d → ¬Yulang.GeneralNominalLocalBoundary.RejectReason b r s d
@Yulang.GeneralNominalLocalBoundary.local_functional : ∀ {v : Yulang.B4Target.Vocabulary}
  {b : Yulang.GeneralNominalLocalBoundary.Fields v} {r : v.Registry} {s : v.State} {d : v.Demand}
  {left right : Yulang.CommonRoleOutermostResolver.Frontier v.Demand},
  Yulang.GeneralNominalLocalBoundary.Local b r s d left →
    Yulang.GeneralNominalLocalBoundary.Local b r s d right → left = right
@Yulang.GeneralNominalLocalBoundary.local_total : ∀ {v : Yulang.B4Target.Vocabulary}
  {b : Yulang.GeneralNominalLocalBoundary.Fields v} {r : v.Registry} {s : v.State} {d : v.Demand},
  Yulang.GeneralNominalLocalBoundary.SurvivorChildrenFunctional b r s d →
    ∃ frontier, Yulang.GeneralNominalLocalBoundary.Local b r s d frontier
@Yulang.GeneralNominalLocalBoundary.local_total_decidable : ∀ {v : Yulang.B4Target.Vocabulary}
  {b : Yulang.GeneralNominalLocalBoundary.Fields v} {r : v.Registry} {s : v.State} {d : v.Demand},
  Yulang.GeneralNominalLocalBoundary.SurvivorChildrenFunctional b r s d →
    ∀ [Decidable (b.RootPending r s d)] [Decidable (b.RootK2 r s d)] [Decidable (b.CandidateK2 r s d)]
      [Decidable (b.InspectionPending r s d)] [Decidable (∃ key children, b.Survivor r s d key children)]
      [(key : Nat) → Decidable (∃ key' children', b.Survivor r s d key' children' ∧ key ≠ key')],
      ∃ frontier, Yulang.GeneralNominalLocalBoundary.Local b r s d frontier
@Yulang.GeneralNominalLocalBoundary.local_extension : ∀ {v : Yulang.B4Target.Vocabulary}
  {b : Yulang.GeneralNominalLocalBoundary.Fields v} {r : v.Registry} {s : v.State} {d : v.Demand}
  (remaining : Yulang.GeneralNominalLocalBoundary.Remaining v)
  (frontier : Yulang.CommonRoleOutermostResolver.Frontier v.Demand),
  Yulang.GeneralNominalLocalBoundary.Local b r s d frontier ↔
    Yulang.B4TargetV3.Local (Yulang.GeneralNominalLocalBoundary.complete b remaining) r s d frontier
Yulang.GeneralNominalLocalBoundary.survivor_functional : ∀ (roles : Yulang.Roles.RoleDecls)
  (registry : Yulang.GeneralDeclarations.Registry),
  (Yulang.GeneralNominalLocalBoundary.generalFields roles).Checked registry →
    ∀ (context : Yulang.GeneralNominalCandidates.Context) (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Yulang.GeneralNominalLocalBoundary.SurvivorChildrenFunctional
        (Yulang.GeneralNominalLocalBoundary.generalFields roles) registry context root
Yulang.GeneralNominalLocalBoundary.general_local_total : ∀ (roles : Yulang.Roles.RoleDecls)
  (registry : Yulang.GeneralDeclarations.Registry),
  (Yulang.GeneralNominalLocalBoundary.generalFields roles).Checked registry →
    ∀ (context : Yulang.GeneralNominalCandidates.Context) (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      ∃ frontier,
        Yulang.GeneralNominalLocalBoundary.Local (Yulang.GeneralNominalLocalBoundary.generalFields roles) registry
          context root frontier
Yulang.GeneralNominalLocalBoundary.general_local_functional : ∀ (roles : Yulang.Roles.RoleDecls)
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (first last : Yulang.CommonRoleOutermostResolver.Frontier (Yulang.GeneralSourceDictionaries.Occurrence roles)),
  Yulang.GeneralNominalLocalBoundary.Local (Yulang.GeneralNominalLocalBoundary.generalFields roles) registry context
      root first →
    Yulang.GeneralNominalLocalBoundary.Local (Yulang.GeneralNominalLocalBoundary.generalFields roles) registry context
        root last →
      first = last
@Yulang.GeneralNominalLocalBoundary.candidate_trichotomy : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  ¬Yulang.GeneralNominalState.RootPending context.state root.demand →
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration),
      declaration ∈ registry.declarations →
        ∀ (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration),
          declaration.role = root.demand.role →
            Yulang.GeneralNominalCandidates.Failed registry context root declaration ∨
              Yulang.GeneralNominalCandidates.Prepared registry context root declaration checked ∨
                Yulang.GeneralNominalCandidates.InspectionPending registry context root
@Yulang.GeneralNominalLocalBoundary.failed_not_prepared : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration),
  Yulang.GeneralNominalCandidates.Failed registry context root declaration →
    ¬Yulang.GeneralNominalCandidates.Prepared registry context root declaration checked
Yulang.GeneralNominalLocalBoundary.root_pending_excludes_candidates : ∀ (roles : Yulang.Roles.RoleDecls)
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralNominalState.RootPending context.state root.demand →
    (∀ (key : Nat) (children : List (Yulang.GeneralNominalCandidates.vocabulary roles).Demand),
        ¬(Yulang.GeneralNominalLocalBoundary.generalFields roles).Survivor registry context root key children) ∧
      ¬(Yulang.GeneralNominalLocalBoundary.generalFields roles).InspectionPending registry context root ∧
        ¬(Yulang.GeneralNominalLocalBoundary.generalFields roles).CandidateK2 registry context root ∧
          ¬(Yulang.GeneralNominalLocalBoundary.generalFields roles).RootK2 registry context root
@Yulang.GeneralNominalLocalBoundary.blocked_defers : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  ¬Yulang.GeneralNominalState.RootPending context.state root.demand →
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration),
      declaration ∈ registry.declarations →
        Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration →
          declaration.role = root.demand.role →
            ∀ (bounds : List (Yulang.GeneralNominalInspection.Bounds context.state)),
              Yulang.GeneralNominalCandidates.arguments context root = Option.some bounds →
                (Yulang.GeneralNominalCandidates.report context declaration bounds).blocked ≠ [] →
                  Yulang.GeneralNominalCandidates.InspectionPending registry context root
Yulang.GeneralNominalLocalBoundary.unsupported_layout_deferred : ∀
  (constructors : Yulang.GeneralDeclarationPatterns.Constructors)
  (interpretation : Yulang.GeneralNominalInspection.Interpretation) (key : Nat)
  (arguments : List Yulang.GeneralDeclarationPatterns.Pattern)
  (declaration : Yulang.GeneralDeclarationPatterns.Constructor),
  constructors key = Option.some declaration →
    interpretation.primitives key = Option.none →
      (declaration.parameters.all fun x => x == Yulang.GeneralDeclarationPatterns.ParameterKind.type) = Bool.false →
        Yulang.GeneralNominalInspection.translate constructors interpretation
            (Yulang.GeneralDeclarationPatterns.Pattern.app key arguments) =
          Yulang.GeneralNominalInspection.Query.deferred (Yulang.GeneralDeclarationPatterns.Pattern.app key arguments)
Yulang.GeneralNominalIntervalExamples.source_models : ∀ (a b : Yulang.Inference.Base),
  Yulang.GeneralNominalState.Models Yulang.GeneralNominalIntervalExamples.source
    (Yulang.GeneralNominalIntervalExamples.model a b)
Yulang.GeneralNominalIntervalExamples.nonpoint_extract : Yulang.GeneralNominalProjectionPropagation.extract
    Yulang.GeneralNominalIntervalExamples.source 0 Yulang.GeneralNominalIntervalExamples.descriptor 0 [[7]]
    Yulang.GeneralNominalIntervalExamples.descriptor.arguments =
  Option.some [Yulang.GeneralNominalIntervalExamples.first]
Yulang.GeneralNominalIntervalExamples.nonpoint_models : ∀ (a b : Yulang.Inference.Base),
  Yulang.GeneralNominalProjections.Models
    { source := Yulang.GeneralNominalIntervalExamples.source,
      bindings := [Yulang.GeneralNominalIntervalExamples.first] }
    (Yulang.GeneralNominalIntervalExamples.model a b)
Yulang.GeneralNominalIntervalExamples.different_endpoints : ∀ (a b : Yulang.Inference.Base),
  2 ≠ 3 ∧
    (Yulang.GeneralNominalIntervalExamples.model a b 2).fst ≠ (Yulang.GeneralNominalIntervalExamples.model a b 3).fst
Yulang.GeneralNominalIntervalExamples.nonpoint_ordinary_propagation : ∀ (a b : Yulang.Inference.Base),
  ∃ atoms,
    Yulang.GeneralNominalProjectionPropagation.compile Yulang.GeneralNominalIntervalExamples.source
          [Yulang.GeneralNominalIntervalExamples.first] =
        Option.some atoms ∧
      Yulang.GeneralNominalState.Models
        (Yulang.GeneralNominalState.extend Yulang.GeneralNominalIntervalExamples.source [] atoms)
        (Yulang.GeneralNominalIntervalExamples.model a b)
Yulang.GeneralNominalIntervalExamples.coarse_checks_pass : ∀ (a b : Yulang.Inference.Base),
  ∃ atoms,
    Yulang.GeneralNominalProjectionPropagation.compile Yulang.GeneralNominalIntervalExamples.source
          [Yulang.GeneralNominalIntervalExamples.first, Yulang.GeneralNominalIntervalExamples.last] =
        Option.some atoms ∧
      Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model
        (Yulang.GeneralNominalIntervalExamples.model a b) atoms
Yulang.GeneralNominalIntervalExamples.coarse_actual_conflict : ¬Yulang.GeneralNominalProjections.Models
    { source := Yulang.GeneralNominalIntervalExamples.source,
      bindings := [Yulang.GeneralNominalIntervalExamples.first, Yulang.GeneralNominalIntervalExamples.last] }
    (Yulang.GeneralNominalIntervalExamples.model Yulang.Inference.Base.int Yulang.Inference.Base.str)
Yulang.GeneralNominalIntervalExamples.row_checks_generated : Yulang.GeneralNominalIntervalLaws.checks
    Yulang.GeneralNominalIntervalExamples.base (Yulang.GeneralNominalState.Parameter.row (0, 1))
    (Yulang.GeneralNominalState.Parameter.row (2, 3)) =
  Option.some
    [Yulang.PresenceNormalForm.Atom.rowLe (Yulang.Core.PresenceGeneration.RowTerm.var 0)
        (Yulang.Core.PresenceGeneration.RowTerm.var 1),
      Yulang.PresenceNormalForm.Atom.rowLe (Yulang.Core.PresenceGeneration.RowTerm.var 0)
        (Yulang.Core.PresenceGeneration.RowTerm.var 3),
      Yulang.PresenceNormalForm.Atom.rowLe (Yulang.Core.PresenceGeneration.RowTerm.var 2)
        (Yulang.Core.PresenceGeneration.RowTerm.var 1),
      Yulang.PresenceNormalForm.Atom.rowLe (Yulang.Core.PresenceGeneration.RowTerm.var 2)
        (Yulang.Core.PresenceGeneration.RowTerm.var 3)]
Yulang.GeneralNominalIntervalExamples.index_pending_not_K2 : Yulang.GeneralNominalState.RootPending
    Yulang.GeneralNominalRegressions.indexState' Yulang.GeneralSourceStateExamples.indexDemand ∧
  ¬Yulang.GeneralNominalK2Coverage.RootK2 Yulang.GeneralNominalRegressions.indexState'
      Yulang.GeneralSourceStateExamples.indexDemand
Yulang.GeneralNominalIntervalExamples.loop_K2 : Yulang.GeneralNominalK2Coverage.RootK2
  Yulang.GeneralNominalRegressions.loopState' Yulang.GeneralSourceStateExamples.loopDemand
Yulang.GeneralNominalIntervalExamples.shadow_not_K2 : ¬Yulang.GeneralNominalK2Coverage.RootK2
    Yulang.GeneralNominalRegressions.shadowState' Yulang.GeneralSourceStateExamples.loopDemand
@Yulang.GeneralNominalEmissionOrigins.annotation_erases : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalState.State) (registry : Yulang.GeneralDeclarations.Registry)
  (emission : Yulang.GeneralDeclarationDemands.Emission roles)
  (bindings : List (Yulang.GeneralNominalProjections.Binding state)),
  (Yulang.GeneralNominalEmissionOrigins.annotate state registry emission bindings).emission = emission
@Yulang.GeneralNominalEmissionOrigins.request_origin_exact : ∀ {state : Yulang.GeneralNominalState.State}
  (identity : Nat) (request : Yulang.GeneralDeclarationDemands.InputRequest)
  (bindings : List (Yulang.GeneralNominalProjections.Binding state))
  (entry : Yulang.GeneralNominalEmissionOrigins.InputOrigin),
  entry ∈ Yulang.GeneralNominalEmissionOrigins.requestOrigins identity request bindings ↔
    ∃ name,
      Yulang.GeneralDeclarationPatterns.normalize request.pattern = Yulang.GeneralDeclarationPatterns.Pattern.var name ∧
        ∃ binding,
          binding ∈ bindings ∧
            binding.name = name ∧
              entry =
                { occurrence := identity, position := request.position, endpoints := request.endpoints,
                  origin := binding.origin }
@Yulang.GeneralNominalEmissionOrigins.emitted_input_origin : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalState.State) (registry : Yulang.GeneralDeclarations.Registry) (invocation : Nat)
  (declaration : Yulang.GeneralDeclarations.Declaration) (clause : Yulang.GeneralDeclarations.Clause)
  (valid : Yulang.GeneralDeclarations.Clause.Signature roles clause)
  (capture : Yulang.GeneralDeclarationDemands.Capture)
  (allocation : Yulang.GeneralDeclarationDemands.Allocation roles clause)
  (bindings : List (Yulang.GeneralNominalProjections.Binding state)) (index : Fin (roles clause.role).arity)
  (name : Nat),
  Yulang.GeneralDeclarationPatterns.normalize clause.arguments[↑index] =
      Yulang.GeneralDeclarationPatterns.Pattern.var name →
    ∀ (binding : Yulang.GeneralNominalProjections.Binding state),
      binding ∈ bindings →
        binding.name = name →
          let emission := Yulang.GeneralDeclarationDemands.emit invocation declaration clause valid capture allocation;
          emission.demand.arguments index = capture.inputs name ∧
            { occurrence := Yulang.GeneralNominalEmissionOrigins.occurrence state registry emission, position := ↑index,
                endpoints := capture.inputs name, origin := binding.origin } ∈
              Yulang.GeneralNominalEmissionOrigins.origins state registry emission bindings
@Yulang.GeneralNominalEmissionOrigins.origin_has_observation : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalState.State) (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (registry : Yulang.GeneralDeclarations.Registry) (emission : Yulang.GeneralDeclarationDemands.Emission roles)
  (bindings : List (Yulang.GeneralNominalProjections.Binding state)),
  Yulang.GeneralNominalProjections.Compatible state model bindings →
    ∀ (entry : Yulang.GeneralNominalEmissionOrigins.InputOrigin),
      entry ∈ Yulang.GeneralNominalEmissionOrigins.origins state registry emission bindings →
        entry.occurrence = Yulang.GeneralNominalEmissionOrigins.occurrence state registry emission ∧
          ∃ value, Yulang.GeneralNominalProjections.Observes model entry.origin value
@Yulang.GeneralNominalEmissionOrigins.occurrence_registry_independent : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalState.State) (first last : Yulang.GeneralDeclarations.Registry)
  (emission : Yulang.GeneralDeclarationDemands.Emission roles),
  Yulang.GeneralNominalEmissionOrigins.occurrence state first emission =
    Yulang.GeneralNominalEmissionOrigins.occurrence state last emission
@Yulang.GeneralNominalEmissionOrigins.single_capture_child_bounds : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalState.State) (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (registry : Yulang.GeneralDeclarations.Registry) (invocation : Nat)
  (declaration : Yulang.GeneralDeclarations.Declaration) (clause : Yulang.GeneralDeclarations.Clause)
  (valid : Yulang.GeneralDeclarations.Clause.Signature roles clause)
  (binding : Yulang.GeneralNominalProjections.Binding state) (bounds : Fin state.base.slots × Fin state.base.slots),
  binding.bounds = Yulang.GeneralNominalState.Parameter.type bounds →
    Yulang.GeneralNominalProjections.Binding.Valid state model binding →
      ∀ (index : Fin (roles clause.role).arity),
        Yulang.GeneralDeclarationPatterns.normalize clause.arguments[↑index] =
            Yulang.GeneralDeclarationPatterns.Pattern.var binding.name →
          have capture :=
            Yulang.GeneralNominalAllocation.capture state registry invocation declaration.id
              [(binding.name, state.base.source bounds.fst, state.base.source bounds.snd)];
          have allocation := Yulang.GeneralNominalAllocation.allocation state registry invocation declaration.id clause;
          let demand := Yulang.GeneralDeclarationDemands.childDemand declaration clause valid capture allocation;
          ∃ actual,
            Yulang.GeneralNominalProjections.Observes model binding.origin (Sum.inl actual) ∧
              Yulang.CommonNominalFullCarrier.Subtype (model (demand.arguments index).fst).fst actual ∧
                Yulang.CommonNominalFullCarrier.Subtype actual (model (demand.arguments index).snd).fst
```

### Verification and review for Item 3c

Final required commands, run from `lean/`:

| Exact command | Exit code |
| --- | --- |
| `lake build Yulang.GeneralNominalIntervalLaws Yulang.GeneralNominalProjections Yulang.GeneralNominalProjectionPropagation Yulang.GeneralNominalK2Coverage Yulang.GeneralNominalLocalBoundary Yulang.GeneralNominalIntervalExamples Yulang.GeneralNominalEmissionOrigins > /tmp/astra-interval-focused.log 2>&1` | 0 |
| `lake build Yulang > /tmp/astra-interval-umbrella.log 2>&1` | 0 |
| `lake env lean Audit.lean > /tmp/astra-interval-audit.log 2>&1` | 0 |

The focused build completed 570 jobs; the umbrella build completed 1429 jobs,
including the unchanged cycle-127 modules and previous positive/conflict/pending
regressions. The full dependency audit printed 9074 reports, including all 76
new public theorems exactly once. Its complete dependency set is `propext`,
`Classical.choice`, and `Quot.sound`. These counts include existing results.
The 76-statement inventory was generated by passing imports and `#check @...`
commands to `lake env lean --stdin` through Python; exit 0. The output above is
that inventory without removing premises.

Append-only byte-prefix checks against HEAD passed for Yulang.lean and
Audit.lean. Exactly seven imports and 76 audit commands were appended. The
allowed-path, new-source token/docstring, theorem/signature/audit coverage, and
whitespace checks passed. No existing implementation module, spec, plan, lake
configuration, commit, push, or git reference was changed. Early elaboration
failures were repaired in the new modules before these final successful checks.

The `yulang-proofs` workflow was used. No registered `prover` role/configuration
was available; the primary constructed these bounded derivations and no prover
agent ran. A separate read-only reviewer examined all seven modules, the
singleton emission delta, and the final scope/table. Review found no unsound
stated theorem, and explicitly confirmed that this is **not completion of Item
3c**. The reviewer did not independently rerun the builds or dependency audit.

### Supervisor answer to the mixed-recurrence question (2026-11-12, from spec/06-roles.md K2 decisions)

This is already decided by the spec (2026-11-07 K2 decisions), so it is not a new owner question:
- A nominal-headed node such as `list μ` is **not** a K2 root: "再帰型が型引数の深い位置（例: `list` の中）にあるだけなら、呼び出しは拒否しない", with the example `len [loop 1]` passing. So `Len (list μ)` passes (option 1).
- μ = {next: list μ} **is** an anonymous structural recursive type (an unnamed type that refers to itself; the named-recursion exemption covers named bodies such as `enum tree`, not anonymous types whose self-reference passes through a nominal argument). So `Show μ`, reached via `impl Show (list 'a) where Show 'a`, is rejected at that child, and a candidate whose head pattern must inspect a constructor of μ triggers candidate K2.
Implement this: recurrence edges may pass through nominal *arguments* (never through nominal bodies); the K2 root test applies only at anonymous structural heads (and at non-variable head inspections of them). The owner may still override; if so this note will be updated.


## Item 3d — recursive interval inspection and mixed recurrence (2026-11-12)

Status: proved integration of the invariant type-parameter path, repeated
capture emission, and mixed recurrence on the existing full nominal carrier.
This is substantial progress on Item 3, **not a claim that the whole-language
source boundary is complete**. The new predicates are total mathematical
relations on the existing carriers, but translation and observation coverage
still have the conservative limitations listed below. Those limitations cannot
be removed merely by placing the predicates in nine record fields.

### Representation and source meaning

The carrier is still `GeneralNominalState.State`, with the same ordinary atoms,
source identities, checked normalized snapshot, and full regular nominal
assignment. `GeneralNominalRecursiveInspection` replaces the old point-only
inspection path in the new candidate package. `typeArguments` retains arbitrary
lower/upper identities; it has no endpoint-equality test. Recursive inspection
follows a finite declaration pattern. A variable captures an interval and does
not inspect its descendants. Same-name nominal endpoints expose their explicit
arguments; nominal bodies never supply children. Ordinary self and cross
constraints remain `lo <= up`, `loA <= upB`, and `loB <= upA`, using the same
`GeneralNominalAllocation.propagate` and merge identities.

This follows the centerless invariant-interval decision, spec §6.3 and the
invariance decisions in §6.5. The actual argument in a model is not a new
source variable or a capture substitution. `Origin` records how to observe that
argument in the already assigned nominal value. It also records structural
projections below a nominal parameter. The actual values at repeated occurrences
must be equivalent, even when their coarse interval bounds are identical. This
prevents two different actual arguments, such as `int` and `str`, from being
accepted merely because both lie between bottom and top.

`GeneralNominalRecursivePropagation.Corresponds` links the nominal paths in a
recursive report to the existing `GeneralNominalProjections.Binding` interface.
`projection_compatible` proves the old projection conditions under that
correspondence premise; a total correspondence generator is not proved.
`branch_compiles` then invokes the existing
`GeneralNominalProjectionPropagation.compile_sound`. Its result includes both
the generated ordinary constraints and the retained projection conditions.
Structural paths use the same source model; the new full-carrier record-payload
inversion lemmas validate the nested record/list example. The observation-path
inversion theorem covers a singleton record; it is not a general inversion
for every canonical shape. This is done without replacing a
nominal constructor by a record or a tag.

`GeneralNominalCaptureMerges.repeated_child_correspondence` is not restricted to
a unary or singleton capture. For any nonempty set of occurrences of a declared
input variable, the computed child's interval contains an actual value iff
every contributing interval contains that value. The lower endpoint is the
union of lowers; the upper endpoint is the intersection of uppers. The result
uses the recorded merge equations and the existing deterministic allocation.
All where clauses, their associated equations, declaration identities, and
obligation identities are still emitted by `GeneralDeclarationDemands` through
`GeneralCanonicalChildOrder.canonicalEmit`. No sibling is resolved here.

`GeneralNominalMaterialization` adds branch constraints for supported compound
where inputs and named output requests, including the impl's own explicit
associated definitions. Lower and upper structural expressions use the
respective capture endpoints; actual nominal arguments use the interval and
retain occurrence sharing. Output-only binders use their existing source
identity. These are distinct modes: a structural interval is not collapsed to
an arbitrary representative. The two endpoint-equation theorems state the
separate equalities. Associated defaults still have the limitation below.

`BranchModels` includes the ordinary private state, projection constraints, and
materialization constraints. It implies the original `GeneralNominalState.Models`
and all captured cross constraints. It is **stronger** than models of
`privateState` alone. Item 4 must retain these extra conditions when installing
candidate or child updates. A survivor has a consistent propagated branch;
this does not assert that every model of the unpropagated source already
satisfies that candidate's additional constraints.

### Mixed recurrence and the supervisor answer

The earlier question is closed by the supervisor answer immediately above
this section and spec's K2 decisions at §6.3's discussion of termination:
`Len (list μ)` may select without inspecting μ; `Show (list μ)` may select and
emit `Show μ`; the child is rejected at μ. A non-variable pattern that actually
inspects μ also triggers candidate K2, ahead of ambiguity and independently of
inspection pending in other candidates. Draft addenda 1–4 still gate all K2
reasons by readiness of every unnamed root argument.

`GeneralNominalMixedRecurrence.Edge` is either a normalized structural child
edge or an `ActualArgument` edge. The latter requires, in every source model,
an observation of an explicit nominal argument equivalent to the target source
identity. Literal point parameters satisfy this condition, as do endpoints
proved equivalent in every model. A mere lower or upper bound is not an actual
recurrence edge. Mixed cycles also require existence of a source model, so an
inconsistent source cannot manufacture these semantic edges by vacuity.
`RecursAt` additionally requires a structural head at the reached root; the
previous normalized structural/alias cycle certificate remains a separate
sufficient case. Nominal roots are excluded by `nominal_not_recursive`.

This is an independent normalized source-observation recurrence definition,
not whole-denotation nonfiniteness and not a claim that the original source has
a complete normal form. `actual_edge_sound` states its projection meaning.
No executor, classifier return value, or substitution search appears in it.
The mixed fixture uses `CommonNominalFullGuardedClosure` to construct and prove
a real model of `μ = {next: list μ}`. Its return edge passes through the explicit
list argument. No nominal body is present in the fixture or the edge relation.

### Defined-field package and remaining source obligations

All names below are under `Yulang`. The new package is
`GeneralNominalLocalBoundary.recursiveFields`, defined by reopening that
namespace in the new `GeneralNominalRecursiveBoundary.lean`; the existing file
and `generalFields` definition are unchanged, as required by the append-only
rule. Cycle-127 interfaces, including `EmissionsReady`, remain unchanged.
There is no automatic replacement or claim of transport of its evidence proofs
to the new survivor relation.

| SourceBoundary field | Status and Lean definition | Source justification / limit |
| --- | --- | --- |
| Checked | DEFINED: `recursiveFields.Checked`, using `GeneralDeclarations.Checked` and registry-role equality | Existing §6.3 static checks, output-only rule, and normalization coverage are preserved. |
| Models | DEFINED: `GeneralNominalState.Models` | Same full nominal carrier and shared ordinary/normalized identities. `BranchModels` adds candidate conditions and proves projection back to this field. |
| Step | MISSING | Shared propagation must install the ordinary, projection, and materialization conditions, regenerate observations, and implement the decided same-input demand merge. |
| Stable | MISSING | Requires the actual shared-state progress relation and stable end-of-file rule. |
| Generated | MISSING | Deterministic child lists are defined; general installation, normalized observation production, and closure of generated children are not proved. |
| RootPending | DEFINED: `GeneralNominalState.RootPending` | All unnamed lower heads are needed, per addenda 3–4; named outputs are excluded. |
| RootK2 | DEFINED on the checked observation carrier: `GeneralNominalMixedRecurrence.RootK2`; source normalization coverage remains partial | Structural reached-root recurrence may pass through actual nominal arguments, never bodies; readiness gate retained. No all-source normalization completeness theorem. |
| CandidateK2 | DEFINED: `GeneralNominalRecursiveCandidates.CandidateK2`; source coverage remains partial | `HeadReady` requires consistent head/interval/projection checks, independently of RHS materialization. A visited non-variable position has `RecursAt`. Unsupported head translation still defers. |
| InspectionPending | DEFINED conservative relation: `GeneralNominalRecursiveCandidates.InspectionPending`; full-language coverage remains partial | Ready root and a visible candidate neither prepared nor failed. Genuinely unknown inspected heads defer; implementation coverage gaps also remain pending. It is not yet equivalent to only semantic unknownness. |
| Survivor | DEFINED: `GeneralNominalRecursiveCandidates.Survivor`; full-language coverage remains partial | Recursive non-point inspection, self/cross checks, actual projection sharing, deterministic repeated-capture frames, supported RHS constraints, and every emitted where child. No child resolution or result-tree folding. |
| Evidence | MISSING | Existing dictionary recipes are unchanged; the full evidence bridge for the new branch conditions and all source layouts is not proved. |
| Reorders | DEFINED: `GeneralRegistryReordering.Reorders` | Identity-preserving registry and where-clause reorder relation, unchanged. |
| DictionaryEquivalent | DEFINED: `GeneralDictionaryPayloadOrder.Equivalent` | Existing dictionary observation relation, unchanged; full Evidence remains separate. |

The four vocabulary types remain `GeneralNominalCandidates.vocabulary roles`:
`GeneralDeclarations.Registry`, `GeneralNominalCandidates.Context`,
`GeneralSourceDictionaries.Occurrence roles`, and
`GeneralNominalCommonBridge.Assignment`. They are general carriers, not the
example fixtures. `Remaining` still contains exactly `Step`, `Stable`,
`Generated`, and `Evidence`. `complete (recursiveFields roles) remaining` is a
conditional assembly of the unchanged `B4Target.SourceBoundary`. A closed
`generalBoundary`, `Executor.run`, and a general B4 theorem remain missing.

Local functionality and totality are proved for this package, with survivor
children functional under `Checked`. There is a version with explicit
decidability premises and a classical existence version. Neither supplies an
algorithm deciding the full-carrier consistency or normalization problems.
`recursive_local_extension` identifies this local relation with V3 Local for
any supplied Remaining. `recursive_candidateK2_rejects` has no inspection-pending
exclusion premise. Raw Survivor and CandidateK2 may coexist; the V3 priority
rules determine the local result.

### Regression coverage and exact remaining limits

The new general predicates prove:

- Display on actual `list int` has exactly one survivor, the list declaration,
  with exactly the original `[Display int]` child and occurrence identity.
- Wrap survives with the Container child and its item-equation obligation.
- A nominal variable capture with genuinely different lower/upper denotations
  survives, using the original full-carrier interval fixture.
- With lower `int` and upper `top`, a concrete `list int` head survives. A
  concrete `list str` head is eliminated; with only the list-str declaration
  visible, the V3 local result is rejected.
  The source has a proved model, so elimination is not vacuous.
- An unresolved non-point payload makes a concrete constructor inspection
  pending. It does not reject or fix the unknown payload.
- Repeated ordinary captures with incompatible known bounds have no survivors;
  the coarse actual `list int`/`list str` sharing counterexample remains excluded
  even when its interval checks alone pass. This particular regression excludes
  the specified int/str assignment, not every assignment of the unconstrained
  coarse source.
- The shadow-tail example is not RootK2; the old loop is RootK2; Index remains
  root-pending and not RootK2 under the new root definition.
- The mixed record/list fixture has a model and structural recurrence at μ,
  but no recurrence at the nominal root `list μ`. Len is locally selected with
  no children. Show survives with child `Show μ`, and that child's root is K2.
- A checked head `list {next: 'a}` inspects μ below the nominal argument and
  satisfies the new CandidateK2 definition. The structural projection into
  μ is proved exact on the full carrier.

Remaining technical limits are explicit, rather than new owner questions:

1. Existing `GeneralNominalInspection.translate` still defers row patterns,
   catalogue lower/upper layouts, unsupported variance, arrows, open record
   tails, and residual patterns. `GeneralNominalState.Parameter` cannot yet
   encode a lower/upper catalogue entry as a distinct layout kind. The old row
   interval laws are available, but kind-aware recursive capture and child
   materialization are still missing. No body traversal or invented variance
   interpretation is used to fill this gap.
2. Some known structural shape mismatches remain inspection blockers, rather
   than a proved compatible projection or elimination. Complete record width
   matching and all normalized observations need a source completeness proof.
3. `RootDefined` currently requires an explicit impl-associated definition for
   a requested root output. Role defaults need a faithful source-pattern
   elaboration and positional substitution bridge. Their absence defers; it
   does not reject the candidate.
4. There is no general equivalence between recursive report generation plus
   materialization and an independently complete language-wide applicability
   relation. The interval/projection lemmas are general; the positive examples
   do not establish that missing completeness theorem.
5. The subsequent shared state must retain `ProjectionModels` and materialized
   equations, not just `privateState.ordinary`. Bare variable-child endpoint
   correspondence is proved for repeated captures; source reachability,
   saturation, same-input merging, and final dictionary evidence remain Item 4
   and the evidence bridge. Distinct invocation identities never imply distinct
   denotations, so the decided demand merge remains possible.

The work is converging toward the shared instance: the new Survivor directly
uses the previously isolated interval/projection results, the old allocation
and declaration carriers, and the same full model. It now proves nominal
positive and mixed-recursive examples through that relation. It would be
misleading to equate these results, or generic local totality, with closure of
all general source semantics. The remaining tasks are source adapters and
completeness/persistence bridges, not more isolated scalar classification tests.

### Full theorem statements for Item 3d

The following inventory is generated from `#check @...` for every new public
theorem, retaining its premises and quantifiers. The example namespaces contain
concrete fixtures; the core theorem namespaces remain parametrized by the
shared carriers. Private proof helpers are covered transitively by the audit.

```lean
Yulang.GeneralNominalCaptureMerges.lower_exact : ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (bounds : List Yulang.GeneralSourceState.Interval),
  bounds ≠ [] →
    ∀ (actual : Yulang.CommonNominalFullCarrier.Ty),
      Yulang.CommonNominalFullCarrier.Subtype
          (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.CommonNominalFullCarrier.model model
            (Yulang.GeneralNominalAllocation.lower bounds))
          actual ↔
        ∀ (pair : Yulang.GeneralSourceState.Interval),
          pair ∈ bounds → Yulang.CommonNominalFullCarrier.Subtype (model pair.fst).fst actual
Yulang.GeneralNominalCaptureMerges.upper_exact : ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (bounds : List Yulang.GeneralSourceState.Interval),
  bounds ≠ [] →
    ∀ (actual : Yulang.CommonNominalFullCarrier.Ty),
      Yulang.CommonNominalFullCarrier.Subtype actual
          (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.CommonNominalFullCarrier.model model
            (Yulang.GeneralNominalAllocation.upper bounds)) ↔
        ∀ (pair : Yulang.GeneralSourceState.Interval),
          pair ∈ bounds → Yulang.CommonNominalFullCarrier.Subtype actual (model pair.snd).fst
Yulang.GeneralNominalCaptureMerges.equations_exact : ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (source : Nat) (term : Yulang.Core.PresenceGeneration.TyTerm Nat),
  Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
      (Yulang.GeneralNominalAllocation.equations source term) ↔
    Yulang.CommonNominalFullCarrier.Equivalent (model source).fst
      (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.CommonNominalFullCarrier.model model term)
Yulang.GeneralNominalCaptureMerges.capture_interval_exact : ∀ (state : Yulang.GeneralNominalState.State)
  (registry : Yulang.GeneralDeclarations.Registry) (invocation : Nat)
  (declaration : Yulang.GeneralDeclarations.Declaration) (bindings : Yulang.GeneralNominalAllocation.Bindings)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
      (Yulang.GeneralNominalAllocation.merges state registry invocation declaration bindings) →
    ∀ (name : Nat),
      name ∈ declaration.inputNames →
        Yulang.GeneralNominalAllocation.occurrences bindings name ≠ [] →
          ∀ (actual : Yulang.CommonNominalFullCarrier.Ty),
            Yulang.GeneralNominalCaptureMerges.Fits model
                ((Yulang.GeneralNominalAllocation.capture state registry invocation declaration.id bindings).inputs
                  name)
                actual ↔
              ∀ (bounds : Yulang.GeneralSourceState.Interval),
                bounds ∈ Yulang.GeneralNominalAllocation.occurrences bindings name →
                  Yulang.GeneralNominalCaptureMerges.Fits model bounds actual
Yulang.GeneralNominalCaptureMerges.propagated_capture_exact : ∀ (state : Yulang.GeneralNominalState.State)
  (registry : Yulang.GeneralDeclarations.Registry) (invocation : Nat)
  (declaration : Yulang.GeneralDeclarations.Declaration) (bindings : Yulang.GeneralNominalAllocation.Bindings)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models
      (Yulang.GeneralNominalAllocation.propagate state registry invocation declaration bindings) model →
    ∀ (name : Nat),
      name ∈ declaration.inputNames →
        Yulang.GeneralNominalAllocation.occurrences bindings name ≠ [] →
          ∀ (actual : Yulang.CommonNominalFullCarrier.Ty),
            Yulang.GeneralNominalCaptureMerges.Fits model
                ((Yulang.GeneralNominalAllocation.capture state registry invocation declaration.id bindings).inputs
                  name)
                actual ↔
              ∀ (bounds : Yulang.GeneralSourceState.Interval),
                bounds ∈ Yulang.GeneralNominalAllocation.occurrences bindings name →
                  Yulang.GeneralNominalCaptureMerges.Fits model bounds actual
@Yulang.GeneralNominalCaptureMerges.repeated_child_correspondence : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalState.State) (registry : Yulang.GeneralDeclarations.Registry) (invocation : Nat)
  (declaration : Yulang.GeneralDeclarations.Declaration) (bindings : Yulang.GeneralNominalAllocation.Bindings)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models
      (Yulang.GeneralNominalAllocation.propagate state registry invocation declaration bindings) model →
    ∀ (name : Nat),
      name ∈ declaration.inputNames →
        Yulang.GeneralNominalAllocation.occurrences bindings name ≠ [] →
          ∀ (actual : Yulang.CommonNominalFullCarrier.Ty) (clause : Yulang.GeneralDeclarations.Clause)
            (valid : Yulang.GeneralDeclarations.Clause.Signature roles clause) (index : Fin (roles clause.role).arity),
            Yulang.GeneralDeclarationPatterns.normalize clause.arguments[↑index] =
                Yulang.GeneralDeclarationPatterns.Pattern.var name →
              let child :=
                Yulang.GeneralDeclarationDemands.childDemand declaration clause valid
                  (Yulang.GeneralNominalAllocation.capture state registry invocation declaration.id bindings)
                  (Yulang.GeneralNominalAllocation.allocation state registry invocation declaration.id clause);
              Yulang.GeneralNominalCaptureMerges.Fits model (child.arguments index) actual ↔
                ∀ (bounds : Yulang.GeneralSourceState.Interval),
                  bounds ∈ Yulang.GeneralNominalAllocation.occurrences bindings name →
                    Yulang.GeneralNominalCaptureMerges.Fits model bounds actual
Yulang.GeneralNominalMaterialization.empty_models : ∀ (state : Yulang.GeneralNominalState.State)
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (report : Yulang.GeneralNominalRecursiveInspection.Report state)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalMaterialization.Models state declaration capture report { } model
Yulang.GeneralNominalMaterialization.output_variable_equation : ∀ (state : Yulang.GeneralNominalState.State)
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (report : Yulang.GeneralNominalRecursiveInspection.Report state)
  (generated : Yulang.GeneralNominalMaterialization.Schema) (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalMaterialization.Models state declaration capture report generated model →
    ∀ (name target : Nat),
      name ∈ declaration.outputNames →
        { name := name, origin := Yulang.GeneralNominalRecursiveInspection.Origin.source target,
              mode := Yulang.GeneralNominalMaterialization.Mode.actual } ∈
            generated.variables →
          Yulang.CommonNominalFullCarrier.Equivalent (model target).fst (model (capture.outputs name)).fst
Yulang.GeneralNominalMaterialization.endpoint_variable_equation : ∀ (state : Yulang.GeneralNominalState.State)
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (report : Yulang.GeneralNominalRecursiveInspection.Report state)
  (generated : Yulang.GeneralNominalMaterialization.Schema) (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalMaterialization.Models state declaration capture report generated model →
    ∀ (name target : Nat),
      ¬name ∈ declaration.outputNames →
        { name := name, origin := Yulang.GeneralNominalRecursiveInspection.Origin.source target,
              mode := Yulang.GeneralNominalMaterialization.Mode.lower } ∈
            generated.variables →
          Yulang.CommonNominalFullCarrier.Equivalent (model target).fst (model (capture.inputs name).fst).fst
Yulang.GeneralNominalMaterialization.upper_endpoint_variable_equation : ∀ (state : Yulang.GeneralNominalState.State)
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (report : Yulang.GeneralNominalRecursiveInspection.Report state)
  (generated : Yulang.GeneralNominalMaterialization.Schema) (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalMaterialization.Models state declaration capture report generated model →
    ∀ (name target : Nat),
      ¬name ∈ declaration.outputNames →
        { name := name, origin := Yulang.GeneralNominalRecursiveInspection.Origin.source target,
              mode := Yulang.GeneralNominalMaterialization.Mode.upper } ∈
            generated.variables →
          Yulang.CommonNominalFullCarrier.Equivalent (model target).fst (model (capture.inputs name).snd).fst
@Yulang.GeneralNominalMaterialization.named_outputs_retained : ∀ {roles : Yulang.Roles.RoleDecls}
  (emission : Yulang.GeneralDeclarationDemands.Emission roles)
  (output : Yulang.GeneralDeclarationDemands.OutputRequest),
  output ∈ emission.outputs →
    { pattern := output.pattern, target := output.target, mode := Yulang.GeneralNominalMaterialization.Mode.actual } ∈
      Yulang.GeneralNominalMaterialization.emissionRequests emission
Yulang.GeneralNominalMixedCandidateExample.checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDeclarationExamples.roles
  Yulang.GeneralNominalMixedCandidateExample.declaration
Yulang.GeneralNominalMixedCandidateExample.calculated_report : Yulang.GeneralNominalRecursiveCandidates.report
    Yulang.GeneralNominalMixedCandidateExample.context Yulang.GeneralNominalMixedCandidateExample.declaration [(1, 1)] =
  Yulang.GeneralNominalMixedCandidateExample.calculated
Yulang.GeneralNominalMixedCandidateExample.parameter_observed : Yulang.GeneralNominalRecursiveInspection.Observes
  Yulang.GeneralNominalMixedExamples.model Yulang.GeneralNominalMixedCandidateExample.parameterOrigin
  (Yulang.GeneralNominalMixedExamples.value 0)
Yulang.GeneralNominalMixedCandidateExample.parameter_exact : ∀ (actual : Yulang.CommonNominalFullCarrier.Ty),
  Yulang.GeneralNominalRecursiveInspection.Observes Yulang.GeneralNominalMixedExamples.model
      Yulang.GeneralNominalMixedCandidateExample.parameterOrigin actual →
    Yulang.CommonNominalFullCarrier.Equivalent actual (Yulang.GeneralNominalMixedExamples.value 0)
Yulang.GeneralNominalMixedCandidateExample.payload_observed : Yulang.GeneralNominalRecursiveInspection.Observes
  Yulang.GeneralNominalMixedExamples.model Yulang.GeneralNominalMixedCandidateExample.payloadOrigin
  (Yulang.GeneralNominalMixedExamples.value 1)
Yulang.GeneralNominalMixedCandidateExample.payload_exact : ∀ (actual : Yulang.CommonNominalFullCarrier.Ty),
  Yulang.GeneralNominalRecursiveInspection.Observes Yulang.GeneralNominalMixedExamples.model
      Yulang.GeneralNominalMixedCandidateExample.payloadOrigin actual →
    Yulang.CommonNominalFullCarrier.Equivalent actual (Yulang.GeneralNominalMixedExamples.value 1)
Yulang.GeneralNominalMixedCandidateExample.projection_models : Yulang.GeneralNominalRecursiveInspection.ProjectionModels
  Yulang.GeneralNominalMixedExamples.state Yulang.GeneralNominalMixedCandidateExample.calculated
  Yulang.GeneralNominalMixedExamples.model
Yulang.GeneralNominalMixedCandidateExample.private_models : Yulang.GeneralNominalState.Models
  (Yulang.GeneralNominalRecursiveCandidates.privateState Yulang.GeneralNominalMixedCandidateExample.registry
    Yulang.GeneralNominalMixedCandidateExample.context Yulang.GeneralNominalMixedExamples.showRoot
    Yulang.GeneralNominalMixedCandidateExample.declaration [(1, 1)])
  Yulang.GeneralNominalMixedExamples.model
Yulang.GeneralNominalMixedCandidateExample.candidate_K2 : Yulang.GeneralNominalRecursiveCandidates.CandidateK2
  Yulang.GeneralNominalMixedCandidateExample.registry Yulang.GeneralNominalMixedCandidateExample.context
  Yulang.GeneralNominalMixedExamples.showRoot
Yulang.GeneralNominalMixedExamples.record_equation : Yulang.CommonNominalFullCarrier.Equivalent
  (Yulang.GeneralNominalMixedExamples.value 0)
  (Yulang.CommonNominalFullCarrier.required 7 (Yulang.GeneralNominalMixedExamples.value 1))
Yulang.GeneralNominalMixedExamples.list_equation : Yulang.CommonNominalFullCarrier.Equivalent
  (Yulang.GeneralNominalMixedExamples.value 1)
  (Yulang.CommonNominalFullCarrier.nominal 0 [Sum.inl (Yulang.GeneralNominalMixedExamples.value 0)])
Yulang.GeneralNominalMixedExamples.state_models : Yulang.GeneralNominalState.Models
  Yulang.GeneralNominalMixedExamples.state Yulang.GeneralNominalMixedExamples.model
Yulang.GeneralNominalMixedExamples.structural_edge : Yulang.GeneralSourceK2.Child
  Yulang.GeneralNominalMixedExamples.view 0 1
Yulang.GeneralNominalMixedExamples.nominal_edge : Yulang.GeneralNominalMixedRecurrence.ActualArgument
  Yulang.GeneralNominalMixedExamples.state 1 0
Yulang.GeneralNominalMixedExamples.anonymous_recursive : Yulang.GeneralNominalMixedRecurrence.RecursAt
  Yulang.GeneralNominalMixedExamples.state 0
Yulang.GeneralNominalMixedExamples.list_not_recursive : ¬Yulang.GeneralNominalMixedRecurrence.RecursAt
    Yulang.GeneralNominalMixedExamples.state 1
Yulang.GeneralNominalMixedExamples.child_K2 : Yulang.GeneralNominalMixedRecurrence.RootK2
  Yulang.GeneralNominalMixedExamples.state Yulang.GeneralNominalMixedExamples.childDemand
Yulang.GeneralNominalMixedExamples.list_root_not_K2 : ¬Yulang.GeneralNominalMixedRecurrence.RootK2
    Yulang.GeneralNominalMixedExamples.state Yulang.GeneralNominalMixedExamples.showRoot.demand
Yulang.GeneralNominalMixedRecurrence.point_argument_edge : ∀ (state : Yulang.GeneralNominalState.State)
  (parent child : Fin state.base.slots) (descriptor : Yulang.GeneralNominalState.Descriptor state.base.slots),
  state.nominals parent = some descriptor →
    ∀ (index : Nat),
      descriptor.arguments[index]? = some (Yulang.GeneralNominalState.Parameter.type (child, child)) →
        Yulang.GeneralNominalMixedRecurrence.ActualArgument state parent child
Yulang.GeneralNominalMixedRecurrence.equal_endpoint_edge : ∀ (state : Yulang.GeneralNominalState.State)
  (parent lower upper : Fin state.base.slots) (descriptor : Yulang.GeneralNominalState.Descriptor state.base.slots),
  state.nominals parent = some descriptor →
    ∀ (index : Nat),
      descriptor.arguments[index]? = some (Yulang.GeneralNominalState.Parameter.type (lower, upper)) →
        (∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
            Yulang.GeneralNominalState.Models state model →
              Yulang.CommonNominalFullCarrier.Equivalent (model (state.base.source lower)).fst
                (model (state.base.source upper)).fst) →
          Yulang.GeneralNominalMixedRecurrence.ActualArgument state parent lower
Yulang.GeneralNominalMixedRecurrence.actual_edge_sound : ∀ (state : Yulang.GeneralNominalState.State)
  (parent child : Fin state.base.slots),
  Yulang.GeneralNominalMixedRecurrence.ActualArgument state parent child →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalState.Models state model →
        ∃ descriptor,
          state.nominals parent = some descriptor ∧
            ∃ index actual,
              Yulang.GeneralNominalProjections.Observes model
                  ((Yulang.GeneralNominalProjections.Ref.source (state.base.source parent)).argument
                    descriptor.declaration.name index)
                  (Sum.inl actual) ∧
                Yulang.CommonNominalFullCarrier.Equivalent actual (model (state.base.source child)).fst
Yulang.GeneralNominalMixedRecurrence.nominal_not_recursive : ∀ (state : Yulang.GeneralNominalState.State)
  (root : Fin state.base.slots) (descriptor : Yulang.GeneralNominalState.Descriptor state.base.slots),
  state.nominals root = some descriptor → ¬Yulang.GeneralNominalMixedRecurrence.RecursAt state root
Yulang.GeneralNominalMixedRecurrence.source_path : ∀ (state : Yulang.GeneralNominalState.State)
  (first last : Fin state.base.slots),
  Yulang.GeneralSourceK2.Path state.view first last → Yulang.GeneralNominalMixedRecurrence.Path state first last
@Yulang.GeneralNominalMixedRecurrence.old_rootK2 : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalState.State) (demand : Yulang.GeneralSourceState.Demand roles),
  Yulang.GeneralNominalK2Coverage.RootK2 state demand → Yulang.GeneralNominalMixedRecurrence.RootK2 state demand
@Yulang.GeneralNominalMixedRecurrence.pending_excludes_K2 : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalState.State) (demand : Yulang.GeneralSourceState.Demand roles),
  Yulang.GeneralNominalState.RootPending state demand → ¬Yulang.GeneralNominalMixedRecurrence.RootK2 state demand
Yulang.GeneralNominalMixedRecurrence.mixed_cycle_rejects : ∀ (state : Yulang.GeneralNominalState.State)
  (root nominal : Fin state.base.slots),
  Yulang.GeneralNominalMixedRecurrence.Structural state root →
    Yulang.GeneralSourceK2.Child state.view root nominal →
      Yulang.GeneralNominalMixedRecurrence.ActualArgument state nominal root →
        ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
          Yulang.GeneralNominalState.Models state model → Yulang.GeneralNominalMixedRecurrence.RecursAt state root
Yulang.GeneralNominalNonpointInspectionExamples.int_top : Yulang.CommonNominalFullCarrier.Subtype
  (Yulang.CommonNominalSyntax.Layer.base Yulang.Inference.Base.int) Yulang.CommonNominalSyntax.Layer.top
Yulang.GeneralNominalNonpointInspectionExamples.state_models : Yulang.GeneralNominalState.Models
  Yulang.GeneralNominalNonpointInspectionExamples.state Yulang.GeneralNominalNonpointInspectionExamples.model
Yulang.GeneralNominalNonpointInspectionExamples.endpoints_different : 2 ≠ 3 ∧
  (Yulang.GeneralNominalNonpointInspectionExamples.model 2).fst ≠
    (Yulang.GeneralNominalNonpointInspectionExamples.model 3).fst
Yulang.GeneralNominalNonpointInspectionExamples.int_report : Yulang.GeneralNominalRecursiveCandidates.report
    Yulang.GeneralNominalNonpointInspectionExamples.context Yulang.GeneralNominalNonpointInspectionExamples.intDecl
    [(0, 0)] =
  Yulang.GeneralNominalNonpointInspectionExamples.calculated
Yulang.GeneralNominalNonpointInspectionExamples.str_conflicts : (Yulang.GeneralNominalRecursiveCandidates.report
      Yulang.GeneralNominalNonpointInspectionExamples.context Yulang.GeneralNominalNonpointInspectionExamples.strDecl
      [(0, 0)]).conflicts =
  [(2, 3)]
Yulang.GeneralNominalNonpointInspectionExamples.projected_int : ∀ (actual : Yulang.CommonNominalFullCarrier.Ty),
  Yulang.GeneralNominalRecursiveInspection.Observes Yulang.GeneralNominalNonpointInspectionExamples.model
      Yulang.GeneralNominalNonpointInspectionExamples.parameterOrigin actual →
    Yulang.CommonNominalFullCarrier.Equivalent actual (Yulang.CommonNominalSyntax.Layer.base Yulang.Inference.Base.int)
Yulang.GeneralNominalNonpointInspectionExamples.projection_models : Yulang.GeneralNominalRecursiveInspection.ProjectionModels
  Yulang.GeneralNominalNonpointInspectionExamples.state Yulang.GeneralNominalNonpointInspectionExamples.calculated
  Yulang.GeneralNominalNonpointInspectionExamples.model
Yulang.GeneralNominalNonpointInspectionExamples.int_schema : Yulang.GeneralNominalRecursiveCandidates.generated
    Yulang.GeneralNominalNonpointInspectionExamples.intRegistry Yulang.GeneralNominalNonpointInspectionExamples.context
    Yulang.GeneralNominalNonpointInspectionExamples.root Yulang.GeneralNominalNonpointInspectionExamples.intDecl
    Yulang.GeneralNominalRegressions.concrete_checked [(0, 0)] =
  { }
Yulang.GeneralNominalNonpointInspectionExamples.int_survivor : Yulang.GeneralNominalRecursiveCandidates.Survivor
  Yulang.GeneralNominalNonpointInspectionExamples.intRegistry Yulang.GeneralNominalNonpointInspectionExamples.context
  Yulang.GeneralNominalNonpointInspectionExamples.root 4 []
Yulang.GeneralNominalNonpointInspectionExamples.no_str_survivors : ∀ (key : Nat)
  (children : List (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)),
  ¬Yulang.GeneralNominalRecursiveCandidates.Survivor Yulang.GeneralNominalNonpointInspectionExamples.strRegistry
      Yulang.GeneralNominalNonpointInspectionExamples.context Yulang.GeneralNominalNonpointInspectionExamples.root key
      children
Yulang.GeneralNominalNonpointInspectionExamples.str_checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDeclarationExamples.roles
  Yulang.GeneralNominalNonpointInspectionExamples.strDecl
Yulang.GeneralNominalNonpointInspectionExamples.str_finished_inspection : (Yulang.GeneralNominalRecursiveCandidates.report
        Yulang.GeneralNominalNonpointInspectionExamples.context Yulang.GeneralNominalNonpointInspectionExamples.strDecl
        [(0, 0)]).blocked =
    [] ∧
  (Yulang.GeneralNominalRecursiveCandidates.report Yulang.GeneralNominalNonpointInspectionExamples.context
        Yulang.GeneralNominalNonpointInspectionExamples.strDecl [(0, 0)]).arity =
    []
Yulang.GeneralNominalNonpointInspectionExamples.str_failed : Yulang.GeneralNominalRecursiveCandidates.Failed
  Yulang.GeneralNominalNonpointInspectionExamples.strRegistry Yulang.GeneralNominalNonpointInspectionExamples.context
  Yulang.GeneralNominalNonpointInspectionExamples.root Yulang.GeneralNominalNonpointInspectionExamples.strDecl
  Yulang.GeneralNominalNonpointInspectionExamples.str_checked
Yulang.GeneralNominalNonpointInspectionExamples.str_not_pending : ¬Yulang.GeneralNominalRecursiveCandidates.InspectionPending
    Yulang.GeneralNominalNonpointInspectionExamples.strRegistry Yulang.GeneralNominalNonpointInspectionExamples.context
    Yulang.GeneralNominalNonpointInspectionExamples.root
Yulang.GeneralNominalNonpointInspectionExamples.str_rejected : Yulang.GeneralNominalLocalBoundary.Local
  (Yulang.GeneralNominalLocalBoundary.recursiveFields Yulang.GeneralDeclarationExamples.roles)
  Yulang.GeneralNominalNonpointInspectionExamples.strRegistry Yulang.GeneralNominalNonpointInspectionExamples.context
  Yulang.GeneralNominalNonpointInspectionExamples.root Yulang.CommonRoleOutermostResolver.Frontier.rejected
Yulang.GeneralNominalLocalBoundary.recursive_survivor_functional : ∀ (roles : Yulang.Roles.RoleDecls)
  (registry : Yulang.GeneralDeclarations.Registry),
  (Yulang.GeneralNominalLocalBoundary.recursiveFields roles).Checked registry →
    ∀ (context : Yulang.GeneralNominalRecursiveCandidates.Context)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Yulang.GeneralNominalLocalBoundary.SurvivorChildrenFunctional
        (Yulang.GeneralNominalLocalBoundary.recursiveFields roles) registry context root
Yulang.GeneralNominalLocalBoundary.recursive_local_total : ∀ (roles : Yulang.Roles.RoleDecls)
  (registry : Yulang.GeneralDeclarations.Registry),
  (Yulang.GeneralNominalLocalBoundary.recursiveFields roles).Checked registry →
    ∀ (context : Yulang.GeneralNominalRecursiveCandidates.Context)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      ∃ frontier,
        Yulang.GeneralNominalLocalBoundary.Local (Yulang.GeneralNominalLocalBoundary.recursiveFields roles) registry
          context root frontier
Yulang.GeneralNominalLocalBoundary.recursive_local_total_decidable : ∀ (roles : Yulang.Roles.RoleDecls)
  (registry : Yulang.GeneralDeclarations.Registry),
  (Yulang.GeneralNominalLocalBoundary.recursiveFields roles).Checked registry →
    ∀ (context : Yulang.GeneralNominalRecursiveCandidates.Context)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
      [Decidable ((Yulang.GeneralNominalLocalBoundary.recursiveFields roles).RootPending registry context root)]
      [Decidable ((Yulang.GeneralNominalLocalBoundary.recursiveFields roles).RootK2 registry context root)]
      [Decidable ((Yulang.GeneralNominalLocalBoundary.recursiveFields roles).CandidateK2 registry context root)]
      [Decidable ((Yulang.GeneralNominalLocalBoundary.recursiveFields roles).InspectionPending registry context root)]
      [Decidable
          (∃ key children,
            (Yulang.GeneralNominalLocalBoundary.recursiveFields roles).Survivor registry context root key children)]
      [(key : Nat) →
          Decidable
            (∃ key' children',
              (Yulang.GeneralNominalLocalBoundary.recursiveFields roles).Survivor registry context root key' children' ∧
                key ≠ key')],
      ∃ frontier,
        Yulang.GeneralNominalLocalBoundary.Local (Yulang.GeneralNominalLocalBoundary.recursiveFields roles) registry
          context root frontier
Yulang.GeneralNominalLocalBoundary.recursive_local_functional : ∀ (roles : Yulang.Roles.RoleDecls)
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (first last : Yulang.CommonRoleOutermostResolver.Frontier (Yulang.GeneralSourceDictionaries.Occurrence roles)),
  Yulang.GeneralNominalLocalBoundary.Local (Yulang.GeneralNominalLocalBoundary.recursiveFields roles) registry context
      root first →
    Yulang.GeneralNominalLocalBoundary.Local (Yulang.GeneralNominalLocalBoundary.recursiveFields roles) registry context
        root last →
      first = last
Yulang.GeneralNominalLocalBoundary.recursive_local_extension : ∀ (roles : Yulang.Roles.RoleDecls)
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (remaining : Yulang.GeneralNominalLocalBoundary.Remaining (Yulang.GeneralNominalCandidates.vocabulary roles))
  (frontier : Yulang.CommonRoleOutermostResolver.Frontier (Yulang.GeneralSourceDictionaries.Occurrence roles)),
  Yulang.GeneralNominalLocalBoundary.Local (Yulang.GeneralNominalLocalBoundary.recursiveFields roles) registry context
      root frontier ↔
    Yulang.B4TargetV3.Local
      (Yulang.GeneralNominalLocalBoundary.complete (Yulang.GeneralNominalLocalBoundary.recursiveFields roles) remaining)
      registry context root frontier
@Yulang.GeneralNominalLocalBoundary.recursive_candidate_trichotomy : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  ¬Yulang.GeneralNominalState.RootPending context.state root.demand →
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration),
      declaration ∈ registry.declarations →
        ∀ (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration),
          declaration.role = root.demand.role →
            Yulang.GeneralNominalRecursiveCandidates.Failed registry context root declaration checked ∨
              Yulang.GeneralNominalRecursiveCandidates.Prepared registry context root declaration checked ∨
                Yulang.GeneralNominalRecursiveCandidates.InspectionPending registry context root
@Yulang.GeneralNominalLocalBoundary.recursive_failed_not_prepared : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration),
  Yulang.GeneralNominalRecursiveCandidates.Failed registry context root declaration checked →
    ¬Yulang.GeneralNominalRecursiveCandidates.Prepared registry context root declaration checked
Yulang.GeneralNominalLocalBoundary.recursive_candidateK2_rejects : ∀ (roles : Yulang.Roles.RoleDecls)
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralNominalRecursiveCandidates.CandidateK2 registry context root →
    Yulang.GeneralNominalLocalBoundary.Local (Yulang.GeneralNominalLocalBoundary.recursiveFields roles) registry context
      root Yulang.CommonRoleOutermostResolver.Frontier.rejected
Yulang.GeneralNominalLocalBoundary.recursive_pending_excludes_candidates : ∀ (roles : Yulang.Roles.RoleDecls)
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralNominalState.RootPending context.state root.demand →
    (∀ (key : Nat) (children : List (Yulang.GeneralNominalCandidates.vocabulary roles).Demand),
        ¬(Yulang.GeneralNominalLocalBoundary.recursiveFields roles).Survivor registry context root key children) ∧
      ¬(Yulang.GeneralNominalLocalBoundary.recursiveFields roles).InspectionPending registry context root ∧
        ¬(Yulang.GeneralNominalLocalBoundary.recursiveFields roles).CandidateK2 registry context root ∧
          ¬(Yulang.GeneralNominalLocalBoundary.recursiveFields roles).RootK2 registry context root
@Yulang.GeneralNominalRecursiveCandidates.branch_interval_sound : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
  (bounds : List (Yulang.GeneralNominalInspection.Bounds context.state))
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalRecursiveCandidates.BranchModels registry context root declaration checked bounds model →
    Yulang.GeneralNominalState.Models context.state model ∧
      Yulang.GeneralNominalAllocation.Compatible
          (Yulang.GeneralNominalRecursiveInspection.bindings context.state
            (Yulang.GeneralNominalRecursiveCandidates.report context declaration bounds))
          model ∧
        Yulang.GeneralNominalRecursiveInspection.ProjectionModels context.state
          (Yulang.GeneralNominalRecursiveCandidates.report context declaration bounds) model
@Yulang.GeneralNominalRecursiveCandidates.branch_child_correspondence : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
  (bounds : List (Yulang.GeneralNominalInspection.Bounds context.state))
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalRecursiveCandidates.BranchModels registry context root declaration checked bounds model →
    ∀ (name : Nat),
      name ∈ declaration.inputNames →
        Yulang.GeneralNominalAllocation.occurrences
              (Yulang.GeneralNominalRecursiveInspection.bindings context.state
                (Yulang.GeneralNominalRecursiveCandidates.report context declaration bounds))
              name ≠
            [] →
          ∀ (actual : Yulang.CommonNominalFullCarrier.Ty) (clause : Yulang.GeneralDeclarations.Clause)
            (valid : Yulang.GeneralDeclarations.Clause.Signature roles clause) (index : Fin (roles clause.role).arity),
            Yulang.GeneralDeclarationPatterns.normalize clause.arguments[↑index] =
                Yulang.GeneralDeclarationPatterns.Pattern.var name →
              have captures :=
                Yulang.GeneralNominalRecursiveInspection.bindings context.state
                  (Yulang.GeneralNominalRecursiveCandidates.report context declaration bounds);
              let child :=
                Yulang.GeneralDeclarationDemands.childDemand declaration clause valid
                  (Yulang.GeneralNominalAllocation.capture context.state registry root.identity declaration.id captures)
                  (Yulang.GeneralNominalAllocation.allocation context.state registry root.identity declaration.id
                    clause);
              Yulang.GeneralNominalCaptureMerges.Fits model (child.arguments index) actual ↔
                ∀ (interval : Yulang.GeneralSourceState.Interval),
                  interval ∈ Yulang.GeneralNominalAllocation.occurrences captures name →
                    Yulang.GeneralNominalCaptureMerges.Fits model interval actual
@Yulang.GeneralNominalRecursiveCandidates.survivor_children_functional : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry),
  Yulang.GeneralDeclarations.Checked registry →
    ∀ (context : Yulang.GeneralNominalRecursiveCandidates.Context)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
      (first last : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
      Yulang.GeneralNominalRecursiveCandidates.Survivor registry context root key first →
        Yulang.GeneralNominalRecursiveCandidates.Survivor registry context root key last → first = last
@Yulang.GeneralNominalRecursiveCandidates.blocked_defers : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  ¬Yulang.GeneralNominalState.RootPending context.state root.demand →
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration),
      declaration ∈ registry.declarations →
        Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration →
          declaration.role = root.demand.role →
            ∀ (bounds : List (Yulang.GeneralNominalInspection.Bounds context.state)),
              Yulang.GeneralNominalRecursiveCandidates.arguments context root = some bounds →
                (Yulang.GeneralNominalRecursiveCandidates.report context declaration bounds).blocked ≠ [] →
                  Yulang.GeneralNominalRecursiveCandidates.InspectionPending registry context root
@Yulang.GeneralNominalRecursiveCandidates.candidateK2_not_root_pending : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralNominalRecursiveCandidates.CandidateK2 registry context root →
    ¬Yulang.GeneralNominalState.RootPending context.state root.demand
Yulang.GeneralNominalRecursiveExamples.display_schema : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles),
  root.demand.outputs = [] →
    ∀
      (checked :
        Yulang.GeneralDeclarations.DeclarationChecked registry.constructors Yulang.GeneralDeclarationExamples.roles
          Yulang.GeneralDeclarationExamples.display)
      (bounds : List (Yulang.GeneralNominalInspection.Bounds context.state)),
      Yulang.GeneralNominalRecursiveCandidates.generated registry context root Yulang.GeneralDeclarationExamples.display
          checked bounds =
        { }
Yulang.GeneralNominalRecursiveExamples.display_survivor : Yulang.GeneralNominalRecursiveCandidates.Survivor
  Yulang.GeneralNominalExamples.registry (Yulang.GeneralNominalExamples.context true)
  Yulang.GeneralNominalExamples.displayRoot 1 [Yulang.GeneralNominalExamples.displayChild]
Yulang.GeneralNominalRecursiveExamples.nonpoint_survivor : ∀ (first last : Yulang.Inference.Base),
  Yulang.GeneralNominalRecursiveCandidates.Survivor Yulang.GeneralNominalExamples.registry
    Yulang.GeneralNominalRecursiveExamples.nonpointContext Yulang.GeneralNominalRecursiveExamples.nonpointRoot 1
    Yulang.GeneralNominalRecursiveExamples.nonpointChildren
Yulang.GeneralNominalRecursiveExamples.mixed_children : Yulang.GeneralNominalAllocation.children
    Yulang.GeneralNominalMixedExamples.state Yulang.GeneralNominalExamples.registry
    Yulang.GeneralNominalMixedExamples.showRoot Yulang.GeneralDeclarationExamples.display
    Yulang.GeneralDeclarationExamples.display_checked [(0, 0, 0)] =
  [Yulang.GeneralNominalRecursiveExamples.mixedChild]
Yulang.GeneralNominalRecursiveExamples.show_list_survivor : Yulang.GeneralNominalRecursiveCandidates.Survivor
  Yulang.GeneralNominalExamples.registry Yulang.GeneralNominalMixedExamples.context
  Yulang.GeneralNominalMixedExamples.showRoot 1 [Yulang.GeneralNominalRecursiveExamples.mixedChild]
Yulang.GeneralNominalRecursiveExamples.show_child_K2 : Yulang.GeneralNominalMixedRecurrence.RootK2
  Yulang.GeneralNominalMixedExamples.state Yulang.GeneralNominalRecursiveExamples.mixedChild.demand
Yulang.GeneralNominalRecursiveExamples.wrap_schema : Yulang.GeneralNominalRecursiveCandidates.generated
    Yulang.GeneralNominalExamples.registry (Yulang.GeneralNominalExamples.context true)
    Yulang.GeneralNominalExamples.wrapRoot Yulang.GeneralDeclarationExamples.wrap
    Yulang.GeneralDeclarationExamples.wrap_checked [(0, 0)] =
  {
    variables :=
      [{ name := 1,
          origin := Yulang.GeneralNominalRecursiveInspection.Origin.source Yulang.GeneralNominalExamples.itemTarget,
          mode := Yulang.GeneralNominalMaterialization.Mode.actual }] }
Yulang.GeneralNominalRecursiveExamples.wrap_survivor : Yulang.GeneralNominalRecursiveCandidates.Survivor
  Yulang.GeneralNominalExamples.registry (Yulang.GeneralNominalExamples.context true)
  Yulang.GeneralNominalExamples.wrapRoot 2 [Yulang.GeneralNominalExamples.wrapChild]
Yulang.GeneralNominalRecursiveExamples.len_checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDeclarationExamples.roles
  Yulang.GeneralNominalRecursiveExamples.len
Yulang.GeneralNominalRecursiveExamples.len_schema : Yulang.GeneralNominalRecursiveCandidates.generated
    Yulang.GeneralNominalRecursiveExamples.lenRegistry Yulang.GeneralNominalMixedExamples.context
    Yulang.GeneralNominalRecursiveExamples.lenRoot Yulang.GeneralNominalRecursiveExamples.len
    Yulang.GeneralNominalRecursiveExamples.len_checked [(1, 1)] =
  { }
Yulang.GeneralNominalRecursiveExamples.len_list_survivor : Yulang.GeneralNominalRecursiveCandidates.Survivor
  Yulang.GeneralNominalRecursiveExamples.lenRegistry Yulang.GeneralNominalMixedExamples.context
  Yulang.GeneralNominalRecursiveExamples.lenRoot 30 []
Yulang.GeneralNominalRecursiveInspection.embed_observation : ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (ref : Yulang.GeneralNominalProjections.Ref) (actual : Yulang.CommonNominalFullCarrier.Ty),
  Yulang.GeneralNominalProjections.Observes model ref (Sum.inl actual) →
    Yulang.GeneralNominalRecursiveInspection.Observes model (Yulang.GeneralNominalRecursiveInspection.embed ref) actual
Yulang.GeneralNominalRecursiveInspection.recover_observation : ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (ref : Yulang.GeneralNominalProjections.Ref) (actual : Yulang.CommonNominalFullCarrier.Ty),
  Yulang.GeneralNominalRecursiveInspection.Observes model (Yulang.GeneralNominalRecursiveInspection.embed ref) actual →
    Yulang.GeneralNominalProjections.Observes model ref (Sum.inl actual)
Yulang.GeneralNominalRecursiveInspection.nominal_observation_unique : ∀
  (model : Yulang.GeneralNominalCommonBridge.Assignment) (ref : Yulang.GeneralNominalProjections.Ref)
  (first last : Yulang.CommonNominalFullCarrier.Ty),
  Yulang.GeneralNominalRecursiveInspection.Observes model (Yulang.GeneralNominalRecursiveInspection.embed ref) first →
    Yulang.GeneralNominalRecursiveInspection.Observes model (Yulang.GeneralNominalRecursiveInspection.embed ref) last →
      Yulang.CommonNominalFullCarrier.Equivalent first last
Yulang.GeneralNominalRecursiveInspection.nominal_argument_bounds : ∀ (state : Yulang.GeneralNominalState.State)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models state model →
    ∀ (slot : Fin state.base.slots) (descriptor : Yulang.GeneralNominalState.Descriptor state.base.slots),
      state.nominals slot = some descriptor →
        ∀ (index : Nat) (bounds : Yulang.GeneralNominalInspection.Bounds state),
          descriptor.arguments[index]? = some (Yulang.GeneralNominalState.Parameter.type bounds) →
            (∃ actual,
                Yulang.GeneralNominalRecursiveInspection.Observes model
                  ((Yulang.GeneralNominalRecursiveInspection.Origin.source (state.base.source slot)).nominal
                    descriptor.declaration.name index)
                  actual) ∧
              ∀ (actual : Yulang.CommonNominalFullCarrier.Ty),
                Yulang.GeneralNominalRecursiveInspection.Observes model
                    ((Yulang.GeneralNominalRecursiveInspection.Origin.source (state.base.source slot)).nominal
                      descriptor.declaration.name index)
                    actual →
                  Yulang.GeneralNominalCaptureMerges.Fits model
                    (state.base.source bounds.fst, state.base.source bounds.snd) actual
@Yulang.GeneralNominalRecursiveInspection.nonpoint_type_arguments : ∀ {slots : Nat} (bounds : Fin slots × Fin slots),
  Yulang.GeneralNominalRecursiveInspection.typeArguments [Yulang.GeneralNominalState.Parameter.type bounds] =
    some [bounds]
Yulang.GeneralNominalRecursiveInspection.variable_does_not_inspect : ∀ (state : Yulang.GeneralNominalState.State)
  (names : List Nat) (bounds : Yulang.GeneralNominalInspection.Bounds state)
  (origin : Option Yulang.GeneralNominalRecursiveInspection.Origin),
  (Yulang.GeneralNominalRecursiveInspection.inspect state (Yulang.GeneralNominalInspection.Query.variables names) bounds
        origin).inspected =
    []
Yulang.GeneralNominalRecursiveInspection.unresolved_blocks : ∀ (state : Yulang.GeneralNominalState.State)
  (expected : Nat) (patterns : List Yulang.GeneralNominalInspection.Query)
  (bounds : Yulang.GeneralNominalInspection.Bounds state)
  (origin : Option Yulang.GeneralNominalRecursiveInspection.Origin),
  state.nominals bounds.fst = none →
    state.view.heads bounds.fst =
        Yulang.GeneralNormalizedObservation.Head.deferred Yulang.GeneralNormalizedObservation.Deferred.unresolved →
      (Yulang.GeneralNominalRecursiveInspection.inspect state
            (Yulang.GeneralNominalInspection.Query.nominal expected patterns) bounds origin).blocked ≠
        []
Yulang.GeneralNominalRecursiveInspection.projected_capture_sound : ∀ (state : Yulang.GeneralNominalState.State)
  (report : Yulang.GeneralNominalRecursiveInspection.Report state)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalRecursiveInspection.ProjectionModels state report model →
    ∀ (first last : Yulang.GeneralNominalRecursiveInspection.Capture state),
      first ∈ report.captures →
        last ∈ report.captures →
          first.name = last.name →
            ∀ (origin : Yulang.GeneralNominalRecursiveInspection.Origin),
              first.origin = some origin →
                ∀ (actual : Yulang.CommonNominalFullCarrier.Ty),
                  Yulang.GeneralNominalRecursiveInspection.Observes model origin actual →
                    Yulang.GeneralNominalRecursiveInspection.Fits state model last.bounds actual
Yulang.GeneralNominalRecursivePropagation.projection_compatible : ∀ (state : Yulang.GeneralNominalState.State)
  (report : Yulang.GeneralNominalRecursiveInspection.Report state)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalRecursiveInspection.ProjectionModels state report model →
    ∀ (old : List (Yulang.GeneralNominalProjections.Binding state)),
      Yulang.GeneralNominalRecursivePropagation.Corresponds state report old →
        Yulang.GeneralNominalProjections.Compatible state model old
@Yulang.GeneralNominalRecursivePropagation.branch_compiles : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
  (bounds : List (Yulang.GeneralNominalInspection.Bounds context.state))
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalRecursiveCandidates.BranchModels registry context root declaration checked bounds model →
    ∀ (old : List (Yulang.GeneralNominalProjections.Binding context.state)),
      Yulang.GeneralNominalRecursivePropagation.Corresponds context.state
          (Yulang.GeneralNominalRecursiveCandidates.report context declaration bounds) old →
        ∃ atoms,
          Yulang.GeneralNominalProjectionPropagation.compile context.state old = some atoms ∧
            Yulang.GeneralNominalState.Models (Yulang.GeneralNominalState.extend context.state [] atoms) model ∧
              Yulang.GeneralNominalProjections.Compatible context.state model old
@Yulang.GeneralNominalRecursivePropagation.existing_projection_preserved : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
  (bounds : List (Yulang.GeneralNominalInspection.Bounds context.state))
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalRecursiveCandidates.BranchModels registry context root declaration checked bounds model →
    ∀ (old : List (Yulang.GeneralNominalProjections.Binding context.state)),
      Yulang.GeneralNominalRecursivePropagation.Corresponds context.state
          (Yulang.GeneralNominalRecursiveCandidates.report context declaration bounds) old →
        Yulang.GeneralNominalProjections.Models { source := context.state, bindings := old } model
Yulang.GeneralNominalRecursiveRegressions.index_pending_not_K2 : Yulang.GeneralNominalState.RootPending
    Yulang.GeneralNominalRegressions.indexState' Yulang.GeneralSourceStateExamples.indexDemand ∧
  ¬Yulang.GeneralNominalMixedRecurrence.RootK2 Yulang.GeneralNominalRegressions.indexState'
      Yulang.GeneralSourceStateExamples.indexDemand
Yulang.GeneralNominalRecursiveRegressions.shadow_not_K2 : ¬Yulang.GeneralNominalMixedRecurrence.RootK2
    Yulang.GeneralNominalRegressions.shadowState' Yulang.GeneralSourceStateExamples.loopDemand
Yulang.GeneralNominalRecursiveRegressions.loop_K2 : Yulang.GeneralNominalMixedRecurrence.RootK2
  Yulang.GeneralNominalRegressions.loopState' Yulang.GeneralSourceStateExamples.loopDemand
Yulang.GeneralNominalRecursiveRegressions.unresolved_payload_blocks : (Yulang.GeneralNominalRecursiveCandidates.report
      (Yulang.GeneralNominalExamples.context false) Yulang.GeneralNominalRegressions.concreteList [(0, 0)]).blocked =
  [(1, 1)]
Yulang.GeneralNominalRecursiveRegressions.inspection_pending : Yulang.GeneralNominalRecursiveCandidates.InspectionPending
  Yulang.GeneralNominalRegressions.concreteRegistry (Yulang.GeneralNominalExamples.context false)
  Yulang.GeneralNominalExamples.displayRoot
Yulang.GeneralNominalRecursiveRegressions.repeated_bindings : Yulang.GeneralNominalRecursiveInspection.bindings
    Yulang.GeneralNominalRegressions.conflictState
    (Yulang.GeneralNominalRecursiveCandidates.report Yulang.GeneralNominalRegressions.conflictContext
      Yulang.GeneralCandidateConflictExamples.repeated [(0, 0), (1, 1)]) =
  Yulang.GeneralNominalRegressions.conflicting
Yulang.GeneralNominalRecursiveRegressions.no_conflict_survivors : ∀ (key : Nat)
  (children : List (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)),
  ¬Yulang.GeneralNominalRecursiveCandidates.Survivor Yulang.GeneralCandidateConflictExamples.registry
      Yulang.GeneralNominalRegressions.conflictContext Yulang.GeneralCandidateConflictExamples.root key children
Yulang.GeneralNominalRecursiveRegressions.coarse_actual_conflict : ¬Yulang.GeneralNominalRecursiveInspection.ProjectionModels
    Yulang.GeneralNominalIntervalExamples.source
    {
      captures :=
        [Yulang.GeneralNominalRecursiveRegressions.coarseFirst, Yulang.GeneralNominalRecursiveRegressions.coarseLast] }
    (Yulang.GeneralNominalIntervalExamples.model Yulang.Inference.Base.int Yulang.Inference.Base.str)
Yulang.GeneralNominalRecursiveRegressions.len_not_rootK2 : ¬Yulang.GeneralNominalMixedRecurrence.RootK2
    Yulang.GeneralNominalMixedExamples.state Yulang.GeneralNominalRecursiveExamples.lenRoot.demand
Yulang.GeneralNominalRecursiveRegressions.int_head_conflicts : (Yulang.GeneralNominalRecursiveCandidates.report
      (Yulang.GeneralNominalExamples.context true) Yulang.GeneralNominalExamples.intDisplay [(0, 0)]).conflicts =
  [(0, 0)]
Yulang.GeneralNominalRecursiveRegressions.display_exactly_one : ∀ (key : Nat)
  (children : List (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)),
  Yulang.GeneralNominalRecursiveCandidates.Survivor Yulang.GeneralNominalExamples.registry
      (Yulang.GeneralNominalExamples.context true) Yulang.GeneralNominalExamples.displayRoot key children ↔
    key = 1 ∧ children = [Yulang.GeneralNominalExamples.displayChild]
Yulang.GeneralNominalRecursiveRegressions.nonpoint_unresolved_payload_blocks : (Yulang.GeneralNominalRecursiveCandidates.report
      Yulang.GeneralNominalRecursiveExamples.nonpointContext Yulang.GeneralNominalRegressions.concreteList
      [(0, 0)]).blocked =
  [(2, 3)]
Yulang.GeneralNominalRecursiveRegressions.nonpoint_inspection_pending : Yulang.GeneralNominalRecursiveCandidates.InspectionPending
  Yulang.GeneralNominalRegressions.concreteRegistry Yulang.GeneralNominalRecursiveExamples.nonpointContext
  Yulang.GeneralNominalRecursiveExamples.nonpointRoot
Yulang.GeneralNominalRecursiveRegressions.len_inspected : (Yulang.GeneralNominalRecursiveCandidates.report
      Yulang.GeneralNominalMixedExamples.context Yulang.GeneralNominalRecursiveExamples.len [(1, 1)]).inspected =
  [(1, 1)]
Yulang.GeneralNominalRecursiveRegressions.len_not_candidateK2 : ¬Yulang.GeneralNominalRecursiveCandidates.CandidateK2
    Yulang.GeneralNominalRecursiveExamples.lenRegistry Yulang.GeneralNominalMixedExamples.context
    Yulang.GeneralNominalRecursiveExamples.lenRoot
Yulang.GeneralNominalRecursiveRegressions.len_not_inspection_pending : ¬Yulang.GeneralNominalRecursiveCandidates.InspectionPending
    Yulang.GeneralNominalRecursiveExamples.lenRegistry Yulang.GeneralNominalMixedExamples.context
    Yulang.GeneralNominalRecursiveExamples.lenRoot
Yulang.GeneralNominalRecursiveRegressions.len_selected : Yulang.GeneralNominalLocalBoundary.Local
  (Yulang.GeneralNominalLocalBoundary.recursiveFields Yulang.GeneralDeclarationExamples.roles)
  Yulang.GeneralNominalRecursiveExamples.lenRegistry Yulang.GeneralNominalMixedExamples.context
  Yulang.GeneralNominalRecursiveExamples.lenRoot (Yulang.CommonRoleOutermostResolver.Frontier.selected 30 [])
Yulang.GeneralNominalStructuralProjectionLaws.finite_record_payload : ∀ (label : Nat)
  (a b rest tail : Yulang.CommonNominalFullDemand.Ty Yulang.CommonNominalFullCarrier.Row),
  Yulang.CommonNominalFullDemand.ProducerLe Yulang.Common.rowLe (Yulang.CommonNominalFinite.Ty.record label a rest)
      (Yulang.CommonNominalFinite.Ty.record label b tail) →
    Yulang.CommonNominalFullDemand.ProducerLe Yulang.Common.rowLe a b
Yulang.GeneralNominalStructuralProjectionLaws.record_payload : ∀ (label : Nat)
  (a b rest tail : Yulang.CommonNominalFullCarrier.Ty),
  Yulang.CommonNominalFullCarrier.Subtype (Yulang.CommonNominalFullCarrier.record label a rest)
      (Yulang.CommonNominalFullCarrier.record label b tail) →
    Yulang.CommonNominalFullCarrier.Subtype a b
Yulang.GeneralNominalStructuralProjectionLaws.required_equivalent : ∀ (label : Nat)
  (first last : Yulang.CommonNominalFullCarrier.Ty),
  Yulang.CommonNominalFullCarrier.Equivalent (Yulang.CommonNominalFullCarrier.required label first)
      (Yulang.CommonNominalFullCarrier.required label last) ↔
    Yulang.CommonNominalFullCarrier.Equivalent first last
Yulang.GeneralNominalStructuralProjectionLaws.singleton_shape : ∀ (label : Nat)
  (payload : Yulang.CommonNominalFullCarrier.Ty),
  Yulang.GeneralNominalRecursiveInspection.shapeValue (Yulang.GeneralNormalizedObservation.Shape.record [label])
      [payload] =
    Yulang.CommonNominalFullCarrier.required label payload
Yulang.GeneralNominalStructuralProjectionLaws.record_observation : ∀
  (model : Yulang.GeneralNominalCommonBridge.Assignment) (parent : Yulang.GeneralNominalRecursiveInspection.Origin)
  (label : Nat) (actual payload : Yulang.CommonNominalFullCarrier.Ty),
  (∀ (value : Yulang.CommonNominalFullCarrier.Ty),
      Yulang.GeneralNominalRecursiveInspection.Observes model parent value →
        Yulang.CommonNominalFullCarrier.Equivalent value (Yulang.CommonNominalFullCarrier.required label payload)) →
    Yulang.GeneralNominalRecursiveInspection.Observes model
        (parent.structural (Yulang.GeneralNormalizedObservation.Shape.record [label]) 0) actual →
      Yulang.CommonNominalFullCarrier.Equivalent actual payload
Yulang.GeneralNominalUnaryCaptureFacts.report_exact : ∀ (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (declaration : Yulang.GeneralDeclarations.Declaration) (slot : Fin context.state.base.slots)
  (descriptor : Yulang.GeneralNominalState.Descriptor context.state.base.slots),
  context.state.nominals slot = some descriptor →
    ∀ (binder : Nat) (bounds : Yulang.GeneralNominalInspection.Bounds context.state),
      descriptor.arguments = [Yulang.GeneralNominalState.Parameter.type bounds] →
        Yulang.GeneralNominalInspection.queries context.state context.interpretation declaration =
            [Yulang.GeneralNominalInspection.Query.nominal descriptor.declaration.name
                [Yulang.GeneralNominalInspection.Query.variables [binder]]] →
          Yulang.GeneralNominalRecursiveCandidates.report context declaration [(slot, slot)] =
            Yulang.GeneralNominalUnaryCaptureFacts.captured context.state slot descriptor.declaration.name binder bounds
Yulang.GeneralNominalUnaryCaptureFacts.projection_models : ∀ (state : Yulang.GeneralNominalState.State)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models state model →
    ∀ (slot : Fin state.base.slots) (descriptor : Yulang.GeneralNominalState.Descriptor state.base.slots),
      state.nominals slot = some descriptor →
        ∀ (binder : Nat) (bounds : Yulang.GeneralNominalInspection.Bounds state),
          descriptor.arguments = [Yulang.GeneralNominalState.Parameter.type bounds] →
            Yulang.GeneralNominalRecursiveInspection.ProjectionModels state
              (Yulang.GeneralNominalUnaryCaptureFacts.captured state slot descriptor.declaration.name binder bounds)
              model
Yulang.GeneralNominalUnaryCaptureFacts.propagated_models : ∀ (state : Yulang.GeneralNominalState.State)
  (registry : Yulang.GeneralDeclarations.Registry) (invocation : Nat)
  (declaration : Yulang.GeneralDeclarations.Declaration) (binder : Nat),
  declaration.inputNames = [binder] →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalState.Models state model →
        ∀ (bounds : Yulang.GeneralNominalInspection.Bounds state),
          Yulang.CommonNominalFullCarrier.Subtype (model (state.base.source bounds.fst)).fst
              (model (state.base.source bounds.snd)).fst →
            Yulang.GeneralNominalState.Models
              (Yulang.GeneralNominalAllocation.propagate state registry invocation declaration
                [(binder, state.base.source bounds.fst, state.base.source bounds.snd)])
              model
Yulang.GeneralNominalUnaryCaptureFacts.self_models : ∀ (state : Yulang.GeneralNominalState.State)
  (slot : Fin state.base.slots) (name binder : Nat) (bounds : Yulang.GeneralNominalInspection.Bounds state)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.CommonNominalFullCarrier.Subtype (model (state.base.source bounds.fst)).fst
      (model (state.base.source bounds.snd)).fst →
    Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
      (Yulang.GeneralNominalRecursiveInspection.selfChecks state
        (Yulang.GeneralNominalUnaryCaptureFacts.captured state slot name binder bounds))
Yulang.GeneralNominalUnaryCaptureFacts.initial_fresh : ∀ (state : Yulang.GeneralNominalState.State)
  (registry : Yulang.GeneralDeclarations.Registry) (invocation : Nat),
  List.foldr max 0 (Yulang.GeneralNominalState.sources state) ≤ state.seed →
    Yulang.GeneralNominalAllocation.Fresh state registry invocation
@Yulang.GeneralNominalUnaryCaptureFacts.private_models : ∀ {roles : Yulang.Roles.RoleDecls}
  (context : Yulang.GeneralNominalRecursiveCandidates.Context) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (slot : Fin context.state.base.slots) (descriptor : Yulang.GeneralNominalState.Descriptor context.state.base.slots),
  context.state.nominals slot = some descriptor →
    ∀ (binder : Nat),
      declaration.inputNames = [binder] →
        ∀ (bounds : Yulang.GeneralNominalInspection.Bounds context.state),
          descriptor.arguments = [Yulang.GeneralNominalState.Parameter.type bounds] →
            Yulang.GeneralNominalInspection.queries context.state context.interpretation declaration =
                [Yulang.GeneralNominalInspection.Query.nominal descriptor.declaration.name
                    [Yulang.GeneralNominalInspection.Query.variables [binder]]] →
              ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                Yulang.GeneralNominalState.Models context.state model →
                  Yulang.GeneralNominalState.Models
                      (Yulang.GeneralNominalRecursiveCandidates.privateState registry context root declaration
                        [(slot, slot)])
                      model ∧
                    Yulang.GeneralNominalRecursiveInspection.ProjectionModels context.state
                      (Yulang.GeneralNominalRecursiveCandidates.report context declaration [(slot, slot)]) model
```

### Files and verification for Item 3d

New implementation and proof modules:

- [`GeneralNominalCaptureMerges.lean`](../../lean/Yulang/GeneralNominalCaptureMerges.lean)
- [`GeneralNominalMaterialization.lean`](../../lean/Yulang/GeneralNominalMaterialization.lean)
- [`GeneralNominalMixedCandidateExample.lean`](../../lean/Yulang/GeneralNominalMixedCandidateExample.lean)
- [`GeneralNominalMixedExamples.lean`](../../lean/Yulang/GeneralNominalMixedExamples.lean)
- [`GeneralNominalMixedRecurrence.lean`](../../lean/Yulang/GeneralNominalMixedRecurrence.lean)
- [`GeneralNominalNonpointInspectionExamples.lean`](../../lean/Yulang/GeneralNominalNonpointInspectionExamples.lean)
- [`GeneralNominalRecursiveBoundary.lean`](../../lean/Yulang/GeneralNominalRecursiveBoundary.lean)
- [`GeneralNominalRecursiveCandidates.lean`](../../lean/Yulang/GeneralNominalRecursiveCandidates.lean)
- [`GeneralNominalRecursiveExamples.lean`](../../lean/Yulang/GeneralNominalRecursiveExamples.lean)
- [`GeneralNominalRecursiveInspection.lean`](../../lean/Yulang/GeneralNominalRecursiveInspection.lean)
- [`GeneralNominalRecursivePropagation.lean`](../../lean/Yulang/GeneralNominalRecursivePropagation.lean)
- [`GeneralNominalRecursiveRegressions.lean`](../../lean/Yulang/GeneralNominalRecursiveRegressions.lean)
- [`GeneralNominalStructuralProjectionLaws.lean`](../../lean/Yulang/GeneralNominalStructuralProjectionLaws.lean)
- [`GeneralNominalUnaryCaptureFacts.lean`](../../lean/Yulang/GeneralNominalUnaryCaptureFacts.lean)

Changed existing files: imports appended to `lean/Yulang.lean`; 116 dependency
print commands appended to `lean/Audit.lean`; this Item 3d section appended to
`notes/design/2026-11-11-astra-general-boundary.md`. No existing implementation
module was edited. The earlier sections of this note remain unchanged.

All required commands ran from `lean/`:

| Exact command | Exit code |
| --- | --- |
| `lake build Yulang.GeneralNominalCaptureMerges Yulang.GeneralNominalMaterialization Yulang.GeneralNominalMixedCandidateExample Yulang.GeneralNominalMixedExamples Yulang.GeneralNominalMixedRecurrence Yulang.GeneralNominalNonpointInspectionExamples Yulang.GeneralNominalRecursiveBoundary Yulang.GeneralNominalRecursiveCandidates Yulang.GeneralNominalRecursiveExamples Yulang.GeneralNominalRecursiveInspection Yulang.GeneralNominalRecursivePropagation Yulang.GeneralNominalRecursiveRegressions Yulang.GeneralNominalStructuralProjectionLaws Yulang.GeneralNominalUnaryCaptureFacts > /tmp/astra-survivor-focused.log 2>&1` | 0 |
| `lake build Yulang > /tmp/astra-survivor-umbrella.log 2>&1` | 0 |
| `lake env lean Audit.lean > /tmp/astra-survivor-audit.log 2>&1` | 0 |

The focused build completed 587 jobs. The umbrella build completed 1460 jobs,
including the unchanged dictionary/emission modules. The full audit printed
9288 dependency reports, including all 116 new public theorems exactly once.
The entire dependency set was `propext`, `Classical.choice`, and `Quot.sound`.
These totals include existing results. The 116-statement inventory above was
generated with `lake env lean --stdin` (exit 0) from imports and `#check @...`
commands, with `format.width` set for readability. Earlier elaboration and
inventory-command errors were repaired before these final checks.

Append-only byte-prefix checks against HEAD passed for Yulang.lean, Audit.lean,
and the preexisting design note. New-source forbidden-token/docstring checks,
allowed-path checks, full theorem/signature/audit coverage, and whitespace
checks passed. No spec, plan, lake configuration, commit, push, or git reference
was changed. No Rust/runtime/parser checks were run; this change only adds Lean
modules and their documentation.

The `yulang-proofs` workflow was used. The skill's older rule-file names are
absent in this checkout; the current `rules/INDEX.md` and workflow map were
consulted. No registered `prover` role/configuration was available. The primary
constructed these bounded derivations; no prover agent ran. A separate read-only
reviewer inspected the initial eight modules, the corrected materialization
modes and K2 premises, then all six additions. The reviewer found no defect in
the stated new theorems and confirmed the scope limitations above. A final read-only review of this section also checked the table and scope;
its clarification that the non-point rejection uses only the list-str
declaration has been incorporated. The reviewer did not independently run the
builds or audit. Whole-language source
completeness, runtime reachability, the shared-state transition/evidence
obligations, and the full B4 result were not verified or claimed.

## Item 4 — information-adding transitions and the remaining progress gap (2026-11-12)

**Item 4 is partial, not closed.** The additions provide a persistent transition
journal over the frozen nominal context, independent model-decreasing updates,
exact child installation, pending same-input output equations, operational
closure, and a finite-basis accessibility theorem. They do **not** derive that
finite basis from Checked or finish joint applicability for merged demands.
No concrete general `SourceBoundary`, executor, or B4 proof is assembled.
`GeneralNominalSaturationBoundary` deliberately contains only separate local
and transition field packages. Its `stepModels` and `closure` have the V3 field
shapes for these packages; they are not claimed as filled fields of a faithful
completed source boundary. For that boundary, **12/12 V3 bridge obligations
remain unfilled by this work**, with reusable partial proofs for two shapes.

The existing `GeneralNominalRecursiveCandidates.Survivor`, its allocation,
projection, materialization, dictionary consumers, and all other preexisting
Lean definitions are unchanged. The evidence prover can continue to use them.

### Carrier and storage

`GeneralNominalSaturationState.State roles` wraps
`GeneralNominalCandidates.Context`. Its finite lists retain candidate packets,
source demand sites, parent/child edges, and demand aliases. A packet freezes
its exact original context, registry, checked declaration, source invocation,
and inspected interval list. `Packet.Holds` is exactly the existing
`GeneralNominalRecursiveCandidates.BranchModels`, including ordinary capture
propagation, repeated-capture merging, projection constraints, and all generated
materialization conditions. A later context replacement cannot erase those
conditions: journal `Models` conjoins the current `GeneralNominalState.Models`,
all frozen packets, and the recorded input-origin bounds.

The four vocabulary types are:

| Type | Definition | Status |
| --- | --- | --- |
| Registry | `GeneralDeclarations.Registry` | Unchanged general checked declarations. |
| State | `GeneralNominalSaturationState.State roles` | General nominal context plus persistent journal; source reachability remains a separate condition. |
| Demand | `GeneralSourceDictionaries.Occurrence roles` | Unchanged interval demand, named output obligations, and occurrence identity. |
| Model | `GeneralNominalCommonBridge.Assignment` | Unchanged full nominal carrier; no second semantic carrier. |

The wrapper is necessary because the frozen context contains no persistent
projection/materialization ledger. It is a new additive interface, not a silent
change to the state type used by the evidence work. `source_models` projects a
journal model to the old nominal model. `survivor_interface` is definitional:
local survivor calls still receive exactly `state.context`. Their adequacy with
respect to the stronger journal model needs the explicitly named
`ContextComplete` contract. `complete_consistency` proves the consistency
correspondence when this contract holds; storing a packet does not establish it.

### Thirteen source-boundary fields

All definitions below are independent of an executor. “Partial” records a
missing source correspondence or coverage obligation; it is not a scalar,
unary, or settled fragment substituted for the language.

| Field | Definition / status | Source justification and remaining obligation |
| --- | --- | --- |
| Checked | **Defined**, `GeneralDeclarations.Checked`; `localFields.Checked` also requires registry roles to equal the vocabulary roles. | §6.3 normalized declaration checks, unnamed-input Paterson counts, output-only binder rule; unchanged. |
| Models | **Defined**, `GeneralNominalSaturationState.Models`. | Draft model-decreasing propagation and §6.5 centerless intervals. Retains every installed ordinary, projection, and associated condition. Context feedback remains unproved. |
| Step | **Partial**, `GeneralNominalSaturationSteps.Step`. | Certified enqueue/install/merge/refresh updates described below; draft wait-for-known and addenda 1–4 preserved. Total normalization/materialization feedback, general nonpoint input provenance, and joint merged-demand applicability remain MISSING. |
| Stable | **Partial**, `GeneralNominalSaturationSteps.Stable`. | All generated demands satisfy independent `Registered` and `Closed` conditions. Exactly equivalent to no presently defined update. Full source saturation needs the missing Step coverage, so this is not yet final-file semantic stability. |
| Generated | **Defined for the journal**, `GeneralNominalSaturationState.Generated`; source completeness remains partial. | Reflexive/transitive recorded child closure, closed under same-input aliases, retaining original occurrences. `reachable_journal` and `generated_recorded` derive provenance for states reached from `initial`; arbitrary records are not certified source histories. |
| RootPending | **Defined**, `GeneralNominalState.RootPending`, projected through `localFields`. | Addenda 3/4: every unnamed lower head is needed; named outputs are excluded. |
| RootK2 | **Defined frozen predicate**, `GeneralNominalMixedRecurrence.RootK2`. | Reached structural root recurrence, including paths through explicit nominal arguments, never nominal bodies. The pure nominal cycle below exposes an additional source-domain/coverage issue; no definition is changed. |
| CandidateK2 | **Defined frozen predicate**, `GeneralNominalRecursiveCandidates.CandidateK2`. | §6.3 constructor inspection K2 before ambiguity; joint journal feedback remains a correspondence obligation. |
| InspectionPending | **Defined frozen predicate**, `GeneralNominalRecursiveCandidates.InspectionPending`. | Unknown inspection remains deferred. A journal-complete final classifier is not proved. |
| Survivor | **Defined frozen predicate**, `GeneralNominalRecursiveCandidates.Survivor`. | §6.3 alternatives and conjunctive children; §6.5 interval capture and cross checks. No child success is required by installation. Joint applicability of aliased requests remains MISSING. |
| Evidence | **MISSING here**, owned by the other prover. | This work defines only the output facet needed for the merge preservation theorem, not dictionary evidence. |
| Reorders | **Defined**, `GeneralRegistryReordering.Reorders`. | Identity-preserving declaration and clause permutations; unchanged. Transition order invariance is not proved. |
| DictionaryEquivalent | **Defined**, `GeneralDictionaryPayloadOrder.Equivalent`. | Existing source-identity dictionary ordering; unchanged. |

`Executor.run` remains MISSING. There is no fake completion of the four old
`GeneralNominalLocalBoundary.Remaining` fields. `transitions` stores three
partial transition signatures separately; it is not passed to `complete`.

### Updates and their exact scope

1. **Installation.** `Installable` requires the existing V3 local
   `.selected key children` result, the same actual visible checked declaration,
   exact argument localization, existing `Prepared` (including source freshness),
   a journal-consistent branch witness, completed available same-input merges,
   and agreement with already recorded choices in its alias class.
   Installation uses the existing candidate-private ordinary propagation and
   freezes the complete `BranchModels`. It records **every** emitted child and
   its deterministic invocation/clause identity. It does not test the children.
   `install_models` is an iff with the old journal models conjoined with the
   selected packet. `initial_selected_installation` proves a real first update
   for every selected candidate with a nonempty child list, not merely that a
   hypothetical update would be sound. The Display example instantiates it.
   Root-pending, root-K2, and candidate-K2 demands cannot be installed.

2. **Normalized observations.** `GeneralNominalRefinements.Refines` transports
   ordinary constraints, raw-head equations via normalized `Rewrites`, interval
   identities, descriptors and parameter endpoints, known observations, source
   reservation/ownership, constructor catalogue, and the persistent seed.
   `models` proves full-carrier model inclusion. `Refresh` also requires that
   *every* current journal model satisfies the proposed successor context,
   preserves the interpretation, and allocates no unrelated source. Its update
   requires a newly known source in the existing support. `refresh_models` is
   an iff: certified regeneration loses no journal model. This is a checked
   relation, not a total producer of snapshots. It does not yet cover all
   candidate-relevant propagation between already-known heads or automatically
   materialize newly reserved compound endpoints as source slots.

3. **Actual inputs and merging.** A `Site` separates input provenance from
   lower/upper bounds. `SameInputs` requires the same role and pointwise
   equivalence of **actual observations in every current journal model**.
   Same source IDs have a theorem; a witnessed unequal actual input vector
   rules merging out. Equal/coincident interval endpoints alone never establish
   equality between two unrelated nonpoint actual arguments. Named outputs do
   not enter this test. `outputAtoms` adds both inequalities for every equal-name
   pair of requested outputs, and `merge` records their demand alias while
   retaining both original occurrences and all their output obligations.
   It is permitted while root heads are pending. The Index regression merges
   output source 2 with source 3 while its second input remains unknown, and
   supplies an actual preserved full-carrier model.

4. **No replay without information.** Enqueue adds a missing linked demand site;
   installation requires a constraint or child edge not already entailed or
   recorded; merging requires a new alias relation; refresh requires a newly
   known source. `fresh_fact` proves a newly true persistent fact for every
   Step. This rules out merely appending duplicate equations as “progress”.

5. **Reachability.** Enqueue prevents a linked but unregistered root from being
   silently treated as finished. `Reachable` is the real Step closure from
   `initial`, and `reachable_journal` proves canonical site provenance and
   packet-backed child edges. `Generated` includes alias closure because the
   owner's rule combines demand computations; original source diagnostic
   occurrences and named obligations are retained. It does not replace a failed
   child by a root rejection.

Two review findings deliberately remain open rather than hidden by the field
package. First, current canonical emission uses `pointSite`; nonpoint children
retain unknown actual-input provenance. The earlier
`GeneralNominalEmissionOrigins` sidecar and repeated-capture correspondence
lemmas are available, but a general recursive report/materialization producer
that supplies every child's exact actual provenance is not connected here.
Arbitrary origins merely fitting a child interval are forbidden: they could
cause false merges. Second, retaining every aliased site's outputs is not yet
joint applicability. `ChoiceCompatible` guards a new installation against choices already recorded
in its current alias class; consistency after later class merges remains
unproved. The guard can also block an independently selected alias whose key
differs. A complete merged request must conjoin all named obligations
and either resolve them together or retain the proper diagnostic result. The
current `Stable` relation only closes the certified updates; it does not claim
that this missing joint computation has happened.

### Associated determination and dictionary-model preservation

`dictionary_outputs_preserved` and `merge_dictionary_models` preserve all
models whose two dictionary **output facets use one common, input-congruent
`AssociatedMeaning`**. The facet includes the actual input observations and
every requested output equation. It is explicitly not a replacement for full
dictionary Evidence. `checked_associated_equation` uses
`GeneralDeclarations.capture_determines_associated` to prove equality of realized
outputs of the **same checked declaration**, under the actual capture-agreement
and child-output interpretation premises of that theorem.

The remaining dictionary bridge must show that complete evidence for the two
merged demands supplies that common interpretation (or an equivalent shared
choice/capture argument). It cannot be dropped by citing local determination:
`GeneralNominalAssociatedDeterminationScope.overlapping_registry_checked`
checks two declarations with the same normalized input head and distinct
associated RHS patterns; `same_head_different_associated` proves that pattern
inequality. These are an overlap/checking regression, **not** a theorem that
two conflicting full dictionary Evidence witnesses exist or a theorem of
full-carrier output inequivalence. Owner semantics already require shared
same-input demand resolution; the missing joint producer/evidence proof is an
implementation obligation, not a request to choose a different merge rule.

### Progress: proved conditional result and a concrete obstruction

`finite_interval_paterson` derives strict descent of the sum of lower and upper
**finite normalized pattern** sizes directly from `DeclarationChecked`.
Only unnamed clause arguments appear, so associated-output-only binders do not
enter this measure (§6.3). Checked also provides finite declaration and clause
lists. Neither fact proves that all future capture/materialization instances
on arbitrary regular nominal states occupy a finite set of source obligations.

`FiniteBasis registry root initial` states precisely the missing finite-support
premise: a finite list of facts such that each Step reachable from the actual
initial journal makes some listed fact newly true. Facts represent recorded
sites, entailed packet constraints, generated edges, aliases, and known heads.
Every fact is monotone under Steps. `accessible_of_finite_basis` proves `Acc`
by counting the still-missing facts. There is no fuel field, no finite basis
constructed from Checked, and no claim that the requested unconditional
`progress` field is proved.

`GeneralNominalProgressObstruction` gives a nonvacuous obstruction on the
**frozen general context**, not a narrow classifier:

- One nominal source slot denotes `μ ≈ list μ`, using
  `CommonNominalFullGuardedClosure`; `state_models` proves the full model.
- `actual_self_edge` is an actual nominal argument edge; no nominal body is
  consulted. `root_not_recursive` follows from the frozen structural-root K2
  predicate.
- The singleton registry contains the checked spec Display-list declaration.
  At every invocation `selected` proves its actual general local selection,
  with the exact allocated next child demanding Display at the same source.
- `child_not_accessible` proves that the frozen V3 local child relation is not
  accessible, by induction on a putative accessibility proof.

This falsifies an unrestricted `whereAccessible` claim on the existing context
carrier with Checked alone. It does **not** prove source reachability of this
state, or disprove termination of a completed merging Step solver. A valid
source-formation restriction or a clarified observation distinction is needed
before promoting a finite-pattern descent argument to that carrier. Merely
assuming that the source-slot graph is finite does not exclude this example:
it has one slot.

### Full public theorem statements

The following inventory contains all 80 new public theorem types, printed by
Lean with all implicit parameters exposed. The transition and dictionary
premises are retained exactly; helper lemmas are included so none is promoted
by omitting a hypothesis.

```lean
Yulang.GeneralNominalAssociatedDeterminationScope.overlapping_registry_checked : Yulang.GeneralDeclarations.Checked
  Yulang.GeneralNominalAssociatedDeterminationScope.registry
Yulang.GeneralNominalAssociatedDeterminationScope.same_head_different_associated : Yulang.GeneralNominalAssociatedDeterminationScope.first.normalHead =
    Yulang.GeneralNominalAssociatedDeterminationScope.last.normalHead ∧
  Yulang.GeneralDeclarationPatterns.Pattern.subst (fun name => Yulang.GeneralDeclarationPatterns.Pattern.var name)
      (Yulang.GeneralDeclarationPatterns.normalize
        Yulang.GeneralNominalAssociatedDeterminationScope.first.associated[0].rhs) ≠
    Yulang.GeneralDeclarationPatterns.Pattern.subst (fun name => Yulang.GeneralDeclarationPatterns.Pattern.var name)
      (Yulang.GeneralDeclarationPatterns.normalize
        Yulang.GeneralNominalAssociatedDeterminationScope.last.associated[0].rhs)
Yulang.GeneralNominalDemandMerging.source_same : ∀ (models : Yulang.GeneralNominalCommonBridge.Assignment → Prop)
  (identity : Nat),
  Yulang.GeneralNominalDemandMerging.SameOrigin models (Yulang.GeneralNominalRecursiveInspection.Origin.source identity)
    (Yulang.GeneralNominalRecursiveInspection.Origin.source identity)
@Yulang.GeneralNominalDemandMerging.same_inputs_denote : ∀ {roles : Yulang.Roles.RoleDecls}
  (models : Yulang.GeneralNominalCommonBridge.Assignment → Prop)
  (first last : Yulang.GeneralNominalDemandMerging.Site roles),
  Yulang.GeneralNominalDemandMerging.SameInputs models first last →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      models model →
        ∀ (a b : List Yulang.CommonNominalFullCarrier.Ty),
          Yulang.GeneralNominalDemandMerging.Denotes model first a →
            Yulang.GeneralNominalDemandMerging.Denotes model last b →
              Yulang.GeneralNominalDemandMerging.All₂ Yulang.CommonNominalFullCarrier.Equivalent a b
@Yulang.GeneralNominalDemandMerging.different_inputs_prevent_merge : ∀ {roles : Yulang.Roles.RoleDecls}
  (models : Yulang.GeneralNominalCommonBridge.Assignment → Prop)
  (first last : Yulang.GeneralNominalDemandMerging.Site roles) (model : Yulang.GeneralNominalCommonBridge.Assignment),
  models model →
    ∀ (a b : List Yulang.CommonNominalFullCarrier.Ty),
      Yulang.GeneralNominalDemandMerging.Denotes model first a →
        Yulang.GeneralNominalDemandMerging.Denotes model last b →
          ¬Yulang.GeneralNominalDemandMerging.All₂ Yulang.CommonNominalFullCarrier.Equivalent a b →
            ¬Yulang.GeneralNominalDemandMerging.SameInputs models first last
@Yulang.GeneralNominalDemandMerging.unknown_input_prevents_merge : ∀ {roles : Yulang.Roles.RoleDecls}
  (models : Yulang.GeneralNominalCommonBridge.Assignment → Prop)
  (first last : Yulang.GeneralNominalDemandMerging.Site roles),
  none ∈ first.inputs → ¬Yulang.GeneralNominalDemandMerging.SameInputs models first last
@Yulang.GeneralNominalDemandMerging.output_atoms_exact : ∀ {roles : Yulang.Roles.RoleDecls}
  (first last : Yulang.GeneralNominalDemandMerging.Site roles) (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
      (Yulang.GeneralNominalDemandMerging.outputAtoms first last) ↔
    ∀ (a : Yulang.GeneralSourceState.Output),
      a ∈ first.occurrence.demand.outputs →
        ∀ (b : Yulang.GeneralSourceState.Output),
          b ∈ last.occurrence.demand.outputs →
            a.name = b.name → Yulang.CommonNominalFullCarrier.Equivalent (model a.target).fst (model b.target).fst
@Yulang.GeneralNominalDemandMerging.dictionary_outputs_preserved : ∀ {roles : Yulang.Roles.RoleDecls}
  (models : Yulang.GeneralNominalCommonBridge.Assignment → Prop)
  (first last : Yulang.GeneralNominalDemandMerging.Site roles),
  Yulang.GeneralNominalDemandMerging.SameInputs models first last →
    ∀ (meaning : Yulang.GeneralNominalDemandMerging.AssociatedMeaning)
      (model : Yulang.GeneralNominalCommonBridge.Assignment),
      models model →
        Yulang.GeneralNominalDemandMerging.DictionaryOutputs meaning model first →
          Yulang.GeneralNominalDemandMerging.DictionaryOutputs meaning model last →
            Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
              (Yulang.GeneralNominalDemandMerging.outputAtoms first last)
@Yulang.GeneralNominalDemandMerging.merge_preserves_dictionary_models : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalState.State) (first last : Yulang.GeneralNominalDemandMerging.Site roles),
  Yulang.GeneralNominalDemandMerging.SameInputs (Yulang.GeneralNominalState.Models state) first last →
    ∀ (meaning : Yulang.GeneralNominalDemandMerging.AssociatedMeaning)
      (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalState.Models state model →
        Yulang.GeneralNominalDemandMerging.DictionaryOutputs meaning model first →
          Yulang.GeneralNominalDemandMerging.DictionaryOutputs meaning model last →
            Yulang.GeneralNominalState.Models
              (Yulang.GeneralNominalState.extend state [] (Yulang.GeneralNominalDemandMerging.outputAtoms first last))
              model
@Yulang.GeneralNominalDemandMerging.checked_associated_equation : ∀
  {constructors : Yulang.GeneralDeclarationPatterns.Constructors} {roles : Yulang.Roles.RoleDecls}
  {declaration : Yulang.GeneralDeclarations.Declaration},
  Yulang.GeneralDeclarations.DeclarationChecked constructors roles declaration →
    ∀ (associated : Yulang.GeneralDeclarations.Associated)
      (first last : Nat → Yulang.GeneralDeclarationPatterns.Pattern),
      Yulang.GeneralDeclarations.CapturesAgree declaration first last →
        Yulang.GeneralDeclarations.SatisfiesOutputs associated declaration first →
          Yulang.GeneralDeclarations.SatisfiesOutputs associated declaration last →
            ∀ (equation : Yulang.GeneralDeclarations.Equation),
              equation ∈ declaration.associated →
                ∀ (interpret : Yulang.GeneralDeclarationPatterns.Pattern → Yulang.CommonNominalFullCarrier.Ty)
                  (model : Yulang.GeneralNominalCommonBridge.Assignment) (a b : Nat),
                  Yulang.CommonNominalFullCarrier.Equivalent (model a).fst
                      (interpret
                        (Yulang.GeneralDeclarationPatterns.Pattern.subst first
                          (Yulang.GeneralDeclarationPatterns.normalize equation.rhs))) →
                    Yulang.CommonNominalFullCarrier.Equivalent (model b).fst
                        (interpret
                          (Yulang.GeneralDeclarationPatterns.Pattern.subst last
                            (Yulang.GeneralDeclarationPatterns.normalize equation.rhs))) →
                      Yulang.CommonNominalFullCarrier.Equivalent (model a).fst (model b).fst
Yulang.GeneralNominalProgressObstruction.equation : Yulang.CommonNominalFullCarrier.Equivalent
  Yulang.GeneralNominalProgressObstruction.value
  (Yulang.CommonNominalFullCarrier.nominal 0 [Sum.inl Yulang.GeneralNominalProgressObstruction.value])
Yulang.GeneralNominalProgressObstruction.state_models : Yulang.GeneralNominalState.Models
  Yulang.GeneralNominalProgressObstruction.state Yulang.GeneralNominalProgressObstruction.model
Yulang.GeneralNominalProgressObstruction.actual_self_edge : Yulang.GeneralNominalMixedRecurrence.ActualArgument
  Yulang.GeneralNominalProgressObstruction.state 0 0
Yulang.GeneralNominalProgressObstruction.root_not_recursive : ¬Yulang.GeneralNominalMixedRecurrence.RecursAt
    Yulang.GeneralNominalProgressObstruction.state 0
Yulang.GeneralNominalProgressObstruction.registry_checked : Yulang.GeneralDeclarations.Checked
  Yulang.GeneralNominalProgressObstruction.registry
Yulang.GeneralNominalProgressObstruction.exact_children : ∀ (invocation : Nat),
  Yulang.GeneralNominalAllocation.children Yulang.GeneralNominalProgressObstruction.state
      Yulang.GeneralNominalProgressObstruction.registry (Yulang.GeneralNominalProgressObstruction.root invocation)
      Yulang.GeneralDeclarationExamples.display Yulang.GeneralDeclarationExamples.display_checked [(0, 0, 0)] =
    [Yulang.GeneralNominalProgressObstruction.root (Yulang.GeneralNominalProgressObstruction.next invocation)]
Yulang.GeneralNominalProgressObstruction.survivor : ∀ (invocation : Nat),
  Yulang.GeneralNominalRecursiveCandidates.Survivor Yulang.GeneralNominalProgressObstruction.registry
    Yulang.GeneralNominalProgressObstruction.context (Yulang.GeneralNominalProgressObstruction.root invocation) 1
    [Yulang.GeneralNominalProgressObstruction.root (Yulang.GeneralNominalProgressObstruction.next invocation)]
Yulang.GeneralNominalProgressObstruction.selected : ∀ (invocation : Nat),
  Yulang.GeneralNominalLocalBoundary.Local
    (Yulang.GeneralNominalLocalBoundary.recursiveFields Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralNominalProgressObstruction.registry Yulang.GeneralNominalProgressObstruction.context
    (Yulang.GeneralNominalProgressObstruction.root invocation)
    (Yulang.CommonRoleOutermostResolver.Frontier.selected 1
      [Yulang.GeneralNominalProgressObstruction.root (Yulang.GeneralNominalProgressObstruction.next invocation)])
Yulang.GeneralNominalProgressObstruction.child_not_accessible : ∀ (invocation : Nat),
  ¬Acc
      (Yulang.CommonRoleOutermostResolver.Child
        (Yulang.GeneralNominalLocalBoundary.Local
          (Yulang.GeneralNominalLocalBoundary.recursiveFields Yulang.GeneralDeclarationExamples.roles)
          Yulang.GeneralNominalProgressObstruction.registry Yulang.GeneralNominalProgressObstruction.context))
      (Yulang.GeneralNominalProgressObstruction.root invocation)
@Yulang.GeneralNominalRefinements.rename_kind : ∀ {first last : Nat} (embed : Fin first → Fin last)
  (parameter : Yulang.GeneralNominalState.Parameter first),
  (Yulang.GeneralNominalRefinements.renameParameter embed parameter).kind = parameter.kind
@Yulang.GeneralNominalRefinements.assignment_transport : ∀ {before after : Yulang.GeneralNominalState.State}
  (refinement : Yulang.GeneralNominalRefinements.Refines before after)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalCommonBridge.assignment after.base model ∘ refinement.base.embed =
    Yulang.GeneralNominalCommonBridge.assignment before.base model
@Yulang.GeneralNominalRefinements.fits_transport : ∀ {before after : Yulang.GeneralNominalState.State}
  (refinement : Yulang.GeneralNominalRefinements.Refines before after)
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (parameter : Yulang.GeneralNominalState.Parameter before.base.slots)
  (value : Yulang.CommonNominalFullCarrier.Argument),
  Yulang.GeneralNominalState.Fits after.base model
      (Yulang.GeneralNominalRefinements.renameParameter refinement.base.embed parameter) value ↔
    Yulang.GeneralNominalState.Fits before.base model parameter value
@Yulang.GeneralNominalRefinements.fitsAll_transport : ∀ {before after : Yulang.GeneralNominalState.State}
  (refinement : Yulang.GeneralNominalRefinements.Refines before after)
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (parameters : List (Yulang.GeneralNominalState.Parameter before.base.slots))
  (values : List Yulang.CommonNominalFullCarrier.Argument),
  Yulang.GeneralNominalState.FitsAll after.base model
      (List.map (Yulang.GeneralNominalRefinements.renameParameter refinement.base.embed) parameters) values →
    Yulang.GeneralNominalState.FitsAll before.base model parameters values
@Yulang.GeneralNominalRefinements.models : ∀ {before after : Yulang.GeneralNominalState.State}
  (refinement : Yulang.GeneralNominalRefinements.Refines before after)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models after model → Yulang.GeneralNominalState.Models before model
@Yulang.GeneralNominalRefinements.pending_backwards : ∀ {before after : Yulang.GeneralNominalState.State}
  {roles : Yulang.Roles.RoleDecls} (refinement : Yulang.GeneralNominalRefinements.Refines before after)
  (demand : Yulang.GeneralSourceState.Demand roles),
  Yulang.GeneralNominalState.RootPending after demand → Yulang.GeneralNominalState.RootPending before demand
@Yulang.GeneralNominalRefinements.sources : ∀ {before after : Yulang.GeneralNominalState.State}
  (refinement : Yulang.GeneralNominalRefinements.Refines before after) (source : Nat),
  source ∈ Yulang.GeneralNominalState.sources before → source ∈ Yulang.GeneralNominalState.sources after
@Yulang.GeneralNominalRefinements.linked : ∀ {before after : Yulang.GeneralNominalState.State}
  {roles : Yulang.Roles.RoleDecls} (refinement : Yulang.GeneralNominalRefinements.Refines before after)
  (demand : Yulang.GeneralSourceState.Demand roles),
  Yulang.GeneralNominalState.Linked before demand → Yulang.GeneralNominalState.Linked after demand
Yulang.GeneralNominalSaturationBoundary.stepModels : ∀ (roles : Yulang.Roles.RoleDecls)
  (registry : (Yulang.GeneralNominalSaturationBoundary.vocabulary roles).Registry),
  (Yulang.GeneralNominalSaturationBoundary.localFields roles).Checked registry →
    ∀ (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
      (before after : Yulang.GeneralNominalSaturationState.State roles),
      (Yulang.GeneralNominalSaturationBoundary.transitions roles).Step registry root before after →
        ∀ (model : (Yulang.GeneralNominalSaturationBoundary.vocabulary roles).Model),
          (Yulang.GeneralNominalSaturationBoundary.localFields roles).Models after model →
            (Yulang.GeneralNominalSaturationBoundary.localFields roles).Models before model
Yulang.GeneralNominalSaturationBoundary.closure : ∀ (roles : Yulang.Roles.RoleDecls)
  (registry : (Yulang.GeneralNominalSaturationBoundary.vocabulary roles).Registry),
  (Yulang.GeneralNominalSaturationBoundary.localFields roles).Checked registry →
    ∀ (state : Yulang.GeneralNominalSaturationState.State roles)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      (∀ (after : Yulang.GeneralNominalSaturationState.State roles),
          ¬(Yulang.GeneralNominalSaturationBoundary.transitions roles).Step registry root state after) →
        (Yulang.GeneralNominalSaturationBoundary.transitions roles).Stable registry state root ∧
          ∀ (child : Yulang.GeneralSourceDictionaries.Occurrence roles),
            (Yulang.GeneralNominalSaturationBoundary.transitions roles).Generated registry state root child →
              (Yulang.GeneralNominalSaturationBoundary.transitions roles).Stable registry state child
Yulang.GeneralNominalSaturationBoundary.survivor_interface : ∀ (roles : Yulang.Roles.RoleDecls)
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
  (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
  (Yulang.GeneralNominalSaturationBoundary.localFields roles).Survivor registry state root key children ↔
    Yulang.GeneralNominalRecursiveCandidates.Survivor registry state.context root key children
Yulang.GeneralNominalSaturationBoundary.source_models : ∀ (roles : Yulang.Roles.RoleDecls)
  (state : Yulang.GeneralNominalSaturationState.State roles) (model : Yulang.GeneralNominalCommonBridge.Assignment),
  (Yulang.GeneralNominalSaturationBoundary.localFields roles).Models state model →
    Yulang.GeneralNominalState.Models state.context.state model
Yulang.GeneralNominalSaturationBoundary.progress_of_basis : ∀ (roles : Yulang.Roles.RoleDecls)
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (basis : Yulang.GeneralNominalSaturationProgress.FiniteBasis registry root state),
  Acc (fun next current => (Yulang.GeneralNominalSaturationBoundary.transitions roles).Step registry root current next)
    state
Yulang.GeneralNominalSaturationExamples.display_selected : Yulang.GeneralNominalLocalBoundary.Local
  (Yulang.GeneralNominalLocalBoundary.recursiveFields Yulang.GeneralDeclarationExamples.roles)
  Yulang.GeneralNominalExamples.registry (Yulang.GeneralNominalExamples.context true)
  Yulang.GeneralNominalExamples.displayRoot
  (Yulang.CommonRoleOutermostResolver.Frontier.selected 1 [Yulang.GeneralNominalExamples.displayChild])
Yulang.GeneralNominalSaturationExamples.display_installs_all_children : ∃ packet,
  packet.registry = Yulang.GeneralNominalExamples.registry ∧
    packet.context = Yulang.GeneralNominalExamples.context true ∧
      packet.site.occurrence = Yulang.GeneralNominalExamples.displayRoot ∧
        packet.declaration.id = 1 ∧
          packet.children = [Yulang.GeneralNominalExamples.displayChild] ∧
            Yulang.GeneralNominalSaturationSteps.Step Yulang.GeneralNominalExamples.registry
              Yulang.GeneralNominalExamples.displayRoot
              (Yulang.GeneralNominalSaturationState.initial (Yulang.GeneralNominalExamples.context true)
                Yulang.GeneralNominalExamples.displayRoot)
              (Yulang.GeneralNominalSaturationState.install
                (Yulang.GeneralNominalSaturationState.initial (Yulang.GeneralNominalExamples.context true)
                  Yulang.GeneralNominalExamples.displayRoot)
                packet (Yulang.GeneralNominalSaturationState.pointEmitted packet))
Yulang.GeneralNominalSaturationExamples.pending_inputs_same : Yulang.GeneralNominalDemandMerging.SameInputs
  (Yulang.GeneralNominalSaturationState.Models Yulang.GeneralNominalSaturationExamples.pendingState)
  Yulang.GeneralNominalSaturationExamples.firstSite Yulang.GeneralNominalSaturationExamples.lastSite
Yulang.GeneralNominalSaturationExamples.pending_merge_step : ∀ (registry : Yulang.GeneralDeclarations.Registry),
  Yulang.GeneralNominalState.RootPending Yulang.GeneralNominalSaturationExamples.pendingState.context.state
      Yulang.GeneralNominalSaturationExamples.indexFirst.demand ∧
    Yulang.GeneralNominalSaturationSteps.Step registry Yulang.GeneralNominalSaturationExamples.indexFirst
      Yulang.GeneralNominalSaturationExamples.pendingState
      (Yulang.GeneralNominalSaturationState.merge Yulang.GeneralNominalSaturationExamples.pendingState
        Yulang.GeneralNominalSaturationExamples.firstSite Yulang.GeneralNominalSaturationExamples.lastSite)
Yulang.GeneralNominalSaturationExamples.pending_merge_preserves_model : Yulang.GeneralNominalSaturationState.Models
  (Yulang.GeneralNominalSaturationState.merge Yulang.GeneralNominalSaturationExamples.pendingState
    Yulang.GeneralNominalSaturationExamples.firstSite Yulang.GeneralNominalSaturationExamples.lastSite)
  Yulang.GeneralNominalSaturationExamples.indexModel
Yulang.GeneralNominalSaturationExamples.pending_merge_output_equation : ∀
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models
      (Yulang.GeneralNominalSaturationState.merge Yulang.GeneralNominalSaturationExamples.pendingState
        Yulang.GeneralNominalSaturationExamples.firstSite Yulang.GeneralNominalSaturationExamples.lastSite)
      model →
    Yulang.CommonNominalFullCarrier.Equivalent (model 2).fst (model 3).fst
@Yulang.GeneralNominalSaturationInstallation.initial_selected_installation : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
  (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
  Yulang.GeneralNominalLocalBoundary.Local (Yulang.GeneralNominalLocalBoundary.recursiveFields roles) registry context
      root (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
    children ≠ [] →
      ∃ packet,
        packet.registry = registry ∧
          packet.context = context ∧
            packet.site.occurrence = root ∧
              packet.declaration.id = key ∧
                packet.children = children ∧
                  Yulang.GeneralNominalSaturationSteps.Step registry root
                      (Yulang.GeneralNominalSaturationState.initial context root)
                      (Yulang.GeneralNominalSaturationState.install
                        (Yulang.GeneralNominalSaturationState.initial context root) packet
                        (Yulang.GeneralNominalSaturationState.pointEmitted packet)) ∧
                    (∀ (child : Yulang.GeneralSourceDictionaries.Occurrence roles),
                        child ∈ children →
                          Yulang.GeneralNominalSaturationState.Generated
                            (Yulang.GeneralNominalSaturationState.install
                              (Yulang.GeneralNominalSaturationState.initial context root) packet
                              (Yulang.GeneralNominalSaturationState.pointEmitted packet))
                            root child) ∧
                      ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                        Yulang.GeneralNominalSaturationState.Models
                            (Yulang.GeneralNominalSaturationState.install
                              (Yulang.GeneralNominalSaturationState.initial context root) packet
                              (Yulang.GeneralNominalSaturationState.pointEmitted packet))
                            model ↔
                          Yulang.GeneralNominalState.Models context.state model ∧ packet.Holds model
@Yulang.GeneralNominalSaturationInvariants.canonical_update : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSaturationState.State roles},
  Yulang.GeneralNominalSaturationInvariants.Canonical before →
    Yulang.GeneralNominalSaturationSteps.At registry before focus after →
      Yulang.GeneralNominalSaturationInvariants.Canonical after
@Yulang.GeneralNominalSaturationInvariants.edges_update : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSaturationState.State roles},
  Yulang.GeneralNominalSaturationInvariants.EdgesRecorded before →
    Yulang.GeneralNominalSaturationSteps.At registry before focus after →
      Yulang.GeneralNominalSaturationInvariants.EdgesRecorded after
@Yulang.GeneralNominalSaturationInvariants.reachable_journal : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {context : Yulang.GeneralNominalCandidates.Context}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles} {state : Yulang.GeneralNominalSaturationState.State roles},
  Yulang.GeneralNominalSaturationInvariants.Reachable registry context root state →
    Yulang.GeneralNominalSaturationInvariants.Canonical state ∧
      Yulang.GeneralNominalSaturationInvariants.EdgesRecorded state ∧
        ∃ site, site ∈ state.sites ∧ site.occurrence = root
@Yulang.GeneralNominalSaturationInvariants.generated_recorded : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {context : Yulang.GeneralNominalCandidates.Context}
  {root child : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {state : Yulang.GeneralNominalSaturationState.State roles},
  Yulang.GeneralNominalSaturationInvariants.Reachable registry context root state →
    Yulang.GeneralNominalSaturationState.Generated state root child →
      ∃ site, site ∈ state.sites ∧ site.occurrence = child
@Yulang.GeneralNominalSaturationInvariants.merged_outputs_retained : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (first last : Yulang.GeneralNominalDemandMerging.Site roles),
  first ∈ state.sites →
    last ∈ state.sites →
      first ∈ (Yulang.GeneralNominalSaturationState.merge state first last).sites ∧
        last ∈ (Yulang.GeneralNominalSaturationState.merge state first last).sites
@Yulang.GeneralNominalSaturationInvariants.complete_consistency : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles),
  Yulang.GeneralNominalSaturationState.ContextComplete state →
    ∀ (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
      (declaration : Yulang.GeneralDeclarations.Declaration)
      (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
      (bounds : List (Yulang.GeneralNominalInspection.Bounds state.context.state)),
      Yulang.GeneralNominalRecursiveCandidates.Consistent registry state.context root declaration checked bounds ↔
        ∃ model,
          Yulang.GeneralNominalSaturationState.Models state model ∧
            Yulang.GeneralNominalRecursiveCandidates.BranchModels registry state.context root declaration checked bounds
              model
@Yulang.GeneralNominalSaturationProgress.monotone : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralNominalSaturationState.State roles},
  Yulang.GeneralNominalSaturationSteps.Extends before after →
    ∀ (fact : Yulang.GeneralNominalSaturationProgress.Fact roles),
      Yulang.GeneralNominalSaturationProgress.Holds before fact →
        Yulang.GeneralNominalSaturationProgress.Holds after fact
@Yulang.GeneralNominalSaturationProgress.fresh_fact : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralNominalSaturationState.State roles} {registry : Yulang.GeneralDeclarations.Registry}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalSaturationSteps.Step registry root before after →
    ∃ fact,
      ¬Yulang.GeneralNominalSaturationProgress.Holds before fact ∧
        Yulang.GeneralNominalSaturationProgress.Holds after fact
@Yulang.GeneralNominalSaturationProgress.remaining_monotone : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralNominalSaturationState.State roles}
  (facts : List (Yulang.GeneralNominalSaturationProgress.Fact roles)),
  Yulang.GeneralNominalSaturationSteps.Extends before after →
    Yulang.GeneralNominalSaturationProgress.remaining facts after ≤
      Yulang.GeneralNominalSaturationProgress.remaining facts before
@Yulang.GeneralNominalSaturationProgress.remaining_decreases : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralNominalSaturationState.State roles}
  (facts : List (Yulang.GeneralNominalSaturationProgress.Fact roles)),
  Yulang.GeneralNominalSaturationSteps.Extends before after →
    ∀ (fact : Yulang.GeneralNominalSaturationProgress.Fact roles),
      fact ∈ facts →
        ¬Yulang.GeneralNominalSaturationProgress.Holds before fact →
          Yulang.GeneralNominalSaturationProgress.Holds after fact →
            Yulang.GeneralNominalSaturationProgress.remaining facts after <
              Yulang.GeneralNominalSaturationProgress.remaining facts before
@Yulang.GeneralNominalSaturationProgress.accessible_of_finite_basis : ∀ {roles : Yulang.Roles.RoleDecls}
  {start : Yulang.GeneralNominalSaturationState.State roles} {registry : Yulang.GeneralDeclarations.Registry}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  (basis : Yulang.GeneralNominalSaturationProgress.FiniteBasis registry root start),
  Acc (fun next current => Yulang.GeneralNominalSaturationSteps.Step registry root current next) start
@Yulang.GeneralNominalSaturationProgress.finite_interval_paterson : ∀ {roles : Yulang.Roles.RoleDecls}
  {constructors : Yulang.GeneralDeclarationPatterns.Constructors}
  {declaration : Yulang.GeneralDeclarations.Declaration},
  Yulang.GeneralDeclarations.DeclarationChecked constructors roles declaration →
    ∀ (clause : Yulang.GeneralDeclarations.Clause),
      clause ∈ declaration.requirements →
        ∀ (lower upper : Nat → Yulang.GeneralDeclarationPatterns.Pattern),
          Yulang.Roles.argsSize
                (Yulang.GeneralDeclarationPatterns.counted
                  (Yulang.GeneralDeclarationPatterns.substArgs lower clause.arguments)) +
              Yulang.Roles.argsSize
                (Yulang.GeneralDeclarationPatterns.counted
                  (Yulang.GeneralDeclarationPatterns.substArgs upper clause.arguments)) <
            Yulang.Roles.argsSize
                (Yulang.GeneralDeclarationPatterns.counted
                  (Yulang.GeneralDeclarationPatterns.substArgs lower declaration.head)) +
              Yulang.Roles.argsSize
                (Yulang.GeneralDeclarationPatterns.counted
                  (Yulang.GeneralDeclarationPatterns.substArgs upper declaration.head))
@Yulang.GeneralNominalSaturationState.point_holds : ∀ {roles : Yulang.Roles.RoleDecls}
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.SiteHolds (Yulang.GeneralNominalDemandMerging.pointSite root) model
@Yulang.GeneralNominalSaturationState.Emitted.exact : ∀ {roles : Yulang.Roles.RoleDecls}
  {packet : Yulang.GeneralNominalSaturationState.Packet roles}
  (emitted : Yulang.GeneralNominalSaturationState.Emitted packet),
  List.map Yulang.GeneralNominalDemandMerging.Site.occurrence emitted.sites = packet.children
@Yulang.GeneralNominalSaturationState.Emitted.sound : ∀ {roles : Yulang.Roles.RoleDecls}
  {packet : Yulang.GeneralNominalSaturationState.Packet roles}
  (emitted : Yulang.GeneralNominalSaturationState.Emitted packet)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  packet.Holds model →
    ∀ (site : Yulang.GeneralNominalDemandMerging.Site roles),
      site ∈ emitted.sites → Yulang.GeneralNominalSaturationState.SiteHolds site model
@Yulang.GeneralNominalSaturationState.initial_models : ∀ {roles : Yulang.Roles.RoleDecls}
  (context : Yulang.GeneralNominalCandidates.Context) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralNominalSaturationState.initial context root) model ↔
    Yulang.GeneralNominalState.Models context.state model
@Yulang.GeneralNominalSaturationState.generated_trans : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles}
  {root middle child : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalSaturationState.Generated state root middle →
    Yulang.GeneralNominalSaturationState.Generated state middle child →
      Yulang.GeneralNominalSaturationState.Generated state root child
@Yulang.GeneralNominalSaturationState.enqueue_models : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralNominalSaturationState.enqueue state root) model ↔
    Yulang.GeneralNominalSaturationState.Models state model
@Yulang.GeneralNominalSaturationState.context_complete_models : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles),
  Yulang.GeneralNominalSaturationState.ContextComplete state →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models state model ↔
        Yulang.GeneralNominalState.Models state.context.state model
@Yulang.GeneralNominalSaturationState.install_models : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (packet : Yulang.GeneralNominalSaturationState.Packet roles)
  (emitted : Yulang.GeneralNominalSaturationState.Emitted packet),
  packet.context = state.context →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralNominalSaturationState.install state packet emitted)
          model ↔
        Yulang.GeneralNominalSaturationState.Models state model ∧ packet.Holds model
@Yulang.GeneralNominalSaturationState.merge_models : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (first last : Yulang.GeneralNominalDemandMerging.Site roles) (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralNominalSaturationState.merge state first last) model ↔
    Yulang.GeneralNominalSaturationState.Models state model ∧
      Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
        (Yulang.GeneralNominalDemandMerging.outputAtoms first last)
@Yulang.GeneralNominalSaturationState.merge_dictionary_models : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (first last : Yulang.GeneralNominalDemandMerging.Site roles),
  Yulang.GeneralNominalDemandMerging.SameInputs (Yulang.GeneralNominalSaturationState.Models state) first last →
    ∀ (meaning : Yulang.GeneralNominalDemandMerging.AssociatedMeaning)
      (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models state model →
        Yulang.GeneralNominalDemandMerging.DictionaryOutputs meaning model first →
          Yulang.GeneralNominalDemandMerging.DictionaryOutputs meaning model last →
            Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralNominalSaturationState.merge state first last)
              model
@Yulang.GeneralNominalSaturationSteps.refresh_models : ∀ {roles : Yulang.Roles.RoleDecls}
  {before : Yulang.GeneralNominalSaturationState.State roles} {context : Yulang.GeneralNominalCandidates.Context}
  (certificate : Yulang.GeneralNominalSaturationSteps.Refresh before context)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralNominalSaturationState.regenerate before context) model ↔
    Yulang.GeneralNominalSaturationState.Models before model
@Yulang.GeneralNominalSaturationSteps.at_extends : ∀ {registry : Yulang.GeneralDeclarations.Registry}
  {roles : Yulang.Roles.RoleDecls} {before : Yulang.GeneralNominalSaturationState.State roles}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {after : Yulang.GeneralNominalSaturationState.State roles},
  Yulang.GeneralNominalSaturationSteps.At registry before focus after →
    Yulang.GeneralNominalSaturationSteps.Extends before after
@Yulang.GeneralNominalSaturationSteps.step_extends : ∀ {registry : Yulang.GeneralDeclarations.Registry}
  {roles : Yulang.Roles.RoleDecls} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSaturationState.State roles},
  Yulang.GeneralNominalSaturationSteps.Step registry root before after →
    Yulang.GeneralNominalSaturationSteps.Extends before after
@Yulang.GeneralNominalSaturationSteps.step_models : ∀ {registry : Yulang.GeneralDeclarations.Registry}
  {roles : Yulang.Roles.RoleDecls} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSaturationState.State roles},
  Yulang.GeneralNominalSaturationSteps.Step registry root before after →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models after model → Yulang.GeneralNominalSaturationState.Models before model
@Yulang.GeneralNominalSaturationSteps.alias_monotone : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralNominalSaturationState.State roles} {first last : Nat},
  Yulang.GeneralNominalSaturationSteps.Extends before after →
    Yulang.GeneralNominalSaturationState.Alias before first last →
      Yulang.GeneralNominalSaturationState.Alias after first last
@Yulang.GeneralNominalSaturationSteps.generated_monotone : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralNominalSaturationState.State roles}
  {root child : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalSaturationSteps.Extends before after →
    Yulang.GeneralNominalSaturationState.Generated before root child →
      Yulang.GeneralNominalSaturationState.Generated after root child
@Yulang.GeneralNominalSaturationSteps.installed_committed : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (packet : Yulang.GeneralNominalSaturationState.Packet roles)
  (emitted : Yulang.GeneralNominalSaturationState.Emitted packet),
  Yulang.GeneralNominalSaturationSteps.Committed (Yulang.GeneralNominalSaturationState.install state packet emitted)
    packet
@Yulang.GeneralNominalSaturationSteps.installed_children : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (packet : Yulang.GeneralNominalSaturationState.Packet roles)
  (emitted : Yulang.GeneralNominalSaturationState.Emitted packet)
  (child : Yulang.GeneralSourceDictionaries.Occurrence roles),
  child ∈ packet.children →
    Yulang.GeneralNominalSaturationState.Generated (Yulang.GeneralNominalSaturationState.install state packet emitted)
      packet.site.occurrence child
@Yulang.GeneralNominalSaturationSteps.merged_inputs : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (first last : Yulang.GeneralNominalDemandMerging.Site roles),
  Yulang.GeneralNominalSaturationState.Alias (Yulang.GeneralNominalSaturationState.merge state first last)
    first.occurrence.identity last.occurrence.identity
@Yulang.GeneralNominalSaturationSteps.replay_does_not_add_information : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (packet : Yulang.GeneralNominalSaturationState.Packet roles),
  Yulang.GeneralNominalSaturationSteps.Committed state packet →
    ¬(Yulang.GeneralNominalSaturationSteps.Installable registry state packet ∧
        ¬Yulang.GeneralNominalSaturationSteps.Committed state packet)
@Yulang.GeneralNominalSaturationSteps.pending_never_installed : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (packet : Yulang.GeneralNominalSaturationState.Packet roles),
  Yulang.GeneralNominalState.RootPending state.context.state packet.site.occurrence.demand →
    ¬Yulang.GeneralNominalSaturationSteps.Installable registry state packet
@Yulang.GeneralNominalSaturationSteps.rootK2_never_installed : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (packet : Yulang.GeneralNominalSaturationState.Packet roles),
  Yulang.GeneralNominalMixedRecurrence.RootK2 state.context.state packet.site.occurrence.demand →
    ¬Yulang.GeneralNominalSaturationSteps.Installable registry state packet
@Yulang.GeneralNominalSaturationSteps.candidateK2_never_installed : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (packet : Yulang.GeneralNominalSaturationState.Packet roles),
  Yulang.GeneralNominalRecursiveCandidates.CandidateK2 registry state.context packet.site.occurrence →
    ¬Yulang.GeneralNominalSaturationSteps.Installable registry state packet
@Yulang.GeneralNominalSaturationSteps.closed_iff_no_update : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles} {focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {registry : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralNominalSaturationSteps.Registered state focus ∧
      Yulang.GeneralNominalSaturationSteps.Closed registry state focus ↔
    ∀ (after : Yulang.GeneralNominalSaturationState.State roles),
      ¬Yulang.GeneralNominalSaturationSteps.At registry state focus after
@Yulang.GeneralNominalSaturationSteps.halted_stable : ∀ {registry : Yulang.GeneralDeclarations.Registry}
  {roles : Yulang.Roles.RoleDecls} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {state : Yulang.GeneralNominalSaturationState.State roles},
  (∀ (after : Yulang.GeneralNominalSaturationState.State roles),
      ¬Yulang.GeneralNominalSaturationSteps.Step registry root state after) →
    Yulang.GeneralNominalSaturationSteps.Stable registry state root
@Yulang.GeneralNominalSaturationSteps.stable_generated : ∀ {registry : Yulang.GeneralDeclarations.Registry}
  {roles : Yulang.Roles.RoleDecls} {state : Yulang.GeneralNominalSaturationState.State roles}
  {root child : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalSaturationSteps.Stable registry state root →
    Yulang.GeneralNominalSaturationState.Generated state root child →
      Yulang.GeneralNominalSaturationSteps.Stable registry state child
@Yulang.GeneralNominalSaturationSteps.stable_halted : ∀ {registry : Yulang.GeneralDeclarations.Registry}
  {roles : Yulang.Roles.RoleDecls} {state : Yulang.GeneralNominalSaturationState.State roles}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalSaturationSteps.Stable registry state root →
    ∀ (after : Yulang.GeneralNominalSaturationState.State roles),
      ¬Yulang.GeneralNominalSaturationSteps.Step registry root state after
@Yulang.GeneralNominalSaturationSteps.halted_closure : ∀ {registry : Yulang.GeneralDeclarations.Registry}
  {roles : Yulang.Roles.RoleDecls} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {state : Yulang.GeneralNominalSaturationState.State roles},
  (∀ (after : Yulang.GeneralNominalSaturationState.State roles),
      ¬Yulang.GeneralNominalSaturationSteps.Step registry root state after) →
    Yulang.GeneralNominalSaturationSteps.Stable registry state root ∧
      ∀ (child : Yulang.GeneralSourceDictionaries.Occurrence roles),
        Yulang.GeneralNominalSaturationState.Generated state root child →
          Yulang.GeneralNominalSaturationSteps.Stable registry state child
@Yulang.GeneralNominalSaturationSteps.steps_models : ∀ {registry : Yulang.GeneralDeclarations.Registry}
  {roles : Yulang.Roles.RoleDecls} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSaturationState.State roles},
  Yulang.B4Target.Steps (Yulang.GeneralNominalSaturationSteps.Step registry root) before after →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models after model → Yulang.GeneralNominalSaturationState.Models before model
```

### Files, verification, and unverified obligations

Added modules:

- [`GeneralNominalAssociatedDeterminationScope.lean`](../../lean/Yulang/GeneralNominalAssociatedDeterminationScope.lean)
- [`GeneralNominalDemandMerging.lean`](../../lean/Yulang/GeneralNominalDemandMerging.lean)
- [`GeneralNominalProgressObstruction.lean`](../../lean/Yulang/GeneralNominalProgressObstruction.lean)
- [`GeneralNominalRefinements.lean`](../../lean/Yulang/GeneralNominalRefinements.lean)
- [`GeneralNominalSaturationBoundary.lean`](../../lean/Yulang/GeneralNominalSaturationBoundary.lean)
- [`GeneralNominalSaturationExamples.lean`](../../lean/Yulang/GeneralNominalSaturationExamples.lean)
- [`GeneralNominalSaturationInstallation.lean`](../../lean/Yulang/GeneralNominalSaturationInstallation.lean)
- [`GeneralNominalSaturationInvariants.lean`](../../lean/Yulang/GeneralNominalSaturationInvariants.lean)
- [`GeneralNominalSaturationProgress.lean`](../../lean/Yulang/GeneralNominalSaturationProgress.lean)
- [`GeneralNominalSaturationState.lean`](../../lean/Yulang/GeneralNominalSaturationState.lean)
- [`GeneralNominalSaturationSteps.lean`](../../lean/Yulang/GeneralNominalSaturationSteps.lean)

Changed existing files: appended 11 imports to `lean/Yulang.lean`, appended
80 public-theorem dependency print commands to `lean/Audit.lean`, and appended
this Item 4 section to the design note. All three preserve their HEAD byte
prefixes. No existing implementation module, spec, plan, configuration, commit,
push, or git reference was changed.

The exact final verification commands, run from `lean/`, were:

```sh
lake build Yulang.GeneralNominalAssociatedDeterminationScope Yulang.GeneralNominalDemandMerging Yulang.GeneralNominalProgressObstruction Yulang.GeneralNominalRefinements Yulang.GeneralNominalSaturationBoundary Yulang.GeneralNominalSaturationExamples Yulang.GeneralNominalSaturationInstallation Yulang.GeneralNominalSaturationInvariants Yulang.GeneralNominalSaturationProgress Yulang.GeneralNominalSaturationState Yulang.GeneralNominalSaturationSteps > /tmp/astra-step-focused.log 2>&1
lake build Yulang > /tmp/astra-step-umbrella.log 2>&1
lake env lean Audit.lean > /tmp/astra-step-audit.log 2>&1
```

Each command exited **0**. Focused build: 594 jobs. Umbrella: 1471 jobs,
including the unchanged dictionary consumers and previous interval/K2
regressions. Full audit: 9368 dependency reports, all 80 new public theorems
exactly once; the entire dependency set was `propext`, `Classical.choice`, and
`Quot.sound`. Signature extraction with
`lake env lean /tmp/astra-step-signatures.lean > /tmp/astra-step-signatures.txt 2>&1`
exited 0. New-source token, docstring-start, whitespace, path, import/signature/
public-theorem coverage, append-only checks, and `git diff --check` passed.
Earlier elaboration errors and two commands launched from the wrong directory
were corrected before these final checks; they are not counted as successful
verification. Available disk space at the final check was 581 GiB.

The `yulang-proofs` skill was applied. Its older referenced rule files and a
registered custom `prover` configuration were unavailable; the current rule
map was consulted. The primary constructed the bounded derivations directly;
no prover agent ran. A separate read-only reviewer inspected the transition
rules, found the arbitrary-fitting-origin and lost-output hazards, reviewed
their conservative fixes, inspected the nominal-cycle proof, and checked the
scope report. Its final corrections concerning later class merges and the
§6.5 interval citation are incorporated. The reviewer did not rerun the builds
or audit.

Not verified or claimed: source reachability of the nominal cycle; exclusion
of such cycles by a source-formation theorem; general nonpoint/compound child
origin production; total snapshot regeneration and source-slot materialization;
joint merged-demand applicability and completion of every named obligation;
global Evidence-to-common-output-meaning correspondence; Step termination from
Checked; V3 where accessibility, execution, and the complete B4 statement;
transition order independence; Rust/parser/runtime behavior. No test of the
illustrative source program below was performed.

The work is converging on the real carrier in a specific sense: the new updates
use the same checked declarations, deterministic occurrence allocation,
recursive interval/projection reports, and materialization conditions as the
unchanged Survivor and dictionary work. Display installation and pending Index
merging have non-placeholder general-model proofs. It has not converged to
termination yet. Finite-pattern Paterson and fragment termination results do
not supply the missing source-domain or feedback premises; the one-slot nominal
cycle is concrete evidence of that distinction.

### Source-formation question (lazy option first)

The unresolved question is narrower than the already answered mixed record/list
case. Consider the illustrative source shape:

```yulang
my nest(n) = [nest n]
impl Display (list 'a): where 'a: Display
display (nest 0)
```

If inference can produce the anonymous equation `μ ≈ list μ`, the current
nominal context represents it without reading any nominal body. Its reached
head is always nominal, so the existing structural-root K2 predicate does not
reject it. The Lean obstruction above does not assume that this illustrative
program actually generates that state.

1. **Defer promotion until source formation is certified.** Keep the general
   saturation/finite-dictionary result open for such snapshots, and supply a
   source-formation proof that excludes them or identifies the observation at
   which the existing anonymous-recursion rule applies. This is the option
   retained by this development: the completed boundary is not constructed.
2. **Clarify an anonymous recurrence observation for nominal argument cycles.**
   If such source equations are intended to be possible, specify how their
   reached anonymous root is distinguished from the permitted outer `list μ`
   in `len [loop 1]`, while leaving all nominal bodies opaque. Implement that
   distinction additively before attempting unconditional accessibility.

This note does not declare the program legal or illegal, change the K2 rules,
or treat the independent nominal carrier as proof of source reachability.
The pending question is the source-domain/observation bridge needed by the
termination theorem; the owner's same-input merge rule remains settled.

### Owner answer to the source-formation question (2026-11-12): cycle-based K2

The owner chose a clarified observation (close to option 2 of the Item 4 question, and correcting the supervisor's earlier mixed-recurrence answer): K2 is decided on the type graph by whether the **root (or a position a non-variable head pattern inspects) lies on a cycle**. Cycles may pass through nominal *arguments*; nominal bodies stay opaque (named recursion through bodies stays exempt). `nest 0 : μ ≈ list μ` has its root on a cycle, so `display (nest 0)` and `len (nest 0)` are both rejected (even though `impl Len (list 'a)` has no where clause). `len [loop 1] : list ν` has its root off the cycle (it only enters ν's cycle below), so it passes as before. Recorded in spec/06-roles.md (K2 decisions, 2026-11-12). The supervisor's earlier answer ("`list μ` is never a K2 root") is superseded where the `list` node itself lies on a cycle.

## Item 4b — cycle-based K2 and the remaining progress bridge (2026-11-12)

This section supersedes the Item 4 source-formation question with the owner's
answer above. It adds a cycle-based local package and transition relation without
changing any earlier implementation definition. The old nominal self-cycle is
now rejected; its infinite child chain cannot be entered by the new local or
Step relation. **General Step accessibility from Checked alone is still not
proved.** The new finite-support result is for a fixed snapshot and has an
explicit finite-pattern readback premise. It is not a replacement name for the
unconditional B4 termination clause.

### Source authority and the graph being observed

The controlling rule is [spec §6.3/K2, the 2026-11-12 decision](../../spec/06-roles.md):
a reached root, or a position inspected by a non-variable head pattern, rejects
when that position lies on a cycle. Explicit nominal arguments contribute edges;
nominal bodies do not. This differs from asking whether any descendant is cyclic,
or whether the whole denotation has a finite nonrecursive representative. The
readiness gates follow the [approved draft and addenda 1–4](2026-11-08-b4-main-statement-draft.md).
The V3 priority is preserved: root pending first; either K2 reason before
inspection pending and ambiguity; empty-candidate rejection only after inspection
has finished. Children remain a conjunction in the outer diagnostic tree.

`GeneralNominalCycleK2` uses the existing normalized structural `Child` relation
and `GeneralNominalMixedRecurrence.ActualArgument`. It removes the old
structural-root restriction. There are two certificate paths:

- `DirectCycle` follows normalized structural children and explicitly recorded
  point nominal arguments. These are source graph identities and require no
  model witness, even when the ordinary store is inconsistent.
- The general `Cycle` follows structural children and semantic actual-argument
  edges. The latter quantify over source Models and must identify the actual
  argument with a represented slot. `RecursAt` requires a model witness for this
  second path, so an empty model set cannot create a cycle by universal
  quantification alone. `recurs_iff_cycle` proves exact agreement with this graph
  whenever a model is supplied. This is a statement about this observation
  graph, not every possible graph representation of the denotation.

`GeneralNominalCycleEdges.nominal_interval_edge` now derives actual edges for
nonpoint nominal intervals: the lower and upper slot identities may differ.
The existing invariant nominal sandwich law identifies the actual argument
with both endpoints. Both endpoints must have recorded nominal descriptors;
the theorem does not treat mere interval overlap as argument identity. This
reuses the full nominal carrier and its interval laws, without opening bodies
or conducting substitution search.

General observation coverage is still missing. In particular, not every actual
projection necessarily has an equivalent represented source slot. The theorem
above does not cover arbitrary structural bounds, row parameters, or all alias
normalizations. A new `InspectionPending` retains the old pending condition and
additionally defers recognized legacy structural-equivalence K2 observations
when no new cycle certificate exists. `alias_observation_defers` proves the
root case. This fallback does **not** establish that every absent cycle
certificate has been detected and deferred. The local package must therefore
not be promoted to a fully faithful general boundary yet. Existing deferred
constructor-layout paths remain unchanged.

### Thirteen-field ledger

All names in this table are in namespace `Yulang`. None is defined through an
executor. “Defined” means the indicated relation exists with the stated scope;
a remaining correspondence is marked explicitly. No scalar or unary carrier
is substituted for a general field.

| SourceBoundary field | Concrete definition in this additive package | Status and remaining scope |
|---|---|---|
| Checked | `GeneralNominalCycleBoundary.localFields.Checked`, using `GeneralDeclarations.Checked` and registry/role agreement | Defined, unchanged. Normalization, capture-stable Paterson descent, and output-only binder checks remain in the general declaration carrier (§6.3). |
| Models | `GeneralNominalSaturationState.Models` | Defined, unchanged full nominal source model plus packet and merged-site constraints. `CycleSteps.step_models` and `steps_models` prove model inclusion. |
| Step | `GeneralNominalCycleSteps.Step` | Defined certified updates, using the new K2 rules and a joint installation guard. MISSING: complete joint local classification, total feedback/materialization and general progress. |
| Stable | `GeneralNominalCycleSteps.Stable` | Defined as closure under these certified updates at the root and every generated demand. MISSING: correspondence with complete source saturation. |
| Generated | `GeneralNominalSaturationState.Generated` | Defined, unchanged reflexive-transitive emitted-child and alias closure; monotone under the new Step. |
| RootPending | `GeneralNominalState.RootPending` on `state.context.state` | Defined, unchanged: every unnamed lower head is needed; named outputs are excluded (addenda 3–4). |
| RootK2 | `GeneralNominalCycleK2.RootK2` | Defined on linked, ready normalized observations, with no structural-root restriction. MISSING: complete source-to-observation cycle coverage. |
| CandidateK2 | `GeneralNominalCycleK2.CandidateK2` | Defined at the existing recursive report's inspected constructor positions, with HeadReady and root-readiness gates. No inspection-pending gate. Same observation-coverage gap. |
| InspectionPending | `GeneralNominalCycleK2.InspectionPending` | Defined old conservative inspection plus recognized legacy recurrence fallback. MISSING: total detection of unsupported cycle observations. |
| Survivor | `GeneralNominalRecursiveCandidates.Survivor` | Defined, interface unchanged for the Evidence prover. `GeneralNominalJointCandidates.Survivor` is an additional journal-aware condition, not a replacement field. Complete merged-demand classification remains MISSING. |
| Evidence | Not supplied by `GeneralNominalCycleBoundary` | MISSING in this package; separate prover's dictionary work is unchanged. No surrogate Evidence predicate is installed. |
| Reorders | `GeneralRegistryReordering.Reorders` | Defined and reused unchanged; no transition-confluence theorem added. |
| DictionaryEquivalent | `GeneralDictionaryPayloadOrder.Equivalent` | Defined and reused unchanged; this turn does not prove the complete B4 dictionary clause. |

`GeneralNominalCycleBoundary.vocabulary` reuses the Item 4 vocabulary:
`GeneralDeclarations.Registry`, `GeneralNominalSaturationState.State roles`,
`GeneralSourceDictionaries.Occurrence roles`, and
`GeneralNominalCommonBridge.Assignment`. The journal contains the same shared
`GeneralNominalCandidates.Context`; there is no new parallel type model.
`localFields` and `transitions` remain separate partial packages. No
`SourceBoundary`, `Executor.run`, or complete `B4Bridges` value is manufactured.
The exact V3-shaped `stepModels` and `closure` statements are proved for these
packages. `whereAccessible_of_readback` has the extra premise described below;
general `progress` remains MISSING.

### Regressions and progress results

`GeneralNominalCycleRegressions` proves the following with the new predicates:

- The structural loop is RootK2; the normalized shadow example is not RootK2;
  Index remains root pending and is not RootK2.
- `GeneralNominalProgressObstruction`'s μ ≈ list μ is RootK2 for every invocation;
  both Display and Len are rejected. The constructor inspection also establishes
  CandidateK2. The corresponding new child relation is accessible at that root.
- A new, nonempty-model wrapper fixture has ν ≈ {next: ν} at slot 0 and a
  separate `list ν` at slot 1. Every actual outgoing graph edge targets slot 0;
  slot 1 is off-cycle. Len has its real survivor and is selected with no children.
- The earlier mixed fixture has ν ≈ {next: list ν}, where the list node returns
  to ν. Both nodes lie on that cycle. `mixed_list_root_K2` proves that its list
  root now rejects. Its historical old-predicate theorems are left intact and
  are not asserted under the new definition.

`GeneralNominalCycleHalting.obstruction_step_accessible` also proves actual
Step accessibility, not just local rejection, for the initialized old
counterexample. `cycle_initial_halted` checks enqueue/install/merge/refresh:
installation is prohibited by K2, the initial site is already registered, the
singleton class has no new merge, and all supported sources are known so there
is no refresh. The more general initial-halting theorem states that last
known-source premise explicitly. It is not an accessibility theorem for every
state with a rejected root.

`GeneralNominalCycleDescent` derives a graph rank from the finite slot carrier.
Cut off outgoing edges at nodes lying on cycles, enumerate reachable slots, and
count them. Every retained edge strictly decreases that count, which is bounded
by `state.base.slots`; `cut_accessible` follows. The new
`root_edge_decreases` and `inspected_edge_decreases` connect that rank to ready
non-K2 roots and clear candidate-inspected positions, respectively, with an
explicit model for the semantic-edge interpretation. No supplied fuel, depth
limit, or finite-support list occurs in these theorems.

A root off-cycle may still have cyclic descendants: the permitted wrapper is
an explicit example. The useful finite abstraction treats those descendants as
opaque leaves until inspection or a where child reaches them. It would be
incorrect to infer whole-denotation finite-tree equivalence from ¬RootK2.

The separate `GeneralNominalCycleReadback.Readback` premise supplies finite
lower/upper pattern labels for actual demands and ties each selected child to
its actual declaration key, role, located bounds, canonical emitted list, and
clause identity. It additionally requires both parent and child labels to be
instances of that declaration's head and unnamed clause arguments under shared
substitutions. Its exact fields are:

```lean
structure Readback (roles : Roles.RoleDecls) (registry : Registry) (context : GeneralNominalCandidates.Context) where
  lower : Occurrence roles → List Pattern
  upper : Occurrence roles → List Pattern
  selected : ∀ parent key children, Local registry context parent (.selected key children) →
    ∀ child ∈ children, ∃ declaration ∈ registry.declarations,
      ∃ checked : DeclarationChecked registry.constructors roles declaration,
        declaration.id = key ∧ declaration.role = parent.demand.role ∧
      ∃ bounds, GeneralNominalRecursiveCandidates.arguments context parent = some bounds ∧
        child ∈ GeneralNominalAllocation.children context.state registry parent declaration checked
          (GeneralNominalRecursiveInspection.bindings context.state
            (GeneralNominalRecursiveCandidates.report context declaration bounds)) ∧
      ∃ clause ∈ declaration.requirements,
        child.identity = GeneralNominalAllocation.source context.state registry parent.identity
          (GeneralNominalAllocation.origin parent.identity declaration.id 6 clause.id 0) ∧
      ∃ lo hi : Nat → Pattern,
        lower parent = substArgs lo declaration.head ∧ upper parent = substArgs hi declaration.head ∧
        lower child = substArgs lo clause.arguments ∧ upper child = substArgs hi clause.arguments
```

Checked supplies capture-stable strict descent for each such substitution;
`child_decreases` adds the lower and upper sizes, counting only unnamed clause
inputs. The associated output-only binders do not enter that count (§6.3,
2026-11-12 output-only rule). `whereAccessible` then follows. The readback has
no supplied rank or accessibility field, but it is still a substantial
unproved source bridge: the finite labels have not been shown to denote the
actual captures, and no general producer derives them from K2 exclusion.
Consequently this conditional result cannot be reported as closing the target.

`GeneralNominalCycleSupport` recursively constructs the complete list of
selected descendants from Checked and that readback. `finite_descendants`
proves membership exactly matches reflexive-transitive local child reachability.
Thus fixed-snapshot finite support is derived rather than taken as a list
premise. Finiteness of the declarations and clauses is already supplied by the
registry/list carriers; the slot set is also finite. What remains is to derive
the semantic readback and a compatible bound across changing snapshots,
allocations, and journal updates. A separate finite list for each frozen
snapshot does not bound one execution through many snapshots. No general Step
finite basis is inferred from it, and the old conditional finite-basis theorem
is not relabelled as an unconditional result.

### Remaining Item 4 engineering gaps

**Joint applicability and feedback.** `GeneralNominalJointCandidates.Joint`
requires one journal model satisfying the candidate branch for the root and
for every aliased registered request, including every named output constraint.
It also agrees with every previously stored candidate key in that alias class.
`alias_outputs_not_dropped` explicitly exposes the materialization conditions
of an aliased site; `conflicting_journal_eliminates` rules out a branch
inconsistent with the whole journal. This is now a premise of
`GeneralNominalCycleSteps.Installable`, so newly committed choices cannot use
separate incompatible models for different requests. `initial_joint` and
`CycleInstallation.initial_selected_installation` prove that initial selected
candidates with children still have a real update, producing the entire emitted
conjunction and exact branch-model conditions.

This guard is not the full merged-demand solver. Local selection still projects
the unchanged raw-context Survivor, so it can remain ambiguous when the journal
would uniquely select a joint candidate. The packet installs its own conditions;
there is not yet a theorem that every other alias's named obligations are
installed/completed. Nor is there a global invariant resolving conflicting
recorded choices after a later merge. A complete joint classifier and complete
feedback/regeneration into recursive inspection remain MISSING. Halted/Stable
here refers exactly to the certified update relation, not to those missing
source operations.

**Nonpoint child provenance.**
`GeneralNominalCapturedChildOrigins.captured_child_origin` handles a variable
child from an actual retained capture and its recorded observation anchor.
Under BranchModels, the anchor has an observed value, and every such value fits
the emitted child's merged interval, including repeated captures and different
lower/upper endpoints. This reuses the existing projection and repeated-capture
correspondence. It does not accept an arbitrary value that happens to fit an
interval as an origin. Still missing: a total invariant producing the anchor
for every capture, compound-input origin production, and the complete annotated
Emitted list/source-slot materializer. The old `pointEmitted` is unchanged.

**Precise prerequisites still missing for general progress.** Produce a
semantically adequate Readback from complete normalized source observations and
actual reports; prove its correspondence through all allowed refinements and
materializations; derive finite work support for all states reachable from an
initial source state; and connect the full joint classifier and annotated
emissions to that support. Neither Checked alone nor the finite slot set at
one instant currently proves these statements. They are source/proof
correspondences, not new language choices. The owner has settled the cycle
semantics; no new semantic question is introduced by this section.

### Full statements of the new public theorems

The following are Lean's elaborated signatures, including all extra premises.
The cycle/regression and transition results use the general nominal carrier;
the Readback/support results are explicitly conditional bridges. No fragment
result below is presented as B4 progress. Proof bodies are in the linked modules.

```lean
@Yulang.GeneralNominalCapturedChildOrigins.captured_child_origin : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
  (bounds : List (Yulang.GeneralNominalInspection.Bounds context.state))
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalRecursiveCandidates.BranchModels registry context root declaration checked bounds model →
    ∀ (capture : Yulang.GeneralNominalRecursiveInspection.Capture context.state),
      capture ∈ (Yulang.GeneralNominalRecursiveCandidates.report context declaration bounds).captures →
        capture.name ∈ declaration.inputNames →
          ∀ (origin : Yulang.GeneralNominalRecursiveInspection.Origin),
            capture.origin = some origin →
              (origin, capture.bounds) ∈
                  (Yulang.GeneralNominalRecursiveCandidates.report context declaration bounds).anchors →
                ∀ (clause : Yulang.GeneralDeclarations.Clause)
                  (valid : Yulang.GeneralDeclarations.Clause.Signature roles clause)
                  (index : Fin (roles clause.role).arity),
                  Yulang.GeneralDeclarationPatterns.normalize clause.arguments[↑index] =
                      Yulang.GeneralDeclarationPatterns.Pattern.var capture.name →
                    let child :=
                      Yulang.GeneralDeclarationDemands.childDemand declaration clause valid
                        (Yulang.GeneralNominalAllocation.capture context.state registry root.identity declaration.id
                          (Yulang.GeneralNominalRecursiveInspection.bindings context.state
                            (Yulang.GeneralNominalRecursiveCandidates.report context declaration bounds)))
                        (Yulang.GeneralNominalAllocation.allocation context.state registry root.identity declaration.id
                          clause);
                    (∃ actual, Yulang.GeneralNominalRecursiveInspection.Observes model origin actual) ∧
                      ∀ (actual : Yulang.CommonNominalFullCarrier.Ty),
                        Yulang.GeneralNominalRecursiveInspection.Observes model origin actual →
                          Yulang.GeneralNominalCaptureMerges.Fits model (child.arguments index) actual
@Yulang.GeneralNominalCycleBoundary.local_projection : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (frontier : Yulang.CommonRoleOutermostResolver.Frontier (Yulang.GeneralSourceDictionaries.Occurrence roles)),
  Yulang.GeneralNominalLocalBoundary.Local (Yulang.GeneralNominalCycleBoundary.localFields roles) registry state root
      frontier ↔
    Yulang.GeneralNominalCycleK2.Local registry state.context root frontier
Yulang.GeneralNominalCycleBoundary.stepModels : ∀ (roles : Yulang.Roles.RoleDecls)
  (registry : (Yulang.GeneralNominalCycleBoundary.vocabulary roles).Registry),
  (Yulang.GeneralNominalCycleBoundary.localFields roles).Checked registry →
    ∀ (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
      (before after : Yulang.GeneralNominalSaturationState.State roles),
      (Yulang.GeneralNominalCycleBoundary.transitions roles).Step registry root before after →
        ∀ (model : (Yulang.GeneralNominalCycleBoundary.vocabulary roles).Model),
          (Yulang.GeneralNominalCycleBoundary.localFields roles).Models after model →
            (Yulang.GeneralNominalCycleBoundary.localFields roles).Models before model
Yulang.GeneralNominalCycleBoundary.closure : ∀ (roles : Yulang.Roles.RoleDecls)
  (registry : (Yulang.GeneralNominalCycleBoundary.vocabulary roles).Registry),
  (Yulang.GeneralNominalCycleBoundary.localFields roles).Checked registry →
    ∀ (state : Yulang.GeneralNominalSaturationState.State roles)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      (∀ (after : Yulang.GeneralNominalSaturationState.State roles),
          ¬(Yulang.GeneralNominalCycleBoundary.transitions roles).Step registry root state after) →
        (Yulang.GeneralNominalCycleBoundary.transitions roles).Stable registry state root ∧
          ∀ (child : Yulang.GeneralSourceDictionaries.Occurrence roles),
            (Yulang.GeneralNominalCycleBoundary.transitions roles).Generated registry state root child →
              (Yulang.GeneralNominalCycleBoundary.transitions roles).Stable registry state child
@Yulang.GeneralNominalCycleBoundary.whereAccessible_of_readback : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry),
  Yulang.GeneralDeclarations.Checked registry →
    ∀ (state : Yulang.GeneralNominalSaturationState.State roles)
      (readback : Yulang.GeneralNominalCycleReadback.Readback roles registry state.context)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Acc
        (Yulang.CommonRoleOutermostResolver.Child
          (Yulang.GeneralNominalLocalBoundary.Local (Yulang.GeneralNominalCycleBoundary.localFields roles) registry
            state))
        root
@Yulang.GeneralNominalCycleBoundary.survivor_unchanged : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
  (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
  (Yulang.GeneralNominalCycleBoundary.localFields roles).Survivor registry state root key children ↔
    Yulang.GeneralNominalRecursiveCandidates.Survivor registry state.context root key children
Yulang.GeneralNominalCycleDescent.path_original : ∀ (state : Yulang.GeneralNominalState.State)
  {first last : Fin state.base.slots},
  Yulang.GeneralNominalCycleDescent.CutPath state first last → Yulang.GeneralNominalCycleK2.Path state first last
Yulang.GeneralNominalCycleDescent.path_trans : ∀ (state : Yulang.GeneralNominalState.State)
  {a b c : Fin state.base.slots},
  Yulang.GeneralNominalCycleDescent.CutPath state a b →
    Yulang.GeneralNominalCycleDescent.CutPath state b c → Yulang.GeneralNominalCycleDescent.CutPath state a c
Yulang.GeneralNominalCycleDescent.mem_reached : ∀ (state : Yulang.GeneralNominalState.State)
  (source target : Fin state.base.slots),
  target ∈ Yulang.GeneralNominalCycleDescent.reached state source ↔
    Yulang.GeneralNominalCycleDescent.CutPath state source target
Yulang.GeneralNominalCycleDescent.rank_bounded : ∀ (state : Yulang.GeneralNominalState.State)
  (source : Fin state.base.slots), Yulang.GeneralNominalCycleDescent.rank state source ≤ state.base.slots
Yulang.GeneralNominalCycleDescent.rank_decreases : ∀ (state : Yulang.GeneralNominalState.State)
  (source target : Fin state.base.slots),
  Yulang.GeneralNominalCycleDescent.CutEdge state source target →
    Yulang.GeneralNominalCycleDescent.rank state target < Yulang.GeneralNominalCycleDescent.rank state source
Yulang.GeneralNominalCycleDescent.cut_accessible : ∀ (state : Yulang.GeneralNominalState.State)
  (root : Fin state.base.slots),
  Acc (fun child parent => Yulang.GeneralNominalCycleDescent.CutEdge state parent child) root
Yulang.GeneralNominalCycleDescent.cyclic_leaf : ∀ (state : Yulang.GeneralNominalState.State)
  (root : Fin state.base.slots),
  Yulang.GeneralNominalCycleK2.Cycle state root →
    ∀ (child : Fin state.base.slots), ¬Yulang.GeneralNominalCycleDescent.CutEdge state root child
Yulang.GeneralNominalCycleEdges.nominal_interval_actual : ∀ (state : Yulang.GeneralNominalState.State)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models state model →
    ∀ (lower upper : Fin state.base.slots) (left right : Yulang.GeneralNominalState.Descriptor state.base.slots),
      state.nominals lower = some left →
        state.nominals upper = some right →
          ∀ (actual : Yulang.CommonNominalFullCarrier.Ty),
            Yulang.CommonNominalFullCarrier.Subtype (model (state.base.source lower)).fst actual ∧
                Yulang.CommonNominalFullCarrier.Subtype actual (model (state.base.source upper)).fst →
              Yulang.CommonNominalFullCarrier.Equivalent actual (model (state.base.source lower)).fst ∧
                Yulang.CommonNominalFullCarrier.Equivalent actual (model (state.base.source upper)).fst
Yulang.GeneralNominalCycleEdges.nominal_interval_edge : ∀ (state : Yulang.GeneralNominalState.State)
  (parent lower upper : Fin state.base.slots)
  (descriptor left right : Yulang.GeneralNominalState.Descriptor state.base.slots),
  state.nominals parent = some descriptor →
    state.nominals lower = some left →
      state.nominals upper = some right →
        ∀ (index : Nat),
          descriptor.arguments[index]? = some (Yulang.GeneralNominalState.Parameter.type (lower, upper)) →
            Yulang.GeneralNominalMixedRecurrence.ActualArgument state parent lower ∧
              Yulang.GeneralNominalMixedRecurrence.ActualArgument state parent upper
@Yulang.GeneralNominalCycleHalting.initial_generated : ∀ {roles : Yulang.Roles.RoleDecls}
  (context : Yulang.GeneralNominalCandidates.Context) (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralNominalSaturationState.Generated (Yulang.GeneralNominalSaturationState.initial context root) root
      focus →
    focus = root
@Yulang.GeneralNominalCycleHalting.cycle_initial_halted : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralNominalCycleK2.RootK2 context.state root.demand →
    (∀ (source : Nat),
        source ∈ Yulang.GeneralNominalState.sources context.state →
          Yulang.GeneralNominalState.Known context.state source) →
      ∀ (after : Yulang.GeneralNominalSaturationState.State roles),
        ¬Yulang.GeneralNominalCycleSteps.Step registry root (Yulang.GeneralNominalSaturationState.initial context root)
            after
@Yulang.GeneralNominalCycleHalting.cycle_initial_accessible : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralNominalCycleK2.RootK2 context.state root.demand →
    (∀ (source : Nat),
        source ∈ Yulang.GeneralNominalState.sources context.state →
          Yulang.GeneralNominalState.Known context.state source) →
      Acc (fun next current => Yulang.GeneralNominalCycleSteps.Step registry root current next)
        (Yulang.GeneralNominalSaturationState.initial context root)
Yulang.GeneralNominalCycleHalting.obstruction_step_accessible : ∀ (invocation : Nat),
  Acc
    (fun next current =>
      Yulang.GeneralNominalCycleSteps.Step Yulang.GeneralNominalProgressObstruction.registry
        (Yulang.GeneralNominalProgressObstruction.root invocation) current next)
    (Yulang.GeneralNominalSaturationState.initial Yulang.GeneralNominalProgressObstruction.context
      (Yulang.GeneralNominalProgressObstruction.root invocation))
@Yulang.GeneralNominalCycleInstallation.initial_selected_installation : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
  (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
  Yulang.GeneralNominalCycleK2.Local registry context root
      (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
    children ≠ [] →
      ∃ packet,
        packet.registry = registry ∧
          packet.context = context ∧
            packet.site.occurrence = root ∧
              packet.declaration.id = key ∧
                packet.children = children ∧
                  Yulang.GeneralNominalCycleSteps.Step registry root
                      (Yulang.GeneralNominalSaturationState.initial context root)
                      (Yulang.GeneralNominalSaturationState.install
                        (Yulang.GeneralNominalSaturationState.initial context root) packet
                        (Yulang.GeneralNominalSaturationState.pointEmitted packet)) ∧
                    (∀ (child : Yulang.GeneralSourceDictionaries.Occurrence roles),
                        child ∈ children →
                          Yulang.GeneralNominalSaturationState.Generated
                            (Yulang.GeneralNominalSaturationState.install
                              (Yulang.GeneralNominalSaturationState.initial context root) packet
                              (Yulang.GeneralNominalSaturationState.pointEmitted packet))
                            root child) ∧
                      ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                        Yulang.GeneralNominalSaturationState.Models
                            (Yulang.GeneralNominalSaturationState.install
                              (Yulang.GeneralNominalSaturationState.initial context root) packet
                              (Yulang.GeneralNominalSaturationState.pointEmitted packet))
                            model ↔
                          Yulang.GeneralNominalState.Models context.state model ∧ packet.Holds model
@Yulang.GeneralNominalCycleK2.direct_edge_sound : ∀ {state : Yulang.GeneralNominalState.State}
  {parent child : Fin state.base.slots},
  Yulang.GeneralNominalCycleK2.DirectEdge state parent child → Yulang.GeneralNominalCycleK2.Edge state parent child
@Yulang.GeneralNominalCycleK2.direct_path_sound : ∀ {state : Yulang.GeneralNominalState.State}
  {first last : Fin state.base.slots},
  Yulang.GeneralNominalCycleK2.DirectPath state first last → Yulang.GeneralNominalCycleK2.Path state first last
@Yulang.GeneralNominalCycleK2.structural_path_direct : ∀ {state : Yulang.GeneralNominalState.State}
  {first last : Fin state.base.slots},
  Yulang.GeneralSourceK2.Path state.view first last → Yulang.GeneralNominalCycleK2.DirectPath state first last
@Yulang.GeneralNominalCycleK2.cycle_rejects : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalState.State) (demand : Yulang.GeneralSourceState.Demand roles),
  Yulang.GeneralNominalState.Linked state demand →
    ¬Yulang.GeneralNominalState.RootPending state demand →
      ∀ (index : Fin (roles demand.role).arity) (slot : Fin state.base.slots),
        state.base.source slot = (demand.arguments index).fst →
          Yulang.GeneralNominalCycleK2.Cycle state slot →
            ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
              Yulang.GeneralNominalState.Models state model → Yulang.GeneralNominalCycleK2.RootK2 state demand
Yulang.GeneralNominalCycleK2.recurs_cycle : ∀ (state : Yulang.GeneralNominalState.State) (root : Fin state.base.slots),
  Yulang.GeneralNominalCycleK2.RecursAt state root → Yulang.GeneralNominalCycleK2.Cycle state root
Yulang.GeneralNominalCycleK2.recurs_iff_cycle : ∀ (state : Yulang.GeneralNominalState.State)
  (root : Fin state.base.slots) (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models state model →
    (Yulang.GeneralNominalCycleK2.RecursAt state root ↔ Yulang.GeneralNominalCycleK2.Cycle state root)
@Yulang.GeneralNominalCycleK2.structural_cycle_rejects : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalState.State) (demand : Yulang.GeneralSourceState.Demand roles),
  Yulang.GeneralNominalState.Linked state demand →
    ¬Yulang.GeneralNominalState.RootPending state demand →
      ∀ (index : Fin (roles demand.role).arity) (slot : Fin state.base.slots),
        state.base.source slot = (demand.arguments index).fst →
          Yulang.GeneralSourceK2.Cycle state.view slot → Yulang.GeneralNominalCycleK2.RootK2 state demand
@Yulang.GeneralNominalCycleK2.direct_cycle_rejects : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalState.State) (demand : Yulang.GeneralSourceState.Demand roles),
  Yulang.GeneralNominalState.Linked state demand →
    ¬Yulang.GeneralNominalState.RootPending state demand →
      ∀ (index : Fin (roles demand.role).arity) (slot : Fin state.base.slots),
        state.base.source slot = (demand.arguments index).fst →
          Yulang.GeneralNominalCycleK2.DirectCycle state slot → Yulang.GeneralNominalCycleK2.RootK2 state demand
@Yulang.GeneralNominalCycleK2.alias_observation_defers : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralNominalMixedRecurrence.RootK2 context.state root.demand →
    ¬Yulang.GeneralNominalCycleK2.RootK2 context.state root.demand →
      ¬Yulang.GeneralNominalCycleK2.CandidateK2 registry context root →
        Yulang.GeneralNominalCycleK2.Local registry context root Yulang.CommonRoleOutermostResolver.Frontier.pending
@Yulang.GeneralNominalCycleK2.pending_excludes_K2 : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalState.State) (demand : Yulang.GeneralSourceState.Demand roles),
  Yulang.GeneralNominalState.RootPending state demand → ¬Yulang.GeneralNominalCycleK2.RootK2 state demand
@Yulang.GeneralNominalCycleK2.candidateK2_not_pending : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralNominalCycleK2.CandidateK2 registry context root →
    ¬Yulang.GeneralNominalState.RootPending context.state root.demand
@Yulang.GeneralNominalCycleK2.root_rejected : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralNominalCycleK2.RootK2 context.state root.demand →
    Yulang.GeneralNominalCycleK2.Local registry context root Yulang.CommonRoleOutermostResolver.Frontier.rejected
@Yulang.GeneralNominalCycleK2.prepared_cycle : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  ¬Yulang.GeneralNominalState.RootPending context.state root.demand →
    ∀ (declaration : Yulang.GeneralDeclarations.Declaration),
      declaration ∈ registry.declarations →
        ∀ (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration),
          declaration.role = root.demand.role →
            Yulang.GeneralNominalRecursiveCandidates.Prepared registry context root declaration checked →
              ∀ (bounds : List (Yulang.GeneralNominalInspection.Bounds context.state)),
                Yulang.GeneralNominalRecursiveCandidates.arguments context root = some bounds →
                  ∀ (visited : Yulang.GeneralNominalInspection.Bounds context.state),
                    visited ∈ (Yulang.GeneralNominalRecursiveCandidates.report context declaration bounds).inspected →
                      Yulang.GeneralNominalCycleK2.RecursAt context.state visited.fst →
                        Yulang.GeneralNominalCycleK2.CandidateK2 registry context root
@Yulang.GeneralNominalCycleK2.candidate_rejected : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralNominalCycleK2.CandidateK2 registry context root →
    Yulang.GeneralNominalCycleK2.Local registry context root Yulang.CommonRoleOutermostResolver.Frontier.rejected
@Yulang.GeneralNominalCycleK2.selected_not_K2 : ∀ {registry : Yulang.GeneralDeclarations.Registry}
  {context : Yulang.GeneralNominalRecursiveCandidates.Context} {roles : Yulang.Roles.RoleDecls}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  {children : List (Yulang.GeneralNominalCandidates.vocabulary roles).Demand},
  Yulang.GeneralNominalCycleK2.Local registry context root
      (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
    ¬Yulang.GeneralNominalCycleK2.RootK2 context.state root.demand ∧
      ¬Yulang.GeneralNominalCycleK2.CandidateK2 registry context root
@Yulang.GeneralNominalCycleK2.local_total : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry),
  Yulang.GeneralDeclarations.Checked registry →
    ∀ (context : Yulang.GeneralNominalRecursiveCandidates.Context)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      ∃ frontier, Yulang.GeneralNominalCycleK2.Local registry context root frontier
@Yulang.GeneralNominalCycleK2.local_functional : ∀ {registry : Yulang.GeneralDeclarations.Registry}
  {context : Yulang.GeneralNominalRecursiveCandidates.Context} {roles : Yulang.Roles.RoleDecls}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {a b : Yulang.CommonRoleOutermostResolver.Frontier (Yulang.GeneralNominalCandidates.vocabulary roles).Demand},
  Yulang.GeneralNominalCycleK2.Local registry context root a →
    Yulang.GeneralNominalCycleK2.Local registry context root b → a = b
@Yulang.GeneralNominalCycleK2.rejected_accessible : ∀ {registry : Yulang.GeneralDeclarations.Registry}
  {context : Yulang.GeneralNominalRecursiveCandidates.Context} {roles : Yulang.Roles.RoleDecls}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalCycleK2.Local registry context root Yulang.CommonRoleOutermostResolver.Frontier.rejected →
    Acc (Yulang.CommonRoleOutermostResolver.Child (Yulang.GeneralNominalCycleK2.Local registry context)) root
@Yulang.GeneralNominalCycleK2.rootK2_accessible : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralNominalCycleK2.RootK2 context.state root.demand →
    Acc (Yulang.CommonRoleOutermostResolver.Child (Yulang.GeneralNominalCycleK2.Local registry context)) root
@Yulang.GeneralNominalCycleReadback.child_decreases : ∀ {registry : Yulang.GeneralDeclarations.Registry}
  {roles : Yulang.Roles.RoleDecls} {context : Yulang.GeneralNominalCandidates.Context},
  Yulang.GeneralDeclarations.Checked registry →
    ∀ (readback : Yulang.GeneralNominalCycleReadback.Readback roles registry context)
      (parent child : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Yulang.CommonRoleOutermostResolver.Child (Yulang.GeneralNominalCycleK2.Local registry context) child parent →
        Yulang.GeneralNominalCycleReadback.weight readback child <
          Yulang.GeneralNominalCycleReadback.weight readback parent
@Yulang.GeneralNominalCycleReadback.whereAccessible : ∀ {registry : Yulang.GeneralDeclarations.Registry}
  {roles : Yulang.Roles.RoleDecls} {context : Yulang.GeneralNominalCandidates.Context},
  Yulang.GeneralDeclarations.Checked registry →
    ∀ (readback : Yulang.GeneralNominalCycleReadback.Readback roles registry context)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Acc (Yulang.CommonRoleOutermostResolver.Child (Yulang.GeneralNominalCycleK2.Local registry context)) root
Yulang.GeneralNominalCycleRegressions.loop_K2 : Yulang.GeneralNominalCycleK2.RootK2
  Yulang.GeneralNominalRegressions.loopState' Yulang.GeneralSourceStateExamples.loopDemand
Yulang.GeneralNominalCycleRegressions.shadow_not_K2 : ¬Yulang.GeneralNominalCycleK2.RootK2
    Yulang.GeneralNominalRegressions.shadowState' Yulang.GeneralSourceStateExamples.loopDemand
Yulang.GeneralNominalCycleRegressions.index_pending_not_K2 : Yulang.GeneralNominalState.RootPending
    Yulang.GeneralNominalRegressions.indexState' Yulang.GeneralSourceStateExamples.indexDemand ∧
  ¬Yulang.GeneralNominalCycleK2.RootK2 Yulang.GeneralNominalRegressions.indexState'
      Yulang.GeneralSourceStateExamples.indexDemand
Yulang.GeneralNominalCycleRegressions.nominal_cycle_K2 : ∀ (invocation : Nat),
  Yulang.GeneralNominalCycleK2.RootK2 Yulang.GeneralNominalProgressObstruction.state
    (Yulang.GeneralNominalProgressObstruction.root invocation).demand
Yulang.GeneralNominalCycleRegressions.nominal_candidate_K2 : ∀ (invocation : Nat),
  Yulang.GeneralNominalCycleK2.CandidateK2 Yulang.GeneralNominalProgressObstruction.registry
    Yulang.GeneralNominalProgressObstruction.context (Yulang.GeneralNominalProgressObstruction.root invocation)
Yulang.GeneralNominalCycleRegressions.nominal_display_rejected : ∀ (invocation : Nat),
  Yulang.GeneralNominalCycleK2.Local Yulang.GeneralNominalProgressObstruction.registry
    Yulang.GeneralNominalProgressObstruction.context (Yulang.GeneralNominalProgressObstruction.root invocation)
    Yulang.CommonRoleOutermostResolver.Frontier.rejected
Yulang.GeneralNominalCycleRegressions.obstruction_child_accessible : ∀ (invocation : Nat),
  Acc
    (Yulang.CommonRoleOutermostResolver.Child
      (Yulang.GeneralNominalCycleK2.Local Yulang.GeneralNominalProgressObstruction.registry
        Yulang.GeneralNominalProgressObstruction.context))
    (Yulang.GeneralNominalProgressObstruction.root invocation)
Yulang.GeneralNominalCycleRegressions.nominal_len_K2 : Yulang.GeneralNominalCycleK2.RootK2
  Yulang.GeneralNominalProgressObstruction.state Yulang.GeneralNominalCycleRegressions.nominalLenRoot.demand
Yulang.GeneralNominalCycleRegressions.nominal_len_rejected : Yulang.GeneralNominalCycleK2.Local
  Yulang.GeneralNominalRecursiveExamples.lenRegistry Yulang.GeneralNominalProgressObstruction.context
  Yulang.GeneralNominalCycleRegressions.nominalLenRoot Yulang.CommonRoleOutermostResolver.Frontier.rejected
Yulang.GeneralNominalCycleRegressions.mixed_list_root_K2 : Yulang.GeneralNominalCycleK2.RootK2
  Yulang.GeneralNominalMixedExamples.state Yulang.GeneralNominalMixedExamples.showRoot.demand
Yulang.GeneralNominalCycleRegressions.wrapper_len_survivor : Yulang.GeneralNominalRecursiveCandidates.Survivor
  Yulang.GeneralNominalRecursiveExamples.lenRegistry Yulang.GeneralNominalCycleWrapper.context
  Yulang.GeneralNominalRecursiveExamples.lenRoot 30 []
Yulang.GeneralNominalCycleRegressions.wrapper_len_not_K2 : ¬Yulang.GeneralNominalCycleK2.RootK2
    Yulang.GeneralNominalCycleWrapper.state Yulang.GeneralNominalRecursiveExamples.lenRoot.demand
Yulang.GeneralNominalCycleRegressions.wrapper_len_selected : Yulang.GeneralNominalCycleK2.Local
  Yulang.GeneralNominalRecursiveExamples.lenRegistry Yulang.GeneralNominalCycleWrapper.context
  Yulang.GeneralNominalRecursiveExamples.lenRoot (Yulang.CommonRoleOutermostResolver.Frontier.selected 30 [])
@Yulang.GeneralNominalCycleSteps.installable_joint : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSaturationState.State roles}
  {packet : Yulang.GeneralNominalSaturationState.Packet roles},
  Yulang.GeneralNominalCycleSteps.Installable registry state packet →
    Yulang.GeneralNominalJointCandidates.Joint registry state packet.site.occurrence packet.declaration.id
@Yulang.GeneralNominalCycleSteps.refresh_models : ∀ {roles : Yulang.Roles.RoleDecls}
  {before : Yulang.GeneralNominalSaturationState.State roles} {context : Yulang.GeneralNominalCandidates.Context}
  (certificate : Yulang.GeneralNominalCycleSteps.Refresh before context)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralNominalSaturationState.regenerate before context) model ↔
    Yulang.GeneralNominalSaturationState.Models before model
@Yulang.GeneralNominalCycleSteps.at_extends : ∀ {registry : Yulang.GeneralDeclarations.Registry}
  {roles : Yulang.Roles.RoleDecls} {before : Yulang.GeneralNominalSaturationState.State roles}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {after : Yulang.GeneralNominalSaturationState.State roles},
  Yulang.GeneralNominalCycleSteps.At registry before focus after → Yulang.GeneralNominalCycleSteps.Extends before after
@Yulang.GeneralNominalCycleSteps.step_extends : ∀ {registry : Yulang.GeneralDeclarations.Registry}
  {roles : Yulang.Roles.RoleDecls} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSaturationState.State roles},
  Yulang.GeneralNominalCycleSteps.Step registry root before after → Yulang.GeneralNominalCycleSteps.Extends before after
@Yulang.GeneralNominalCycleSteps.step_models : ∀ {registry : Yulang.GeneralDeclarations.Registry}
  {roles : Yulang.Roles.RoleDecls} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSaturationState.State roles},
  Yulang.GeneralNominalCycleSteps.Step registry root before after →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models after model → Yulang.GeneralNominalSaturationState.Models before model
@Yulang.GeneralNominalCycleSteps.alias_monotone : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralNominalSaturationState.State roles} {first last : Nat},
  Yulang.GeneralNominalCycleSteps.Extends before after →
    Yulang.GeneralNominalSaturationState.Alias before first last →
      Yulang.GeneralNominalSaturationState.Alias after first last
@Yulang.GeneralNominalCycleSteps.generated_monotone : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralNominalSaturationState.State roles}
  {root child : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalCycleSteps.Extends before after →
    Yulang.GeneralNominalSaturationState.Generated before root child →
      Yulang.GeneralNominalSaturationState.Generated after root child
@Yulang.GeneralNominalCycleSteps.installed_committed : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (packet : Yulang.GeneralNominalSaturationState.Packet roles)
  (emitted : Yulang.GeneralNominalSaturationState.Emitted packet),
  Yulang.GeneralNominalCycleSteps.Committed (Yulang.GeneralNominalSaturationState.install state packet emitted) packet
@Yulang.GeneralNominalCycleSteps.installed_children : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (packet : Yulang.GeneralNominalSaturationState.Packet roles)
  (emitted : Yulang.GeneralNominalSaturationState.Emitted packet)
  (child : Yulang.GeneralSourceDictionaries.Occurrence roles),
  child ∈ packet.children →
    Yulang.GeneralNominalSaturationState.Generated (Yulang.GeneralNominalSaturationState.install state packet emitted)
      packet.site.occurrence child
@Yulang.GeneralNominalCycleSteps.merged_inputs : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (first last : Yulang.GeneralNominalDemandMerging.Site roles),
  Yulang.GeneralNominalSaturationState.Alias (Yulang.GeneralNominalSaturationState.merge state first last)
    first.occurrence.identity last.occurrence.identity
@Yulang.GeneralNominalCycleSteps.replay_does_not_add_information : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (packet : Yulang.GeneralNominalSaturationState.Packet roles),
  Yulang.GeneralNominalCycleSteps.Committed state packet →
    ¬(Yulang.GeneralNominalCycleSteps.Installable registry state packet ∧
        ¬Yulang.GeneralNominalCycleSteps.Committed state packet)
@Yulang.GeneralNominalCycleSteps.pending_never_installed : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (packet : Yulang.GeneralNominalSaturationState.Packet roles),
  Yulang.GeneralNominalState.RootPending state.context.state packet.site.occurrence.demand →
    ¬Yulang.GeneralNominalCycleSteps.Installable registry state packet
@Yulang.GeneralNominalCycleSteps.rootK2_never_installed : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (packet : Yulang.GeneralNominalSaturationState.Packet roles),
  Yulang.GeneralNominalCycleK2.RootK2 state.context.state packet.site.occurrence.demand →
    ¬Yulang.GeneralNominalCycleSteps.Installable registry state packet
@Yulang.GeneralNominalCycleSteps.candidateK2_never_installed : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (packet : Yulang.GeneralNominalSaturationState.Packet roles),
  Yulang.GeneralNominalCycleK2.CandidateK2 registry state.context packet.site.occurrence →
    ¬Yulang.GeneralNominalCycleSteps.Installable registry state packet
@Yulang.GeneralNominalCycleSteps.closed_iff_no_update : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles} {focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {registry : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralNominalCycleSteps.Registered state focus ∧ Yulang.GeneralNominalCycleSteps.Closed registry state focus ↔
    ∀ (after : Yulang.GeneralNominalSaturationState.State roles),
      ¬Yulang.GeneralNominalCycleSteps.At registry state focus after
@Yulang.GeneralNominalCycleSteps.halted_stable : ∀ {registry : Yulang.GeneralDeclarations.Registry}
  {roles : Yulang.Roles.RoleDecls} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {state : Yulang.GeneralNominalSaturationState.State roles},
  (∀ (after : Yulang.GeneralNominalSaturationState.State roles),
      ¬Yulang.GeneralNominalCycleSteps.Step registry root state after) →
    Yulang.GeneralNominalCycleSteps.Stable registry state root
@Yulang.GeneralNominalCycleSteps.stable_generated : ∀ {registry : Yulang.GeneralDeclarations.Registry}
  {roles : Yulang.Roles.RoleDecls} {state : Yulang.GeneralNominalSaturationState.State roles}
  {root child : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalCycleSteps.Stable registry state root →
    Yulang.GeneralNominalSaturationState.Generated state root child →
      Yulang.GeneralNominalCycleSteps.Stable registry state child
@Yulang.GeneralNominalCycleSteps.stable_halted : ∀ {registry : Yulang.GeneralDeclarations.Registry}
  {roles : Yulang.Roles.RoleDecls} {state : Yulang.GeneralNominalSaturationState.State roles}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalCycleSteps.Stable registry state root →
    ∀ (after : Yulang.GeneralNominalSaturationState.State roles),
      ¬Yulang.GeneralNominalCycleSteps.Step registry root state after
@Yulang.GeneralNominalCycleSteps.halted_closure : ∀ {registry : Yulang.GeneralDeclarations.Registry}
  {roles : Yulang.Roles.RoleDecls} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {state : Yulang.GeneralNominalSaturationState.State roles},
  (∀ (after : Yulang.GeneralNominalSaturationState.State roles),
      ¬Yulang.GeneralNominalCycleSteps.Step registry root state after) →
    Yulang.GeneralNominalCycleSteps.Stable registry state root ∧
      ∀ (child : Yulang.GeneralSourceDictionaries.Occurrence roles),
        Yulang.GeneralNominalSaturationState.Generated state root child →
          Yulang.GeneralNominalCycleSteps.Stable registry state child
@Yulang.GeneralNominalCycleSteps.steps_models : ∀ {registry : Yulang.GeneralDeclarations.Registry}
  {roles : Yulang.Roles.RoleDecls} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSaturationState.State roles},
  Yulang.B4Target.Steps (Yulang.GeneralNominalCycleSteps.Step registry root) before after →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models after model → Yulang.GeneralNominalSaturationState.Models before model
@Yulang.GeneralNominalCycleSupport.frontier_local : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {context : Yulang.GeneralNominalCandidates.Context}
  (checked : Yulang.GeneralDeclarations.Checked registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralNominalCycleK2.Local registry context root (Yulang.GeneralNominalCycleSupport.frontier checked root)
@Yulang.GeneralNominalCycleSupport.children_exact : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {context : Yulang.GeneralNominalCandidates.Context}
  (checked : Yulang.GeneralDeclarations.Checked registry)
  (root child : Yulang.GeneralSourceDictionaries.Occurrence roles),
  child ∈ Yulang.GeneralNominalCycleSupport.children checked root ↔
    Yulang.CommonRoleOutermostResolver.Child (Yulang.GeneralNominalCycleK2.Local registry context) child root
@Yulang.GeneralNominalCycleSupport.root_mem_support : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {context : Yulang.GeneralNominalCandidates.Context}
  (checked : Yulang.GeneralDeclarations.Checked registry)
  (readback : Yulang.GeneralNominalCycleReadback.Readback roles registry context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  root ∈ Yulang.GeneralNominalCycleSupport.support checked readback root
@Yulang.GeneralNominalCycleSupport.child_support_subset : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {context : Yulang.GeneralNominalCandidates.Context}
  (checked : Yulang.GeneralDeclarations.Checked registry)
  (readback : Yulang.GeneralNominalCycleReadback.Readback roles registry context)
  (parent child : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.CommonRoleOutermostResolver.Child (Yulang.GeneralNominalCycleK2.Local registry context) child parent →
    Yulang.GeneralNominalCycleSupport.support checked readback child ⊆
      Yulang.GeneralNominalCycleSupport.support checked readback parent
@Yulang.GeneralNominalCycleSupport.reached_in_support : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {context : Yulang.GeneralNominalCandidates.Context}
  {root child : Yulang.GeneralSourceDictionaries.Occurrence roles}
  (checked : Yulang.GeneralDeclarations.Checked registry)
  (readback : Yulang.GeneralNominalCycleReadback.Readback roles registry context),
  Yulang.GeneralNominalCycleSupport.Reaches registry context root child →
    child ∈ Yulang.GeneralNominalCycleSupport.support checked readback root
@Yulang.GeneralNominalCycleSupport.support_reached : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {context : Yulang.GeneralNominalCandidates.Context}
  (checked : Yulang.GeneralDeclarations.Checked registry)
  (readback : Yulang.GeneralNominalCycleReadback.Readback roles registry context)
  (root child : Yulang.GeneralSourceDictionaries.Occurrence roles),
  child ∈ Yulang.GeneralNominalCycleSupport.support checked readback root →
    Yulang.GeneralNominalCycleSupport.Reaches registry context root child
@Yulang.GeneralNominalCycleSupport.finite_descendants : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {context : Yulang.GeneralNominalCandidates.Context},
  Yulang.GeneralDeclarations.Checked registry →
    ∀ (readback : Yulang.GeneralNominalCycleReadback.Readback roles registry context)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      ∃ demands,
        ∀ (child : Yulang.GeneralSourceDictionaries.Occurrence roles),
          child ∈ demands ↔ Yulang.GeneralNominalCycleSupport.Reaches registry context root child
Yulang.GeneralNominalCycleWrapper.record_equation : Yulang.CommonNominalFullCarrier.Equivalent
  (Yulang.GeneralNominalCycleWrapper.value 0)
  (Yulang.CommonNominalFullCarrier.required 7 (Yulang.GeneralNominalCycleWrapper.value 0))
Yulang.GeneralNominalCycleWrapper.list_equation : Yulang.CommonNominalFullCarrier.Equivalent
  (Yulang.GeneralNominalCycleWrapper.value 1)
  (Yulang.CommonNominalFullCarrier.nominal 0 [Sum.inl (Yulang.GeneralNominalCycleWrapper.value 0)])
Yulang.GeneralNominalCycleWrapper.state_models : Yulang.GeneralNominalState.Models
  Yulang.GeneralNominalCycleWrapper.state Yulang.GeneralNominalCycleWrapper.model
Yulang.GeneralNominalCycleWrapper.edge_target_zero : ∀ (first last : Fin 2),
  Yulang.GeneralNominalCycleK2.Edge Yulang.GeneralNominalCycleWrapper.state first last → last = 0
Yulang.GeneralNominalCycleWrapper.list_off_cycle : ¬Yulang.GeneralNominalCycleK2.Cycle
    Yulang.GeneralNominalCycleWrapper.state 1
@Yulang.GeneralNominalJointCandidates.initial_joint : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration),
  declaration ∈ registry.declarations →
    ∀ (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration),
      declaration.role = root.demand.role →
        ∀ (bounds : List (Yulang.GeneralNominalInspection.Bounds context.state)),
          Yulang.GeneralNominalRecursiveCandidates.arguments context root = some bounds →
            Yulang.GeneralNominalRecursiveCandidates.Prepared registry context root declaration checked →
              ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                Yulang.GeneralNominalRecursiveCandidates.BranchModels registry context root declaration checked bounds
                    model →
                  Yulang.GeneralNominalJointCandidates.Joint registry
                    (Yulang.GeneralNominalSaturationState.initial context root) root declaration.id
@Yulang.GeneralNominalJointCandidates.old_survivor : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSaturationState.State roles}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat}
  {children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)},
  Yulang.GeneralNominalJointCandidates.Survivor registry state root key children →
    Yulang.GeneralNominalRecursiveCandidates.Survivor registry state.context root key children
@Yulang.GeneralNominalJointCandidates.all_alias_conditions : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSaturationState.State roles}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat},
  Yulang.GeneralNominalJointCandidates.Joint registry state root key →
    ∃ model,
      Yulang.GeneralNominalSaturationState.Models state model ∧
        Yulang.GeneralNominalJointCandidates.BranchAt registry state root key model ∧
          ∀ (site : Yulang.GeneralNominalDemandMerging.Site roles),
            Yulang.GeneralNominalJointCandidates.Related state root site →
              Yulang.GeneralNominalJointCandidates.BranchAt registry state site.occurrence key model
@Yulang.GeneralNominalJointCandidates.alias_outputs_not_dropped : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSaturationState.State roles}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat},
  Yulang.GeneralNominalJointCandidates.Joint registry state root key →
    ∀ (site : Yulang.GeneralNominalDemandMerging.Site roles),
      Yulang.GeneralNominalJointCandidates.Related state root site →
        ∃ model,
          Yulang.GeneralNominalSaturationState.Models state model ∧
            ∃ declaration,
              declaration ∈ registry.declarations ∧
                ∃ checked,
                  declaration.id = key ∧
                    ∃ bounds,
                      Yulang.GeneralNominalRecursiveCandidates.arguments state.context site.occurrence = some bounds ∧
                        Yulang.GeneralNominalMaterialization.Models state.context.state declaration
                          (Yulang.GeneralNominalAllocation.capture state.context.state registry site.occurrence.identity
                            declaration.id
                            (Yulang.GeneralNominalRecursiveInspection.bindings state.context.state
                              (Yulang.GeneralNominalRecursiveCandidates.report state.context declaration bounds)))
                          (Yulang.GeneralNominalRecursiveCandidates.report state.context declaration bounds)
                          (Yulang.GeneralNominalRecursiveCandidates.generated registry state.context site.occurrence
                            declaration checked bounds)
                          model
@Yulang.GeneralNominalJointCandidates.conflicting_recorded_choices : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (first last : Yulang.GeneralNominalSaturationState.Packet roles),
  first ∈ state.packets →
    last ∈ state.packets →
      Yulang.GeneralNominalSaturationState.Alias state root.identity first.site.occurrence.identity →
        Yulang.GeneralNominalSaturationState.Alias state root.identity last.site.occurrence.identity →
          first.declaration.id ≠ last.declaration.id →
            ∀ (registry : Yulang.GeneralDeclarations.Registry) (key : Nat),
              ¬Yulang.GeneralNominalJointCandidates.Joint registry state root key
@Yulang.GeneralNominalJointCandidates.joint_consistent_with_journal : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSaturationState.State roles}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles} {key : Nat},
  Yulang.GeneralNominalJointCandidates.Joint registry state root key →
    ∃ model, Yulang.GeneralNominalSaturationState.Models state model
@Yulang.GeneralNominalJointCandidates.conflicting_journal_eliminates : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat),
  (∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models state model →
        ¬Yulang.GeneralNominalJointCandidates.BranchAt registry state root key model) →
    ¬Yulang.GeneralNominalJointCandidates.Joint registry state root key
@Yulang.GeneralNominalJointCandidates.survivor_functional : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry),
  Yulang.GeneralDeclarations.Checked registry →
    ∀ (state : Yulang.GeneralNominalSaturationState.State roles)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
      (first last : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
      Yulang.GeneralNominalJointCandidates.Survivor registry state root key first →
        Yulang.GeneralNominalJointCandidates.Survivor registry state root key last → first = last
Yulang.GeneralNominalCycleDescent.root_edge_decreases : ∀ (state : Yulang.GeneralNominalState.State)
  {roles : Yulang.Roles.RoleDecls} (demand : Yulang.GeneralSourceState.Demand roles),
  Yulang.GeneralNominalState.Linked state demand →
    ¬Yulang.GeneralNominalState.RootPending state demand →
      ¬Yulang.GeneralNominalCycleK2.RootK2 state demand →
        ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
          Yulang.GeneralNominalState.Models state model →
            ∀ (index : Fin (roles demand.role).arity) (root child : Fin state.base.slots),
              state.base.source root = (demand.arguments index).fst →
                Yulang.GeneralNominalCycleK2.Edge state root child →
                  Yulang.GeneralNominalCycleDescent.rank state child < Yulang.GeneralNominalCycleDescent.rank state root
@Yulang.GeneralNominalCycleDescent.inspected_edge_decreases : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  ¬Yulang.GeneralNominalState.RootPending context.state root.demand →
    ¬Yulang.GeneralNominalCycleK2.CandidateK2 registry context root →
      ∀ (declaration : Yulang.GeneralDeclarations.Declaration),
        declaration ∈ registry.declarations →
          Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration →
            declaration.role = root.demand.role →
              Yulang.GeneralNominalRecursiveCandidates.HeadReady registry context root declaration →
                ∀ (bounds : List (Yulang.GeneralNominalInspection.Bounds context.state)),
                  Yulang.GeneralNominalRecursiveCandidates.arguments context root = some bounds →
                    ∀ (visited : Yulang.GeneralNominalInspection.Bounds context.state),
                      visited ∈ (Yulang.GeneralNominalRecursiveCandidates.report context declaration bounds).inspected →
                        ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                          Yulang.GeneralNominalState.Models context.state model →
                            ∀ (child : Fin context.state.base.slots),
                              Yulang.GeneralNominalCycleK2.Edge context.state visited.fst child →
                                Yulang.GeneralNominalCycleDescent.rank context.state child <
                                  Yulang.GeneralNominalCycleDescent.rank context.state visited.fst
```

### Files and verification

Added modules:

- [`GeneralNominalCapturedChildOrigins.lean`](../../lean/Yulang/GeneralNominalCapturedChildOrigins.lean)
- [`GeneralNominalCycleBoundary.lean`](../../lean/Yulang/GeneralNominalCycleBoundary.lean)
- [`GeneralNominalCycleDescent.lean`](../../lean/Yulang/GeneralNominalCycleDescent.lean)
- [`GeneralNominalCycleEdges.lean`](../../lean/Yulang/GeneralNominalCycleEdges.lean)
- [`GeneralNominalCycleHalting.lean`](../../lean/Yulang/GeneralNominalCycleHalting.lean)
- [`GeneralNominalCycleInstallation.lean`](../../lean/Yulang/GeneralNominalCycleInstallation.lean)
- [`GeneralNominalCycleK2.lean`](../../lean/Yulang/GeneralNominalCycleK2.lean)
- [`GeneralNominalCycleReadback.lean`](../../lean/Yulang/GeneralNominalCycleReadback.lean)
- [`GeneralNominalCycleRegressions.lean`](../../lean/Yulang/GeneralNominalCycleRegressions.lean)
- [`GeneralNominalCycleSteps.lean`](../../lean/Yulang/GeneralNominalCycleSteps.lean)
- [`GeneralNominalCycleSupport.lean`](../../lean/Yulang/GeneralNominalCycleSupport.lean)
- [`GeneralNominalCycleWrapper.lean`](../../lean/Yulang/GeneralNominalCycleWrapper.lean)
- [`GeneralNominalJointCandidates.lean`](../../lean/Yulang/GeneralNominalJointCandidates.lean)

Changed existing files: appended 13 imports to `lean/Yulang.lean`, appended
96 public-theorem dependency print commands to `lean/Audit.lean`, and appended
this Item 4b section. No old implementation definitions or lines were edited.
The existing Survivor interface used by the Evidence prover is unchanged.
No spec, plan, configuration, commit, push, or git reference was changed.

Final commands, from `lean/`:

```sh
lake build Yulang.GeneralNominalCapturedChildOrigins Yulang.GeneralNominalCycleBoundary Yulang.GeneralNominalCycleDescent Yulang.GeneralNominalCycleEdges Yulang.GeneralNominalCycleHalting Yulang.GeneralNominalCycleInstallation Yulang.GeneralNominalCycleK2 Yulang.GeneralNominalCycleReadback Yulang.GeneralNominalCycleRegressions Yulang.GeneralNominalCycleSteps Yulang.GeneralNominalCycleSupport Yulang.GeneralNominalCycleWrapper Yulang.GeneralNominalJointCandidates > /tmp/astra-cycle-k2-focused.log 2>&1
lake build Yulang > /tmp/astra-cycle-k2-umbrella.log 2>&1
lake env lean Audit.lean > /tmp/astra-cycle-k2-audit.log 2>&1
```

Each command exited **0**. The focused build covered 606 jobs; the umbrella
build covered 1502 jobs, including the unchanged dictionary consumers and
historical regression modules. The full dependency audit produced 9589 reports,
with all 96 new public theorems present exactly once. Its entire reported
dependency set was `propext`, `Classical.choice`, and `Quot.sound`.

`lake env lean /tmp/astra-cycle-k2-signatures.lean > /tmp/astra-cycle-k2-signatures.txt 2>&1`
also exited 0. The signatures above came from that output. Earlier elaboration
errors, including dependent Local elimination and the signature printer option,
were corrected before these final checks; those failed attempts are not reported
as successful checks. Existing Lean byte-prefix preservation, new-source token
and docstring-line checks, theorem/import/audit coverage, whitespace and allowed
path checks also passed. Only append operations affect existing Lean files.

The `yulang-proofs` skill was applied. As in Item 4, no registered custom
`prover` launch configuration was available. The primary constructed the
bounded derivations; no prover agent ran. A separate read-only reviewer checked
the cycle certificates, model nonvacuity, legacy-observation deferral, Joint
installation guard, readback/support premises, and the final narrative. Its
scope corrections are incorporated. The reviewer did not rerun builds or the
dependency audit.

Not verified or claimed: complete source-to-cycle observation coverage;
production of a semantically adequate Readback; general Step accessibility from
Checked; a uniform finite basis across refinements and allocations; complete
joint classification/output installation; preservation of all selected choices
under later merges; total nonpoint/compound child provenance and snapshot
materialization; completed Evidence or executor fields; transition order
independence; the complete V3 bridges or B4 statement; Rust/parser/runtime
behavior or execution of the illustrative Yulang programs.

This work is converging more directly than additional isolated scalar or unary
proofs: the new K2 predicates, rank, installation guard, child provenance and
transition model inclusion all use the same general nominal state, actual
recursive reports, canonical child allocation and dictionary-facing Survivor.
The earlier concrete obstruction is removed for the actual new Step. However,
convergence is not completion: the unconstructed readback and cross-update
support are exactly where finite-pattern Paterson results still fail to imply
general source progress. Further fragment examples alone will not close those
bridges.

## Item 4c — source formation, administrative termination, and readback obstructions (2026-11-12)

**B4 clause (1) is not closed by this change.** General accessibility of the
unchanged `GeneralNominalCycleSteps.Step` and unconditional where accessibility
remain open. Two concrete interface defects now explain why the Item 4b
finite-pattern premise cannot simply be constructed from finite source data:
endpoint-exact pattern readback is false for an accepted nonpoint nominal input,
and canonical sites discard nonpoint provenance even when ordinary constraints
prove the endpoints equal. Both defects have Lean theorems below. Neither is
reported as a formal refutation of general termination. A possible infinite
update mechanism is recorded separately as an unformalized falsifier.

The positive results are a source-formation contract preserved by the unchanged
Step, source-derived interval/capture readback, a total anchor invariant for
retained capture origins, and accessibility of **every merge/refresh-only
sequence**, with its finite basis derived from the starting state. There is
also an explicit SourceBoundary family with Evidence as a parameter. Exactly
five of the twelve V3 bridge fields are proved for that family; seven remain
open, including the two requested accessibility fields.

### Authority, source formation, and preserved interfaces

The [approved draft and addenda](2026-11-08-b4-main-statement-draft.md),
[spec §6.3](../../spec/06-roles.md), and its 2026-11-12 K2 decision continue to
control the definitions. No language choice was made. In particular, every
unnamed argument is needed, output-only binders cannot become child inputs,
where clauses remain a conjunction, and actual cycle detection may follow
nominal arguments but never nominal bodies. The same-input rule includes
provably equal inputs, not just identical endpoint numbers.

`GeneralNominalSourceFormation.InitialSource registry context root` contains:
registry/role agreement; the existing constructor/primitive metadata contract;
linked root endpoints and outputs; self-bounded unnamed intervals in every
source model; every initial source identity below the persistent allocation
seed; and an empty allocation-ownership list. Finite slots, finite ordinary
constraints, and checked normalized observations are already fields of the
shared nominal state. Initialization uses the existing `initial`, so the packet,
edge, and alias journals are empty and the root site is registered.

`SourceFormed registry root state` is the inductive closure of those initial
records under the existing Step. It contains **no Readback, finite work list,
rank, accessibility, or termination premise**. `formed_iff_reachable` identifies
it exactly with a finite trace from such initial data; `step_preserves` proves
closure. Separate proofs derive seed and metadata preservation, initial frame
freshness, model inclusion back to the initial source, canonical site production,
recorded child edges, and registration of every generated occurrence. Thus
enqueue cannot fire on a generated demand in a SourceFormed state.

This is a certified-carrier formation contract and operational trace closure,
not a proof that an inference implementation produces it. `Checked registry`
is still a separate premise; SourceFormed does not certify declarations. It
allows unresolved heads, nonpoint intervals, and finite graphs with recursion;
it neither assumes finite denotations for every model nor excludes valid
nonpoint examples to force a size proof. It is not yet strong enough to derive
global progress.

`GeneralNominalCycleCompatibility` proves new selected judgments and updates
transport to the frozen earlier local/transition contracts. That recovers the
existing journal invariants without changing their producers. No existing Step,
Stable, Committed, Survivor, Emitted, or Evidence-facing definition was edited.
The new `stable_capture_exact` theorem retains the **Installable** premise:
Stable makes an eligible packet Committed, after which its capture constraints
hold in every journal model. It does not silently strengthen this to every raw
selected candidate without proving its joint eligibility. This distinction
matters for the I-23/V4 Evidence work.

### Semantically adequate interval readback, and a false stronger interpretation

`GeneralNominalSourceReadback.input` is the actual source allocation's merged
interval. `packet_capture_exact` proves, for every branch model and every actual
value, that fitting this interval is equivalent to fitting every original
occurrence of that binder. No centre or searched substitution is introduced.
`committed_capture_exact` and `stable_capture_exact` move that statement to every
journal model after commitment. These are semantic interval correspondences;
they are not finite Pattern labels or a Paterson measure.

`GeneralNominalCaptureAnchors.inspect_anchored` and `many_anchored` are mutual
induction proofs over the real recursive inspector. Every capture retaining
`some origin` also has `(origin, bounds)` in the report's anchors, including
nonpoint endpoint inspection and appended reports. `report_anchored` supplies
the previously missing producer invariant. Consequently
`SourceReadback.variable_child_origin` no longer asks the caller for an anchor
membership proof: actual observation existence and membership in the emitted
merged interval follow from source inspection and BranchModels. Captures whose
origin is `none`, and compound child provenance, remain separate issues.

The old `GeneralNominalCycleReadback.Readback` forces both parent and child
labels to be exact finite substitutions of a declaration's head and clause.
That may be a useful abstract ranking certificate, but interpreting these
labels as the actual endpoint denotations is too strong. The formal example in
`GeneralNominalReadbackCounterexample` reuses the existing general nonpoint
nominal carrier and checked Display declaration:

- The root is a known nominal list whose argument descriptor has different
  lower/upper source identities. In one real model the actual list is
  `list int`, and those argument endpoints are bottom and top.
- The general Survivor selects the list declaration and emits Display with
  those original argument endpoints. `selected` proves the new cycle-based
  Local judgment; `no_cycle` proves the entire represented graph is acyclic.
- This initial state satisfies InitialSource and SourceFormed, and the registry
  is Checked. The example is not excluded by source formation.
- The old Readback equations force the parent lower label to be `list (lo a)`
  and the child lower label to be `lo a`. If both denote the original endpoints,
  nominal invariance forces `lo a` equivalent to int, while the child requires
  it equivalent to bottom. The full-carrier probe separates these values.

`endpoint_exact_readback_impossible` quantifies over every old Readback and every
interpretation respecting the list constructor. It refutes the additional
`LowerExact` property. It does **not** prove that abstract Readback is empty,
that no interval-sensitive abstraction exists, or that Step is nonterminating.
The required replacement must relate matched structure and merged intervals by
containment/projection and prove an appropriate size bound; equality to each
original endpoint cannot be used as that bridge.

### Finite support across administrative updates

`GeneralNominalAdministrativeProgress.Update` consists exactly of the existing
merge and refresh update constructors, with their original guards. Each such
update maps back to the unchanged CycleSteps.At. It does not replace Step or
remove candidate installation from Step.

The finite support is computed, not supplied:

```text
support(start) = source IDs of start's context
                 ++ named output target IDs of start's registered sites
facts(start)   = Known(source), for source in support(start)
                 ++ Alias(a,b), for each pair of start's registered sites
```

Merges preserve the site list and can mention only those registered output
identities. Refresh preserves the site list and is constrained by its existing
source-support contract. `supported_update` proves that the source support is
preserved and a fact in this concrete finite list becomes true. All those facts
persist by the existing transition extension laws. Counting remaining false
facts therefore strictly decreases, yielding `accessible registry start` for
**every** starting journal, with no Checked, SourceFormed, FiniteBasis, or rank
argument. SourceFormed additionally supplies `formed_step_cases`: every actual
Step is either one of these administrative updates or a genuine uncommitted
candidate installation. There is no third enqueue case on a generated demand.

This bounds administrative sequences between installations; it does not bound
arbitrarily many installations. `SourceFormation.installation_reserves` also
shows why the initial source list alone cannot be a global support: an install
reserves identities strictly above the initial seed. A finite global basis must
bound the number and identities of candidate frames generated by descent; that
bound has not been derived. The Item 4b fixed-snapshot support theorem is not
misreported as such a bound.

### A formal obstruction in canonical site production

`GeneralNominalCanonicalSiteObstruction.nonpoint_not_related` proves that a
canonical pointSite with any unequal endpoint IDs cannot satisfy SameInputs
with **any** site. `formed_site_not_related` extends this to all such sites
reachable by the unchanged Step, because the actual producer always emits
canonical pointSite records.

The concrete theorem `equal_known_input_still_unmergeable` includes all of:
Checked registry; SourceFormed initial journal; both endpoints known; a real
journal model; and equivalence of the endpoints in **every** journal model.
Nevertheless the canonical site's SameInputs self-relation is false. Here the
two endpoint identities are distinct, but an ordinary equation proves their
values equal. Thus this is not ambiguity about the actual value of a broad
interval: it exposes lost provable identity in the current producer. The
owner's same-input rule already covers it.

The capture-anchor result does not fix this producer automatically. The frozen
`Emitted.canonical` requires `packet.children.map pointSite`; it cannot retain a
nonpoint capture origin merely because another theorem has recovered that
origin. Complete same-input recognition, annotation retention, and journal
constraint feedback into K2 are still required before claiming a complete
source transition system. SourceFormed was not strengthened to exclude this
valid interval case.

### Unformalized candidate for an infinite update chain

This is a falsifier to investigate, **not a proved counterexample to Acc**.
The independent reviewer found no blocking gate in the current contracts, but
neither the complete declaration certificate nor the infinite family of
refresh/update witnesses was constructed in Lean in this change.

Consider the declaration shape:

```yulang
impl R (list 'a) where R('a, out = 'a):
  type out = list 'a
```

The unnamed where input descends from `list 'a` to `'a`; the named equation uses
an input binder. Start with distinct lower/upper IDs `lo`, `up`, an ordinary
equation `lo ≈ up`, a known outer list parameterized by `(lo,up)`, and a root
request `out = lo`. Installing its branch makes the journal entail the recursive
equation `A ≈ list A`; the fresh named output of the where child denotes A too.
The two child endpoint IDs still differ, so pointSite records no provenance and
SameInputs cannot force the merge that would expose the output equality in the
ordinary context.

The proposed next refresh represents lo/up as list nodes pointing to that fresh
output, which remains unresolved. The stronger journal justifies these heads,
while raw context Models can still contain finite-depth list assignments ending
at the fresh output. Thus the context's semantic actual-argument graph need not
have a return edge. A next installation can reserve another frame/output and
repeat the construction. The journal has a regular `μ ≈ list μ` model throughout,
while each finite raw context can look acyclic. With identical endpoint IDs,
pointSite would retain provenance and merging would expose the equality; the
nonpoint case is the suspected escape.

This mechanism must be ruled out or formalized before a positive general Acc
proof is sound. It points to the already identified producer/feedback gap, not
a new owner semantic question. The lazy implementation position remains: do
not promote the current partial source boundary to B4 termination. Preserve the
frozen interfaces and build an additive, provenance-retaining transition bridge
with complete ordinary/projection/materialization feedback, or prove a concrete
blocking invariant for the existing relation. A source-formation predicate that
simply includes the desired rank would not answer the task.

### Concrete boundary and the twelve V3 bridge fields

`GeneralNominalProgressBoundary.boundary roles evidence` assembles the existing
cycle-based local fields with the unchanged CycleSteps Step/Stable and journal
Generated. Its sole field parameter is the explicitly supplied Evidence
relation. Its vocabulary uses the general Registry, shared journal State,
Occurrence Demand, and full nominal Assignment. `frontiers` is explicitly a
**noncomputable classical selection** of the already independent Local relation;
this change does not provide an executable driver or decidability algorithm.

The following count is for this precise mathematical boundary family, for every
Evidence argument. It does not certify whole-language coverage of the source
relations or hide the outstanding SourceFormed/progress bridge.

| V3 B4Bridges field | Status for `boundary roles evidence` |
|---|---|
| progress | **OPEN**. Administrative accessibility is not full Step accessibility, even with SourceFormed. |
| execution | **OPEN**. No Executor.run supplied. |
| halted | **OPEN**. No final executor state supplied. |
| closure | **PROVED**: `GeneralNominalProgressBoundary.closure`, exact V3 field statement on every state. |
| stepModels | **PROVED**: `GeneralNominalProgressBoundary.stepModels`, exact V3 field statement on every state. |
| frontierLocal | **PROVED**: `GeneralNominalProgressBoundary.frontierLocal`, for the explicitly chosen classical protocol. |
| localIdentity | **PROVED**: `GeneralNominalProgressBoundary.localIdentity`, on every registry/state. |
| whereAccessible | **OPEN**. `whereAccessible_of_readback` still has the extra old Readback premise; SourceFormed does not discharge it. |
| treeExecution | **OPEN**. No executor/tree-production bridge. |
| canonicalLocalOrder | **OPEN**. No execution-order independence proof. |
| dictionaryRefl | **PROVED**: `GeneralNominalProgressBoundary.dictionaryRefl`. |
| evidenceNode | **OPEN here**, Evidence parameter only. I-23's stable-state V4 revision belongs to the other prover; no V4 claim is made. |

Thus **5/12 field statements proved; 7/12 open** for this Evidence-parameterized
boundary. The proofs of closure and stepModels need no SourceFormed premise;
their unrestricted statements are stronger than the requested formation-limited
versions. There is no complete B4Bridges value or completed B4 theorem.

### Thirteen-field source ledger

All fields are independent of an executor. “Defined” below describes the
existing certified relation; the separate coverage qualifications are retained.
No narrow fragment is used as a replacement general field.

| SourceBoundary field | Lean definition / status |
|---|---|
| Checked | Defined: `GeneralNominalCycleBoundary.localFields.Checked`, using `GeneralDeclarations.Checked` and role agreement. Separate from SourceFormed. |
| Models | Defined: `GeneralNominalSaturationState.Models`, unchanged full source plus journal conditions. |
| Step | Defined: `GeneralNominalCycleSteps.Step`, unchanged. General termination, complete provenance and feedback remain **MISSING**. |
| Stable | Defined: `GeneralNominalCycleSteps.Stable`, unchanged closure under these certified updates. Complete source-saturation correspondence remains **MISSING**. |
| Generated | Defined: `GeneralNominalSaturationState.Generated`, unchanged. Formed traces now derive registration for every generated occurrence. |
| RootPending | Defined: `GeneralNominalState.RootPending` on the context, unchanged. |
| RootK2 | Defined: `GeneralNominalCycleK2.RootK2` on the context. Complete source/journal cycle-observation correspondence remains **MISSING**. |
| CandidateK2 | Defined: `GeneralNominalCycleK2.CandidateK2`, unchanged; same observation/feedback qualification. |
| InspectionPending | Defined: `GeneralNominalCycleK2.InspectionPending`, unchanged; complete detection of every unsupported observation remains **MISSING**. |
| Survivor | Defined: `GeneralNominalRecursiveCandidates.Survivor`, unchanged. Complete joint local classification remains **MISSING**. |
| Evidence | Explicit parameter `GeneralNominalProgressBoundary.Evidence roles`; concrete Evidence integration remains **MISSING in this package**. |
| Reorders | Defined: `GeneralRegistryReordering.Reorders`, unchanged. |
| DictionaryEquivalent | Defined: `GeneralDictionaryPayloadOrder.Equivalent`, unchanged; reflexivity now appears as the exact boundary bridge field. |

### Full statements of new public theorems

The following are Lean's elaborated signatures. Conditional results retain their
premises. The source readback and obstruction theorems, and the administrative
termination result, are not presented as the requested general progress theorem.

```lean
@Yulang.GeneralNominalAdministrativeProgress.as_update : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {before after : Yulang.GeneralNominalSaturationState.State roles},
  Yulang.GeneralNominalAdministrativeProgress.Update registry before after →
    ∃ focus, Yulang.GeneralNominalCycleSteps.At registry before focus after
@Yulang.GeneralNominalAdministrativeProgress.sites_unchanged : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {before after : Yulang.GeneralNominalSaturationState.State roles},
  Yulang.GeneralNominalAdministrativeProgress.Update registry before after → after.sites = before.sites
@Yulang.GeneralNominalAdministrativeProgress.sources_bounded : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {before after : Yulang.GeneralNominalSaturationState.State roles},
  Yulang.GeneralNominalAdministrativeProgress.Update registry before after →
    Yulang.GeneralNominalState.sources after.context.state ⊆ Yulang.GeneralNominalAdministrativeProgress.support before
@Yulang.GeneralNominalAdministrativeProgress.supported_update : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry}
  (start before after : Yulang.GeneralNominalSaturationState.State roles),
  before.sites = start.sites →
    Yulang.GeneralNominalState.sources before.context.state ⊆
        Yulang.GeneralNominalAdministrativeProgress.support start →
      Yulang.GeneralNominalAdministrativeProgress.Update registry before after →
        after.sites = start.sites ∧
          Yulang.GeneralNominalState.sources after.context.state ⊆
              Yulang.GeneralNominalAdministrativeProgress.support start ∧
            ∃ fact,
              fact ∈ Yulang.GeneralNominalAdministrativeProgress.facts start ∧
                ¬Yulang.GeneralNominalSaturationProgress.Holds before fact ∧
                  Yulang.GeneralNominalSaturationProgress.Holds after fact
@Yulang.GeneralNominalAdministrativeProgress.accessible : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (start : Yulang.GeneralNominalSaturationState.State roles),
  Acc (fun next current => Yulang.GeneralNominalAdministrativeProgress.Update registry current next) start
@Yulang.GeneralNominalAdministrativeProgress.formed_step_cases : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {before after : Yulang.GeneralNominalSaturationState.State roles}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalSourceFormation.SourceFormed registry root before →
    Yulang.GeneralNominalCycleSteps.Step registry root before after →
      Yulang.GeneralNominalAdministrativeProgress.Update registry before after ∨
        ∃ packet emitted,
          Yulang.GeneralNominalCycleSteps.Installable registry before packet ∧
            ¬Yulang.GeneralNominalCycleSteps.Committed before packet ∧
              after = Yulang.GeneralNominalSaturationState.install before packet emitted
@Yulang.GeneralNominalCanonicalSiteObstruction.nonpoint_not_related : ∀ {roles : Yulang.Roles.RoleDecls}
  (models : Yulang.GeneralNominalCommonBridge.Assignment → Prop)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (index : Fin (roles root.demand.role).arity),
  (root.demand.arguments index).fst ≠ (root.demand.arguments index).snd →
    ∀ (other : Yulang.GeneralNominalDemandMerging.Site roles),
      ¬Yulang.GeneralNominalDemandMerging.SameInputs models (Yulang.GeneralNominalDemandMerging.pointSite root) other
@Yulang.GeneralNominalCanonicalSiteObstruction.formed_site_not_related : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralNominalSourceFormation.SourceFormed registry root state →
    ∀ (site : Yulang.GeneralNominalDemandMerging.Site roles),
      site ∈ state.sites →
        ∀ (index : Fin (roles site.occurrence.demand.role).arity),
          (site.occurrence.demand.arguments index).fst ≠ (site.occurrence.demand.arguments index).snd →
            ∀ (other : Yulang.GeneralNominalDemandMerging.Site roles),
              ¬Yulang.GeneralNominalDemandMerging.SameInputs (Yulang.GeneralNominalSaturationState.Models state) site
                  other
Yulang.GeneralNominalCanonicalSiteObstruction.equivalent_endpoints : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models Yulang.GeneralNominalCanonicalSiteObstruction.state assignment →
    Yulang.CommonNominalFullCarrier.Equivalent (assignment 0).fst (assignment 1).fst
Yulang.GeneralNominalCanonicalSiteObstruction.state_models : Yulang.GeneralNominalState.Models
  Yulang.GeneralNominalCanonicalSiteObstruction.state Yulang.GeneralNominalCanonicalSiteObstruction.model
Yulang.GeneralNominalCanonicalSiteObstruction.initial_source : Yulang.GeneralNominalSourceFormation.InitialSource
  Yulang.GeneralNominalCanonicalSiteObstruction.registry Yulang.GeneralNominalCanonicalSiteObstruction.context
  Yulang.GeneralNominalCanonicalSiteObstruction.root
Yulang.GeneralNominalCanonicalSiteObstruction.formed : Yulang.GeneralNominalSourceFormation.SourceFormed
  Yulang.GeneralNominalCanonicalSiteObstruction.registry Yulang.GeneralNominalCanonicalSiteObstruction.root
  (Yulang.GeneralNominalSaturationState.initial Yulang.GeneralNominalCanonicalSiteObstruction.context
    Yulang.GeneralNominalCanonicalSiteObstruction.root)
Yulang.GeneralNominalCanonicalSiteObstruction.known_inputs : Yulang.GeneralNominalState.Known
    Yulang.GeneralNominalCanonicalSiteObstruction.state 0 ∧
  Yulang.GeneralNominalState.Known Yulang.GeneralNominalCanonicalSiteObstruction.state 1
Yulang.GeneralNominalCanonicalSiteObstruction.equal_known_input_still_unmergeable : Yulang.GeneralDeclarations.Checked
    Yulang.GeneralNominalCanonicalSiteObstruction.registry ∧
  Yulang.GeneralNominalSourceFormation.SourceFormed Yulang.GeneralNominalCanonicalSiteObstruction.registry
      Yulang.GeneralNominalCanonicalSiteObstruction.root
      (Yulang.GeneralNominalSaturationState.initial Yulang.GeneralNominalCanonicalSiteObstruction.context
        Yulang.GeneralNominalCanonicalSiteObstruction.root) ∧
    (Yulang.GeneralNominalState.Known Yulang.GeneralNominalCanonicalSiteObstruction.state 0 ∧
        Yulang.GeneralNominalState.Known Yulang.GeneralNominalCanonicalSiteObstruction.state 1) ∧
      (∃ assignment,
          Yulang.GeneralNominalSaturationState.Models
            (Yulang.GeneralNominalSaturationState.initial Yulang.GeneralNominalCanonicalSiteObstruction.context
              Yulang.GeneralNominalCanonicalSiteObstruction.root)
            assignment) ∧
        (∀ (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
            Yulang.GeneralNominalSaturationState.Models
                (Yulang.GeneralNominalSaturationState.initial Yulang.GeneralNominalCanonicalSiteObstruction.context
                  Yulang.GeneralNominalCanonicalSiteObstruction.root)
                assignment →
              Yulang.CommonNominalFullCarrier.Equivalent (assignment 0).fst (assignment 1).fst) ∧
          ¬Yulang.GeneralNominalDemandMerging.SameInputs
              (Yulang.GeneralNominalSaturationState.Models
                (Yulang.GeneralNominalSaturationState.initial Yulang.GeneralNominalCanonicalSiteObstruction.context
                  Yulang.GeneralNominalCanonicalSiteObstruction.root))
              (Yulang.GeneralNominalDemandMerging.pointSite Yulang.GeneralNominalCanonicalSiteObstruction.root)
              (Yulang.GeneralNominalDemandMerging.pointSite Yulang.GeneralNominalCanonicalSiteObstruction.root)
Yulang.GeneralNominalCaptureAnchors.inspect_anchored : ∀ (state : Yulang.GeneralNominalState.State)
  (query : Yulang.GeneralNominalInspection.Query) (bounds : Yulang.GeneralNominalInspection.Bounds state)
  (origin : Option Yulang.GeneralNominalRecursiveInspection.Origin),
  Yulang.GeneralNominalCaptureAnchors.Anchored
    (Yulang.GeneralNominalRecursiveInspection.inspect state query bounds origin)
Yulang.GeneralNominalCaptureAnchors.many_anchored : ∀ (state : Yulang.GeneralNominalState.State)
  (queries : List Yulang.GeneralNominalInspection.Query) (bounds : List (Yulang.GeneralNominalInspection.Bounds state))
  (origins : Nat → Option Yulang.GeneralNominalRecursiveInspection.Origin) (index : Nat),
  Yulang.GeneralNominalCaptureAnchors.Anchored
    (Yulang.GeneralNominalRecursiveInspection.inspectMany state queries bounds origins index)
Yulang.GeneralNominalCaptureAnchors.report_anchored : ∀ (context : Yulang.GeneralNominalCandidates.Context)
  (declaration : Yulang.GeneralDeclarations.Declaration)
  (bounds : List (Yulang.GeneralNominalInspection.Bounds context.state)),
  Yulang.GeneralNominalCaptureAnchors.Anchored
    (Yulang.GeneralNominalRecursiveCandidates.report context declaration bounds)
@Yulang.GeneralNominalCycleCompatibility.selected_legacy : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {key : Nat}
  {children : List (Yulang.GeneralNominalCandidates.vocabulary roles).Demand}
  (context : Yulang.GeneralNominalCandidates.Context) (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralNominalCycleK2.Local registry context root
      (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
    Yulang.GeneralNominalLocalBoundary.Local (Yulang.GeneralNominalLocalBoundary.recursiveFields roles) registry context
      root (Yulang.CommonRoleOutermostResolver.Frontier.selected key children)
@Yulang.GeneralNominalCycleCompatibility.installable_legacy : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSaturationState.State roles}
  {packet : Yulang.GeneralNominalSaturationState.Packet roles},
  Yulang.GeneralNominalCycleSteps.Installable registry state packet →
    Yulang.GeneralNominalSaturationSteps.Installable registry state packet
@Yulang.GeneralNominalCycleCompatibility.update_legacy : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {before after : Yulang.GeneralNominalSaturationState.State roles}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalCycleSteps.At registry before focus after →
    Yulang.GeneralNominalSaturationSteps.At registry before focus after
@Yulang.GeneralNominalCycleCompatibility.step_legacy : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {before after : Yulang.GeneralNominalSaturationState.State roles}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalCycleSteps.Step registry root before after →
    Yulang.GeneralNominalSaturationSteps.Step registry root before after
@Yulang.GeneralNominalCycleCompatibility.steps_legacy : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {before after : Yulang.GeneralNominalSaturationState.State roles}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.B4Target.Steps (Yulang.GeneralNominalCycleSteps.Step registry root) before after →
    Yulang.B4Target.Steps (Yulang.GeneralNominalSaturationSteps.Step registry root) before after
@Yulang.GeneralNominalCycleCompatibility.generated_recorded : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {context : Yulang.GeneralNominalCandidates.Context}
  {root child : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {state : Yulang.GeneralNominalSaturationState.State roles},
  Yulang.B4Target.Steps (Yulang.GeneralNominalCycleSteps.Step registry root)
      (Yulang.GeneralNominalSaturationState.initial context root) state →
    Yulang.GeneralNominalSaturationState.Generated state root child →
      ∃ site, site ∈ state.sites ∧ site.occurrence = child
Yulang.GeneralNominalProgressBoundary.local_correspondence : ∀ (roles : Yulang.Roles.RoleDecls)
  (evidence : Yulang.GeneralNominalProgressBoundary.Evidence roles) (registry : Yulang.GeneralDeclarations.Registry)
  (state : Yulang.GeneralNominalSaturationState.State roles) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (frontier : Yulang.CommonRoleOutermostResolver.Frontier (Yulang.GeneralSourceDictionaries.Occurrence roles)),
  Yulang.B4TargetV3.Local (Yulang.GeneralNominalProgressBoundary.boundary roles evidence) registry state root frontier ↔
    Yulang.GeneralNominalCycleK2.Local registry state.context root frontier
Yulang.GeneralNominalProgressBoundary.localIdentity : ∀ (roles : Yulang.Roles.RoleDecls)
  (evidence : Yulang.GeneralNominalProgressBoundary.Evidence roles)
  (registry : (Yulang.GeneralNominalProgressBoundary.vocabulary roles).Registry)
  (state : (Yulang.GeneralNominalProgressBoundary.vocabulary roles).State),
  (Yulang.GeneralNominalProgressBoundary.frontiers roles evidence registry state).Local =
    Yulang.B4TargetV3.Local (Yulang.GeneralNominalProgressBoundary.boundary roles evidence) registry state
Yulang.GeneralNominalProgressBoundary.frontierLocal : ∀ (roles : Yulang.Roles.RoleDecls)
  (evidence : Yulang.GeneralNominalProgressBoundary.Evidence roles)
  (registry : (Yulang.GeneralNominalProgressBoundary.vocabulary roles).Registry),
  (Yulang.GeneralNominalProgressBoundary.boundary roles evidence).Checked registry →
    ∀ (state : (Yulang.GeneralNominalProgressBoundary.vocabulary roles).State)
      (root : (Yulang.GeneralNominalProgressBoundary.vocabulary roles).Demand)
      (frontier :
        Yulang.CommonRoleOutermostResolver.Frontier (Yulang.GeneralNominalProgressBoundary.vocabulary roles).Demand),
      (Yulang.GeneralNominalProgressBoundary.frontiers roles evidence registry state).frontier root = frontier ↔
        Yulang.B4TargetV3.Local (Yulang.GeneralNominalProgressBoundary.boundary roles evidence) registry state root
          frontier
Yulang.GeneralNominalProgressBoundary.stepModels : ∀ (roles : Yulang.Roles.RoleDecls)
  (evidence : Yulang.GeneralNominalProgressBoundary.Evidence roles)
  (registry : (Yulang.GeneralNominalProgressBoundary.vocabulary roles).Registry),
  (Yulang.GeneralNominalProgressBoundary.boundary roles evidence).Checked registry →
    ∀ (root : (Yulang.GeneralNominalProgressBoundary.vocabulary roles).Demand)
      (before after : (Yulang.GeneralNominalProgressBoundary.vocabulary roles).State),
      (Yulang.GeneralNominalProgressBoundary.boundary roles evidence).Step registry root before after →
        ∀ (model : (Yulang.GeneralNominalProgressBoundary.vocabulary roles).Model),
          (Yulang.GeneralNominalProgressBoundary.boundary roles evidence).Models after model →
            (Yulang.GeneralNominalProgressBoundary.boundary roles evidence).Models before model
Yulang.GeneralNominalProgressBoundary.closure : ∀ (roles : Yulang.Roles.RoleDecls)
  (evidence : Yulang.GeneralNominalProgressBoundary.Evidence roles)
  (registry : (Yulang.GeneralNominalProgressBoundary.vocabulary roles).Registry),
  (Yulang.GeneralNominalProgressBoundary.boundary roles evidence).Checked registry →
    ∀ (state : (Yulang.GeneralNominalProgressBoundary.vocabulary roles).State)
      (root : (Yulang.GeneralNominalProgressBoundary.vocabulary roles).Demand),
      (∀ (after : (Yulang.GeneralNominalProgressBoundary.vocabulary roles).State),
          ¬(Yulang.GeneralNominalProgressBoundary.boundary roles evidence).Step registry root state after) →
        (Yulang.GeneralNominalProgressBoundary.boundary roles evidence).Stable registry state root ∧
          ∀ (child : (Yulang.GeneralNominalProgressBoundary.vocabulary roles).Demand),
            (Yulang.GeneralNominalProgressBoundary.boundary roles evidence).Generated registry state root child →
              (Yulang.GeneralNominalProgressBoundary.boundary roles evidence).Stable registry state child
Yulang.GeneralNominalProgressBoundary.dictionaryRefl : ∀ (roles : Yulang.Roles.RoleDecls)
  (evidence : Yulang.GeneralNominalProgressBoundary.Evidence roles)
  (dictionary : Yulang.CommonRoleOutermostResolver.Dictionary),
  (Yulang.GeneralNominalProgressBoundary.boundary roles evidence).DictionaryEquivalent dictionary dictionary
Yulang.GeneralNominalProgressBoundary.whereAccessible_of_readback : ∀ (roles : Yulang.Roles.RoleDecls)
  (evidence : Yulang.GeneralNominalProgressBoundary.Evidence roles) (registry : Yulang.GeneralDeclarations.Registry),
  (Yulang.GeneralNominalProgressBoundary.boundary roles evidence).Checked registry →
    ∀ (state : Yulang.GeneralNominalSaturationState.State roles)
      (readback : Yulang.GeneralNominalCycleReadback.Readback roles registry state.context)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Acc
        (Yulang.CommonRoleOutermostResolver.Child
          (Yulang.B4TargetV3.Local (Yulang.GeneralNominalProgressBoundary.boundary roles evidence) registry state))
        root
Yulang.GeneralNominalProgressBoundary.step_preserves_formation : ∀ (roles : Yulang.Roles.RoleDecls)
  (evidence : Yulang.GeneralNominalProgressBoundary.Evidence roles) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (before after : Yulang.GeneralNominalSaturationState.State roles),
  Yulang.GeneralNominalSourceFormation.SourceFormed registry root before →
    (Yulang.GeneralNominalProgressBoundary.boundary roles evidence).Step registry root before after →
      Yulang.GeneralNominalSourceFormation.SourceFormed registry root after
Yulang.GeneralNominalProgressBoundary.models_trace : ∀ (roles : Yulang.Roles.RoleDecls)
  (evidence : Yulang.GeneralNominalProgressBoundary.Evidence roles) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (before after : Yulang.GeneralNominalSaturationState.State roles),
  Yulang.B4Target.Steps ((Yulang.GeneralNominalProgressBoundary.boundary roles evidence).Step registry root) before
      after →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      (Yulang.GeneralNominalProgressBoundary.boundary roles evidence).Models after model →
        (Yulang.GeneralNominalProgressBoundary.boundary roles evidence).Models before model
Yulang.GeneralNominalReadbackCounterexample.checked : Yulang.GeneralDeclarations.Checked
  Yulang.GeneralNominalReadbackCounterexample.registry
Yulang.GeneralNominalReadbackCounterexample.children_exact : Yulang.GeneralNominalReadbackCounterexample.children =
  [Yulang.GeneralNominalReadbackCounterexample.child]
Yulang.GeneralNominalReadbackCounterexample.prepared : Yulang.GeneralNominalRecursiveCandidates.Prepared
  Yulang.GeneralNominalReadbackCounterexample.registry Yulang.GeneralNominalReadbackCounterexample.context
  Yulang.GeneralNominalReadbackCounterexample.root Yulang.GeneralDeclarationExamples.display
  Yulang.GeneralDeclarationExamples.display_checked
Yulang.GeneralNominalReadbackCounterexample.survivor : Yulang.GeneralNominalRecursiveCandidates.Survivor
  Yulang.GeneralNominalReadbackCounterexample.registry Yulang.GeneralNominalReadbackCounterexample.context
  Yulang.GeneralNominalReadbackCounterexample.root 1 Yulang.GeneralNominalReadbackCounterexample.children
Yulang.GeneralNominalReadbackCounterexample.initial_source : Yulang.GeneralNominalSourceFormation.InitialSource
  Yulang.GeneralNominalReadbackCounterexample.registry Yulang.GeneralNominalReadbackCounterexample.context
  Yulang.GeneralNominalReadbackCounterexample.root
Yulang.GeneralNominalReadbackCounterexample.formed : Yulang.GeneralNominalSourceFormation.SourceFormed
  Yulang.GeneralNominalReadbackCounterexample.registry Yulang.GeneralNominalReadbackCounterexample.root
  (Yulang.GeneralNominalSaturationState.initial Yulang.GeneralNominalReadbackCounterexample.context
    Yulang.GeneralNominalReadbackCounterexample.root)
Yulang.GeneralNominalReadbackCounterexample.no_cycle : ∀
  (slot : Fin Yulang.GeneralNominalReadbackCounterexample.source.base.slots),
  ¬Yulang.GeneralNominalCycleK2.Cycle Yulang.GeneralNominalReadbackCounterexample.source slot
Yulang.GeneralNominalReadbackCounterexample.selected : Yulang.GeneralNominalCycleK2.Local
  Yulang.GeneralNominalReadbackCounterexample.registry Yulang.GeneralNominalReadbackCounterexample.context
  Yulang.GeneralNominalReadbackCounterexample.root
  (Yulang.CommonRoleOutermostResolver.Frontier.selected 1 Yulang.GeneralNominalReadbackCounterexample.children)
Yulang.GeneralNominalReadbackCounterexample.endpoint_exact_readback_impossible : ∀
  (readback :
    Yulang.GeneralNominalCycleReadback.Readback Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralNominalReadbackCounterexample.registry Yulang.GeneralNominalReadbackCounterexample.context)
  (interpret : Yulang.GeneralDeclarationPatterns.Pattern → Yulang.CommonNominalFullCarrier.Ty),
  (∀ (pattern : Yulang.GeneralDeclarationPatterns.Pattern),
      Yulang.CommonNominalFullCarrier.Equivalent (interpret (Yulang.GeneralDeclarationPatterns.Pattern.app 0 [pattern]))
        (Yulang.CommonNominalFullCarrier.nominal 0 [Sum.inl (interpret pattern)])) →
    ¬Yulang.GeneralNominalReadbackCounterexample.LowerExact readback interpret
@Yulang.GeneralNominalSourceFormation.formed_iff_reachable : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  (state : Yulang.GeneralNominalSaturationState.State roles),
  Yulang.GeneralNominalSourceFormation.SourceFormed registry root state ↔
    ∃ context,
      Yulang.GeneralNominalSourceFormation.InitialSource registry context root ∧
        Yulang.B4Target.Steps (Yulang.GeneralNominalCycleSteps.Step registry root)
          (Yulang.GeneralNominalSaturationState.initial context root) state
@Yulang.GeneralNominalSourceFormation.step_preserves : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSaturationState.State roles},
  Yulang.GeneralNominalSourceFormation.SourceFormed registry root before →
    Yulang.GeneralNominalCycleSteps.Step registry root before after →
      Yulang.GeneralNominalSourceFormation.SourceFormed registry root after
@Yulang.GeneralNominalSourceFormation.initial_journal : ∀ {roles : Yulang.Roles.RoleDecls}
  (context : Yulang.GeneralNominalCandidates.Context) (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  (Yulang.GeneralNominalSaturationState.initial context root).packets = [] ∧
    (Yulang.GeneralNominalSaturationState.initial context root).edges = [] ∧
      (Yulang.GeneralNominalSaturationState.initial context root).aliases = []
@Yulang.GeneralNominalSourceFormation.seed_update : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {before after : Yulang.GeneralNominalSaturationState.State roles}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalCycleSteps.At registry before focus after → after.context.state.seed = before.context.state.seed
@Yulang.GeneralNominalSourceFormation.seed_trace : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSaturationState.State roles},
  Yulang.B4Target.Steps (Yulang.GeneralNominalCycleSteps.Step registry root) before after →
    after.context.state.seed = before.context.state.seed
@Yulang.GeneralNominalSourceFormation.metadata_update : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {before after : Yulang.GeneralNominalSaturationState.State roles}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalRecursiveCandidates.Metadata registry before.context →
    Yulang.GeneralNominalCycleSteps.At registry before focus after →
      Yulang.GeneralNominalRecursiveCandidates.Metadata registry after.context
@Yulang.GeneralNominalSourceFormation.formed_metadata : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  (state : Yulang.GeneralNominalSaturationState.State roles),
  Yulang.GeneralNominalSourceFormation.SourceFormed registry root state →
    registry.roles = roles ∧ Yulang.GeneralNominalRecursiveCandidates.Metadata registry state.context
@Yulang.GeneralNominalSourceFormation.initial_fresh : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  (context : Yulang.GeneralNominalCandidates.Context),
  Yulang.GeneralNominalSourceFormation.InitialSource registry context root →
    ∀ (invocation : Nat), Yulang.GeneralNominalAllocation.Fresh context.state registry invocation
@Yulang.GeneralNominalSourceFormation.formed_provenance : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  (state : Yulang.GeneralNominalSaturationState.State roles),
  Yulang.GeneralNominalSourceFormation.SourceFormed registry root state →
    ∃ context,
      Yulang.GeneralNominalSourceFormation.InitialSource registry context root ∧
        state.context.state.seed = context.state.seed ∧
          (∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
              Yulang.GeneralNominalSaturationState.Models state model →
                Yulang.GeneralNominalState.Models context.state model) ∧
            Yulang.GeneralNominalSaturationInvariants.Canonical state ∧
              Yulang.GeneralNominalSaturationInvariants.EdgesRecorded state
@Yulang.GeneralNominalSourceFormation.generated_registered : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  (state : Yulang.GeneralNominalSaturationState.State roles),
  Yulang.GeneralNominalSourceFormation.SourceFormed registry root state →
    ∀ (focus : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Yulang.GeneralNominalSaturationState.Generated state root focus →
        ∃ site, site ∈ state.sites ∧ site.occurrence = focus
@Yulang.GeneralNominalSourceFormation.enqueue_unavailable : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  (state : Yulang.GeneralNominalSaturationState.State roles),
  Yulang.GeneralNominalSourceFormation.SourceFormed registry root state →
    ∀ (focus : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Yulang.GeneralNominalSaturationState.Generated state root focus →
        ¬∀ (site : Yulang.GeneralNominalDemandMerging.Site roles), site ∈ state.sites → site.occurrence ≠ focus
@Yulang.GeneralNominalSourceFormation.installation_reserves : ∀ {roles : Yulang.Roles.RoleDecls}
  (packet : Yulang.GeneralNominalSaturationState.Packet roles) (origin : Yulang.GeneralNominalAllocation.Origin),
  origin ∈ Yulang.GeneralNominalAllocation.keys packet.registry packet.site.occurrence.identity →
    Yulang.GeneralNominalAllocation.source packet.context.state packet.registry packet.site.occurrence.identity origin ∈
        Yulang.GeneralNominalState.sources packet.privateContext.state ∧
      packet.context.state.seed <
        Yulang.GeneralNominalAllocation.source packet.context.state packet.registry packet.site.occurrence.identity
          origin
@Yulang.GeneralNominalSourceReadback.packet_capture_exact : ∀ {roles : Yulang.Roles.RoleDecls}
  (packet : Yulang.GeneralNominalSaturationState.Packet roles) (model : Yulang.GeneralNominalCommonBridge.Assignment),
  packet.Holds model →
    ∀ (name : Nat),
      name ∈ packet.declaration.inputNames →
        Yulang.GeneralNominalAllocation.occurrences packet.bindings name ≠ [] →
          ∀ (actual : Yulang.CommonNominalFullCarrier.Ty),
            Yulang.GeneralNominalCaptureMerges.Fits model (Yulang.GeneralNominalSourceReadback.input packet name)
                actual ↔
              ∀ (bounds : Yulang.GeneralSourceState.Interval),
                bounds ∈ Yulang.GeneralNominalAllocation.occurrences packet.bindings name →
                  Yulang.GeneralNominalCaptureMerges.Fits model bounds actual
@Yulang.GeneralNominalSourceReadback.committed_capture_exact : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (packet : Yulang.GeneralNominalSaturationState.Packet roles),
  Yulang.GeneralNominalCycleSteps.Committed state packet →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models state model →
        ∀ (name : Nat),
          name ∈ packet.declaration.inputNames →
            Yulang.GeneralNominalAllocation.occurrences packet.bindings name ≠ [] →
              ∀ (actual : Yulang.CommonNominalFullCarrier.Ty),
                Yulang.GeneralNominalCaptureMerges.Fits model (Yulang.GeneralNominalSourceReadback.input packet name)
                    actual ↔
                  ∀ (bounds : Yulang.GeneralSourceState.Interval),
                    bounds ∈ Yulang.GeneralNominalAllocation.occurrences packet.bindings name →
                      Yulang.GeneralNominalCaptureMerges.Fits model bounds actual
@Yulang.GeneralNominalSourceReadback.stable_capture_exact : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralNominalCycleSteps.Stable registry state root →
    ∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
      packet.site.occurrence = root →
        Yulang.GeneralNominalCycleSteps.Installable registry state packet →
          ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
            Yulang.GeneralNominalSaturationState.Models state model →
              ∀ (name : Nat),
                name ∈ packet.declaration.inputNames →
                  Yulang.GeneralNominalAllocation.occurrences packet.bindings name ≠ [] →
                    ∀ (actual : Yulang.CommonNominalFullCarrier.Ty),
                      Yulang.GeneralNominalCaptureMerges.Fits model
                          (Yulang.GeneralNominalSourceReadback.input packet name) actual ↔
                        ∀ (bounds : Yulang.GeneralSourceState.Interval),
                          bounds ∈ Yulang.GeneralNominalAllocation.occurrences packet.bindings name →
                            Yulang.GeneralNominalCaptureMerges.Fits model bounds actual
@Yulang.GeneralNominalSourceReadback.variable_child_origin : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalRecursiveCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (declaration : Yulang.GeneralDeclarations.Declaration)
  (checked : Yulang.GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
  (bounds : List (Yulang.GeneralNominalInspection.Bounds context.state))
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalRecursiveCandidates.BranchModels registry context root declaration checked bounds model →
    ∀ (capture : Yulang.GeneralNominalRecursiveInspection.Capture context.state),
      capture ∈ (Yulang.GeneralNominalRecursiveCandidates.report context declaration bounds).captures →
        capture.name ∈ declaration.inputNames →
          ∀ (origin : Yulang.GeneralNominalRecursiveInspection.Origin),
            capture.origin = some origin →
              ∀ (clause : Yulang.GeneralDeclarations.Clause)
                (valid : Yulang.GeneralDeclarations.Clause.Signature roles clause)
                (index : Fin (roles clause.role).arity),
                Yulang.GeneralDeclarationPatterns.normalize clause.arguments[↑index] =
                    Yulang.GeneralDeclarationPatterns.Pattern.var capture.name →
                  let child :=
                    Yulang.GeneralDeclarationDemands.childDemand declaration clause valid
                      (Yulang.GeneralNominalAllocation.capture context.state registry root.identity declaration.id
                        (Yulang.GeneralNominalRecursiveInspection.bindings context.state
                          (Yulang.GeneralNominalRecursiveCandidates.report context declaration bounds)))
                      (Yulang.GeneralNominalAllocation.allocation context.state registry root.identity declaration.id
                        clause);
                  (∃ actual, Yulang.GeneralNominalRecursiveInspection.Observes model origin actual) ∧
                    ∀ (actual : Yulang.CommonNominalFullCarrier.Ty),
                      Yulang.GeneralNominalRecursiveInspection.Observes model origin actual →
                        Yulang.GeneralNominalCaptureMerges.Fits model (child.arguments index) actual
```

### Files and checks

Added modules:

- [`GeneralNominalAdministrativeProgress.lean`](../../lean/Yulang/GeneralNominalAdministrativeProgress.lean)
- [`GeneralNominalCanonicalSiteObstruction.lean`](../../lean/Yulang/GeneralNominalCanonicalSiteObstruction.lean)
- [`GeneralNominalCaptureAnchors.lean`](../../lean/Yulang/GeneralNominalCaptureAnchors.lean)
- [`GeneralNominalCycleCompatibility.lean`](../../lean/Yulang/GeneralNominalCycleCompatibility.lean)
- [`GeneralNominalProgressBoundary.lean`](../../lean/Yulang/GeneralNominalProgressBoundary.lean)
- [`GeneralNominalReadbackCounterexample.lean`](../../lean/Yulang/GeneralNominalReadbackCounterexample.lean)
- [`GeneralNominalSourceFormation.lean`](../../lean/Yulang/GeneralNominalSourceFormation.lean)
- [`GeneralNominalSourceReadback.lean`](../../lean/Yulang/GeneralNominalSourceReadback.lean)

Changed existing files: appended eight imports to `lean/Yulang.lean`, appended
57 public-theorem dependency print commands to `lean/Audit.lean`, and appended
this Item 4c section to the design note. Existing Step/Stable/Committed and all
other implementation lines are unchanged. No spec, plan, lake configuration,
commit, push, or git reference was changed.

Final commands from `lean/`:

```sh
lake build Yulang.GeneralNominalAdministrativeProgress Yulang.GeneralNominalCanonicalSiteObstruction Yulang.GeneralNominalCaptureAnchors Yulang.GeneralNominalCycleCompatibility Yulang.GeneralNominalProgressBoundary Yulang.GeneralNominalReadbackCounterexample Yulang.GeneralNominalSourceFormation Yulang.GeneralNominalSourceReadback > /tmp/astra-progress-focused.log 2>&1
lake build Yulang > /tmp/astra-progress-umbrella.log 2>&1
lake env lean Audit.lean > /tmp/astra-progress-audit.log 2>&1
```

All three commands exited **0**. The focused build completed 614 jobs and the
umbrella build completed 1520 jobs. The audit emitted 9735 dependency records;
each of the 57 new public theorem names appeared exactly once. Across the entire
audit, the only reported foundations were `propext`, `Classical.choice`, and
`Quot.sound`; there were no error diagnostics. Original byte prefixes of the two
existing Lean files were verified intact. Added source and this section passed
the restricted-token scan; `git diff --check` passed.

The [yulang-proofs skill](/home/momota1029/.codex/skills/yulang-proofs/SKILL.md)
was applied, including a separate read-only review of the new definitions and
proof statements. The reviewer found no theorem-level defect or frozen-interface
incompatibility and confirmed the five-field count. That review did not run
independent builds and is not a substitute for the Lean checks above.

Not verified or proved: an inference producer for InitialSource; general Step
accessibility; a globally finite set of installation frames; a construction of
the old Readback or an adequate interval-sensitive replacement rank;
unconditional where accessibility; complete nonpoint/compound child provenance;
complete journal-to-observation feedback; complete joint local classification;
a formal infinite update trace; an executable driver; or the B4 statement. The
abstract Readback is not proved impossible. These qualifications also apply to
the formal SourceBoundary assembly: it is not a completed faithful language
boundary merely because all structure fields now have expressions.

This work is converging on the shared general carriers: all new semantic facts
use the real allocation, nominal interval inspector, emitted demands, and
journal updates, rather than a scalar or settled fragment. However, more finite
pattern lemmas alone will not close the source bridge. The formal nonpoint
readback obstruction and the canonical-site provenance defect identify concrete
producer obligations that a global termination proof must handle. No new owner
semantic decision is needed for those defects; the existing interval, same-input,
and K2 decisions already determine the required behavior.

## Item 4d — provenance, journal feedback, and the R obstruction (2026-11-12)

The prioritized finite feedback obstruction is now proved on the old relation,
and its continuation is blocked on an additive journal-aware relation. A real
checked, SourceFormed, satisfiable two-step example installs the R packet and
refreshes its emitted child's lower root into a K2 rejection. **General B4
termination is still open.** Administrative termination is derived, but the
installation descent certificate and unconditional where accessibility are not.
No infinite trace of the old relation is claimed.

### Authority and unchanged interfaces

The definitions follow [spec §6.3](../../spec/06-roles.md) (same-input demands,
associated outputs, unnamed-input Paterson checking), its 2026-11-12 root-on-cycle
K2 decision, and the [draft addenda 1–4](2026-11-08-b4-main-statement-draft.md).
The owner's current clarification says that installed packets, materialized
outputs, and merges are solver information and therefore must affect K2 and
same-input recognition. No new language choice is made or requested.

All existing Lean implementation lines remain intact, including the old
`Emitted.canonical`, Step, Stable, Committed, and dictionary-facing Survivor.
The new boundary is `GeneralNominalFeedbackBoundary.boundary roles evidence`.
It shares the old general Registry, nominal journal State, Occurrence demands,
Assignment, allocation, and full where-child lists. Evidence is still supplied
as a parameter. `survivor_unchanged` states the exact old Survivor correspondence.

This uses the permitted **separate emission and transition variant**. It is not
claimed to be a relational superset of the old Step: retaining every old update
would retain any bad old continuation too. Installation effects are model-equivalent;
installation eligibility is strengthened by journal-aware K2 and merging.
There is no execution bisimulation or executor in this change.

### Provenance and same-input recognition

`GeneralNominalFeedbackSites.OriginAt` records the actual declaration clause,
its signature, the emitted child identity, the input position, and a matching
variable capture in the real inspection report. `childOrigin` selects a retained
origin from this finite source provenance; `childSite` preserves it even when
its interval endpoints differ. The existing repeated-capture correspondence
proves that this actual value fits the emitted merged interval. The selected
origin is not an arbitrary value fitting that interval, and no centre or searched
type substitution is introduced. If no retained variable origin exists, the
existing conservative point-site fallback remains.

`emitted` contains exactly the old `packet.children`, including named equations,
with their identities and order. The new Step fixes this producer; the general
`Emission.sound` certificate alone does not authorize arbitrary emissions.
`install_models` states the exact conjunction of old journal Models and the
packet's conditions; `install_equivalent` identifies it with the old canonical
installation's model set. The old and new journals can have different provenance
annotations while retaining the same demand identities and semantic conditions.

`recover` additionally fills a missing origin only if the **same interval's**
lower and upper endpoints are equivalent in every journal model. It then uses
the lower endpoint's actual source identity. Existing origins are retained.
`recover_sound` proves the result's SiteHolds condition. Equality of two broad
intervals or a shared bound is insufficient. `SameInputs` applies the existing
all-input observation equivalence to the recovered sites, using full journal
Models. Named outputs are not input positions compared by SameInputs; their entailed
consequences may contribute to journal equality.

The generic merge theorem preserves models satisfying both recovered sites'
DictionaryOutputs under the same congruent associated interpretation. This
retains the existing Evidence-side interpretation premise; it does not invent
a proof that arbitrary independently supplied dictionaries share that meaning.
The existing `capture_determines_associated` bridge remains the declaration-side
basis for that interface.

Regressions prove both that the Item 4c nonpoint self-recognition defect is
repaired and that two **distinct occurrence identities** with nonpoint inputs
perform a real new merge. Its associated output targets become equal, and a
concrete model of the merged state proves the example is nonvacuous.

### Journal observations, K2, and feedback transitions

`GeneralNominalFeedbackK2` defines a graph over the finite list of source
identities of the context:

- Structural edges use the checked normalized view, transporting their endpoints
  by journal-entailed equality. Hidden-field removal remains the existing
  normalization's responsibility.
- Nominal edges require an observation of an **actual explicit argument** and
  its equality to the destination in every full journal model. They can use
  associated-output/materialization information absent from raw context Models.
  Nominal bodies never supply edges.
- Equality transports a constructor edge; equality alone is never an edge.
- New semantic recurrence requires a real journal model. Inconsistent stores
  cannot create a new cycle by vacuous universal entailment.

The new RootK2 and CandidateK2 extend the old cycle predicates. Candidate K2
uses actual positions inspected by non-variable patterns; variables introduce
no inspection. Both keep the readiness gates. Local retains V3's priorities:
pending first, either K2 reason before inspection pending/ambiguity, and empty
candidate rejection guarded by completed inspection. New nominal edges have
explicit observation soundness and model-restriction lemmas.

The new Step includes origin-preserving installation, journal-aware merging,
the existing certified head-refresh contract, and `equate`. The latter adds
ordinary source equality already entailed by the journal, only when it is not
yet entailed by raw context Models. It preserves journal Models exactly and
makes the equality available to the raw context. No redundant spelling of an
already entailed equality earns a step. A new installation must satisfy both
the old full eligibility condition and the new Local/MergesClosed conditions.
Unknown roots cannot be installed merely because a candidate is unique.

Stable is closure under these new updates over every Generated occurrence.
`stable_committed` proves commitment for every **Installable** generated packet;
it does not drop joint eligibility and claim commitment for every raw selected
candidate. `stable_equality_feedback` proves that stable journals expose every
entailed equality between supported source identities to raw Models.

**Coverage limit:** journal Argument is an independent semantic observation
relation, not a total normalization algorithm. Structural materialization
without a checked normalized structural view, arbitrary missing head production,
compound child provenance, and complete joint local classification remain open.
The following concrete refresh is constructed; the general producer of all
required normalized snapshots is not. These limitations are not replaced by
false rejection or by a fragment classifier.

### The old finite obstruction and the blocked new continuation

The real declaration is checked by the general checker:

```yulang
impl R (list 'a) where R('a, out = 'a):
    type out = list 'a
```

There are no output-only binders in this declaration. The unnamed child input
is strictly smaller than the head; the associated equation uses an input binder.
The four-slot source has list descriptors at slots 0/1, parameter endpoints 2/3,
and the ordinary equation `2 ≈ 3`. Its root is `R` on `(0,0)` requesting `out = 2`.
The where child uses the nonpoint interval `(2,3)` and a fresh named output target.

`FeedbackObstruction.old_step` proves an actual old CycleSteps installation.
`old_formed` proves reachability from InitialSource; `checked` checks the registry.
The regular nominal model `μ ≈ list μ` satisfies the packet and installed journal.
The actual generated materialization schema has the source-2 list test and the
associated variable uses; `packet_self_argument` derives source 2's actual
nominal self-edge from those constraints and the ordinary endpoint equation.

Yet the old private context has a different, finite model: slots 0/1 are
`list int`, and slots 2/3 and fresh identities are `int`. That model violates the
packet's source-2 nominal test. Hence `old_context_incomplete` proves that raw
context Models omit real installed information. `old_child_pending` confirms
that the old child's lower head is still unresolved. This is a reachable finite
feedback obstruction, **not** an infinite old trace or a proof that every old
scheduler diverges. The old relation can also choose a sufficiently informative
refresh. Its installation guard does not require `ContextComplete`.

`FeedbackRefresh.self_equation` proves `source 2 ≈ list(source 2)` in every packet
model. Its actual `refresh_certificate` retains the old nonpoint descriptors and
adds the entailed descriptor at slot 2 with argument `(2,2)`. The certificate
proves Refines, unchanged source support/interpretation, and exact preservation
of all journal models. It yields a real new refresh Step and a raw DirectCycle.

`FeedbackRegressions.two_steps_reject_child` combines the new initial installation
and refresh: Checked, SourceFormed, the two-step path, a journal model, and the
child's new Local rejection are proved together. The child is rejected for its
own reached root cycle; no failed child is folded into a parent rejection.

The general `FeedbackSteps.self_argument_blocks_trace` is stronger than merely
exhibiting that refresh: once a journal entails a self-argument at source x,
**no packet with unnamed lower endpoint x can be installed after any finite
new-Step trace**. Entailment persists by model inclusion. A purported enabled
installation supplies its own model witness and readiness, which force RootK2
and contradict its new Local selection. `FeedbackObstruction.chain_blocked`
specializes this to the emitted R child. Thus another child installation cannot
escape by choosing a weak refresh. The theorem does not assert a scheduling
fairness property or that every trace takes the displayed refresh.

### Progress proved, and exact remaining obligations

Every new update adds a persistent fact: a site, packet condition, child edge,
alias, known head, or raw source equality. `FeedbackProgress` proves both journal
model inclusion and raw-context model inclusion, so equality facts persist.
It supplies `accessible_of_finite_basis` for the new relation, retaining the
finite-basis premise explicitly.

`FeedbackAdministrative.accessible` is stronger in its domain: accessibility of
**all merge/refresh/equality-only sequences** is derived for every starting
journal without a supplied basis. The computed support is the starting source
IDs plus registered output targets. The computed facts are Known entries,
alias pairs of registered sites, and equality pairs of those supported IDs.
No administrative step changes the site list. Model inclusion preserves facts,
and each update makes a previously false fact true. Duplicated ordinary atoms
therefore cannot reset this measure. Candidate installations remain in the full
Step and may introduce fresh identities beyond this support.

`FeedbackDescent` proves recorded child provenance and registration of every
Generated demand on SourceFormed traces. Consequently enqueue cannot be the
next update there. It reduces full progress to this exact sufficient contract:

```lean
structure InstallationDescent (registry : Registry) (root : Occurrence roles) where
  rank : State roles → Nat
  administrative : ∀ before after, SourceFormed registry root before →
    GeneralNominalFeedbackAdministrative.Update registry before after →
    rank after ≤ rank before
  installation : ∀ before, SourceFormed registry root before → ∀ packet : Packet roles,
    Installable registry before packet → ¬ Committed before packet →
    rank (GeneralNominalFeedbackSites.install before packet
      (GeneralNominalFeedbackSites.emitted packet)) < rank before
```

`accessible_of_installation_descent` proves full Step accessibility from this
contract and SourceFormed, using nested induction on rank and the independently
proved administrative accessibility. **No construction of InstallationDescent
from Checked and source data is supplied.** It must account for the entire
pending work of conjunction children, invariant nonpoint captures, source
allocation, and restrictions caused by later information. The old endpoint-exact
readback interpretation remains invalid; its Item 4c obstruction was not removed
by fixing feedback. A derived well-founded installation measure can replace this
sufficient natural-number contract if necessary.

For unconditional where accessibility, the sufficient missing correspondence
is a source-derived rank on occurrences with strict decrease on
`CommonRoleOutermostResolver.Child (GeneralNominalFeedbackK2.Local registry state)`
for Checked, SourceFormed states (or an equivalent derived accessibility proof).
The implemented `whereAccessible_of_readback` still takes the old Readback as a
premise and transports selected nodes to the old relation. Neither a rank nor
Readback is inserted into SourceFormed. SourceFormed continues to mean initial
finite certified source data followed by actual new Steps, with Checked separate.

These are formation-qualified goals. The current boundary's State type is still
the unrestricted shared journal carrier; promoting a formation-qualified progress
result to V3's all-state field would additionally require an appropriate
initial-state restriction or an all-state proof. No such promotion is claimed.

### Twelve V3 bridge fields for the new boundary

This count is specifically for
`GeneralNominalFeedbackBoundary.boundary roles evidence`, for arbitrary Evidence,
and `GeneralNominalFeedbackBoundary.frontiers roles evidence`. The frontiers
remain a noncomputable classical choice of the independent Local judgment.

| V3 field | Status |
|---|---|
| progress | **OPEN**. `progress_of_installation_descent` has the explicit unconstructed descent premise and SourceFormed. |
| execution | **OPEN**. No executor. |
| halted | **OPEN**. No executor final-state bridge. |
| closure | **PROVED**, exact field: `FeedbackBoundary.closure`. |
| stepModels | **PROVED**, exact field: `FeedbackBoundary.stepModels`. |
| frontierLocal | **PROVED**, exact field: `FeedbackBoundary.frontierLocal`. |
| localIdentity | **PROVED**, exact field: `FeedbackBoundary.localIdentity`. |
| whereAccessible | **OPEN**. Extra Readback premise remains. |
| treeExecution | **OPEN**. No execution/tree correspondence. |
| canonicalLocalOrder | **OPEN**. No final-state order-independence proof. |
| dictionaryRefl | **PROVED**, exact field: `FeedbackBoundary.dictionaryRefl`. |
| evidenceNode | **OPEN in this package**. Evidence is supplied; the other prover owns its V4 integration. |

Thus **5/12 exact field statements, 7/12 open**. Conditional progress and
conditional where accessibility are not counted as closed fields. The formal
assembly is not a completed whole-language B4 boundary.

### Thirteen-field source ledger

All fields are independent of an executor; no narrow carrier replaces a general
field. “Defined” retains the source-coverage qualifications above.

| SourceBoundary field | Definition / status in the new boundary |
|---|---|
| Checked | Existing general Checked plus role agreement, inherited by `FeedbackK2.fields`. |
| Models | `GeneralNominalSaturationState.Models`, unchanged full journal relation. |
| Step | `GeneralNominalFeedbackSteps.Step`; additive model-equivalent installation effects, new provenance and feedback guards. General termination **MISSING**. |
| Stable | `GeneralNominalFeedbackSteps.Stable`; closure for all Generated demands. Eligible packets committed; supported equality feedback complete at stability. General normalized-source saturation correspondence **MISSING**. |
| Generated | `GeneralNominalSaturationState.Generated`, unchanged. Registration proved on new SourceFormed traces. |
| RootPending | Existing `GeneralNominalState.RootPending` on raw normalized context; general entailed-head producer **MISSING**. |
| RootK2 | `GeneralNominalFeedbackK2.RootK2`; old certificates plus journal-derived cycles. Complete structural observation production **MISSING**. |
| CandidateK2 | `GeneralNominalFeedbackK2.CandidateK2`; journal cycles at actual inspected positions. Same production qualification. |
| InspectionPending | Existing cycle-aware InspectionPending, inherited. Complete joint classification/observation coverage **MISSING**. |
| Survivor | Existing `GeneralNominalRecursiveCandidates.Survivor`, unchanged; exact boundary correspondence proved. |
| Evidence | Explicit `GeneralNominalFeedbackBoundary.Evidence roles` parameter; concrete integration **MISSING here**. |
| Reorders | Existing `GeneralRegistryReordering.Reorders`. |
| DictionaryEquivalent | Existing `GeneralDictionaryPayloadOrder.Equivalent`; exact boundary reflexivity proved. |

### Full new public theorem statements

The following are Lean's elaborated signatures. Extra hypotheses are retained;
conditional progress is not represented as an unconditional source theorem.

```lean
@Yulang.GeneralNominalFeedbackAdministrative.as_update : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {before after : Yulang.GeneralNominalSaturationState.State roles},
  Yulang.GeneralNominalFeedbackAdministrative.Update registry before after →
    ∃ focus, Yulang.GeneralNominalFeedbackSteps.At registry before focus after
@Yulang.GeneralNominalFeedbackAdministrative.sites_unchanged : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {before after : Yulang.GeneralNominalSaturationState.State roles},
  Yulang.GeneralNominalFeedbackAdministrative.Update registry before after → after.sites = before.sites
@Yulang.GeneralNominalFeedbackAdministrative.sources_bounded : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {before after : Yulang.GeneralNominalSaturationState.State roles},
  Yulang.GeneralNominalFeedbackAdministrative.Update registry before after →
    Yulang.GeneralNominalState.sources after.context.state ⊆ Yulang.GeneralNominalAdministrativeProgress.support before
@Yulang.GeneralNominalFeedbackAdministrative.supported_update : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry}
  (start before after : Yulang.GeneralNominalSaturationState.State roles),
  before.sites = start.sites →
    Yulang.GeneralNominalState.sources before.context.state ⊆
        Yulang.GeneralNominalAdministrativeProgress.support start →
      Yulang.GeneralNominalFeedbackAdministrative.Update registry before after →
        after.sites = start.sites ∧
          Yulang.GeneralNominalState.sources after.context.state ⊆
              Yulang.GeneralNominalAdministrativeProgress.support start ∧
            ∃ fact,
              fact ∈ Yulang.GeneralNominalFeedbackAdministrative.facts start ∧
                ¬Yulang.GeneralNominalFeedbackProgress.Holds before fact ∧
                  Yulang.GeneralNominalFeedbackProgress.Holds after fact
@Yulang.GeneralNominalFeedbackAdministrative.accessible : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (start : Yulang.GeneralNominalSaturationState.State roles),
  Acc (fun next current => Yulang.GeneralNominalFeedbackAdministrative.Update registry current next) start
Yulang.GeneralNominalFeedbackBoundary.local_correspondence : ∀ (roles : Yulang.Roles.RoleDecls)
  (evidence : Yulang.GeneralNominalFeedbackBoundary.Evidence roles) (registry : Yulang.GeneralDeclarations.Registry)
  (state : Yulang.GeneralNominalSaturationState.State roles) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (frontier : Yulang.CommonRoleOutermostResolver.Frontier (Yulang.GeneralSourceDictionaries.Occurrence roles)),
  Yulang.B4TargetV3.Local (Yulang.GeneralNominalFeedbackBoundary.boundary roles evidence) registry state root frontier ↔
    Yulang.GeneralNominalFeedbackK2.Local registry state root frontier
Yulang.GeneralNominalFeedbackBoundary.localIdentity : ∀ (roles : Yulang.Roles.RoleDecls)
  (evidence : Yulang.GeneralNominalFeedbackBoundary.Evidence roles)
  (registry : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).Registry)
  (state : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).State),
  (Yulang.GeneralNominalFeedbackBoundary.frontiers roles evidence registry state).Local =
    Yulang.B4TargetV3.Local (Yulang.GeneralNominalFeedbackBoundary.boundary roles evidence) registry state
Yulang.GeneralNominalFeedbackBoundary.frontierLocal : ∀ (roles : Yulang.Roles.RoleDecls)
  (evidence : Yulang.GeneralNominalFeedbackBoundary.Evidence roles)
  (registry : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).Registry),
  (Yulang.GeneralNominalFeedbackBoundary.boundary roles evidence).Checked registry →
    ∀ (state : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).State)
      (root : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).Demand)
      (frontier :
        Yulang.CommonRoleOutermostResolver.Frontier (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).Demand),
      (Yulang.GeneralNominalFeedbackBoundary.frontiers roles evidence registry state).frontier root = frontier ↔
        Yulang.B4TargetV3.Local (Yulang.GeneralNominalFeedbackBoundary.boundary roles evidence) registry state root
          frontier
Yulang.GeneralNominalFeedbackBoundary.stepModels : ∀ (roles : Yulang.Roles.RoleDecls)
  (evidence : Yulang.GeneralNominalFeedbackBoundary.Evidence roles)
  (registry : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).Registry),
  (Yulang.GeneralNominalFeedbackBoundary.boundary roles evidence).Checked registry →
    ∀ (root : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).Demand)
      (before after : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).State),
      (Yulang.GeneralNominalFeedbackBoundary.boundary roles evidence).Step registry root before after →
        ∀ (model : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).Model),
          (Yulang.GeneralNominalFeedbackBoundary.boundary roles evidence).Models after model →
            (Yulang.GeneralNominalFeedbackBoundary.boundary roles evidence).Models before model
Yulang.GeneralNominalFeedbackBoundary.closure : ∀ (roles : Yulang.Roles.RoleDecls)
  (evidence : Yulang.GeneralNominalFeedbackBoundary.Evidence roles)
  (registry : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).Registry),
  (Yulang.GeneralNominalFeedbackBoundary.boundary roles evidence).Checked registry →
    ∀ (state : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).State)
      (root : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).Demand),
      (∀ (after : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).State),
          ¬(Yulang.GeneralNominalFeedbackBoundary.boundary roles evidence).Step registry root state after) →
        (Yulang.GeneralNominalFeedbackBoundary.boundary roles evidence).Stable registry state root ∧
          ∀ (child : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).Demand),
            (Yulang.GeneralNominalFeedbackBoundary.boundary roles evidence).Generated registry state root child →
              (Yulang.GeneralNominalFeedbackBoundary.boundary roles evidence).Stable registry state child
Yulang.GeneralNominalFeedbackBoundary.dictionaryRefl : ∀ (roles : Yulang.Roles.RoleDecls)
  (evidence : Yulang.GeneralNominalFeedbackBoundary.Evidence roles)
  (dictionary : Yulang.CommonRoleOutermostResolver.Dictionary),
  (Yulang.GeneralNominalFeedbackBoundary.boundary roles evidence).DictionaryEquivalent dictionary dictionary
Yulang.GeneralNominalFeedbackBoundary.whereAccessible_of_readback : ∀ (roles : Yulang.Roles.RoleDecls)
  (evidence : Yulang.GeneralNominalFeedbackBoundary.Evidence roles) (registry : Yulang.GeneralDeclarations.Registry),
  (Yulang.GeneralNominalFeedbackBoundary.boundary roles evidence).Checked registry →
    ∀ (state : Yulang.GeneralNominalSaturationState.State roles)
      (readback : Yulang.GeneralNominalCycleReadback.Readback roles registry state.context)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Acc
        (Yulang.CommonRoleOutermostResolver.Child
          (Yulang.B4TargetV3.Local (Yulang.GeneralNominalFeedbackBoundary.boundary roles evidence) registry state))
        root
Yulang.GeneralNominalFeedbackBoundary.step_preserves_formation : ∀ (roles : Yulang.Roles.RoleDecls)
  (evidence : Yulang.GeneralNominalFeedbackBoundary.Evidence roles) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (before after : Yulang.GeneralNominalSaturationState.State roles),
  Yulang.GeneralNominalFeedbackSteps.SourceFormed registry root before →
    (Yulang.GeneralNominalFeedbackBoundary.boundary roles evidence).Step registry root before after →
      Yulang.GeneralNominalFeedbackSteps.SourceFormed registry root after
Yulang.GeneralNominalFeedbackBoundary.models_trace : ∀ (roles : Yulang.Roles.RoleDecls)
  (evidence : Yulang.GeneralNominalFeedbackBoundary.Evidence roles) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (before after : Yulang.GeneralNominalSaturationState.State roles),
  Yulang.B4Target.Steps ((Yulang.GeneralNominalFeedbackBoundary.boundary roles evidence).Step registry root) before
      after →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      (Yulang.GeneralNominalFeedbackBoundary.boundary roles evidence).Models after model →
        (Yulang.GeneralNominalFeedbackBoundary.boundary roles evidence).Models before model
Yulang.GeneralNominalFeedbackBoundary.progress_of_installation_descent : ∀ (roles : Yulang.Roles.RoleDecls)
  (evidence : Yulang.GeneralNominalFeedbackBoundary.Evidence roles) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (descent : Yulang.GeneralNominalFeedbackDescent.InstallationDescent registry root)
  (state : Yulang.GeneralNominalSaturationState.State roles),
  Yulang.GeneralNominalFeedbackSteps.SourceFormed registry root state →
    Acc
      (fun next current =>
        (Yulang.GeneralNominalFeedbackBoundary.boundary roles evidence).Step registry root current next)
      state
Yulang.GeneralNominalFeedbackBoundary.survivor_unchanged : ∀ (roles : Yulang.Roles.RoleDecls)
  (evidence : Yulang.GeneralNominalFeedbackBoundary.Evidence roles) (registry : Yulang.GeneralDeclarations.Registry)
  (state : Yulang.GeneralNominalSaturationState.State roles) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
  (Yulang.GeneralNominalFeedbackBoundary.boundary roles evidence).Survivor registry state root key children ↔
    Yulang.GeneralNominalRecursiveCandidates.Survivor registry state.context root key children
@Yulang.GeneralNominalFeedbackDescent.edges_update : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSaturationState.State roles},
  Yulang.GeneralNominalSaturationInvariants.EdgesRecorded before →
    Yulang.GeneralNominalFeedbackSteps.At registry before focus after →
      Yulang.GeneralNominalSaturationInvariants.EdgesRecorded after
@Yulang.GeneralNominalFeedbackDescent.formed_journal : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {state : Yulang.GeneralNominalSaturationState.State roles},
  Yulang.GeneralNominalFeedbackSteps.SourceFormed registry root state →
    Yulang.GeneralNominalSaturationInvariants.EdgesRecorded state ∧ ∃ site, site ∈ state.sites ∧ site.occurrence = root
@Yulang.GeneralNominalFeedbackDescent.generated_registered : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root child : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {state : Yulang.GeneralNominalSaturationState.State roles},
  Yulang.GeneralNominalFeedbackSteps.SourceFormed registry root state →
    Yulang.GeneralNominalSaturationState.Generated state root child →
      ∃ site, site ∈ state.sites ∧ site.occurrence = child
@Yulang.GeneralNominalFeedbackDescent.formed_step_cases : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSaturationState.State roles},
  Yulang.GeneralNominalFeedbackSteps.SourceFormed registry root before →
    Yulang.GeneralNominalFeedbackSteps.Step registry root before after →
      Yulang.GeneralNominalFeedbackAdministrative.Update registry before after ∨
        ∃ packet,
          Yulang.GeneralNominalFeedbackSteps.Installable registry before packet ∧
            ¬Yulang.GeneralNominalFeedbackSteps.Committed before packet ∧
              after =
                Yulang.GeneralNominalFeedbackSites.install before packet
                  (Yulang.GeneralNominalFeedbackSites.emitted packet)
@Yulang.GeneralNominalFeedbackDescent.accessible_of_installation_descent : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  (descent : Yulang.GeneralNominalFeedbackDescent.InstallationDescent registry root)
  (state : Yulang.GeneralNominalSaturationState.State roles),
  Yulang.GeneralNominalFeedbackSteps.SourceFormed registry root state →
    Acc (fun next current => Yulang.GeneralNominalFeedbackSteps.Step registry root current next) state
@Yulang.GeneralNominalFeedbackK2.root_ready : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles} {root : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalFeedbackK2.RootK2 state root →
    ¬Yulang.GeneralNominalState.RootPending state.context.state root.demand
@Yulang.GeneralNominalFeedbackK2.candidate_ready : ∀ {registry : Yulang.GeneralDeclarations.Registry}
  {roles : Yulang.Roles.RoleDecls} {state : Yulang.GeneralNominalSaturationState.State roles}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalFeedbackK2.CandidateK2 registry state root →
    ¬Yulang.GeneralNominalState.RootPending state.context.state root.demand
@Yulang.GeneralNominalFeedbackK2.root_rejected : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralNominalFeedbackK2.RootK2 state root →
    Yulang.GeneralNominalFeedbackK2.Local registry state root Yulang.CommonRoleOutermostResolver.Frontier.rejected
@Yulang.GeneralNominalFeedbackK2.candidate_rejected : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralNominalFeedbackK2.CandidateK2 registry state root →
    Yulang.GeneralNominalFeedbackK2.Local registry state root Yulang.CommonRoleOutermostResolver.Frontier.rejected
@Yulang.GeneralNominalFeedbackK2.selected_legacy : ∀ {registry : Yulang.GeneralDeclarations.Registry}
  {roles : Yulang.Roles.RoleDecls} {state : Yulang.GeneralNominalSaturationState.State roles}
  {root : (Yulang.GeneralNominalCycleBoundary.vocabulary roles).Demand} {key : Nat}
  {children : List (Yulang.GeneralNominalCycleBoundary.vocabulary roles).Demand},
  Yulang.GeneralNominalFeedbackK2.Local registry state root
      (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
    Yulang.GeneralNominalCycleK2.Local registry state.context root
      (Yulang.CommonRoleOutermostResolver.Frontier.selected key children)
@Yulang.GeneralNominalFeedbackK2.local_total : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry),
  Yulang.GeneralDeclarations.Checked registry →
    ∀ (state : Yulang.GeneralNominalSaturationState.State roles)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      ∃ frontier, Yulang.GeneralNominalFeedbackK2.Local registry state root frontier
@Yulang.GeneralNominalFeedbackK2.local_functional : ∀ {registry : Yulang.GeneralDeclarations.Registry}
  {roles : Yulang.Roles.RoleDecls} {state : Yulang.GeneralNominalSaturationState.State roles}
  {root : (Yulang.GeneralNominalCycleBoundary.vocabulary roles).Demand}
  {first last :
    Yulang.CommonRoleOutermostResolver.Frontier (Yulang.GeneralNominalCycleBoundary.vocabulary roles).Demand},
  Yulang.GeneralNominalFeedbackK2.Local registry state root first →
    Yulang.GeneralNominalFeedbackK2.Local registry state root last → first = last
@Yulang.GeneralNominalFeedbackK2.equal_refl : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles) (source : Nat),
  Yulang.GeneralNominalFeedbackK2.Equal state source source
@Yulang.GeneralNominalFeedbackK2.equal_trans : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles} {first middle last : Nat},
  Yulang.GeneralNominalFeedbackK2.Equal state first middle →
    Yulang.GeneralNominalFeedbackK2.Equal state middle last → Yulang.GeneralNominalFeedbackK2.Equal state first last
@Yulang.GeneralNominalFeedbackK2.actual_argument : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles) (parent child : Fin state.context.state.base.slots),
  Yulang.GeneralNominalMixedRecurrence.ActualArgument state.context.state parent child →
    Yulang.GeneralNominalFeedbackK2.Argument state (state.context.state.base.source parent)
      (state.context.state.base.source child)
@Yulang.GeneralNominalFeedbackK2.argument_equal_target : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles} {first middle last : Nat},
  Yulang.GeneralNominalFeedbackK2.Argument state first middle →
    Yulang.GeneralNominalFeedbackK2.Equal state middle last → Yulang.GeneralNominalFeedbackK2.Argument state first last
@Yulang.GeneralNominalFeedbackK2.endpoint_argument : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles) (parent lower upper : Fin state.context.state.base.slots)
  (descriptor : Yulang.GeneralNominalState.Descriptor state.context.state.base.slots),
  state.context.state.nominals parent = some descriptor →
    ∀ (index : Nat),
      descriptor.arguments[index]? = some (Yulang.GeneralNominalState.Parameter.type (lower, upper)) →
        Yulang.GeneralNominalFeedbackK2.Equal state (state.context.state.base.source lower)
            (state.context.state.base.source upper) →
          Yulang.GeneralNominalFeedbackK2.Argument state (state.context.state.base.source parent)
            (state.context.state.base.source lower)
@Yulang.GeneralNominalFeedbackK2.self_argument_cycle : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles) (source : Nat),
  source ∈ Yulang.GeneralNominalState.sources state.context.state →
    Yulang.GeneralNominalFeedbackK2.Argument state source source →
      ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
        Yulang.GeneralNominalSaturationState.Models state model → Yulang.GeneralNominalFeedbackK2.RecursAt state source
@Yulang.GeneralNominalFeedbackK2.root_self_argument : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles) (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralNominalState.Linked state.context.state root.demand →
    ¬Yulang.GeneralNominalState.RootPending state.context.state root.demand →
      ∀ (index : Fin (roles root.demand.role).arity),
        Yulang.GeneralNominalFeedbackK2.Argument state (root.demand.arguments index).fst
            (root.demand.arguments index).fst →
          ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
            Yulang.GeneralNominalSaturationState.Models state model → Yulang.GeneralNominalFeedbackK2.RootK2 state root
@Yulang.GeneralNominalFeedbackK2.argument_sound : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles} {first last : Nat},
  Yulang.GeneralNominalFeedbackK2.Argument state first last →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models state model →
        ∃ name index actual,
          Yulang.GeneralNominalProjections.Observes model
              ((Yulang.GeneralNominalProjections.Ref.source first).argument name index) (Sum.inl actual) ∧
            Yulang.CommonNominalFullCarrier.Equivalent actual (model last).fst
@Yulang.GeneralNominalFeedbackK2.argument_model_restriction : ∀ {roles : Yulang.Roles.RoleDecls} {first last : Nat}
  {before after : Yulang.GeneralNominalSaturationState.State roles},
  (∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models after model →
        Yulang.GeneralNominalSaturationState.Models before model) →
    Yulang.GeneralNominalFeedbackK2.Argument before first last →
      Yulang.GeneralNominalFeedbackK2.Argument after first last
Yulang.GeneralNominalFeedbackObstruction.declaration_checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDeclarationExamples.roles
  Yulang.GeneralNominalFeedbackObstruction.declaration
Yulang.GeneralNominalFeedbackObstruction.checked : Yulang.GeneralDeclarations.Checked
  Yulang.GeneralNominalFeedbackObstruction.registry
Yulang.GeneralNominalFeedbackObstruction.report_exact : Yulang.GeneralNominalRecursiveCandidates.report
    Yulang.GeneralNominalFeedbackObstruction.context Yulang.GeneralNominalFeedbackObstruction.declaration [(0, 0)] =
  Yulang.GeneralNominalUnaryCaptureFacts.captured Yulang.GeneralNominalFeedbackObstruction.source 0 0 0 (2, 3)
Yulang.GeneralNominalFeedbackObstruction.children_exact : Yulang.GeneralNominalFeedbackObstruction.packet.children =
  [Yulang.GeneralNominalFeedbackObstruction.child]
Yulang.GeneralNominalFeedbackObstruction.schema_exact : Yulang.GeneralNominalRecursiveCandidates.generated
    Yulang.GeneralNominalFeedbackObstruction.registry Yulang.GeneralNominalFeedbackObstruction.context
    Yulang.GeneralNominalFeedbackObstruction.root Yulang.GeneralNominalFeedbackObstruction.declaration
    Yulang.GeneralNominalFeedbackObstruction.declaration_checked [(0, 0)] =
  {
    variables :=
      [{ name := 0, origin := (Yulang.GeneralNominalRecursiveInspection.Origin.source 2).nominal 0 0,
          mode := Yulang.GeneralNominalMaterialization.Mode.actual },
        { name := 0,
          origin :=
            Yulang.GeneralNominalRecursiveInspection.Origin.source Yulang.GeneralNominalFeedbackObstruction.output,
          mode := Yulang.GeneralNominalMaterialization.Mode.actual }],
    tests :=
      [(Yulang.GeneralNominalRecursiveInspection.Origin.source 2,
          Yulang.GeneralNominalRecursiveInspection.Test.nominal 0 1)] }
Yulang.GeneralNominalFeedbackObstruction.source_models : Yulang.GeneralNominalState.Models
  Yulang.GeneralNominalFeedbackObstruction.source Yulang.GeneralNominalFeedbackObstruction.model
Yulang.GeneralNominalFeedbackObstruction.packet_models : Yulang.GeneralNominalFeedbackObstruction.packet.Holds
  Yulang.GeneralNominalFeedbackObstruction.model
Yulang.GeneralNominalFeedbackObstruction.old_installed_models : Yulang.GeneralNominalSaturationState.Models
  Yulang.GeneralNominalFeedbackObstruction.oldInstalled Yulang.GeneralNominalFeedbackObstruction.model
Yulang.GeneralNominalFeedbackObstruction.installed_models : Yulang.GeneralNominalSaturationState.Models
  Yulang.GeneralNominalFeedbackObstruction.installed Yulang.GeneralNominalFeedbackObstruction.model
Yulang.GeneralNominalFeedbackObstruction.journal_endpoints : ∀ (m : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalFeedbackObstruction.packet.Holds m →
    Yulang.CommonNominalFullCarrier.Equivalent (m 2).fst (m 3).fst
Yulang.GeneralNominalFeedbackObstruction.packet_self_argument : ∀ (m : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalFeedbackObstruction.packet.Holds m →
    ∃ actual,
      Yulang.GeneralNominalProjections.Observes m ((Yulang.GeneralNominalProjections.Ref.source 2).argument 0 0)
          (Sum.inl actual) ∧
        Yulang.CommonNominalFullCarrier.Equivalent actual (m 2).fst
Yulang.GeneralNominalFeedbackObstruction.old_journal_self_argument : Yulang.GeneralNominalFeedbackK2.Argument
  Yulang.GeneralNominalFeedbackObstruction.oldInstalled 2 2
Yulang.GeneralNominalFeedbackObstruction.journal_self_argument : Yulang.GeneralNominalFeedbackK2.Argument
  Yulang.GeneralNominalFeedbackObstruction.installed 2 2
Yulang.GeneralNominalFeedbackObstruction.chain_blocked : ∀
  (after : Yulang.GeneralNominalSaturationState.State Yulang.GeneralDeclarationExamples.roles),
  Yulang.B4Target.Steps
      (Yulang.GeneralNominalFeedbackSteps.Step Yulang.GeneralNominalFeedbackObstruction.registry
        Yulang.GeneralNominalFeedbackObstruction.root)
      Yulang.GeneralNominalFeedbackObstruction.installed after →
    ∀ (next : Yulang.GeneralNominalSaturationState.Packet Yulang.GeneralDeclarationExamples.roles),
      next.site.occurrence = Yulang.GeneralNominalFeedbackObstruction.child →
        ¬Yulang.GeneralNominalFeedbackSteps.Installable Yulang.GeneralNominalFeedbackObstruction.registry after next
Yulang.GeneralNominalFeedbackObstruction.finite_source_models : Yulang.GeneralNominalState.Models
  Yulang.GeneralNominalFeedbackObstruction.source Yulang.GeneralNominalFeedbackObstruction.finiteModel
Yulang.GeneralNominalFeedbackObstruction.finite_private_models : Yulang.GeneralNominalState.Models
  Yulang.GeneralNominalFeedbackObstruction.packet.privateContext.state
  Yulang.GeneralNominalFeedbackObstruction.finiteModel
Yulang.GeneralNominalFeedbackObstruction.finite_not_packet : ¬Yulang.GeneralNominalFeedbackObstruction.packet.Holds
    Yulang.GeneralNominalFeedbackObstruction.finiteModel
Yulang.GeneralNominalFeedbackObstruction.old_context_incomplete : ¬Yulang.GeneralNominalSaturationState.ContextComplete
    Yulang.GeneralNominalFeedbackObstruction.oldInstalled
Yulang.GeneralNominalFeedbackObstruction.source_acyclic : ∀
  (slot : Fin Yulang.GeneralNominalFeedbackObstruction.source.base.slots),
  ¬Yulang.GeneralNominalCycleK2.Cycle Yulang.GeneralNominalFeedbackObstruction.source slot
Yulang.GeneralNominalFeedbackObstruction.prepared : Yulang.GeneralNominalRecursiveCandidates.Prepared
  Yulang.GeneralNominalFeedbackObstruction.registry Yulang.GeneralNominalFeedbackObstruction.context
  Yulang.GeneralNominalFeedbackObstruction.root Yulang.GeneralNominalFeedbackObstruction.declaration
  Yulang.GeneralNominalFeedbackObstruction.declaration_checked
Yulang.GeneralNominalFeedbackObstruction.survivor : Yulang.GeneralNominalRecursiveCandidates.Survivor
  Yulang.GeneralNominalFeedbackObstruction.registry Yulang.GeneralNominalFeedbackObstruction.context
  Yulang.GeneralNominalFeedbackObstruction.root 2 [Yulang.GeneralNominalFeedbackObstruction.child]
Yulang.GeneralNominalFeedbackObstruction.old_selected : Yulang.GeneralNominalCycleK2.Local
  Yulang.GeneralNominalFeedbackObstruction.registry Yulang.GeneralNominalFeedbackObstruction.context
  Yulang.GeneralNominalFeedbackObstruction.root
  (Yulang.CommonRoleOutermostResolver.Frontier.selected 2 [Yulang.GeneralNominalFeedbackObstruction.child])
Yulang.GeneralNominalFeedbackObstruction.old_enabled : Yulang.GeneralNominalCycleSteps.Installable
  Yulang.GeneralNominalFeedbackObstruction.registry Yulang.GeneralNominalFeedbackObstruction.initialState
  Yulang.GeneralNominalFeedbackObstruction.packet
Yulang.GeneralNominalFeedbackObstruction.old_step : Yulang.GeneralNominalCycleSteps.Step
  Yulang.GeneralNominalFeedbackObstruction.registry Yulang.GeneralNominalFeedbackObstruction.root
  Yulang.GeneralNominalFeedbackObstruction.initialState Yulang.GeneralNominalFeedbackObstruction.oldInstalled
Yulang.GeneralNominalFeedbackObstruction.initial_source : Yulang.GeneralNominalSourceFormation.InitialSource
  Yulang.GeneralNominalFeedbackObstruction.registry Yulang.GeneralNominalFeedbackObstruction.context
  Yulang.GeneralNominalFeedbackObstruction.root
Yulang.GeneralNominalFeedbackObstruction.old_formed : Yulang.GeneralNominalSourceFormation.SourceFormed
  Yulang.GeneralNominalFeedbackObstruction.registry Yulang.GeneralNominalFeedbackObstruction.root
  Yulang.GeneralNominalFeedbackObstruction.oldInstalled
Yulang.GeneralNominalFeedbackObstruction.old_child_pending : Yulang.GeneralNominalState.RootPending
  Yulang.GeneralNominalFeedbackObstruction.oldInstalled.context.state
  Yulang.GeneralNominalFeedbackObstruction.child.demand
@Yulang.GeneralNominalFeedbackProgress.at_extends : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {before after : Yulang.GeneralNominalSaturationState.State roles}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalFeedbackSteps.At registry before focus after →
    Yulang.GeneralNominalFeedbackProgress.Extends before after
@Yulang.GeneralNominalFeedbackProgress.monotone : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralNominalSaturationState.State roles},
  Yulang.GeneralNominalFeedbackProgress.Extends before after →
    ∀ (fact : Yulang.GeneralNominalFeedbackProgress.Fact roles),
      Yulang.GeneralNominalFeedbackProgress.Holds before fact → Yulang.GeneralNominalFeedbackProgress.Holds after fact
@Yulang.GeneralNominalFeedbackProgress.fresh_fact : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSaturationState.State roles},
  Yulang.GeneralNominalFeedbackSteps.Step registry root before after →
    ∃ fact,
      ¬Yulang.GeneralNominalFeedbackProgress.Holds before fact ∧ Yulang.GeneralNominalFeedbackProgress.Holds after fact
@Yulang.GeneralNominalFeedbackProgress.remaining_decreases : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralNominalSaturationState.State roles}
  (facts : List (Yulang.GeneralNominalFeedbackProgress.Fact roles)),
  Yulang.GeneralNominalFeedbackProgress.Extends before after →
    ∀ (fact : Yulang.GeneralNominalFeedbackProgress.Fact roles),
      fact ∈ facts →
        ¬Yulang.GeneralNominalFeedbackProgress.Holds before fact →
          Yulang.GeneralNominalFeedbackProgress.Holds after fact →
            Yulang.GeneralNominalFeedbackProgress.remaining facts after <
              Yulang.GeneralNominalFeedbackProgress.remaining facts before
@Yulang.GeneralNominalFeedbackProgress.accessible_of_finite_basis : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {start : Yulang.GeneralNominalSaturationState.State roles}
  (basis : Yulang.GeneralNominalFeedbackProgress.FiniteBasis registry root start),
  Acc (fun next current => Yulang.GeneralNominalFeedbackSteps.Step registry root current next) start
Yulang.GeneralNominalFeedbackRefresh.self_equation : ∀ (m : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalFeedbackObstruction.packet.Holds m →
    Yulang.CommonNominalFullCarrier.Equivalent (m 2).fst (Yulang.CommonNominalFullCarrier.nominal 0 [Sum.inl (m 2).fst])
Yulang.GeneralNominalFeedbackRefresh.child_known : Yulang.GeneralNominalState.Known
  Yulang.GeneralNominalFeedbackRefresh.refreshedState 2
Yulang.GeneralNominalFeedbackRefresh.refresh_step : Yulang.GeneralNominalFeedbackSteps.Step
  Yulang.GeneralNominalFeedbackObstruction.registry Yulang.GeneralNominalFeedbackObstruction.root
  Yulang.GeneralNominalFeedbackObstruction.installed Yulang.GeneralNominalFeedbackRefresh.refreshed
Yulang.GeneralNominalFeedbackRefresh.refresh_models : ∀ (m : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralNominalFeedbackRefresh.refreshed m ↔
    Yulang.GeneralNominalSaturationState.Models Yulang.GeneralNominalFeedbackObstruction.installed m
Yulang.GeneralNominalFeedbackRefresh.child_linked : Yulang.GeneralNominalState.Linked
  Yulang.GeneralNominalFeedbackRefresh.refreshedState Yulang.GeneralNominalFeedbackObstruction.child.demand
Yulang.GeneralNominalFeedbackRefresh.child_raw_K2 : Yulang.GeneralNominalCycleK2.RootK2
  Yulang.GeneralNominalFeedbackRefresh.refreshedState Yulang.GeneralNominalFeedbackObstruction.child.demand
Yulang.GeneralNominalFeedbackRefresh.child_rejected : Yulang.GeneralNominalFeedbackK2.Local
  Yulang.GeneralNominalFeedbackObstruction.registry Yulang.GeneralNominalFeedbackRefresh.refreshed
  Yulang.GeneralNominalFeedbackObstruction.child Yulang.CommonRoleOutermostResolver.Frontier.rejected
Yulang.GeneralNominalFeedbackRefresh.child_never_expanded : ∀
  (next : Yulang.GeneralNominalSaturationState.Packet Yulang.GeneralDeclarationExamples.roles),
  next.site.occurrence = Yulang.GeneralNominalFeedbackObstruction.child →
    ¬Yulang.GeneralNominalFeedbackSteps.Installable Yulang.GeneralNominalFeedbackObstruction.registry
        Yulang.GeneralNominalFeedbackRefresh.refreshed next
Yulang.GeneralNominalFeedbackRegressions.initial_acyclic : ∀ (source : Nat),
  ¬Yulang.GeneralNominalFeedbackK2.Cycle Yulang.GeneralNominalFeedbackObstruction.initialState source
Yulang.GeneralNominalFeedbackRegressions.selected : Yulang.GeneralNominalFeedbackK2.Local
  Yulang.GeneralNominalFeedbackObstruction.registry Yulang.GeneralNominalFeedbackObstruction.initialState
  Yulang.GeneralNominalFeedbackObstruction.root
  (Yulang.CommonRoleOutermostResolver.Frontier.selected 2 [Yulang.GeneralNominalFeedbackObstruction.child])
Yulang.GeneralNominalFeedbackRegressions.enabled : Yulang.GeneralNominalFeedbackSteps.Installable
  Yulang.GeneralNominalFeedbackObstruction.registry Yulang.GeneralNominalFeedbackObstruction.initialState
  Yulang.GeneralNominalFeedbackObstruction.packet
Yulang.GeneralNominalFeedbackRegressions.install_step : Yulang.GeneralNominalFeedbackSteps.Step
  Yulang.GeneralNominalFeedbackObstruction.registry Yulang.GeneralNominalFeedbackObstruction.root
  Yulang.GeneralNominalFeedbackObstruction.initialState Yulang.GeneralNominalFeedbackObstruction.installed
Yulang.GeneralNominalFeedbackRegressions.formed : Yulang.GeneralNominalFeedbackSteps.SourceFormed
  Yulang.GeneralNominalFeedbackObstruction.registry Yulang.GeneralNominalFeedbackObstruction.root
  Yulang.GeneralNominalFeedbackObstruction.installed
Yulang.GeneralNominalFeedbackRegressions.two_steps_reject_child : Yulang.GeneralDeclarations.Checked
    Yulang.GeneralNominalFeedbackObstruction.registry ∧
  Yulang.GeneralNominalFeedbackSteps.SourceFormed Yulang.GeneralNominalFeedbackObstruction.registry
      Yulang.GeneralNominalFeedbackObstruction.root Yulang.GeneralNominalFeedbackRefresh.refreshed ∧
    Yulang.B4Target.Steps
        (Yulang.GeneralNominalFeedbackSteps.Step Yulang.GeneralNominalFeedbackObstruction.registry
          Yulang.GeneralNominalFeedbackObstruction.root)
        Yulang.GeneralNominalFeedbackObstruction.initialState Yulang.GeneralNominalFeedbackRefresh.refreshed ∧
      Yulang.GeneralNominalSaturationState.Models Yulang.GeneralNominalFeedbackRefresh.refreshed
          Yulang.GeneralNominalFeedbackObstruction.model ∧
        Yulang.GeneralNominalFeedbackK2.Local Yulang.GeneralNominalFeedbackObstruction.registry
          Yulang.GeneralNominalFeedbackRefresh.refreshed Yulang.GeneralNominalFeedbackObstruction.child
          Yulang.CommonRoleOutermostResolver.Frontier.rejected
Yulang.GeneralNominalFeedbackRegressions.child_origin : Yulang.GeneralNominalFeedbackSites.OriginAt
  Yulang.GeneralNominalFeedbackObstruction.packet Yulang.GeneralNominalFeedbackObstruction.child 0
  ((Yulang.GeneralNominalRecursiveInspection.Origin.source 0).nominal 0 0)
Yulang.GeneralNominalFeedbackRegressions.nonpoint_origin_retained : (Yulang.GeneralNominalFeedbackObstruction.child.demand.arguments
        ⟨0, Yulang.GeneralNominalFeedbackRegressions.nonpoint_origin_retained._proof_1⟩).fst ≠
    (Yulang.GeneralNominalFeedbackObstruction.child.demand.arguments
        ⟨0, Yulang.GeneralNominalFeedbackRegressions.nonpoint_origin_retained._proof_1⟩).snd ∧
  ∃ origin,
    (Yulang.GeneralNominalFeedbackSites.childSite Yulang.GeneralNominalFeedbackObstruction.packet
              Yulang.GeneralNominalFeedbackObstruction.child).inputs[0]? =
        some (some origin) ∧
      Yulang.GeneralNominalFeedbackSites.OriginAt Yulang.GeneralNominalFeedbackObstruction.packet
        Yulang.GeneralNominalFeedbackObstruction.child 0 origin
@Yulang.GeneralNominalFeedbackRegressions.recovered_point_inputs : ∀ {roles' : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles')
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles'),
  (∀ (index : Fin (roles' root.demand.role).arity),
      Yulang.GeneralNominalFeedbackSites.EndpointEqual state (root.demand.arguments index)) →
    (Yulang.GeneralNominalFeedbackSites.recover state (Yulang.GeneralNominalDemandMerging.pointSite root)).inputs =
      List.ofFn fun index =>
        some (Yulang.GeneralNominalRecursiveInspection.Origin.source (root.demand.arguments index).fst)
@Yulang.GeneralNominalFeedbackRegressions.recovered_point_self : ∀ {roles' : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles')
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles'),
  (∀ (index : Fin (roles' root.demand.role).arity),
      Yulang.GeneralNominalFeedbackSites.EndpointEqual state (root.demand.arguments index)) →
    Yulang.GeneralNominalFeedbackSites.SameInputs state (Yulang.GeneralNominalDemandMerging.pointSite root)
      (Yulang.GeneralNominalDemandMerging.pointSite root)
Yulang.GeneralNominalFeedbackRegressions.equal_nonpoint_now_recognized : Yulang.GeneralNominalFeedbackSites.SameInputs
  (Yulang.GeneralNominalSaturationState.initial Yulang.GeneralNominalCanonicalSiteObstruction.context
    Yulang.GeneralNominalCanonicalSiteObstruction.root)
  (Yulang.GeneralNominalDemandMerging.pointSite Yulang.GeneralNominalCanonicalSiteObstruction.root)
  (Yulang.GeneralNominalDemandMerging.pointSite Yulang.GeneralNominalCanonicalSiteObstruction.root)
Yulang.GeneralNominalFeedbackRegressions.distinct_nonpoint_inputs_same : Yulang.GeneralNominalFeedbackSites.SameInputs
  Yulang.GeneralNominalFeedbackRegressions.mergeState
  (Yulang.GeneralNominalDemandMerging.pointSite Yulang.GeneralNominalFeedbackRegressions.mergeFirst)
  (Yulang.GeneralNominalDemandMerging.pointSite Yulang.GeneralNominalFeedbackRegressions.mergeLast)
Yulang.GeneralNominalFeedbackRegressions.distinct_nonpoint_merge_step : Yulang.GeneralNominalFeedbackSteps.Step
  Yulang.GeneralNominalFeedbackObstruction.registry Yulang.GeneralNominalFeedbackRegressions.mergeFirst
  Yulang.GeneralNominalFeedbackRegressions.mergeState
  (Yulang.GeneralNominalSaturationState.merge Yulang.GeneralNominalFeedbackRegressions.mergeState
    (Yulang.GeneralNominalDemandMerging.pointSite Yulang.GeneralNominalFeedbackRegressions.mergeFirst)
    (Yulang.GeneralNominalDemandMerging.pointSite Yulang.GeneralNominalFeedbackRegressions.mergeLast))
Yulang.GeneralNominalFeedbackRegressions.distinct_nonpoint_output_equation : ∀
  (m : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models
      (Yulang.GeneralNominalSaturationState.merge Yulang.GeneralNominalFeedbackRegressions.mergeState
        (Yulang.GeneralNominalDemandMerging.pointSite Yulang.GeneralNominalFeedbackRegressions.mergeFirst)
        (Yulang.GeneralNominalDemandMerging.pointSite Yulang.GeneralNominalFeedbackRegressions.mergeLast))
      m →
    Yulang.CommonNominalFullCarrier.Equivalent (m 2).fst (m 3).fst
Yulang.GeneralNominalFeedbackRegressions.distinct_nonpoint_merge_has_model : Yulang.GeneralNominalSaturationState.Models
  (Yulang.GeneralNominalSaturationState.merge Yulang.GeneralNominalFeedbackRegressions.mergeState
    (Yulang.GeneralNominalDemandMerging.pointSite Yulang.GeneralNominalFeedbackRegressions.mergeFirst)
    (Yulang.GeneralNominalDemandMerging.pointSite Yulang.GeneralNominalFeedbackRegressions.mergeLast))
  Yulang.GeneralNominalFeedbackObstruction.finiteModel
@Yulang.GeneralNominalFeedbackSites.origin_sound : ∀ {roles : Yulang.Roles.RoleDecls}
  (packet : Yulang.GeneralNominalSaturationState.Packet roles)
  (child : Yulang.GeneralSourceDictionaries.Occurrence roles) (index : Fin (roles child.demand.role).arity)
  (origin : Yulang.GeneralNominalRecursiveInspection.Origin),
  Yulang.GeneralNominalFeedbackSites.OriginAt packet child (↑index) origin →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      packet.Holds model →
        (∃ actual, Yulang.GeneralNominalRecursiveInspection.Observes model origin actual) ∧
          ∀ (actual : Yulang.CommonNominalFullCarrier.Ty),
            Yulang.GeneralNominalRecursiveInspection.Observes model origin actual →
              Yulang.GeneralNominalCaptureMerges.Fits model (child.demand.arguments index) actual
@Yulang.GeneralNominalFeedbackSites.child_retains_origin : ∀ {roles : Yulang.Roles.RoleDecls}
  (packet : Yulang.GeneralNominalSaturationState.Packet roles)
  (child : Yulang.GeneralSourceDictionaries.Occurrence roles) (index : Fin (roles child.demand.role).arity),
  (∃ origin, Yulang.GeneralNominalFeedbackSites.OriginAt packet child (↑index) origin) →
    ∃ origin,
      (Yulang.GeneralNominalFeedbackSites.childSite packet child).inputs[↑index]? = some (some origin) ∧
        Yulang.GeneralNominalFeedbackSites.OriginAt packet child (↑index) origin
@Yulang.GeneralNominalFeedbackSites.child_sound : ∀ {roles : Yulang.Roles.RoleDecls}
  (packet : Yulang.GeneralNominalSaturationState.Packet roles)
  (child : Yulang.GeneralSourceDictionaries.Occurrence roles) (model : Yulang.GeneralNominalCommonBridge.Assignment),
  packet.Holds model →
    Yulang.GeneralNominalSaturationState.SiteHolds (Yulang.GeneralNominalFeedbackSites.childSite packet child) model
@Yulang.GeneralNominalFeedbackSites.install_models : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (packet : Yulang.GeneralNominalSaturationState.Packet roles)
  (emission : Yulang.GeneralNominalFeedbackSites.Emission packet),
  packet.context = state.context →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralNominalFeedbackSites.install state packet emission)
          model ↔
        Yulang.GeneralNominalSaturationState.Models state model ∧ packet.Holds model
@Yulang.GeneralNominalFeedbackSites.install_equivalent : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (packet : Yulang.GeneralNominalSaturationState.Packet roles)
  (emission : Yulang.GeneralNominalFeedbackSites.Emission packet),
  packet.context = state.context →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralNominalFeedbackSites.install state packet emission)
          model ↔
        Yulang.GeneralNominalSaturationState.Models
          (Yulang.GeneralNominalSaturationState.install state packet
            (Yulang.GeneralNominalSaturationState.pointEmitted packet))
          model
@Yulang.GeneralNominalFeedbackSites.recover_sound : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles) (site : Yulang.GeneralNominalDemandMerging.Site roles)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models state model →
    Yulang.GeneralNominalSaturationState.SiteHolds site model →
      Yulang.GeneralNominalSaturationState.SiteHolds (Yulang.GeneralNominalFeedbackSites.recover state site) model
@Yulang.GeneralNominalFeedbackSites.merge_dictionary_models : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (first last : Yulang.GeneralNominalDemandMerging.Site roles),
  Yulang.GeneralNominalFeedbackSites.SameInputs state first last →
    ∀ (meaning : Yulang.GeneralNominalDemandMerging.AssociatedMeaning)
      (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models state model →
        Yulang.GeneralNominalDemandMerging.DictionaryOutputs meaning model
            (Yulang.GeneralNominalFeedbackSites.recover state first) →
          Yulang.GeneralNominalDemandMerging.DictionaryOutputs meaning model
              (Yulang.GeneralNominalFeedbackSites.recover state last) →
            Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralNominalSaturationState.merge state first last)
              model
@Yulang.GeneralNominalFeedbackSteps.equate_models : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles) (first last : Nat),
  Yulang.GeneralNominalFeedbackK2.Equal state first last →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralNominalFeedbackSteps.equate state first last) model ↔
        Yulang.GeneralNominalSaturationState.Models state model
@Yulang.GeneralNominalFeedbackSteps.equate_feedback : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles) (first last : Nat),
  Yulang.GeneralNominalFeedbackSteps.RawEqual (Yulang.GeneralNominalFeedbackSteps.equate state first last) first last
@Yulang.GeneralNominalFeedbackSteps.at_models : ∀ {registry : Yulang.GeneralDeclarations.Registry}
  {roles : Yulang.Roles.RoleDecls} {before : Yulang.GeneralNominalSaturationState.State roles}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {after : Yulang.GeneralNominalSaturationState.State roles},
  Yulang.GeneralNominalFeedbackSteps.At registry before focus after →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models after model → Yulang.GeneralNominalSaturationState.Models before model
@Yulang.GeneralNominalFeedbackSteps.step_models : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSaturationState.State roles},
  Yulang.GeneralNominalFeedbackSteps.Step registry root before after →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models after model → Yulang.GeneralNominalSaturationState.Models before model
@Yulang.GeneralNominalFeedbackSteps.steps_models : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSaturationState.State roles},
  Yulang.B4Target.Steps (Yulang.GeneralNominalFeedbackSteps.Step registry root) before after →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models after model → Yulang.GeneralNominalSaturationState.Models before model
@Yulang.GeneralNominalFeedbackSteps.installed_committed : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (packet : Yulang.GeneralNominalSaturationState.Packet roles),
  Yulang.GeneralNominalFeedbackSteps.Committed
    (Yulang.GeneralNominalFeedbackSites.install state packet (Yulang.GeneralNominalFeedbackSites.emitted packet)) packet
@Yulang.GeneralNominalFeedbackSteps.installed_children : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (packet : Yulang.GeneralNominalSaturationState.Packet roles)
  (child : Yulang.GeneralSourceDictionaries.Occurrence roles),
  child ∈ packet.children →
    Yulang.GeneralNominalSaturationState.Generated
      (Yulang.GeneralNominalFeedbackSites.install state packet (Yulang.GeneralNominalFeedbackSites.emitted packet))
      packet.site.occurrence child
@Yulang.GeneralNominalFeedbackSteps.rootK2_never_installed : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSaturationState.State roles}
  {packet : Yulang.GeneralNominalSaturationState.Packet roles},
  Yulang.GeneralNominalFeedbackK2.RootK2 state packet.site.occurrence →
    ¬Yulang.GeneralNominalFeedbackSteps.Installable registry state packet
@Yulang.GeneralNominalFeedbackSteps.candidateK2_never_installed : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSaturationState.State roles}
  {packet : Yulang.GeneralNominalSaturationState.Packet roles},
  Yulang.GeneralNominalFeedbackK2.CandidateK2 registry state packet.site.occurrence →
    ¬Yulang.GeneralNominalFeedbackSteps.Installable registry state packet
@Yulang.GeneralNominalFeedbackSteps.pending_never_installed : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSaturationState.State roles}
  {packet : Yulang.GeneralNominalSaturationState.Packet roles},
  Yulang.GeneralNominalState.RootPending state.context.state packet.site.occurrence.demand →
    ¬Yulang.GeneralNominalFeedbackSteps.Installable registry state packet
@Yulang.GeneralNominalFeedbackSteps.halted_stable : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSaturationState.State roles}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles},
  (∀ (after : Yulang.GeneralNominalSaturationState.State roles),
      ¬Yulang.GeneralNominalFeedbackSteps.Step registry root state after) →
    Yulang.GeneralNominalFeedbackSteps.Stable registry state root
@Yulang.GeneralNominalFeedbackSteps.stable_halted : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSaturationState.State roles}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalFeedbackSteps.Stable registry state root →
    ∀ (after : Yulang.GeneralNominalSaturationState.State roles),
      ¬Yulang.GeneralNominalFeedbackSteps.Step registry root state after
@Yulang.GeneralNominalFeedbackSteps.stable_generated : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSaturationState.State roles}
  {root child : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalFeedbackSteps.Stable registry state root →
    Yulang.GeneralNominalSaturationState.Generated state root child →
      Yulang.GeneralNominalFeedbackSteps.Stable registry state child
@Yulang.GeneralNominalFeedbackSteps.closure : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSaturationState.State roles}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles},
  (∀ (after : Yulang.GeneralNominalSaturationState.State roles),
      ¬Yulang.GeneralNominalFeedbackSteps.Step registry root state after) →
    Yulang.GeneralNominalFeedbackSteps.Stable registry state root ∧
      ∀ (child : Yulang.GeneralSourceDictionaries.Occurrence roles),
        Yulang.GeneralNominalSaturationState.Generated state root child →
          Yulang.GeneralNominalFeedbackSteps.Stable registry state child
@Yulang.GeneralNominalFeedbackSteps.stable_committed : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSaturationState.State roles}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalFeedbackSteps.Stable registry state root →
    ∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
      Yulang.GeneralNominalSaturationState.Generated state root packet.site.occurrence →
        Yulang.GeneralNominalFeedbackSteps.Installable registry state packet →
          Yulang.GeneralNominalFeedbackSteps.Committed state packet
@Yulang.GeneralNominalFeedbackSteps.stable_equality_feedback : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSaturationState.State roles}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalFeedbackSteps.Stable registry state root →
    ∀ (first last : Nat),
      first ∈ Yulang.GeneralNominalState.sources state.context.state →
        last ∈ Yulang.GeneralNominalState.sources state.context.state →
          Yulang.GeneralNominalFeedbackK2.Equal state first last →
            Yulang.GeneralNominalFeedbackSteps.RawEqual state first last
@Yulang.GeneralNominalFeedbackSteps.stable_merges : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {state : Yulang.GeneralNominalSaturationState.State roles}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalFeedbackSteps.Stable registry state root →
    ∀ (first last : Yulang.GeneralNominalDemandMerging.Site roles),
      first ∈ state.sites →
        last ∈ state.sites →
          Yulang.GeneralNominalSaturationState.Generated state root first.occurrence →
            Yulang.GeneralNominalFeedbackSites.SameInputs state first last →
              Yulang.GeneralNominalSaturationState.Alias state first.occurrence.identity last.occurrence.identity
@Yulang.GeneralNominalFeedbackSteps.step_preserves : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSaturationState.State roles},
  Yulang.GeneralNominalFeedbackSteps.SourceFormed registry root before →
    Yulang.GeneralNominalFeedbackSteps.Step registry root before after →
      Yulang.GeneralNominalFeedbackSteps.SourceFormed registry root after
@Yulang.GeneralNominalFeedbackSteps.self_argument_blocks_trace : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSaturationState.State roles} (source : Nat),
  Yulang.GeneralNominalFeedbackK2.Argument before source source →
    Yulang.B4Target.Steps (Yulang.GeneralNominalFeedbackSteps.Step registry root) before after →
      ∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles)
        (index : Fin (roles packet.site.occurrence.demand.role).arity),
        (packet.site.occurrence.demand.arguments index).fst = source →
          ¬Yulang.GeneralNominalFeedbackSteps.Installable registry after packet
```

### Files, checks, and remaining scope

Added modules:

- [GeneralNominalFeedbackAdministrative.lean](../../lean/Yulang/GeneralNominalFeedbackAdministrative.lean)
- [GeneralNominalFeedbackBoundary.lean](../../lean/Yulang/GeneralNominalFeedbackBoundary.lean)
- [GeneralNominalFeedbackDescent.lean](../../lean/Yulang/GeneralNominalFeedbackDescent.lean)
- [GeneralNominalFeedbackK2.lean](../../lean/Yulang/GeneralNominalFeedbackK2.lean)
- [GeneralNominalFeedbackObstruction.lean](../../lean/Yulang/GeneralNominalFeedbackObstruction.lean)
- [GeneralNominalFeedbackProgress.lean](../../lean/Yulang/GeneralNominalFeedbackProgress.lean)
- [GeneralNominalFeedbackRefresh.lean](../../lean/Yulang/GeneralNominalFeedbackRefresh.lean)
- [GeneralNominalFeedbackRegressions.lean](../../lean/Yulang/GeneralNominalFeedbackRegressions.lean)
- [GeneralNominalFeedbackSites.lean](../../lean/Yulang/GeneralNominalFeedbackSites.lean)
- [GeneralNominalFeedbackSteps.lean](../../lean/Yulang/GeneralNominalFeedbackSteps.lean)

Existing changes are append-only: ten imports in `lean/Yulang.lean`, 118 public
theorem dependency-print entries in `lean/Audit.lean`, and this Item 4d section.
No existing implementation definition, spec, plan, lake configuration, commit,
push, or git reference was changed.

Final commands from `lean/`, all with exit code **0**:

```sh
lake build Yulang.GeneralNominalFeedbackAdministrative Yulang.GeneralNominalFeedbackBoundary Yulang.GeneralNominalFeedbackDescent Yulang.GeneralNominalFeedbackK2 Yulang.GeneralNominalFeedbackObstruction Yulang.GeneralNominalFeedbackProgress Yulang.GeneralNominalFeedbackRefresh Yulang.GeneralNominalFeedbackRegressions Yulang.GeneralNominalFeedbackSites Yulang.GeneralNominalFeedbackSteps > /tmp/astra-feedback-focused.log 2>&1
lake build Yulang > /tmp/astra-feedback-umbrella.log 2>&1
lake env lean Audit.lean > /tmp/astra-feedback-audit.log 2>&1
```

The focused build completed 623 jobs; the umbrella build completed 1530 jobs.
The audit contained 9853 dependency records. All 118 new public theorems occurred
exactly once, with no unexpected foundations or error diagnostics; the reported
foundations were limited to `propext`, `Classical.choice`, and `Quot.sound`.
The theorem-signature extraction also exited 0. Append-only/path checks, the
restricted-token scan of added source and this section, and `git diff --check`
were run. No broad build is represented as evidence of the missing mathematical
installation bound.

The [yulang-proofs skill](/home/momota1029/.codex/skills/yulang-proofs/SKILL.md)
was used. There is no registered prover role/configuration in this checkout or
callable role in the collaboration schema. The primary constructed bounded
proofs directly, with a separate read-only reviewer; no prover agent ran.
Independent review found no theorem-level defect in the new source contracts,
finite obstruction, refresh, administrative bound, conditional descent, or
five-field count. The reviewer did not run an independent build.

Not proved: an infinite old Step trace; inevitable refresh scheduling; a total
producer of journal-normalized structural and nominal snapshots; complete
compound/nonpoint provenance; complete joint local classification; a source
construction of InstallationDescent or another global installation bound;
unconditional where accessibility; an inference implementation's InitialSource
producer; an executor; final-state order independence; or the B4 statement.
The new boundary remains a mathematical assembly for certified partial source
relations, with Evidence explicit, not a certification of whole-language coverage.

The work is converging on the general instance in a concrete way: actual
associated-output constraints now have a proved path to observed K2, and real
nonpoint child origins survive emission. The old raw/journal discrepancy is
proved on a reachable state and its proposed continuation is blocked by the new
rule. Further fragment proofs would not discharge the remaining obligation:
the next proof needs an interval-sensitive global installation measure and
complete source feedback/provenance, rather than more point-pattern examples.

## Item 4e — installation orders and associated-output growth (2026-11-12)

**Status: general termination remains open.** This section constructs an
arbitrary-well-founded-order version of the installation descent interface and
proves its accessibility theorem. It does not construct an inhabitant of that
interface. It also supplies a checked, source-formed counterexample to two
suggested measures, using actual feedback installation and refresh. It does
**not** prove an infinite concrete feedback Step trace or refute general Acc.
No existing boundary, transition, candidate, or dictionary interface changes.

### The checked example and its source correspondence

The declaration is:

```yulang
impl R (list 'a) where R('a, out = 'b):
    type out = list 'b
```

Consider the inferred demand `R(list A, out = A)`. This is demand notation, not
a claim that a complete surface program was parsed. Constructor 0 is the
catalogue's nominal `list`, role 1 has one unnamed input and named output 0,
input binder 0 represents `'a`, and output binder 1 represents `'b`.

`GeneralNominalOutputGrowth.declaration_checked` uses the existing general
`DeclarationChecked`, including `StableSmaller` via `unary_descent`. The unnamed
child is `'a`, strictly smaller than `list 'a` under every finite pattern
capture. Binder `'b` occurs only in named outputs and the impl's own associated
definition. This obeys §6.3's output-only decision and its exclusion of named
outputs from Paterson counting. The carrier, checker, capture, child emitter,
materialization, and nominal model are the existing general ones.

An installation captures A, allocates B using the existing invocation-indexed
allocator, emits exactly `R(A, out = B)`, and installs `A ≈ list B`. The new
`packet_output_equation` proves that equation from the actual packet's
materialization obligations. There is no substitution search or chosen
interval centre; these examples use point intervals, a legitimate special case
of the general carrier. `output_fresh` proves B is above the source seed.

`GeneralNominalOutputGrowthPackets.install_step length` proves an actual
feedback Step from `snapshot length`. Each snapshot is independently
SourceFormed with a finite chain of nominal source descriptors and an empty
journal. `enabled` discharges the full current installation guards, including
joint applicability, both local classifications, and merge closure. These
snapshots are **not** claimed to be consecutive states of one trace.

For length zero, `GeneralNominalOutputGrowthRefresh.two_steps_ready` proves an
actual two-Step trace: installation, then a journal-justified refresh. The
refresh adds the already-reserved B as a source slot and the entailed descriptor
`A ≈ list B`; it preserves every journal model and all old observations. Its
child is ready and satisfies neither RootK2 nor CandidateK2.
`different_inputs_not_merged` rules out SameInputs between the parent and this
child at the refreshed state. This is stronger than merely observing distinct
source identifiers: the proof uses their different denotations in a model of
the complete journal, after provenance recovery.

The schematic continuation is:

```text
R(list A, out=A)
  emits R(A, out=B), with A ≈ list B
  emits R(B, out=C), with B ≈ list C
  emits R(C, out=D), with C ≈ list D
  ...
```

Only the first installation and refresh of this common trace are proved here.
A second Installable certificate and an inductive realization of every later
row as feedback Steps have not been constructed. This distinction matters:
the finite certificates cannot establish non-accessibility by themselves.

### Why the proposed sizes do not close the proof

1. **Size of denotations in every journal model.** The full nominal carrier
   contains the regular value μ with μ ≈ list μ. The constant μ assignment is
   a model of the actual installed packet and complete journal. Parent and
   emitted child have literally the same denotation in that assignment.
   `no_modelwise_child_rank` proves that no function of that denotation into
   *any* well-founded order strictly decreases in every journal model. This
   theorem concerns a real installation, not an assumed abstract transition.
   The model does not supply a dictionary, and no dictionary premise is added
   to the solver's existing Models definition.
2. **Minimum finite input height across the current models.** Define the
   minimum over types equivalent to the finite unary nominal tower
   `list^n int`. The initial parent has minimum height 1. The installed child
   also has minimum height 1; after the proved refresh it still has height 1.
   `minimum_does_not_descend` proves the failure of strict descent. The
   one-outstanding-demand multiset containing this minimum therefore cannot
   strictly decrease by replacing the parent with this child. This rules out
   that measure, not every possible multiset measure.
3. **Paterson at the declaration side.** StableSmaller is proved for this
   declaration; it compares parent and child under one fixed capture.
   Materialization subsequently refines the captured variable to another
   constructor layer. A declaration-size label alone must repeatedly attach
   the same declaration to the apparent continuation. A proof that transfers
   fixed-capture descent through these changing captures is still missing.
4. **Finite identities and type-cycle K2.** For every finite equation prefix
   `x_i ≈ list x_(i+1)` there is a finite tower model ending in `int`.
   `prefix_not_equal` separates different supported positions in that model.
   `feedback_acyclic` proves that actual nominal observation edges decrease
   tower depth whenever such a model exists and there are no structural
   edges. It applies to the concrete initial, installed, and refreshed states,
   including journal equality transport. Thus K2 does not reject the proved
   finite trace. Finite support at each snapshot is not a uniform support
   bound over installations; the next output binder is freshly reserved.

The prefix equation model statements use the same nominal Assignment and
Equivalent, not a replacement classifier. They do not identify arbitrary
finite prefixes with reachable states of one fixed initial snapshot. No
absence of all future K2 or merge events is claimed for the concrete Step.

### Generalized installation order and exact remaining lemma

`GeneralNominalFeedbackWellFounded.InstallationOrder registry root` contains:

- an arbitrary universe-polymorphic type `Measure`, relation `before`, and
  `WellFounded before`;
- a rank on the actual journal States;
- administrative updates preserve the rank or decrease it under `before`;
- every enabled, uncommitted installation from a SourceFormed state strictly
  decreases it.

`accessible` proves Acc of the complete feedback Step. The proof nests the
well-founded rank induction with the existing administrative accessibility
proof, using the proved SourceFormed Step case split. `ofNat` embeds the old
InstallationDescent without changing it. `boundary_progress` states the result
for exactly `GeneralNominalFeedbackBoundary.boundary roles evidence`, with the
installation-order premise visible.

The remaining source construction, at this sufficient interface, is:

```lean
∀ (roles : Roles.RoleDecls) (registry : GeneralDeclarations.Registry)
  (root : GeneralSourceDictionaries.Occurrence roles),
  registry.roles = roles → GeneralDeclarations.Checked registry →
  Nonempty (GeneralNominalFeedbackWellFounded.InstallationOrder registry root)
```

Alternatively, one could prove Acc directly without this global rank interface.
Neither result is established. The generalized interface is sufficient, not a
claim that every termination proof must take this particular form.

For the apparent counterexample, the exact missing negative result is an
inductive realization with a **fixed** initial context and root: a sequence of
SourceFormed states whose consecutive elements are joined by nonempty feedback
Step traces, each containing another installation with the retained origins,
fresh ownership, journal-compatible witness, and complete Installable guards.
The current finite trace and finite-prefix models do not discharge that lemma.

`fixed_snapshot_whereAccessible` does prove child accessibility for each
example's frozen initial snapshot: its selected root emits one pending child.
`boundary_example_whereAccessible` transports this to the actual V3 Local of
the feedback boundary. It is an example theorem, not the general V3 field.
General source readback and unconditional where accessibility remain open.

### Boundary field table (13 fields)

The concrete boundary is unchanged:
`GeneralNominalFeedbackBoundary.boundary roles evidence`. Every classification
field below is independent of an executor. These are definitions, not a claim
of completed whole-language coverage; Item 4d's provenance, joint
classification, and normalization coverage limitations remain.

| Field | Definition/status | Item 4e consequence |
|---|---|---|
| Checked | `registry.roles = roles ∧ GeneralDeclarations.Checked registry` | The output-growth declaration passes this general check. |
| Models | `GeneralNominalSaturationState.Models` | Full journal models used in every concrete certificate; finite and regular witnesses retained. |
| Step | `GeneralNominalFeedbackSteps.Step` | Defined; one installation plus refresh proved; general Acc MISSING. |
| Stable | `GeneralNominalFeedbackSteps.Stable` | Defined, unchanged; no claim that the example reaches Stable. |
| Generated | `GeneralNominalSaturationState.Generated` | Defined, unchanged; the refresh uses an actually emitted child. |
| RootPending | `GeneralNominalState.RootPending state.context.state root.demand` | Defined; the example child is initially pending and ready after refresh. |
| RootK2 | `GeneralNominalFeedbackK2.RootK2` | Defined; both raw and journal cycle branches excluded on the refreshed child. |
| CandidateK2 | `GeneralNominalFeedbackK2.CandidateK2` | Defined; both branches excluded on the refreshed child. |
| InspectionPending | `GeneralNominalCycleK2.InspectionPending registry state.context root` | Defined, unchanged; no complete second classification after refresh is claimed. |
| Survivor | `GeneralNominalRecursiveCandidates.Survivor registry state.context root` | Defined, unchanged; exact general capture/emission used by the example. |
| Evidence | Explicit `evidence : GeneralNominalFeedbackBoundary.Evidence roles` parameter | Concrete integration remains MISSING in this boundary; other prover's interfaces untouched. |
| Reorders | `GeneralRegistryReordering.Reorders` | Defined, unchanged. |
| DictionaryEquivalent | `GeneralDictionaryPayloadOrder.Equivalent` | Defined, unchanged. |

Vocabulary remains Registry = `GeneralDeclarations.Registry`, State =
`GeneralNominalSaturationState.State roles`, Demand =
`GeneralSourceDictionaries.Occurrence roles`, Model =
`GeneralNominalCommonBridge.Assignment`. No Executor.run is defined here.

### Exact V3 field count

**5/12**, for the unchanged feedback boundary and its existing independent
classical `frontiers`:

| V3 bridge | Status |
|---|---|
| progress | MISSING; only conditional `boundary_progress`. |
| execution | MISSING; no executor. |
| halted | MISSING; no executor. |
| closure | Proved previously by `GeneralNominalFeedbackBoundary.closure`. |
| stepModels | Proved previously by `GeneralNominalFeedbackBoundary.stepModels`. |
| frontierLocal | Proved previously by `GeneralNominalFeedbackBoundary.frontierLocal`. |
| localIdentity | Proved previously by `GeneralNominalFeedbackBoundary.localIdentity`. |
| whereAccessible | MISSING generally; conditional readback and new example theorem only. |
| treeExecution | MISSING; no executor. |
| canonicalLocalOrder | MISSING for final states. |
| dictionaryRefl | Proved previously by `GeneralNominalFeedbackBoundary.dictionaryRefl`. |
| evidenceNode | MISSING for this parameterized boundary. |

V3 quantifies over all states; even a future SourceFormed-qualified progress
proof would need a formed-state carrier restriction or a stronger theorem to
count as its literal all-state field. Nothing in this section increments the
accepted count or changes the other prover's Stable/Committed contract.

### OWNER QUESTION — recursive associated-output head growth

This question concerns §6.3's still-open associated-RHS reference cycles (T13),
not the settled type-graph K2 rule. The observed graph `list A → A → B` in the
proved trace is acyclic. A regular model alone does not establish an entailed
type cycle. All equations and genuine K2 evidence must continue to feed back.
The example demonstrates failures of the proposed measures, not a theorem that
an additional language restriction is necessary; richer solver reasoning might
supply another answer.

For the declaration and requested `R(list A, out=A)` above, how should expansion
of the now-ready child `R(A, out=B)` be treated when the only support for its
head `A ≈ list B` is a provisional associated-output equation from its own
unresolved ancestor/dependency cycle?

1. **Lazy option first:** retain the equation for ordinary constraints,
   equality, and K2, but defer that child's expansion until its needed head has
   support independent of the provisional output packets in its unresolved
   dependency cycle. Resume when source constraints or discharged/outside-cycle
   demands supply that support. This is a targeted restriction on circular
   justification of expansion, not a ban on output-to-input propagation or
   independent sibling updates. It blocks this example at the first child.
   It leaves `Wrap(list int, out=list B) → Container(int, item=B)` expandable,
   because the child's input head `int` is already source-supported. Any final
   unresolved result is handled only at the stable end of the file.
2. **Declaration restriction:** reject cycles of associated-output-producing
   where dependencies that can feed constructor growth back into their own
   unnamed input obligations. A blanket ban on output-only binders in compound
   associated RHSs would also reject the accepted Wrap example, so that blanket
   restriction is not proposed. A precise cyclic-dependency check and its
   sufficiency would still need design and proof.

Option 1 is the smallest operational restriction identified here that blocks
this concrete continuation while preserving the accepted Wrap use and ordinary
sibling feedback. Its sufficiency for **all** checked declarations and arbitrary
intervals is **not** proved; neither is global minimality among possible rules.
No proposed restriction is installed, and no new rejection or pending reason is
silently added. The current definitions keep the choice open.

### Full public theorem statements

The following signatures are extracted by Lean from the six new modules.
Private helpers and data definitions are omitted; all public theorems have
matching appended dependency-print entries in Audit.lean.

```lean
@Yulang.GeneralNominalFeedbackWellFounded.accessible.{u_1} : ∀ {roles : Yulang.Roles.RoleDecls}
  {registry : Yulang.GeneralDeclarations.Registry} {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  (order : Yulang.GeneralNominalFeedbackWellFounded.InstallationOrder.{u_1} registry root)
  (state : Yulang.GeneralNominalSaturationState.State roles),
  Yulang.GeneralNominalFeedbackSteps.SourceFormed registry root state →
    Acc.{1} (fun next current => Yulang.GeneralNominalFeedbackSteps.Step registry root current next) state
Yulang.GeneralNominalFeedbackWellFounded.boundary_progress.{u_1} : ∀ (roles : Yulang.Roles.RoleDecls)
  (evidence : Yulang.GeneralNominalFeedbackBoundary.Evidence roles) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (order : Yulang.GeneralNominalFeedbackWellFounded.InstallationOrder.{u_1} registry root)
  (state : Yulang.GeneralNominalSaturationState.State roles),
  Yulang.GeneralNominalFeedbackSteps.SourceFormed registry root state →
    Acc.{1}
      (fun next current =>
        Yulang.B4Target.SourceBoundary.Step.{0} (Yulang.GeneralNominalFeedbackBoundary.boundary roles evidence) registry
          root current next)
      state
Yulang.GeneralNominalOutputGrowth.declaration_checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDeclarationExamples.roles
  Yulang.GeneralNominalOutputGrowth.declaration
Yulang.GeneralNominalOutputGrowth.checked : Yulang.GeneralDeclarations.Checked
  Yulang.GeneralNominalOutputGrowth.registry
Yulang.GeneralNominalOutputGrowth.output_only : Eq.{1} Yulang.GeneralNominalOutputGrowth.declaration.outputNames
    (List.cons.{0} 1 List.nil.{0}) ∧
  Eq.{1} Yulang.GeneralNominalOutputGrowth.declaration.inputNames (List.cons.{0} 0 List.nil.{0}) ∧
    Eq.{1} Yulang.GeneralNominalOutputGrowth.clause.arguments
      (List.cons.{0} (Yulang.GeneralDeclarationPatterns.Pattern.var 0) List.nil.{0})
Yulang.GeneralNominalOutputGrowth.child_equations : ∀ (input output : Nat)
  (allocation :
    Yulang.GeneralDeclarationDemands.Allocation Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralNominalOutputGrowth.clause),
  (Eq.{1}
      (Yulang.GeneralDeclarationDemands.childDemand Yulang.GeneralNominalOutputGrowth.declaration
          Yulang.GeneralNominalOutputGrowth.clause Yulang.GeneralNominalOutputGrowth.clauseChecked
          (Yulang.GeneralNominalOutputGrowth.capture input output) allocation).arguments
      fun x => Prod.mk.{0, 0} input input) ∧
    Eq.{1}
      (Yulang.GeneralDeclarationDemands.childDemand Yulang.GeneralNominalOutputGrowth.declaration
          Yulang.GeneralNominalOutputGrowth.clause Yulang.GeneralNominalOutputGrowth.clauseChecked
          (Yulang.GeneralNominalOutputGrowth.capture input output) allocation).outputs
      (List.cons.{0} { name := 0, target := output } List.nil.{0})
Yulang.GeneralNominalOutputGrowth.tower_equivalent : ∀ (first last : Nat),
  Yulang.CommonNominalFullCarrier.Equivalent (Yulang.GeneralNominalOutputGrowth.tower first)
      (Yulang.GeneralNominalOutputGrowth.tower last) ↔
    Eq.{1} first last
Yulang.GeneralNominalOutputGrowth.finite_prefix_models : ∀ (length : Nat),
  Yulang.GeneralNominalOutputGrowth.PrefixModels length (Yulang.GeneralNominalOutputGrowth.finiteModel length)
Yulang.GeneralNominalOutputGrowth.prefix_consistent : ∀ (length : Nat),
  Exists.{1} fun model => Yulang.GeneralNominalOutputGrowth.PrefixModels length model
Yulang.GeneralNominalOutputGrowth.prefix_refines : ∀ (length : Nat)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalOutputGrowth.PrefixModels (HAdd.hAdd.{0, 0, 0} length 1) model →
    Yulang.GeneralNominalOutputGrowth.PrefixModels length model
Yulang.GeneralNominalOutputGrowth.finite_prefix_separates : ∀ (length first last : Nat),
  LE.le.{0} first (HAdd.hAdd.{0, 0, 0} length 1) →
    LE.le.{0} last (HAdd.hAdd.{0, 0, 0} length 1) →
      Ne.{1} first last →
        ¬Yulang.CommonNominalFullCarrier.Equivalent
            (Prod.fst.{0, 0} (Yulang.GeneralNominalOutputGrowth.finiteModel length first))
            (Prod.fst.{0, 0} (Yulang.GeneralNominalOutputGrowth.finiteModel length last))
Yulang.GeneralNominalOutputGrowth.prefix_not_equal : ∀ (length first last : Nat),
  LE.le.{0} first (HAdd.hAdd.{0, 0, 0} length 1) →
    LE.le.{0} last (HAdd.hAdd.{0, 0, 0} length 1) →
      Ne.{1} first last →
        ¬∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
            Yulang.GeneralNominalOutputGrowth.PrefixModels length model →
              Yulang.CommonNominalFullCarrier.Equivalent (Prod.fst.{0, 0} (model first)) (Prod.fst.{0, 0} (model last))
Yulang.GeneralNominalOutputGrowth.old_minimizer_removed : ∀ (length : Nat),
  ¬Yulang.GeneralNominalOutputGrowth.PrefixModels (HAdd.hAdd.{0, 0, 0} length 1)
      (Yulang.GeneralNominalOutputGrowth.finiteModel length)
Yulang.GeneralNominalOutputGrowth.regular_prefix_models : ∀ (length : Nat),
  Yulang.GeneralNominalOutputGrowth.PrefixModels length Yulang.GeneralNominalProgressObstruction.model
@Yulang.GeneralNominalOutputGrowth.no_universal_denotation_rank.{u_1} : ∀ {Measure : Type u_1}
  (less : Measure → Measure → Prop),
  WellFounded.{u_1 + 1} less →
    ∀ (rank : Yulang.CommonNominalFullCarrier.Ty → Measure) (length : Nat),
      ¬∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
          Yulang.GeneralNominalOutputGrowth.PrefixModels length model →
            less (rank (Prod.fst.{0, 0} (model (HAdd.hAdd.{0, 0, 0} length 1)))) (rank (Prod.fst.{0, 0} (model length)))
Yulang.GeneralNominalOutputGrowthModels.observation_decreases : ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (depth : Nat → Nat),
  (∀ (source : Nat), Eq.{1} (Prod.fst.{0, 0} (model source)) (Yulang.GeneralNominalOutputGrowth.tower (depth source))) →
    ∀ (first last name index : Nat) (actual : Yulang.CommonNominalFullCarrier.Ty),
      Yulang.GeneralNominalProjections.Observes model
          ((Yulang.GeneralNominalProjections.Ref.source first).argument name index) (Sum.inl.{0, 0} actual) →
        Yulang.CommonNominalFullCarrier.Equivalent actual (Prod.fst.{0, 0} (model last)) →
          LT.lt.{0} (depth last) (depth first)
@Yulang.GeneralNominalOutputGrowthModels.feedback_acyclic : ∀ {roleDecls : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roleDecls) (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models state model →
    ∀ (depth : Nat → Nat),
      (∀ (source : Nat),
          Eq.{1} (Prod.fst.{0, 0} (model source)) (Yulang.GeneralNominalOutputGrowth.tower (depth source))) →
        (∀ (first last : Nat), ¬Yulang.GeneralNominalFeedbackK2.Structural state first last) →
          ∀ (source : Nat), ¬Yulang.GeneralNominalFeedbackK2.Cycle state source
Yulang.GeneralNominalOutputGrowthModels.source_models : ∀ (length : Nat)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models (Yulang.GeneralNominalOutputGrowthModels.source length) model ↔
    Yulang.GeneralNominalOutputGrowth.PrefixModels length model
Yulang.GeneralNominalOutputGrowthModels.snapshot_models : ∀ (length : Nat)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralNominalOutputGrowthModels.snapshot length) model ↔
    Yulang.GeneralNominalOutputGrowth.PrefixModels length model
Yulang.GeneralNominalOutputGrowthModels.snapshot_acyclic : ∀ (length source : Nat),
  ¬Yulang.GeneralNominalFeedbackK2.Cycle (Yulang.GeneralNominalOutputGrowthModels.snapshot length) source
Yulang.GeneralNominalOutputGrowthModels.raw_acyclic : ∀ (length : Nat)
  (slot : Fin (Yulang.GeneralNominalOutputGrowthModels.source length).base.slots),
  ¬Yulang.GeneralNominalCycleK2.Cycle (Yulang.GeneralNominalOutputGrowthModels.source length) slot
Yulang.GeneralNominalOutputGrowthModels.not_rootK2 : ∀ (length : Nat),
  ¬Yulang.GeneralNominalFeedbackK2.RootK2 (Yulang.GeneralNominalOutputGrowthModels.snapshot length)
      (Yulang.GeneralNominalOutputGrowthModels.root length)
Yulang.GeneralNominalOutputGrowthModels.not_candidateK2 : ∀ (length : Nat),
  ¬Yulang.GeneralNominalFeedbackK2.CandidateK2 Yulang.GeneralNominalOutputGrowth.registry
      (Yulang.GeneralNominalOutputGrowthModels.snapshot length) (Yulang.GeneralNominalOutputGrowthModels.root length)
Yulang.GeneralNominalOutputGrowthModels.source_member : ∀ (length : Nat) (slot : Fin (HAdd.hAdd.{0, 0, 0} length 2)),
  Membership.mem.{0, 0} (Yulang.GeneralNominalState.sources (Yulang.GeneralNominalOutputGrowthModels.source length))
    ↑slot
Yulang.GeneralNominalOutputGrowthModels.metadata : ∀ (length : Nat),
  Yulang.GeneralNominalRecursiveCandidates.Metadata Yulang.GeneralNominalOutputGrowth.registry
    (Yulang.GeneralNominalOutputGrowthModels.context length)
Yulang.GeneralNominalOutputGrowthModels.linked : ∀ (length : Nat),
  Yulang.GeneralNominalState.Linked (Yulang.GeneralNominalOutputGrowthModels.source length)
    (Yulang.GeneralNominalOutputGrowthModels.root length).demand
Yulang.GeneralNominalOutputGrowthModels.initial_source : ∀ (length : Nat),
  Yulang.GeneralNominalSourceFormation.InitialSource Yulang.GeneralNominalOutputGrowth.registry
    (Yulang.GeneralNominalOutputGrowthModels.context length) (Yulang.GeneralNominalOutputGrowthModels.root length)
Yulang.GeneralNominalOutputGrowthModels.formed : ∀ (length : Nat),
  Yulang.GeneralNominalFeedbackSteps.SourceFormed Yulang.GeneralNominalOutputGrowth.registry
    (Yulang.GeneralNominalOutputGrowthModels.root length) (Yulang.GeneralNominalOutputGrowthModels.snapshot length)
Yulang.GeneralNominalOutputGrowthModels.ready : ∀ (length : Nat),
  ¬Yulang.GeneralNominalState.RootPending (Yulang.GeneralNominalOutputGrowthModels.source length)
      (Yulang.GeneralNominalOutputGrowthModels.root length).demand
Yulang.GeneralNominalOutputGrowthPackets.report_exact : ∀ (length : Nat),
  Eq.{1}
    (Yulang.GeneralNominalRecursiveCandidates.report (Yulang.GeneralNominalOutputGrowthModels.context length)
      Yulang.GeneralNominalOutputGrowth.declaration (Yulang.GeneralNominalOutputGrowthPackets.bounds length))
    (Yulang.GeneralNominalUnaryCaptureFacts.captured (Yulang.GeneralNominalOutputGrowthModels.source length)
      (Yulang.GeneralNominalOutputGrowthPackets.slot length) 0 0
      (Prod.mk.{0, 0} (Yulang.GeneralNominalOutputGrowthPackets.endpoint length)
        (Yulang.GeneralNominalOutputGrowthPackets.endpoint length)))
Yulang.GeneralNominalOutputGrowthPackets.bindings_exact : ∀ (length : Nat),
  Eq.{1} (Yulang.GeneralNominalOutputGrowthPackets.packet length).bindings
    (List.cons.{0} (Prod.mk.{0, 0} 0 (Prod.mk.{0, 0} (HAdd.hAdd.{0, 0, 0} length 1) (HAdd.hAdd.{0, 0, 0} length 1)))
      List.nil.{0})
Yulang.GeneralNominalOutputGrowthPackets.children_exact : ∀ (length : Nat),
  Eq.{1} (Yulang.GeneralNominalOutputGrowthPackets.packet length).children
    (List.cons.{0} (Yulang.GeneralNominalOutputGrowthPackets.child length) List.nil.{0})
Yulang.GeneralNominalOutputGrowthPackets.schema_exact : ∀ (length : Nat),
  Eq.{1}
    (Yulang.GeneralNominalRecursiveCandidates.generated Yulang.GeneralNominalOutputGrowth.registry
      (Yulang.GeneralNominalOutputGrowthModels.context length) (Yulang.GeneralNominalOutputGrowthModels.root length)
      Yulang.GeneralNominalOutputGrowth.declaration Yulang.GeneralNominalOutputGrowth.declaration_checked
      (Yulang.GeneralNominalOutputGrowthPackets.bounds length))
    {
      variables :=
        List.cons.{0}
          { name := 1,
            origin :=
              (Yulang.GeneralNominalRecursiveInspection.Origin.source (HAdd.hAdd.{0, 0, 0} length 1)).nominal 0 0,
            mode := Yulang.GeneralNominalMaterialization.Mode.actual }
          (List.cons.{0}
            { name := 1,
              origin :=
                Yulang.GeneralNominalRecursiveInspection.Origin.source
                  (Yulang.GeneralNominalOutputGrowthPackets.output length),
              mode := Yulang.GeneralNominalMaterialization.Mode.actual }
            List.nil.{0}),
      tests :=
        List.cons.{0}
          (Prod.mk.{0, 0} (Yulang.GeneralNominalRecursiveInspection.Origin.source (HAdd.hAdd.{0, 0, 0} length 1))
            (Yulang.GeneralNominalRecursiveInspection.Test.nominal 0 1))
          List.nil.{0} }
Yulang.GeneralNominalOutputGrowthPackets.output_fresh : ∀ (length : Nat),
  LT.lt.{0} (HAdd.hAdd.{0, 0, 0} length 1) (Yulang.GeneralNominalOutputGrowthPackets.output length)
Yulang.GeneralNominalOutputGrowthPackets.packet_models : ∀ (length : Nat)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalOutputGrowth.PrefixModels length model →
    Yulang.CommonNominalFullCarrier.Equivalent (Prod.fst.{0, 0} (model (HAdd.hAdd.{0, 0, 0} length 1)))
        (Yulang.CommonNominalFullCarrier.nominal 0
          (List.cons.{0}
            (Sum.inl.{0, 0} (Prod.fst.{0, 0} (model (Yulang.GeneralNominalOutputGrowthPackets.output length))))
            List.nil.{0})) →
      (Yulang.GeneralNominalOutputGrowthPackets.packet length).Holds model
Yulang.GeneralNominalOutputGrowthPackets.finite_packet_models : ∀ (length : Nat),
  (Yulang.GeneralNominalOutputGrowthPackets.packet length).Holds
    (Yulang.GeneralNominalOutputGrowth.finiteModel (HAdd.hAdd.{0, 0, 0} length 1))
Yulang.GeneralNominalOutputGrowthPackets.regular_packet_models : ∀ (length : Nat),
  (Yulang.GeneralNominalOutputGrowthPackets.packet length).Holds Yulang.GeneralNominalProgressObstruction.model
Yulang.GeneralNominalOutputGrowthPackets.located : ∀ (length : Nat),
  Eq.{1}
    (Yulang.GeneralNominalRecursiveCandidates.arguments (Yulang.GeneralNominalOutputGrowthModels.context length)
      (Yulang.GeneralNominalOutputGrowthModels.root length))
    (Option.some.{0} (Yulang.GeneralNominalOutputGrowthPackets.bounds length))
Yulang.GeneralNominalOutputGrowthPackets.prepared : ∀ (length : Nat),
  Yulang.GeneralNominalRecursiveCandidates.Prepared Yulang.GeneralNominalOutputGrowth.registry
    (Yulang.GeneralNominalOutputGrowthModels.context length) (Yulang.GeneralNominalOutputGrowthModels.root length)
    Yulang.GeneralNominalOutputGrowth.declaration Yulang.GeneralNominalOutputGrowth.declaration_checked
Yulang.GeneralNominalOutputGrowthPackets.survivor : ∀ (length : Nat),
  Yulang.GeneralNominalRecursiveCandidates.Survivor Yulang.GeneralNominalOutputGrowth.registry
    (Yulang.GeneralNominalOutputGrowthModels.context length) (Yulang.GeneralNominalOutputGrowthModels.root length) 2
    (Yulang.GeneralNominalOutputGrowthPackets.packet length).children
Yulang.GeneralNominalOutputGrowthPackets.selected : ∀ (length : Nat),
  Yulang.GeneralNominalFeedbackK2.Local Yulang.GeneralNominalOutputGrowth.registry
    (Yulang.GeneralNominalOutputGrowthModels.snapshot length) (Yulang.GeneralNominalOutputGrowthModels.root length)
    (Yulang.CommonRoleOutermostResolver.Frontier.selected.{0} 2
      (Yulang.GeneralNominalOutputGrowthPackets.packet length).children)
Yulang.GeneralNominalOutputGrowthPackets.enabled : ∀ (length : Nat),
  Yulang.GeneralNominalFeedbackSteps.Installable Yulang.GeneralNominalOutputGrowth.registry
    (Yulang.GeneralNominalOutputGrowthModels.snapshot length) (Yulang.GeneralNominalOutputGrowthPackets.packet length)
Yulang.GeneralNominalOutputGrowthPackets.install_step : ∀ (length : Nat),
  Yulang.GeneralNominalFeedbackSteps.Step Yulang.GeneralNominalOutputGrowth.registry
    (Yulang.GeneralNominalOutputGrowthModels.root length) (Yulang.GeneralNominalOutputGrowthModels.snapshot length)
    (Yulang.GeneralNominalOutputGrowthPackets.installed length)
Yulang.GeneralNominalOutputGrowthPackets.installed_formed : ∀ (length : Nat),
  Yulang.GeneralNominalFeedbackSteps.SourceFormed Yulang.GeneralNominalOutputGrowth.registry
    (Yulang.GeneralNominalOutputGrowthModels.root length) (Yulang.GeneralNominalOutputGrowthPackets.installed length)
Yulang.GeneralNominalOutputGrowthPackets.installed_models : ∀ (length : Nat),
  Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralNominalOutputGrowthPackets.installed length)
    (Yulang.GeneralNominalOutputGrowth.finiteModel (HAdd.hAdd.{0, 0, 0} length 1))
Yulang.GeneralNominalOutputGrowthPackets.installed_acyclic : ∀ (length identity : Nat),
  ¬Yulang.GeneralNominalFeedbackK2.Cycle (Yulang.GeneralNominalOutputGrowthPackets.installed length) identity
Yulang.GeneralNominalOutputGrowthPackets.child_pending : ∀ (length : Nat),
  Yulang.GeneralNominalState.RootPending (Yulang.GeneralNominalOutputGrowthModels.source length)
    (Yulang.GeneralNominalOutputGrowthPackets.child length).demand
Yulang.GeneralNominalOutputGrowthPackets.fixed_snapshot_whereAccessible : ∀ (length : Nat),
  Acc.{1}
    (Yulang.CommonRoleOutermostResolver.Child.{0}
      (Yulang.GeneralNominalFeedbackK2.Local Yulang.GeneralNominalOutputGrowth.registry
        (Yulang.GeneralNominalOutputGrowthModels.snapshot length)))
    (Yulang.GeneralNominalOutputGrowthModels.root length)
Yulang.GeneralNominalOutputGrowthPackets.regular_installed_models : ∀ (length : Nat),
  Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralNominalOutputGrowthPackets.installed length)
    Yulang.GeneralNominalProgressObstruction.model
@Yulang.GeneralNominalOutputGrowthPackets.no_modelwise_child_rank.{u_1} : ∀ {Measure : Type u_1}
  (less : Measure → Measure → Prop),
  WellFounded.{u_1 + 1} less →
    ∀ (rank : Yulang.CommonNominalFullCarrier.Ty → Measure) (length : Nat),
      ¬∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
          Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralNominalOutputGrowthPackets.installed length)
              model →
            less
              (rank
                (Prod.fst.{0, 0}
                  (model
                    (Prod.fst.{0, 0}
                      ((Yulang.GeneralNominalOutputGrowthPackets.child length).demand.arguments ⟨0, ⋯⟩)))))
              (rank
                (Prod.fst.{0, 0}
                  (model
                    (Prod.fst.{0, 0} ((Yulang.GeneralNominalOutputGrowthModels.root length).demand.arguments ⟨0, ⋯⟩)))))
Yulang.GeneralNominalOutputGrowthPackets.packet_output_equation : ∀ (length : Nat)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  (Yulang.GeneralNominalOutputGrowthPackets.packet length).Holds model →
    Yulang.CommonNominalFullCarrier.Equivalent (Prod.fst.{0, 0} (model (HAdd.hAdd.{0, 0, 0} length 1)))
      (Yulang.CommonNominalFullCarrier.nominal 0
        (List.cons.{0}
          (Sum.inl.{0, 0} (Prod.fst.{0, 0} (model (Yulang.GeneralNominalOutputGrowthPackets.output length))))
          List.nil.{0}))
Yulang.GeneralNominalOutputGrowthRefresh.child_known : Yulang.GeneralNominalState.Known
  Yulang.GeneralNominalOutputGrowthRefresh.refreshedState 1
Yulang.GeneralNominalOutputGrowthRefresh.refresh_step : Yulang.GeneralNominalFeedbackSteps.Step
  Yulang.GeneralNominalOutputGrowth.registry (Yulang.GeneralNominalOutputGrowthModels.root 0)
  (Yulang.GeneralNominalOutputGrowthPackets.installed 0) Yulang.GeneralNominalOutputGrowthRefresh.refreshed
Yulang.GeneralNominalOutputGrowthRefresh.refresh_models : ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralNominalOutputGrowthRefresh.refreshed model ↔
    Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralNominalOutputGrowthPackets.installed 0) model
Yulang.GeneralNominalOutputGrowthRefresh.refreshed_formed : Yulang.GeneralNominalFeedbackSteps.SourceFormed
  Yulang.GeneralNominalOutputGrowth.registry (Yulang.GeneralNominalOutputGrowthModels.root 0)
  Yulang.GeneralNominalOutputGrowthRefresh.refreshed
Yulang.GeneralNominalOutputGrowthRefresh.child_ready : ¬Yulang.GeneralNominalState.RootPending
    Yulang.GeneralNominalOutputGrowthRefresh.refreshedState (Yulang.GeneralNominalOutputGrowthPackets.child 0).demand
Yulang.GeneralNominalOutputGrowthRefresh.refreshed_acyclic : ∀ (identity : Nat),
  ¬Yulang.GeneralNominalFeedbackK2.Cycle Yulang.GeneralNominalOutputGrowthRefresh.refreshed identity
Yulang.GeneralNominalOutputGrowthRefresh.raw_acyclic : ∀
  (slot : Fin Yulang.GeneralNominalOutputGrowthRefresh.refreshedState.base.slots),
  ¬Yulang.GeneralNominalCycleK2.Cycle Yulang.GeneralNominalOutputGrowthRefresh.refreshedState slot
Yulang.GeneralNominalOutputGrowthRefresh.child_not_rootK2 : ¬Yulang.GeneralNominalFeedbackK2.RootK2
    Yulang.GeneralNominalOutputGrowthRefresh.refreshed (Yulang.GeneralNominalOutputGrowthPackets.child 0)
Yulang.GeneralNominalOutputGrowthRefresh.child_not_candidateK2 : ¬Yulang.GeneralNominalFeedbackK2.CandidateK2
    Yulang.GeneralNominalOutputGrowth.registry Yulang.GeneralNominalOutputGrowthRefresh.refreshed
    (Yulang.GeneralNominalOutputGrowthPackets.child 0)
Yulang.GeneralNominalOutputGrowthRefresh.two_steps_ready : Yulang.GeneralDeclarations.Checked
    Yulang.GeneralNominalOutputGrowth.registry ∧
  Yulang.GeneralNominalFeedbackSteps.SourceFormed Yulang.GeneralNominalOutputGrowth.registry
      (Yulang.GeneralNominalOutputGrowthModels.root 0) Yulang.GeneralNominalOutputGrowthRefresh.refreshed ∧
    Yulang.B4Target.Steps.{1}
        (Yulang.GeneralNominalFeedbackSteps.Step Yulang.GeneralNominalOutputGrowth.registry
          (Yulang.GeneralNominalOutputGrowthModels.root 0))
        (Yulang.GeneralNominalOutputGrowthModels.snapshot 0) Yulang.GeneralNominalOutputGrowthRefresh.refreshed ∧
      Yulang.GeneralNominalSaturationState.Models Yulang.GeneralNominalOutputGrowthRefresh.refreshed
          (Yulang.GeneralNominalOutputGrowth.finiteModel 1) ∧
        ¬Yulang.GeneralNominalState.RootPending Yulang.GeneralNominalOutputGrowthRefresh.refreshedState
              (Yulang.GeneralNominalOutputGrowthPackets.child 0).demand ∧
          ¬Yulang.GeneralNominalFeedbackK2.RootK2 Yulang.GeneralNominalOutputGrowthRefresh.refreshed
                (Yulang.GeneralNominalOutputGrowthPackets.child 0) ∧
            ¬Yulang.GeneralNominalFeedbackK2.CandidateK2 Yulang.GeneralNominalOutputGrowth.registry
                Yulang.GeneralNominalOutputGrowthRefresh.refreshed (Yulang.GeneralNominalOutputGrowthPackets.child 0)
Yulang.GeneralNominalOutputGrowthRefresh.different_inputs_not_merged : ¬Yulang.GeneralNominalFeedbackSites.SameInputs
    Yulang.GeneralNominalOutputGrowthRefresh.refreshed
    (Yulang.GeneralNominalDemandMerging.pointSite (Yulang.GeneralNominalOutputGrowthModels.root 0))
    (Yulang.GeneralNominalFeedbackSites.childSite (Yulang.GeneralNominalOutputGrowthPackets.packet 0)
      (Yulang.GeneralNominalOutputGrowthPackets.child 0))
Yulang.GeneralNominalOutputGrowthMeasures.initial_minimum : ∀ (length : Nat),
  Yulang.GeneralNominalOutputGrowthMeasures.MinimumHeight
    (Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralNominalOutputGrowthModels.snapshot length)) length 1
Yulang.GeneralNominalOutputGrowthMeasures.installed_child_minimum : ∀ (length : Nat),
  Yulang.GeneralNominalOutputGrowthMeasures.MinimumHeight
    (Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralNominalOutputGrowthPackets.installed length))
    (HAdd.hAdd.{0, 0, 0} length 1) 1
Yulang.GeneralNominalOutputGrowthMeasures.refreshed_child_minimum : Yulang.GeneralNominalOutputGrowthMeasures.MinimumHeight
  (Yulang.GeneralNominalSaturationState.Models Yulang.GeneralNominalOutputGrowthRefresh.refreshed) 1 1
Yulang.GeneralNominalOutputGrowthMeasures.minimum_unique : ∀
  (models : Yulang.GeneralNominalCommonBridge.Assignment → Prop) (source first last : Nat),
  Yulang.GeneralNominalOutputGrowthMeasures.MinimumHeight models source first →
    Yulang.GeneralNominalOutputGrowthMeasures.MinimumHeight models source last → Eq.{1} first last
Yulang.GeneralNominalOutputGrowthMeasures.minimum_does_not_descend : ∀ (first last : Nat),
  Yulang.GeneralNominalOutputGrowthMeasures.MinimumHeight
      (Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralNominalOutputGrowthModels.snapshot 0)) 0 first →
    Yulang.GeneralNominalOutputGrowthMeasures.MinimumHeight
        (Yulang.GeneralNominalSaturationState.Models Yulang.GeneralNominalOutputGrowthRefresh.refreshed) 1 last →
      ¬LT.lt.{0} last first
Yulang.GeneralNominalOutputGrowthMeasures.boundary_example_whereAccessible : ∀
  (evidence : Yulang.GeneralNominalFeedbackBoundary.Evidence Yulang.GeneralDeclarationExamples.roles) (length : Nat),
  Acc.{1}
    (Yulang.CommonRoleOutermostResolver.Child.{0}
      (Yulang.B4TargetV3.Local.{0}
        (Yulang.GeneralNominalFeedbackBoundary.boundary Yulang.GeneralDeclarationExamples.roles evidence)
        Yulang.GeneralNominalOutputGrowth.registry (Yulang.GeneralNominalOutputGrowthModels.snapshot length)))
    (Yulang.GeneralNominalOutputGrowthModels.root length)
```

### Files, verification, and remaining scope

Added:

- `lean/Yulang/GeneralNominalFeedbackWellFounded.lean`
- `lean/Yulang/GeneralNominalOutputGrowth.lean`
- `lean/Yulang/GeneralNominalOutputGrowthModels.lean`
- `lean/Yulang/GeneralNominalOutputGrowthPackets.lean`
- `lean/Yulang/GeneralNominalOutputGrowthRefresh.lean`
- `lean/Yulang/GeneralNominalOutputGrowthMeasures.lean`

Changed only by appending: six imports in `lean/Yulang.lean`, 68 public-theorem
print entries in `lean/Audit.lean`, and this Item 4e section. No spec, plan,
configuration, pre-existing Lean implementation line, commit, push, or git
reference was changed.

Final commands, run from `lean/`, each exited **0**:

```sh
lake build Yulang.GeneralNominalFeedbackWellFounded Yulang.GeneralNominalOutputGrowth Yulang.GeneralNominalOutputGrowthModels Yulang.GeneralNominalOutputGrowthPackets Yulang.GeneralNominalOutputGrowthRefresh Yulang.GeneralNominalOutputGrowthMeasures > /tmp/astra-descent-focused.log 2>&1
lake build Yulang > /tmp/astra-descent-umbrella.log 2>&1
lake env lean Audit.lean > /tmp/astra-descent-audit.log 2>&1
```

The focused build completed 626 jobs and the umbrella build 1536 jobs. Audit
produced 9921 dependency records (9684 nonempty, 237 empty). All 68 new public
theorems were present exactly once; nonempty dependencies were contained in
`{propext, Classical.choice, Quot.sound}`. Signature extraction with
`lake env lean --stdin` exited 0. The final append-only/path audit, restricted
source-token scan, theorem-to-Audit coverage check, and `git diff --check`
passed. Intermediate proof iterations had compiler errors that were corrected;
only the final successful commands above are presented as validation.

The [yulang-proofs skill](/home/momota1029/.codex/skills/yulang-proofs/SKILL.md)
was applied. The checkout and callable collaboration schema provide no
registered prover launch surface; no prover agent ran. The primary constructed
bounded proofs directly. A separate read-only reviewer independently found the
same output-growth pattern and reviewed all six modules and the final scope
statements, finding no theorem-level defect. The reviewer did not run an
independent build.

Not verified/proved: a second Installable after the refreshed child becomes
ready; an infinite trace from one initial state; absence of all future merges
or K2; a general installation measure or Acc; general Readback or where
accessibility; full joint classification/provenance/normalization coverage; an
inference-to-InitialSource producer; surface parsing of the illustrated
inferred demand; a concrete Evidence integration; an executor; final order
independence; or the B4 theorem. The proposed lazy dependency policy has not
been implemented or proved sufficient for general termination.

This work is converging toward the general boundary by testing the missing
proof against the exact checker, packet materialization, allocation, journal,
refresh, K2, and merge definitions. The failed measures are exposed by real
SourceFormed updates, not an alternate scalar classifier. Nevertheless the
termination gap remains substantive: additional isolated fragment termination
proofs would not connect StableSmaller to output-driven growth across updates.
The next useful result is either the missing common-trace realization or a
source dependency argument that blocks it under an explicitly approved policy.

## Item 5a — canonical local order on the feedback boundary

### Result and exact target

The independent Local judgment is now proved invariant under the permitted
visible-declaration and where-clause permutations **at the same full feedback
state**. Selection preserves the identical canonical list of emitted source
obligations, not merely a permutation of implementation keys. The result covers
all general candidates, pending inspection, journal-aware K2, ambiguity, and
rejection. It is not a scalar or settled-fragment theorem.

The exact `canonicalLocalOrder` field remains open. It compares two different
executor-returned states, not the reachable state supplied to both runs. No
concrete executor or final-state agreement theorem was supplied by this task or
by the current concrete boundary. The new exact factorization isolates that
remaining premise without changing the field. The V5 bridge count remains
**6/14**, not 7/14.

Let `B := GeneralDictionaryReachableBoundary.boundary roles`; its underlying
source boundary is exactly `GeneralDictionaryFeedbackEvidence.boundary roles`.
`GeneralDictionaryCanonicalLocalOrder.CanonicalLocalOrder roles e` is the
following existing field, copied literally:

```lean
∀ r r', B.Checked r → B.Checked r' → B.Reorders r r' → ∀ s root,
  B4TargetV5.Reachable B r root s → B4TargetV5.Reachable B r' root s → ∀ d f,
  B4TargetV3.Local B.toSourceBoundary r (e.run r s root).1 d f ↔
    B4TargetV3.Local B.toSourceBoundary r' (e.run r' s root).1 d f
```

The theorem `remaining_field` consumes precisely
`GeneralDictionaryReachableObligations.Remaining roles e` and projects this
property, checking that the new name denotes the actual field. It does not fill
that field.

### Shared-state proof and source fidelity

The new proof chain is:

1. `GeneralNominalRegistryOrder` transports allocation-key membership and
   freshness. Reservation lists may have a different order; only their
   membership matters. A candidate's frame and fresh source IDs do not depend on
   the visible declaration enumeration.
2. The same module transports exact materialization schemas and the actual
   `BranchModels` at the **same assignment**, reusing
   `GeneralDictionaryRecursiveSemanticOrder`. It preserves `Prepared`, `Failed`,
   and `HeadReady`. This does not replace interval propagation with a different
   model or candidate predicate.
3. `children` reuses `GeneralDictionaryEmissionPlans.children_reorders`, backed
   by `GeneralCanonicalChildOrder.canonicalEmit_reorders`. Clauses are ordered
   by their existing unique source IDs. Every clause, associated-output
   equation, occurrence identity, and repeated-capture binding is retained.
   No raw-child-order counterexample exists for this emitter.
4. `GeneralNominalCandidateReordering` transports the actual Survivor relation,
   pending inspection, and cycle predicates. Its `inspection_witness` preserves
   the exact positions inspected by a non-variable pattern; it does not change
   which cycles count as K2. Journal predicates remain attached to the same
   full state.
5. `GeneralNominalLocalReordering.boundary_local` transports all Local rules,
   including their guards. Root pending still precedes rejection; empty
   candidates still require absence of inspection pending; K2 is not gated by
   inspection pending. The theorem requires only `Reorders first last` and
   `first.roles = roles`, not reachability or a registry-wide Checked premise.
   `reachable_local_order` specializes it to exactly the V5 shared-input domain.
6. `resolves` transports the identical full diagnostic tree using
   `B4Skeleton.resolves_transport`. It retains unsuccessful child results and
   does not fold their parent into a root rejection. `child` preserves the exact
   Child relation; `whereAccessible_iff` transports existing accessibility.

This follows spec §6.3's conjunctive, sibling-order-independent where clauses
and the main draft's clause (3). Pending and diagnostic-tree fidelity follow
the draft addenda 1–4. The K2 inspection positions and priority follow spec
§6.3/K2, including the 2026-11-12 cycle decision. The existing
`GeneralRegistryReordering.Reorders` preserves constructor and role catalogues,
declaration IDs, clause IDs, heads, output binders and associated definitions;
it does not license renaming or choosing a preferred implementation. The
existing `GeneralDictionaryPayloadOrder.Equivalent` is unchanged. Because the
canonical source child lists here are equal, a weaker payload-only permutation
relation is unnecessary for Local transport.

### Minimal faithful separation of the remaining order obligation

`GeneralDictionaryCanonicalLocalOrder.FinalStateAgreement roles e` retains
all the field's premises and all demand/frontier quantifiers. Its conclusion is:

```lean
B4TargetV3.Local B.toSourceBoundary r' (e.run r s root).1 d f ↔
  B4TargetV3.Local B.toSourceBoundary r' (e.run r' s root).1 d f
```

Both sides now use `r'`. The proved theorem is exactly:

```lean
CanonicalLocalOrder roles e ↔ FinalStateAgreement roles e
```

Thus the minimal separation is the proved same-state canonical Local law plus
agreement of the final classifications. Replacing the existing field by the
same-state law alone would lose an obligation of B4 clause (3). No target or
Remaining definition was changed. Equality of the two returned states is a
sufficient stronger premise, proved by `of_returned_state_equality`; it is not
asserted to be necessary. Different administrative journals may still classify
identically, which is why the exact factorization uses Local equivalence.

The formal obstruction uses the existing checked general nominal example
registry and its reversed visible order. A shared empty-journal initial state
has an unresolved input head and is proved reachable under both registries.
The deliberately unconstrained executor tests the first declaration ID and
returns that pending state for one order and the existing nominal-cycle state
for the other. Independent Local classifies the latter as rejected by K2. Local
functionality makes the canonicalLocalOrder equivalence impossible at the
pending frontier.

`not_canonicalLocalOrder` proves failure for this particular executor;
`not_all_executors` refutes universal quantification over arbitrary executors.
The counterexample claims neither execution/halting correctness nor final-tree
correctness. In particular it is **not** a counterexample to confluence of a
faithful saturating implementation. It demonstrates why Checked, Reorders and
shared input Reachable alone do not imply the exact requested field. A faithful
executor and a final-state agreement/confluence argument remain to be built.
This is a proof-interface gap, not a new language semantics question.

### Reachable-root where accessibility

The added theorem `GeneralNominalLocalReordering.whereAccessible_of_readback`
has the exact V5 root-domain conclusion:

```lean
Acc (CommonRoleOutermostResolver.Child
  (B4TargetV3.Local B.toSourceBoundary registry state)) root
```

Its premises are Checked registry, Reachable registry root state, and the
explicit additional witness:

```lean
GeneralNominalCycleReadback.Readback roles registry state.context
```

This reuses the existing checked Paterson argument through the feedback-to-cycle
selection bridge. Readback labels lower/upper arguments with finite Patterns
and connects every selected child to the corresponding checked declaration,
clause identity, capture, and substituted labels. Its producer for every
reachable state, and semantic adequacy of those labels, are still missing.
Reachable does not discharge that witness in this development. Therefore
`whereAccessible` is not counted as a new V5 field. No progress/descent work or
associated-output-growth policy was resumed.

### Boundary field inventory and V5 count

The following are the **unchanged existing definitions** used by this proof.
“Defined” describes the field's actual implementation, not completion of all
its B4 laws. No field is supplied by a fragment or by an executor's result.
Vocabulary remains Registry = `GeneralDeclarations.Registry`, State =
`GeneralNominalSaturationState.State roles`, Demand =
`GeneralSourceDictionaries.Occurrence roles`, Model =
`GeneralNominalCommonBridge.Assignment`.

| SourceBoundary field | Concrete definition in the current boundary | Item 5a status |
| --- | --- | --- |
| Checked | `registry.roles = roles ∧ GeneralDeclarations.Checked registry` | Defined; individual checks transport with identities. |
| Models | `GeneralNominalSaturationState.Models` | Defined; fixed-assignment private/branch Models transport proved. |
| Step | `GeneralNominalFeedbackSteps.Step` | Defined, unchanged; general progress open. |
| Stable | `GeneralNominalFeedbackSteps.Stable` | Defined, unchanged. |
| Generated | `GeneralNominalSaturationState.Generated` | Defined, unchanged; exact generated-children bridge open. |
| RootPending | `GeneralNominalState.RootPending state.context.state root.demand` | Defined, registry independent at a fixed state. |
| RootK2 | `GeneralNominalFeedbackK2.RootK2 state root` | Defined, registry independent at a fixed state. |
| CandidateK2 | `GeneralNominalFeedbackK2.CandidateK2 registry state root` | Defined; exact reorder equivalence proved. |
| InspectionPending | `GeneralNominalCycleK2.InspectionPending registry state.context root` | Defined; exact reorder equivalence proved. |
| Survivor | `GeneralNominalRecursiveCandidates.Survivor registry state.context root` | Defined; key and canonical children preserved exactly. |
| Evidence | `GeneralDictionaryFeedbackEvidence.evidence roles` | Defined using `GeneralDictionaryRecursiveEvidence.Evidence`; no new evidence-node law claimed. |
| Reorders | `GeneralRegistryReordering.Reorders` | Defined; only permitted identity-preserving permutations used. |
| DictionaryEquivalent | `GeneralDictionaryPayloadOrder.Equivalent` | Defined, unchanged. |

V5 additionally uses `GeneralDictionaryInitialSource.Initial` and its existing
`reachable_iff_sourceFormed` correspondence. The six proved V5 fields remain
`closure`, `stepModels`, `frontierLocal`, `localIdentity`, `dictionaryRefl`, and
`initialReorders`. The exact eight open fields remain `progress`, `execution`,
`halted`, `whereAccessible`, `treeExecution`, `canonicalLocalOrder`,
`evidenceNode`, and `generatedChildren`. The new same-state result and the
conditional exact-field result do not change that count.

### Files, checks, and limitations

Added five Lean modules:

- `lean/Yulang/GeneralNominalRegistryOrder.lean`
- `lean/Yulang/GeneralNominalCandidateReordering.lean`
- `lean/Yulang/GeneralNominalLocalReordering.lean`
- `lean/Yulang/GeneralDictionaryCanonicalLocalOrder.lean`
- `lean/Yulang/GeneralDictionaryFinalOrderObstruction.lean`

Added `lean/Audit/AstraOrder.lean` with its own imports and 46 public-theorem
print entries, and the small
[module guide](2026-11-12-astra-order-module-guide.md). Appended five imports to
`lean/Yulang.lean` and this section to the design note. The frozen
`lean/Audit.lean` and `lean/README.md`, all pre-existing Lean definitions, spec,
plans, and configuration were left unchanged. No commit, push, or git reference
change was made.

Final commands from `lean/`, all exited **0**:

```sh
lake build Yulang.GeneralNominalRegistryOrder Yulang.GeneralNominalCandidateReordering Yulang.GeneralNominalLocalReordering Yulang.GeneralDictionaryCanonicalLocalOrder Yulang.GeneralDictionaryFinalOrderObstruction > /tmp/astra-order-focused.log 2>&1
lake build Yulang > /tmp/astra-order-umbrella.log 2>&1
lake env lean Audit/AstraOrder.lean > /tmp/astra-order-audit.log 2>&1
```

Focused build: 669 jobs. Umbrella build: 1602 jobs. All 46 new public theorems
appear exactly once in the new audit; their dependencies are contained in
`{propext, Classical.choice, Quot.sound}`. Full signature extraction with
`lake env lean --stdin` exited 0. The append-only/path check, restricted-token
scan, and `git diff --check` passed. Intermediate proof iterations included
compiler errors that were corrected before these final checks.

The [yulang-proofs skill](/home/momota1029/.codex/skills/yulang-proofs/SKILL.md)
was used. The registered prover role was unavailable in this checkout and
callable tool schema; no prover agent ran. The primary constructed the bounded
proofs. A separate read-only reviewer checked all five modules, the final
three tree/child/accessibility corollaries, and the exact scope of the field
factorization and counterexample. That reviewer independently checked the
compiled types and dependencies of the three principal theorems with
`lake env lean --stdin` (exit 0), but did not rebuild independently.

Not verified/proved: execution or halting of a concrete executor; saturation
confluence or final-state Local agreement; general Readback or reachable-root
accessibility without it; progress; journal-to-joint-classification completeness;
the remaining evidence/generated-children bridges; inference-to-InitialSource
production; surface parsing of the obstruction fixture; full B4. The full
`tools/verify-lean.sh` was not run; the requested focused, umbrella, and new-part
audit checks were run instead. The pending owner question about recursive
associated-output growth is unchanged.

This work connects the general definitions directly: the same Survivor,
projection/interval BranchModels, journal-aware K2, canonical source children,
and concrete V5 boundary are used throughout. It is evidence of convergence
beyond fragment-specific order proofs. The remaining final-state agreement
cannot be replaced by more same-state examples: it requires reasoning about
the actual executions and their resulting information.

### Full new public theorem statements

The following is Lean's elaborated output for all 46 public theorem types,
with implicit parameters exposed. The definitions of CanonicalLocalOrder and
FinalStateAgreement are given above; the obstruction fixture and deliberately
unconstrained executor are in `GeneralDictionaryFinalOrderObstruction.lean`.

```text
@Yulang.GeneralNominalRegistryOrder.keys_membership : ∀ {first last : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralRegistryReordering.Reorders first last →
    ∀ (root : Nat) (key : Yulang.GeneralNominalAllocation.Origin),
      key ∈ Yulang.GeneralNominalAllocation.keys first root ↔ key ∈ Yulang.GeneralNominalAllocation.keys last root
@Yulang.GeneralNominalRegistryOrder.fresh : ∀ {first last : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralRegistryReordering.Reorders first last →
    ∀ (state : Yulang.GeneralNominalState.State) (root : Nat),
      Yulang.GeneralNominalAllocation.Fresh state first root ↔ Yulang.GeneralNominalAllocation.Fresh state last root
@Yulang.GeneralNominalRegistryOrder.metadata : ∀ {first last : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralRegistryReordering.Reorders first last →
    ∀ (context : Yulang.GeneralNominalRecursiveCandidates.Context),
      Yulang.GeneralNominalRecursiveCandidates.Metadata first context ↔
        Yulang.GeneralNominalRecursiveCandidates.Metadata last context
@Yulang.GeneralNominalRegistryOrder.private_models : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralDeclarations.Registry} {a b : Yulang.GeneralDeclarations.Declaration},
  Yulang.GeneralRegistryReordering.DeclarationReorders a b →
    ∀ (context : Yulang.GeneralNominalRecursiveCandidates.Context)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
      (bounds : List (Yulang.GeneralNominalInspection.Bounds context.state))
      (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalState.Models
          (Yulang.GeneralNominalRecursiveCandidates.privateState first context root a bounds) model ↔
        Yulang.GeneralNominalState.Models
          (Yulang.GeneralNominalRecursiveCandidates.privateState last context root b bounds) model
@Yulang.GeneralNominalRegistryOrder.generated : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralDeclarations.Registry} {a b : Yulang.GeneralDeclarations.Declaration},
  Yulang.GeneralRegistryReordering.Reorders first last →
    first.roles = roles →
      Yulang.GeneralRegistryReordering.DeclarationReorders a b →
        ∀ (context : Yulang.GeneralNominalRecursiveCandidates.Context)
          (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
          (ac : Yulang.GeneralDeclarations.DeclarationChecked first.constructors roles a)
          (bc : Yulang.GeneralDeclarations.DeclarationChecked last.constructors roles b)
          (bounds : List (Yulang.GeneralNominalInspection.Bounds context.state)),
          Yulang.GeneralNominalRecursiveCandidates.generated first context root a ac bounds =
            Yulang.GeneralNominalRecursiveCandidates.generated last context root b bc bounds
@Yulang.GeneralNominalRegistryOrder.branch_models : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralDeclarations.Registry} {a b : Yulang.GeneralDeclarations.Declaration},
  Yulang.GeneralRegistryReordering.Reorders first last →
    first.roles = roles →
      Yulang.GeneralRegistryReordering.DeclarationReorders a b →
        ∀ (context : Yulang.GeneralNominalRecursiveCandidates.Context)
          (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
          (ac : Yulang.GeneralDeclarations.DeclarationChecked first.constructors roles a)
          (bc : Yulang.GeneralDeclarations.DeclarationChecked last.constructors roles b)
          (bounds : List (Yulang.GeneralNominalInspection.Bounds context.state))
          (model : Yulang.GeneralNominalCommonBridge.Assignment),
          Yulang.GeneralNominalRecursiveCandidates.BranchModels first context root a ac bounds model ↔
            Yulang.GeneralNominalRecursiveCandidates.BranchModels last context root b bc bounds model
@Yulang.GeneralNominalRegistryOrder.request_ready : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralDeclarations.Registry} {a b : Yulang.GeneralDeclarations.Declaration},
  Yulang.GeneralRegistryReordering.Reorders first last →
    first.roles = roles →
      Yulang.GeneralRegistryReordering.DeclarationReorders a b →
        ∀ (context : Yulang.GeneralNominalRecursiveCandidates.Context)
          (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
          (ac : Yulang.GeneralDeclarations.DeclarationChecked first.constructors roles a)
          (bc : Yulang.GeneralDeclarations.DeclarationChecked last.constructors roles b)
          (bounds : List (Yulang.GeneralNominalInspection.Bounds context.state)),
          Yulang.GeneralNominalRecursiveCandidates.RequestReady first context root a ac bounds ↔
            Yulang.GeneralNominalRecursiveCandidates.RequestReady last context root b bc bounds
@Yulang.GeneralNominalRegistryOrder.children : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralDeclarations.Registry} {a b : Yulang.GeneralDeclarations.Declaration},
  Yulang.GeneralRegistryReordering.Reorders first last →
    Yulang.GeneralRegistryReordering.DeclarationReorders a b →
      ∀ (state : Yulang.GeneralNominalState.State) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
        (ac : Yulang.GeneralDeclarations.DeclarationChecked first.constructors roles a)
        (bc : Yulang.GeneralDeclarations.DeclarationChecked last.constructors roles b)
        (bindings : Yulang.GeneralNominalAllocation.Bindings),
        Yulang.GeneralNominalAllocation.children state first root a ac bindings =
          Yulang.GeneralNominalAllocation.children state last root b bc bindings
@Yulang.GeneralNominalRegistryOrder.prepared : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralDeclarations.Registry} {a b : Yulang.GeneralDeclarations.Declaration},
  Yulang.GeneralRegistryReordering.Reorders first last →
    first.roles = roles →
      Yulang.GeneralRegistryReordering.DeclarationReorders a b →
        ∀ (context : Yulang.GeneralNominalRecursiveCandidates.Context)
          (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
          (ac : Yulang.GeneralDeclarations.DeclarationChecked first.constructors roles a)
          (bc : Yulang.GeneralDeclarations.DeclarationChecked last.constructors roles b),
          Yulang.GeneralNominalRecursiveCandidates.Prepared first context root a ac ↔
            Yulang.GeneralNominalRecursiveCandidates.Prepared last context root b bc
@Yulang.GeneralNominalRegistryOrder.failed : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralDeclarations.Registry} {a b : Yulang.GeneralDeclarations.Declaration},
  Yulang.GeneralRegistryReordering.Reorders first last →
    first.roles = roles →
      Yulang.GeneralRegistryReordering.DeclarationReorders a b →
        ∀ (context : Yulang.GeneralNominalRecursiveCandidates.Context)
          (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
          (ac : Yulang.GeneralDeclarations.DeclarationChecked first.constructors roles a)
          (bc : Yulang.GeneralDeclarations.DeclarationChecked last.constructors roles b),
          Yulang.GeneralNominalRecursiveCandidates.Failed first context root a ac ↔
            Yulang.GeneralNominalRecursiveCandidates.Failed last context root b bc
@Yulang.GeneralNominalRegistryOrder.head_ready : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralDeclarations.Registry} {a b : Yulang.GeneralDeclarations.Declaration},
  Yulang.GeneralRegistryReordering.Reorders first last →
    Yulang.GeneralRegistryReordering.DeclarationReorders a b →
      ∀ (context : Yulang.GeneralNominalRecursiveCandidates.Context)
        (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
        Yulang.GeneralNominalRecursiveCandidates.HeadReady first context root a ↔
          Yulang.GeneralNominalRecursiveCandidates.HeadReady last context root b
@Yulang.GeneralNominalCandidateReordering.checked_declaration : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralDeclarations.Registry} {a b : Yulang.GeneralDeclarations.Declaration},
  Yulang.GeneralRegistryReordering.Reorders first last →
    Yulang.GeneralRegistryReordering.DeclarationReorders a b →
      Yulang.GeneralDeclarations.DeclarationChecked first.constructors roles a →
        Yulang.GeneralDeclarations.DeclarationChecked last.constructors roles b
@Yulang.GeneralNominalCandidateReordering.survivor_forward : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralRegistryReordering.Reorders first last →
    first.roles = roles →
      ∀ (context : Yulang.GeneralNominalRecursiveCandidates.Context)
        (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
        (emitted : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
        Yulang.GeneralNominalRecursiveCandidates.Survivor first context root key emitted →
          Yulang.GeneralNominalRecursiveCandidates.Survivor last context root key emitted
@Yulang.GeneralNominalCandidateReordering.survivor : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralRegistryReordering.Reorders first last →
    first.roles = roles →
      ∀ (context : Yulang.GeneralNominalRecursiveCandidates.Context)
        (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
        (emitted : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
        Yulang.GeneralNominalRecursiveCandidates.Survivor first context root key emitted ↔
          Yulang.GeneralNominalRecursiveCandidates.Survivor last context root key emitted
@Yulang.GeneralNominalCandidateReordering.inspection_pending_forward : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralRegistryReordering.Reorders first last →
    first.roles = roles →
      ∀ (context : Yulang.GeneralNominalRecursiveCandidates.Context)
        (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
        Yulang.GeneralNominalRecursiveCandidates.InspectionPending first context root →
          Yulang.GeneralNominalRecursiveCandidates.InspectionPending last context root
@Yulang.GeneralNominalCandidateReordering.inspection_pending : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralRegistryReordering.Reorders first last →
    first.roles = roles →
      ∀ (context : Yulang.GeneralNominalRecursiveCandidates.Context)
        (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
        Yulang.GeneralNominalRecursiveCandidates.InspectionPending first context root ↔
          Yulang.GeneralNominalRecursiveCandidates.InspectionPending last context root
@Yulang.GeneralNominalCandidateReordering.inspection_witness : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralRegistryReordering.Reorders first last →
    ∀ (context : Yulang.GeneralNominalRecursiveCandidates.Context)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
      (property : Yulang.GeneralNominalInspection.Bounds context.state → Prop),
      (∃ a,
          a ∈ first.declarations ∧
            ∃ _ac,
              a.role = root.demand.role ∧
                Yulang.GeneralNominalRecursiveCandidates.HeadReady first context root a ∧
                  ∃ bounds,
                    Yulang.GeneralNominalRecursiveCandidates.arguments context root = some bounds ∧
                      ∃ visited,
                        visited ∈ (Yulang.GeneralNominalRecursiveCandidates.report context a bounds).inspected ∧
                          property visited) ↔
        ∃ b,
          b ∈ last.declarations ∧
            ∃ _bc,
              b.role = root.demand.role ∧
                Yulang.GeneralNominalRecursiveCandidates.HeadReady last context root b ∧
                  ∃ bounds,
                    Yulang.GeneralNominalRecursiveCandidates.arguments context root = some bounds ∧
                      ∃ visited,
                        visited ∈ (Yulang.GeneralNominalRecursiveCandidates.report context b bounds).inspected ∧
                          property visited
@Yulang.GeneralNominalCandidateReordering.recursive_candidateK2 : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralRegistryReordering.Reorders first last →
    ∀ (context : Yulang.GeneralNominalRecursiveCandidates.Context)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Yulang.GeneralNominalRecursiveCandidates.CandidateK2 first context root ↔
        Yulang.GeneralNominalRecursiveCandidates.CandidateK2 last context root
@Yulang.GeneralNominalCandidateReordering.cycle_candidateK2 : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralRegistryReordering.Reorders first last →
    ∀ (context : Yulang.GeneralNominalRecursiveCandidates.Context)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Yulang.GeneralNominalCycleK2.CandidateK2 first context root ↔
        Yulang.GeneralNominalCycleK2.CandidateK2 last context root
@Yulang.GeneralNominalCandidateReordering.cycle_inspection_pending : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralRegistryReordering.Reorders first last →
    first.roles = roles →
      ∀ (context : Yulang.GeneralNominalRecursiveCandidates.Context)
        (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
        Yulang.GeneralNominalCycleK2.InspectionPending first context root ↔
          Yulang.GeneralNominalCycleK2.InspectionPending last context root
@Yulang.GeneralNominalCandidateReordering.feedback_candidateK2 : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralRegistryReordering.Reorders first last →
    ∀ (state : Yulang.GeneralNominalSaturationState.State roles)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Yulang.GeneralNominalFeedbackK2.CandidateK2 first state root ↔
        Yulang.GeneralNominalFeedbackK2.CandidateK2 last state root
@Yulang.GeneralNominalLocalReordering.local_forward : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralRegistryReordering.Reorders first last →
    first.roles = roles →
      ∀ (state : Yulang.GeneralNominalSaturationState.State roles)
        (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
        (frontier : Yulang.CommonRoleOutermostResolver.Frontier (Yulang.GeneralSourceDictionaries.Occurrence roles)),
        Yulang.GeneralNominalFeedbackK2.Local first state root frontier →
          Yulang.GeneralNominalFeedbackK2.Local last state root frontier
@Yulang.GeneralNominalLocalReordering.local_iff : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralRegistryReordering.Reorders first last →
    first.roles = roles →
      ∀ (state : Yulang.GeneralNominalSaturationState.State roles)
        (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
        (frontier : Yulang.CommonRoleOutermostResolver.Frontier (Yulang.GeneralSourceDictionaries.Occurrence roles)),
        Yulang.GeneralNominalFeedbackK2.Local first state root frontier ↔
          Yulang.GeneralNominalFeedbackK2.Local last state root frontier
@Yulang.GeneralNominalLocalReordering.boundary_local : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralRegistryReordering.Reorders first last →
    first.roles = roles →
      ∀ (state : Yulang.GeneralNominalSaturationState.State roles)
        (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
        (frontier : Yulang.CommonRoleOutermostResolver.Frontier (Yulang.GeneralSourceDictionaries.Occurrence roles)),
        Yulang.B4TargetV3.Local (Yulang.GeneralDictionaryFeedbackEvidence.boundary roles) first state root frontier ↔
          Yulang.B4TargetV3.Local (Yulang.GeneralDictionaryFeedbackEvidence.boundary roles) last state root frontier
@Yulang.GeneralNominalLocalReordering.resolves : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralRegistryReordering.Reorders first last →
    first.roles = roles →
      ∀ (state : Yulang.GeneralNominalSaturationState.State roles)
        (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (tree : Yulang.CommonRoleOutermostResolver.Tree),
        Yulang.CommonRoleOutermostResolver.Resolves
            (Yulang.B4TargetV3.Local (Yulang.GeneralDictionaryFeedbackEvidence.boundary roles) first state) root tree ↔
          Yulang.CommonRoleOutermostResolver.Resolves
            (Yulang.B4TargetV3.Local (Yulang.GeneralDictionaryFeedbackEvidence.boundary roles) last state) root tree
@Yulang.GeneralNominalLocalReordering.child : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralRegistryReordering.Reorders first last →
    first.roles = roles →
      ∀ (state : Yulang.GeneralNominalSaturationState.State roles)
        (descendant parent : Yulang.GeneralSourceDictionaries.Occurrence roles),
        Yulang.CommonRoleOutermostResolver.Child
            (Yulang.B4TargetV3.Local (Yulang.GeneralDictionaryFeedbackEvidence.boundary roles) first state) descendant
            parent ↔
          Yulang.CommonRoleOutermostResolver.Child
            (Yulang.B4TargetV3.Local (Yulang.GeneralDictionaryFeedbackEvidence.boundary roles) last state) descendant
            parent
@Yulang.GeneralNominalLocalReordering.whereAccessible_iff : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralDeclarations.Registry},
  Yulang.GeneralRegistryReordering.Reorders first last →
    first.roles = roles →
      ∀ (state : Yulang.GeneralNominalSaturationState.State roles)
        (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
        Acc
            (Yulang.CommonRoleOutermostResolver.Child
              (Yulang.B4TargetV3.Local (Yulang.GeneralDictionaryFeedbackEvidence.boundary roles) first state))
            root ↔
          Acc
            (Yulang.CommonRoleOutermostResolver.Child
              (Yulang.B4TargetV3.Local (Yulang.GeneralDictionaryFeedbackEvidence.boundary roles) last state))
            root
Yulang.GeneralNominalLocalReordering.reachable_local_order : ∀ (roles : Yulang.Roles.RoleDecls)
  (first last : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).Registry),
  (Yulang.GeneralDictionaryReachableBoundary.boundary roles).Checked first →
    (Yulang.GeneralDictionaryReachableBoundary.boundary roles).Checked last →
      (Yulang.GeneralDictionaryReachableBoundary.boundary roles).Reorders first last →
        ∀ (state : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).State)
          (root : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).Demand),
          Yulang.B4TargetV5.Reachable (Yulang.GeneralDictionaryReachableBoundary.boundary roles) first root state →
            Yulang.B4TargetV5.Reachable (Yulang.GeneralDictionaryReachableBoundary.boundary roles) last root state →
              ∀ (demand : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).Demand)
                (frontier :
                  Yulang.CommonRoleOutermostResolver.Frontier
                    (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).Demand),
                Yulang.B4TargetV3.Local (Yulang.GeneralDictionaryReachableBoundary.boundary roles).toSourceBoundary
                    first state demand frontier ↔
                  Yulang.B4TargetV3.Local (Yulang.GeneralDictionaryReachableBoundary.boundary roles).toSourceBoundary
                    last state demand frontier
Yulang.GeneralNominalLocalReordering.canonicalLocalOrder_of_returned_state_equality : ∀ (roles : Yulang.Roles.RoleDecls)
  (executor : Yulang.B4TargetV3.Executor (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles)),
  (∀ (first last : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).Registry),
      (Yulang.GeneralDictionaryReachableBoundary.boundary roles).Checked first →
        (Yulang.GeneralDictionaryReachableBoundary.boundary roles).Checked last →
          (Yulang.GeneralDictionaryReachableBoundary.boundary roles).Reorders first last →
            ∀ (state : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).State)
              (root : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).Demand),
              Yulang.B4TargetV5.Reachable (Yulang.GeneralDictionaryReachableBoundary.boundary roles) first root state →
                Yulang.B4TargetV5.Reachable (Yulang.GeneralDictionaryReachableBoundary.boundary roles) last root state →
                  (executor.run first state root).fst = (executor.run last state root).fst) →
    ∀ (first last : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).Registry),
      (Yulang.GeneralDictionaryReachableBoundary.boundary roles).Checked first →
        (Yulang.GeneralDictionaryReachableBoundary.boundary roles).Checked last →
          (Yulang.GeneralDictionaryReachableBoundary.boundary roles).Reorders first last →
            ∀ (state : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).State)
              (root : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).Demand),
              Yulang.B4TargetV5.Reachable (Yulang.GeneralDictionaryReachableBoundary.boundary roles) first root state →
                Yulang.B4TargetV5.Reachable (Yulang.GeneralDictionaryReachableBoundary.boundary roles) last root state →
                  ∀ (demand : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).Demand)
                    (frontier :
                      Yulang.CommonRoleOutermostResolver.Frontier
                        (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).Demand),
                    Yulang.B4TargetV3.Local (Yulang.GeneralDictionaryReachableBoundary.boundary roles).toSourceBoundary
                        first (executor.run first state root).fst demand frontier ↔
                      Yulang.B4TargetV3.Local
                        (Yulang.GeneralDictionaryReachableBoundary.boundary roles).toSourceBoundary last
                        (executor.run last state root).fst demand frontier
Yulang.GeneralNominalLocalReordering.whereAccessible_of_readback : ∀ (roles : Yulang.Roles.RoleDecls)
  (registry : Yulang.GeneralDeclarations.Registry),
  (Yulang.GeneralDictionaryReachableBoundary.boundary roles).Checked registry →
    ∀ (state : Yulang.GeneralNominalSaturationState.State roles)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Yulang.B4TargetV5.Reachable (Yulang.GeneralDictionaryReachableBoundary.boundary roles) registry root state →
        ∀ (readback : Yulang.GeneralNominalCycleReadback.Readback roles registry state.context),
          Acc
            (Yulang.CommonRoleOutermostResolver.Child
              (Yulang.B4TargetV3.Local (Yulang.GeneralDictionaryReachableBoundary.boundary roles).toSourceBoundary
                registry state))
            root
Yulang.GeneralDictionaryCanonicalLocalOrder.remaining_field : ∀ (roles : Yulang.Roles.RoleDecls)
  (e : Yulang.B4TargetV3.Executor (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles)),
  Yulang.GeneralDictionaryReachableObligations.Remaining roles e →
    Yulang.GeneralDictionaryCanonicalLocalOrder.CanonicalLocalOrder roles e
Yulang.GeneralDictionaryCanonicalLocalOrder.exact_factorization : ∀ (roles : Yulang.Roles.RoleDecls)
  (e : Yulang.B4TargetV3.Executor (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles)),
  Yulang.GeneralDictionaryCanonicalLocalOrder.CanonicalLocalOrder roles e ↔
    Yulang.GeneralDictionaryCanonicalLocalOrder.FinalStateAgreement roles e
Yulang.GeneralDictionaryCanonicalLocalOrder.of_returned_state_equality : ∀ (roles : Yulang.Roles.RoleDecls)
  (e : Yulang.B4TargetV3.Executor (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles)),
  (∀ (r r' : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).Registry),
      (Yulang.GeneralDictionaryReachableBoundary.boundary roles).Checked r →
        (Yulang.GeneralDictionaryReachableBoundary.boundary roles).Checked r' →
          (Yulang.GeneralDictionaryReachableBoundary.boundary roles).Reorders r r' →
            ∀ (s : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).State)
              (root : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).Demand),
              Yulang.B4TargetV5.Reachable (Yulang.GeneralDictionaryReachableBoundary.boundary roles) r root s →
                Yulang.B4TargetV5.Reachable (Yulang.GeneralDictionaryReachableBoundary.boundary roles) r' root s →
                  (e.run r s root).fst = (e.run r' s root).fst) →
    Yulang.GeneralDictionaryCanonicalLocalOrder.CanonicalLocalOrder roles e
Yulang.GeneralDictionaryFinalOrderObstruction.reorders : Yulang.GeneralRegistryReordering.Reorders
  Yulang.GeneralDictionaryFinalOrderObstruction.first Yulang.GeneralDictionaryFinalOrderObstruction.last
Yulang.GeneralDictionaryFinalOrderObstruction.first_checked : (Yulang.GeneralDictionaryReachableBoundary.boundary
      Yulang.GeneralDeclarationExamples.roles).Checked
  Yulang.GeneralDictionaryFinalOrderObstruction.first
Yulang.GeneralDictionaryFinalOrderObstruction.last_checked : (Yulang.GeneralDictionaryReachableBoundary.boundary
      Yulang.GeneralDeclarationExamples.roles).Checked
  Yulang.GeneralDictionaryFinalOrderObstruction.last
Yulang.GeneralDictionaryFinalOrderObstruction.initial_source : Yulang.GeneralNominalSourceFormation.InitialSource
  Yulang.GeneralDictionaryFinalOrderObstruction.first Yulang.GeneralDictionaryFinalOrderObstruction.pendingContext
  Yulang.GeneralDictionaryFinalOrderObstruction.root
Yulang.GeneralDictionaryFinalOrderObstruction.first_reachable : Yulang.B4TargetV5.Reachable
  (Yulang.GeneralDictionaryReachableBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
  Yulang.GeneralDictionaryFinalOrderObstruction.first Yulang.GeneralDictionaryFinalOrderObstruction.root
  Yulang.GeneralDictionaryFinalOrderObstruction.input
Yulang.GeneralDictionaryFinalOrderObstruction.last_reachable : Yulang.B4TargetV5.Reachable
  (Yulang.GeneralDictionaryReachableBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
  Yulang.GeneralDictionaryFinalOrderObstruction.last Yulang.GeneralDictionaryFinalOrderObstruction.root
  Yulang.GeneralDictionaryFinalOrderObstruction.input
Yulang.GeneralDictionaryFinalOrderObstruction.input_pending : Yulang.GeneralNominalState.RootPending
  Yulang.GeneralDictionaryFinalOrderObstruction.pendingSource Yulang.GeneralDictionaryFinalOrderObstruction.root.demand
Yulang.GeneralDictionaryFinalOrderObstruction.pending_local : Yulang.B4TargetV3.Local
  (Yulang.GeneralDictionaryReachableBoundary.boundary Yulang.GeneralDeclarationExamples.roles).toSourceBoundary
  Yulang.GeneralDictionaryFinalOrderObstruction.first Yulang.GeneralDictionaryFinalOrderObstruction.input
  Yulang.GeneralDictionaryFinalOrderObstruction.root Yulang.CommonRoleOutermostResolver.Frontier.pending
Yulang.GeneralDictionaryFinalOrderObstruction.rejected_local : Yulang.B4TargetV3.Local
  (Yulang.GeneralDictionaryReachableBoundary.boundary Yulang.GeneralDeclarationExamples.roles).toSourceBoundary
  Yulang.GeneralDictionaryFinalOrderObstruction.last Yulang.GeneralDictionaryFinalOrderObstruction.cyclic
  Yulang.GeneralDictionaryFinalOrderObstruction.root Yulang.CommonRoleOutermostResolver.Frontier.rejected
Yulang.GeneralDictionaryFinalOrderObstruction.first_returned : (Yulang.GeneralDictionaryFinalOrderObstruction.executor.run
      Yulang.GeneralDictionaryFinalOrderObstruction.first Yulang.GeneralDictionaryFinalOrderObstruction.input
      Yulang.GeneralDictionaryFinalOrderObstruction.root).fst =
  Yulang.GeneralDictionaryFinalOrderObstruction.input
Yulang.GeneralDictionaryFinalOrderObstruction.last_returned : (Yulang.GeneralDictionaryFinalOrderObstruction.executor.run
      Yulang.GeneralDictionaryFinalOrderObstruction.last Yulang.GeneralDictionaryFinalOrderObstruction.input
      Yulang.GeneralDictionaryFinalOrderObstruction.root).fst =
  Yulang.GeneralDictionaryFinalOrderObstruction.cyclic
Yulang.GeneralDictionaryFinalOrderObstruction.not_canonicalLocalOrder : ¬Yulang.GeneralDictionaryCanonicalLocalOrder.CanonicalLocalOrder
    Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryFinalOrderObstruction.executor
Yulang.GeneralDictionaryFinalOrderObstruction.not_all_executors : ¬∀
    (e :
      Yulang.B4TargetV3.Executor
        (Yulang.GeneralNominalFeedbackBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles)),
    Yulang.GeneralDictionaryCanonicalLocalOrder.CanonicalLocalOrder Yulang.GeneralDeclarationExamples.roles e
```

## Item 5b — progress-conditional executor and halted refresh divergence

### Result and scope

The concrete noncomputable feedback executor is now defined, with exactly the
V5 progress field as its explicit parameter. Its `execution`, `halted`, and
`treeExecution` fields are proved with **Progress as the sole additional
premise**. The existing binders of those fields are retained, including the
child-accessibility binder already present in `treeExecution`. B4 clause (1),
`SaturationTotal`, follows conditional on the same Progress premise. No descent
measure or new proof of Progress is supplied.

The proposed confluence route fails for the current feedback relation. There
is a checked, source-formed, inhabited initial state with two actual one-step
refreshes to halted states. They preserve exactly the same models, have no K2
cycle, and disagree at the saturation root: one selects a concrete leaf and the
other is inspection-pending. Both have child accessibility and are read by the
actual `resolve`; their trees are not `SameDiagnostic`. This is an
implementation gap in observation refinement and recursive inspection, not a
language-semantic choice or a result about an arbitrary unconstrained executor.

The exact `canonicalLocalOrder` field for the new choice-based executor remains
open. Universal agreement of all halted outcomes is formally refuted; that does
not by itself refute registry-order agreement of one particular deterministic
choice of outcomes. No weaker same-state result is counted as that field.

### Executor construction and exact premises

`GeneralDictionaryFeedbackExecutor.Progress roles` copies the V5 field:

```lean
∀ r, (boundary roles).Checked r → ∀ s d,
  B4TargetV5.Reachable (boundary roles) r d s →
  Acc (fun next current => (boundary roles).Step r d current next) s
```

Here and below `boundary` is
`GeneralDictionaryReachableBoundary.boundary`; its underlying source boundary
is the unchanged `GeneralDictionaryFeedbackEvidence.boundary roles`.
`exists_halted` is generic in an actual forward Step relation. Well-founded
induction on its reversed accessibility relation either stops immediately or
follows an enabled step and prepends it to the inductively obtained finite
trace. Its complete conclusion is:

```lean
∃ final, B4Target.Steps step state final ∧ ∀ next, ¬ step final next
```

`finalState roles progress registry state root` chooses this witness when the
registry is checked and the input is Reachable. Outside that specified domain
it returns the input state. Reachability of the chosen final state follows by
concatenating the actual finite trace, not by a separate formation assumption.
The halt property yields Stable for the root and all genuinely generated
children, and the actual Step model law yields model inclusion along the trace.

The executor returns that state with
`diagnostic roles registry final root`. This total tree function tests the
existing FrontierExact and child Acc propositions. When both hold it calls
`CommonRoleOutermostResolver.resolve`; otherwise its explicit total extension
returns `.pending`. This extension is **not asserted to classify a
non-accessible child relation correctly**. For checked final states,
FrontierExact is already available from the existing `frontierLocal` theorem.
Progress of Step has not been shown to imply child accessibility. The latter
remains the independent V5 `whereAccessible` field.

This is why the exact requested `treeExecution` field can be proved with only
Progress added: its original statement already quantifies the FrontierExact
and child Acc witnesses at the returned state. Those witnesses select the
resolve branch, and proof irrelevance identifies their proof arguments. Neither
witness is silently required at the public `run` call. The constructor is a
concrete conditional driver, not an unconditional implementation of B4 Exact.

The exact new field theorems are `execution`, `halted`, and `treeExecution` in
`GeneralDictionaryFeedbackExecutor`. `final_reachable`, `final_stable`,
`final_models`, and `saturationTotal` expose the related guarantees. No selected
packet or journal evidence premise was added.

### Concrete fork: equal models, incompatible halted diagnostics

The source idea is a fully concrete leaf declaration and an alias:

```yulang
impl Display (list (list int)):
    ...
x = [[1]]
y = x
display y
```

This is an explanatory surface sketch, not a parser or inference-production
theorem. The formal fixture uses the existing general `Roles` data, constructor
catalogue, nominal/Common carrier, Checked, InitialSource, feedback Step,
recursive Survivor, and independent Local. `list` remains a resolved nominal
constructor, never a structural record/tag.

The five source identities are:

| Source | Information in the initial full state |
| --- | --- |
| 0 (`B`) | Ordinary equation `B ≈ A`; its observed head is unresolved. The root demand uses interval `(B,B)`. |
| 1 (`A`) | Nominal `list` with point parameter `(I,I)`. |
| 2 (`I`) | Nominal `list` with point parameter `(N,N)`. |
| 3 (`N`) | Ordinary equation and observed scalar head `int`. |
| 4 (`U`) | Ordinary equation `U ≈ top`; no supported constructor head. |

The checked registry contains only declaration key 90, head `list (list int)`,
with no variables, outputs, or where clauses. The initial journal is empty and
contains only the root site. `initial_source` and `initial_reachable` establish
the exact V5 source domain. `initial_models` supplies a real model with
`B = A = list (list int)`, `I = list int`, `N = int`, and `U = top`.

Both updates are actual `GeneralNominalFeedbackSteps.At.refresh` steps at the
root. They retain the ordinary equations and all original observations:

- The precise update records `B` as nominal `list` with parameter `(I,I)`.
- The wider update records `B` as nominal `list` with parameter `(I,U)`.

The latter descriptor is semantically sound: the alias and the descriptor of
`A` already fix the actual parameter to `I`, which lies between `I` and top.
`refresh_models_forward` proves this for every original model, not only the
chosen example. `same_models wide m` proves both whole-journal model sets are
exactly the original set. The wider parameter is a centerless interval; no
exists-substitution candidate search or invented central variable is used.

The actual recursive report for the precise descriptor inspects `(0,0)`,
`(2,2)`, and `(3,3)`, with the real nominal projection origins. `point_branch`
holds in every model of that context. `point_survivor` uses the unchanged
general Survivor and has the exact child list `[]`.

For the wider descriptor, inspection of the nested non-variable nominal head
reaches interval `(2,4)`. Its lower endpoint is a known `list`; its upper
endpoint is top and has no nominal descriptor. The current inspector returns
`blocked = [(2,4)]`. Thus `wide_not_prepared` and `wide_not_failed` yield actual
InspectionPending, and independent Local yields pending. This pending result
is conservative in isolation, but its irreparable dependence on refresh's
chosen representation violates final observational confluence.

The support proofs exclude alternative explanations:

- The common inhabited model forces all journal recurrence edges forward
  through the source numbers; no cycle is possible. The raw graph bridges into
  those actual edges. RootK2 and CandidateK2 are false for both outcomes.
- Both outcomes have a single root site, no child edges, and no aliases, so
  enqueue and a novel merge cannot apply.
- In the precise outcome every possible matching terminal packet is already
  semantically Committed: all constraints hold in every model and it emits no
  children. No installation is needed or enabled as new information.
- In the wider outcome the blocked candidate cannot be installed.
- Sources 0–3 are already Known. The only remaining source is 4. The generic
  `GeneralNominalTopObservation.not_known` theorem proves that a model assigning
  top rules out any certified scalar, structural, or nominal head there. Exact
  refresh preserves that model, so no later refresh can have the required
  unknown-to-Known witness.
- The packet journal is empty, so journal equality is already raw equality;
  no novel equate step is available.

Therefore `stable` and `halted` hold for both endpoints. The observed trees are
`.selected 90 []` and `.pending`. `child_accessible` holds for each; `point_reader`
and `wide_reader` evaluate the new executor's tree reader through actual
`resolve`. `different_reader` proves they are not SameDiagnostic. The root is
Generated reflexively, so this refutes even agreement restricted to generated
root demands, not just the stronger field's quantification over arbitrary
other demands.

`no_observational_join` excludes any later reconciliation: every finite trace
from either halted state is reflexive. These states refute the local
observational joinability premise needed before applying Newman's lemma. An
assumed progress proof cannot turn this unjoinable fork into a joinable one.
No argument deriving progress or a new descent restriction was attempted.

### What must change, and what was not decided

The example needs no new owner language decision. The governing draft clause
(3) and spec §6.3 already require order-independent final classifications;
addendum 2 requires retention of diagnostic trees. The two outcomes encode the
same already-known type and satisfy all current source/refresh checks. Choosing
one outcome by update order is not a semantic option implemented here.

The implementation must make final inspection independent of these equivalent
descriptor presentations, or permit a model-preserving observation refinement
that repairs the wider descriptor after its root is already Known. Merely
proving Known monotone or model sets decreasing/equal cannot do that. The
present `Refines.nominals` preserves existing descriptors, and the Step refresh
novelty condition requires a new Known source. A correct additive repair must
address these together with actual projection inspection; simply postponing
again leaves the wider state halted under the current relation. This note does
not select a repair design or change the frozen definitions.

The outstanding recursive associated-output-growth owner question is unrelated
to this finite, variable-free, no-where example and remains unanswered.
Progress/descent stays paused. No new language-semantic question is added.

### Exact remaining order obligation

`GeneralDictionaryExecutorOrderResidual.HaltedLocalOrder roles` states that,
for checked reordered registries, two finite traces from a shared Reachable
input to halted states have identical independent Local judgments for every
demand/frontier. `canonicalLocalOrder_of_halted_order` proves that this would
supply the exact order field for `GeneralDictionaryFeedbackExecutor.executor
roles progress`, using its proved execution and halting fields.

`not_halted_local_order` refutes that premise with the concrete fork and
**reflexive Reorders**. Hence it is an explicit failed sufficient route, not a
new premise being passed to claim B4 completion. The fork does not establish
that `CanonicalLocalOrder roles (executor roles progress)` itself is false:
that property concerns one choice of returned states across registry
permutations. The fixture's singleton registry does not exercise two distinct
permutations. The precise remaining obligation for the chosen executor is still
the `FinalStateAgreement` equivalence isolated in Item 5a, or a repair and proof
that implies it.

### V5 fourteen-field table

For `GeneralDictionaryReachableBoundary.boundary roles` and the new
`executor roles progress`, there are **six existing unconditional laws and
three new laws derived conditional only on Progress**. Progress itself is
assumed, not proved. Four other fields remain unsupported. Thus nine fields
have derivations with the stated dependency split; this is not nine
unconditional laws, nor a proof of termination.

| V5 B4Bridges field | Status | Exact implementation/theorem or remaining dependency |
| --- | --- | --- |
| progress | ASSUMED | `GeneralDictionaryFeedbackExecutor.Progress roles`; unchanged V5 quantifiers. |
| execution | PROVED given Progress | `GeneralDictionaryFeedbackExecutor.execution`. |
| halted | PROVED given Progress | `GeneralDictionaryFeedbackExecutor.halted`. |
| closure | PROVED, existing | `GeneralDictionaryReachableBoundary.closure`. |
| stepModels | PROVED, existing | `GeneralDictionaryReachableBoundary.stepModels`. |
| frontierLocal | PROVED, existing | `GeneralDictionaryReachableBoundary.frontierLocal`. |
| localIdentity | PROVED, existing | `GeneralDictionaryReachableBoundary.localIdentity`. |
| whereAccessible | OPEN | General reachable-root child accessibility; Progress does not yet provide it. The fork endpoints have it concretely. |
| treeExecution | PROVED given Progress | `GeneralDictionaryFeedbackExecutor.treeExecution`; retains the field's original FrontierExact/child Acc binders. |
| canonicalLocalOrder | OPEN | Exact final-state agreement for this executor. Universal halted Local confluence is refuted. |
| dictionaryRefl | PROVED, existing | `GeneralDictionaryReachableBoundary.dictionaryRefl`. |
| evidenceNode | OPEN | Existing concrete source evidence obligation, unchanged. |
| generatedChildren | OPEN | Existing generated-child correspondence obligation, unchanged. |
| initialReorders | PROVED, existing | `GeneralDictionaryReachableBoundary.initialReorders`. |

`GeneralDictionaryExecutorOrderResidual.Remaining roles progress` now lists
only the four unsupported fields. `remaining` constructs the exact existing
`GeneralDictionaryReachableObligations.Remaining` using the supplied Progress
and the three derived execution laws. `bridges` then composes the existing
six laws. Neither theorem supplies the four residual fields or proves
Progress. No Step, Stable, Committed, Evidence, Initial, or boundary definition
was changed.

### Files and validation

Added seven modules:

- `lean/Yulang/GeneralDictionaryFeedbackExecutor.lean`
- `lean/Yulang/GeneralNominalTopObservation.lean`
- `lean/Yulang/GeneralNominalRefreshFork.lean`
- `lean/Yulang/GeneralNominalRefreshForkCycles.lean`
- `lean/Yulang/GeneralNominalRefreshForkClassification.lean`
- `lean/Yulang/GeneralNominalRefreshDivergence.lean`
- `lean/Yulang/GeneralDictionaryExecutorOrderResidual.lean`

Added `lean/Audit/AstraConfluence.lean` with its own imports and all 83 new public
theorem print entries, plus the small
[module guide](2026-11-12-astra-confluence-module-guide.md). Appended seven imports
to `lean/Yulang.lean` and this Item 5b section. The frozen `lean/Audit.lean` and
`lean/README.md` are unchanged. All pre-existing Lean implementation lines,
spec, plans, configuration, and git references are unchanged. No commit or
push was performed.

Final commands from `lean/`, each exited **0**:

```sh
lake build Yulang.GeneralDictionaryFeedbackExecutor Yulang.GeneralNominalTopObservation Yulang.GeneralNominalRefreshFork Yulang.GeneralNominalRefreshForkCycles Yulang.GeneralNominalRefreshForkClassification Yulang.GeneralNominalRefreshDivergence Yulang.GeneralDictionaryExecutorOrderResidual > /tmp/astra-confluence-focused.log 2>&1
lake build Yulang > /tmp/astra-confluence-umbrella.log 2>&1
lake env lean Audit/AstraConfluence.lean > /tmp/astra-confluence-audit.log 2>&1
```

Focused build completed 675 jobs; umbrella build completed 1609 jobs. All 83
new public theorems occur exactly once in the new dependency audit, using only
`propext`, `Classical.choice`, and `Quot.sound`. Full signature extraction with
`lake env lean --stdin` exited 0. The append-only/path check, restricted source
scan, and `git diff --check` passed. Intermediate proof iterations included
compiler errors, all resolved before these final checks.

The yulang-proofs skill was used. No registered prover role was available, and
no prover agent ran. The primary constructed the executor, fixture,
classification, divergence, and residual package. A complementary agent
independently searched for a counterexample and constructed the two small
TopObservation/Cycles support modules; the primary reviewed those source
proofs. That agent separately reviewed the primary's final modules and the
exact field scopes. Independent compiled type/dependency checks for the
principal divergence, reader, executor, and residual theorems exited 0 with
only the permitted dependencies. This is separate review, not self-review of
the support modules. No independent full umbrella rebuild was claimed.

Not verified/proved: general Progress or a descent measure; an unconditional
child-accessibility producer; absence of the executor's fallback for every
checked reachable input; order agreement of the chosen executor; a repair of
the frozen Step/Refines/inspector; commuting installations or merges; general
EvidenceNode/generatedChildren; an inference producer or parser test for the
illustrative surface sketch; or unconditional B4. The full repository verifier
was not run; the requested focused, umbrella, and new audit-part checks were.

The proof work is converging on the actual general instance by testing exact
execution-level claims against the shared nominal model and real source
formation. This example also shows why model-preservation and local
order-invariance alone are insufficient: an implementation can retain the same
information semantically yet halt with different observable inspection states.
The next necessary implementation result is a repair and proof of observation
completeness/refinement for this fork, rather than another fragment confluence
lemma or an assumed Newman premise.

### Full new public theorem statements

The following are Lean's elaborated types for all 83 new public theorems,
with implicit parameters exposed. Progress, the executor's total extension,
and HaltedLocalOrder are defined explicitly above and in their modules.

```text
@Yulang.GeneralDictionaryFeedbackExecutor.trace_trans : ∀ {α : Type u_1} {step : α → α → Prop} {first middle last : α},
  Yulang.B4Target.Steps step first middle →
    Yulang.B4Target.Steps step middle last → Yulang.B4Target.Steps step first last
@Yulang.GeneralDictionaryFeedbackExecutor.exists_halted : ∀ {α : Type u_1} (step : α → α → Prop) (state : α),
  Acc (fun next current => step current next) state →
    ∃ final, Yulang.B4Target.Steps step state final ∧ ∀ (next : α), ¬step final next
Yulang.GeneralDictionaryFeedbackExecutor.final_spec : ∀ (roles : Yulang.Roles.RoleDecls)
  (progress : Yulang.GeneralDictionaryFeedbackExecutor.Progress roles) (registry : Yulang.GeneralDeclarations.Registry),
  (Yulang.GeneralDictionaryReachableBoundary.boundary roles).Checked registry →
    ∀ (state : Yulang.GeneralNominalSaturationState.State roles)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Yulang.B4TargetV5.Reachable (Yulang.GeneralDictionaryReachableBoundary.boundary roles) registry root state →
        Yulang.B4Target.Steps ((Yulang.GeneralDictionaryReachableBoundary.boundary roles).Step registry root) state
            (Yulang.GeneralDictionaryFeedbackExecutor.finalState roles progress registry state root) ∧
          ∀ (next : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).State),
            ¬(Yulang.GeneralDictionaryReachableBoundary.boundary roles).Step registry root
                (Yulang.GeneralDictionaryFeedbackExecutor.finalState roles progress registry state root) next
Yulang.GeneralDictionaryFeedbackExecutor.diagnostic_eq_resolve : ∀ (roles : Yulang.Roles.RoleDecls)
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (exact :
    Yulang.CommonRoleOutermostResolver.FrontierExact
      (Yulang.GeneralDictionaryReachableBoundary.frontiers roles registry state))
  (accessible :
    Acc
      (Yulang.CommonRoleOutermostResolver.Child
        (Yulang.GeneralDictionaryReachableBoundary.frontiers roles registry state).Local)
      root),
  Yulang.GeneralDictionaryFeedbackExecutor.diagnostic roles registry state root =
    Yulang.CommonRoleOutermostResolver.resolve
      (Yulang.GeneralDictionaryReachableBoundary.frontiers roles registry state) exact root accessible
Yulang.GeneralDictionaryFeedbackExecutor.execution : ∀ (roles : Yulang.Roles.RoleDecls)
  (progress : Yulang.GeneralDictionaryFeedbackExecutor.Progress roles)
  (r : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).Registry),
  (Yulang.GeneralDictionaryReachableBoundary.boundary roles).Checked r →
    ∀ (s : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).State)
      (d : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).Demand),
      Yulang.B4TargetV5.Reachable (Yulang.GeneralDictionaryReachableBoundary.boundary roles) r d s →
        Yulang.B4Target.Steps ((Yulang.GeneralDictionaryReachableBoundary.boundary roles).Step r d) s
          ((Yulang.GeneralDictionaryFeedbackExecutor.executor roles progress).run r s d).fst
Yulang.GeneralDictionaryFeedbackExecutor.halted : ∀ (roles : Yulang.Roles.RoleDecls)
  (progress : Yulang.GeneralDictionaryFeedbackExecutor.Progress roles)
  (r : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).Registry),
  (Yulang.GeneralDictionaryReachableBoundary.boundary roles).Checked r →
    ∀ (s : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).State)
      (d : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).Demand),
      Yulang.B4TargetV5.Reachable (Yulang.GeneralDictionaryReachableBoundary.boundary roles) r d s →
        ∀ (next : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).State),
          ¬(Yulang.GeneralDictionaryReachableBoundary.boundary roles).Step r d
              ((Yulang.GeneralDictionaryFeedbackExecutor.executor roles progress).run r s d).fst next
Yulang.GeneralDictionaryFeedbackExecutor.treeExecution : ∀ (roles : Yulang.Roles.RoleDecls)
  (progress : Yulang.GeneralDictionaryFeedbackExecutor.Progress roles)
  (r : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).Registry),
  (Yulang.GeneralDictionaryReachableBoundary.boundary roles).Checked r →
    ∀ (s : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).State)
      (d : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).Demand),
      Yulang.B4TargetV5.Reachable (Yulang.GeneralDictionaryReachableBoundary.boundary roles) r d s →
        ∀
          (exact :
            Yulang.CommonRoleOutermostResolver.FrontierExact
              (Yulang.GeneralDictionaryReachableBoundary.frontiers roles r
                ((Yulang.GeneralDictionaryFeedbackExecutor.executor roles progress).run r s d).fst))
          (accessible :
            Acc
              (Yulang.CommonRoleOutermostResolver.Child
                (Yulang.GeneralDictionaryReachableBoundary.frontiers roles r
                    ((Yulang.GeneralDictionaryFeedbackExecutor.executor roles progress).run r s d).fst).Local)
              d),
          ((Yulang.GeneralDictionaryFeedbackExecutor.executor roles progress).run r s d).snd =
            Yulang.CommonRoleOutermostResolver.resolve
              (Yulang.GeneralDictionaryReachableBoundary.frontiers roles r
                ((Yulang.GeneralDictionaryFeedbackExecutor.executor roles progress).run r s d).fst)
              exact d accessible
Yulang.GeneralDictionaryFeedbackExecutor.final_reachable : ∀ (roles : Yulang.Roles.RoleDecls)
  (progress : Yulang.GeneralDictionaryFeedbackExecutor.Progress roles) (registry : Yulang.GeneralDeclarations.Registry),
  (Yulang.GeneralDictionaryReachableBoundary.boundary roles).Checked registry →
    ∀ (state : Yulang.GeneralNominalSaturationState.State roles)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Yulang.B4TargetV5.Reachable (Yulang.GeneralDictionaryReachableBoundary.boundary roles) registry root state →
        Yulang.B4TargetV5.Reachable (Yulang.GeneralDictionaryReachableBoundary.boundary roles) registry root
          ((Yulang.GeneralDictionaryFeedbackExecutor.executor roles progress).run registry state root).fst
Yulang.GeneralDictionaryFeedbackExecutor.final_stable : ∀ (roles : Yulang.Roles.RoleDecls)
  (progress : Yulang.GeneralDictionaryFeedbackExecutor.Progress roles) (registry : Yulang.GeneralDeclarations.Registry),
  (Yulang.GeneralDictionaryReachableBoundary.boundary roles).Checked registry →
    ∀ (state : Yulang.GeneralNominalSaturationState.State roles)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Yulang.B4TargetV5.Reachable (Yulang.GeneralDictionaryReachableBoundary.boundary roles) registry root state →
        (Yulang.GeneralDictionaryReachableBoundary.boundary roles).Stable registry
            ((Yulang.GeneralDictionaryFeedbackExecutor.executor roles progress).run registry state root).fst root ∧
          ∀ (child : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).Demand),
            (Yulang.GeneralDictionaryReachableBoundary.boundary roles).Generated registry
                ((Yulang.GeneralDictionaryFeedbackExecutor.executor roles progress).run registry state root).fst root
                child →
              (Yulang.GeneralDictionaryReachableBoundary.boundary roles).Stable registry
                ((Yulang.GeneralDictionaryFeedbackExecutor.executor roles progress).run registry state root).fst child
Yulang.GeneralDictionaryFeedbackExecutor.final_models : ∀ (roles : Yulang.Roles.RoleDecls)
  (progress : Yulang.GeneralDictionaryFeedbackExecutor.Progress roles) (registry : Yulang.GeneralDeclarations.Registry),
  (Yulang.GeneralDictionaryReachableBoundary.boundary roles).Checked registry →
    ∀ (state : Yulang.GeneralNominalSaturationState.State roles)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Yulang.B4TargetV5.Reachable (Yulang.GeneralDictionaryReachableBoundary.boundary roles) registry root state →
        ∀ (model : (Yulang.GeneralNominalFeedbackBoundary.vocabulary roles).Model),
          (Yulang.GeneralDictionaryReachableBoundary.boundary roles).Models
              ((Yulang.GeneralDictionaryFeedbackExecutor.executor roles progress).run registry state root).fst model →
            (Yulang.GeneralDictionaryReachableBoundary.boundary roles).Models state model
Yulang.GeneralDictionaryFeedbackExecutor.saturationTotal : ∀ (roles : Yulang.Roles.RoleDecls)
  (progress : Yulang.GeneralDictionaryFeedbackExecutor.Progress roles),
  Yulang.B4TargetV5.SaturationTotal (Yulang.GeneralDictionaryReachableBoundary.boundary roles)
    (Yulang.GeneralDictionaryFeedbackExecutor.executor roles progress)
Yulang.GeneralNominalTopObservation.le_top : ∀ (value : Yulang.CommonNominalFullCarrier.Ty),
  Yulang.CommonNominalFullCarrier.Subtype value Yulang.CommonNominalSyntax.Layer.top
Yulang.GeneralNominalTopObservation.top_not_scalar : ∀ (base : Yulang.Inference.Base),
  ¬Yulang.CommonNominalFullCarrier.Subtype Yulang.CommonNominalSyntax.Layer.top
      (Yulang.CommonNominalSyntax.Layer.base base)
Yulang.GeneralNominalTopObservation.top_not_nominal : ∀ (name : Nat)
  (arguments : List Yulang.CommonNominalFullCarrier.Argument),
  ¬Yulang.CommonNominalFullCarrier.Subtype Yulang.CommonNominalSyntax.Layer.top
      (Yulang.CommonNominalFullCarrier.nominal name arguments)
@Yulang.GeneralNominalTopObservation.top_not_shape : ∀ {slots : Nat} (shape : Yulang.GeneralNormalizedObservation.Shape)
  (children : Fin shape.arity → Fin slots)
  (assignment : Fin slots → Yulang.Core.PresenceGeneration.Comp Yulang.CommonNominalFullCarrier.model),
  ¬Yulang.CommonNominalFullCarrier.Subtype Yulang.CommonNominalSyntax.Layer.top
      (Yulang.Core.PresenceGeneration.TyTerm.eval Yulang.CommonNominalFullCarrier.model assignment
        (shape.term children))
Yulang.GeneralNominalTopObservation.not_known : ∀ (state : Yulang.GeneralNominalState.State)
  (model : Yulang.GeneralNominalCommonBridge.Assignment) (source : Nat),
  Yulang.GeneralNominalState.Models state model →
    (model source).fst = Yulang.CommonNominalSyntax.Layer.top → ¬Yulang.GeneralNominalState.Known state source
Yulang.GeneralNominalRefreshFork.declaration_checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDeclarationExamples.roles
  Yulang.GeneralNominalRefreshFork.declaration
Yulang.GeneralNominalRefreshFork.registry_checked : Yulang.GeneralDeclarations.Checked
  Yulang.GeneralNominalRefreshFork.registry
@Yulang.GeneralNominalRefreshFork.alias_zero : ∀ {choice : Option Bool}
  (m : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models (Yulang.GeneralNominalRefreshFork.state choice) m →
    Yulang.CommonNominalFullCarrier.Equivalent (m 0).fst (m 1).fst
@Yulang.GeneralNominalRefreshFork.scalar_three : ∀ {choice : Option Bool}
  (m : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models (Yulang.GeneralNominalRefreshFork.state choice) m →
    Yulang.CommonNominalFullCarrier.Equivalent (m 3).fst
      (Yulang.CommonNominalSyntax.Layer.base Yulang.Inference.Base.int)
@Yulang.GeneralNominalRefreshFork.top_four : ∀ {choice : Option Bool}
  (m : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models (Yulang.GeneralNominalRefreshFork.state choice) m →
    Yulang.CommonNominalFullCarrier.Equivalent (m 4).fst Yulang.CommonNominalSyntax.Layer.top
Yulang.GeneralNominalRefreshFork.refresh_models_forward : ∀ (wide : Bool)
  (m : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models (Yulang.GeneralNominalRefreshFork.state none) m →
    Yulang.GeneralNominalState.Models (Yulang.GeneralNominalRefreshFork.state (some wide)) m
Yulang.GeneralNominalRefreshFork.initial_pending : Yulang.GeneralNominalState.RootPending
  (Yulang.GeneralNominalRefreshFork.state none) Yulang.GeneralNominalRefreshFork.root.demand
Yulang.GeneralNominalRefreshFork.zero_known : ∀ (wide : Bool),
  Yulang.GeneralNominalState.Known (Yulang.GeneralNominalRefreshFork.state (some wide)) 0
Yulang.GeneralNominalRefreshFork.refresh_step : ∀ (wide : Bool),
  Yulang.GeneralNominalFeedbackSteps.Step Yulang.GeneralNominalRefreshFork.registry
    Yulang.GeneralNominalRefreshFork.root Yulang.GeneralNominalRefreshFork.before
    (Yulang.GeneralNominalRefreshFork.after wide)
Yulang.GeneralNominalRefreshFork.same_models : ∀ (wide : Bool) (m : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralNominalRefreshFork.after wide) m ↔
    Yulang.GeneralNominalSaturationState.Models Yulang.GeneralNominalRefreshFork.before m
Yulang.GeneralNominalRefreshFork.initial_models : Yulang.GeneralNominalSaturationState.Models
  Yulang.GeneralNominalRefreshFork.before Yulang.GeneralNominalRefreshFork.model
Yulang.GeneralNominalRefreshFork.after_models : ∀ (wide : Bool),
  Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralNominalRefreshFork.after wide)
    Yulang.GeneralNominalRefreshFork.model
Yulang.GeneralNominalRefreshFork.source_bound : ∀ (choice : Option Bool) (source : Nat),
  source ∈ Yulang.GeneralNominalState.sources (Yulang.GeneralNominalRefreshFork.state choice) → source < 5
Yulang.GeneralNominalRefreshFork.linked : ∀ (choice : Option Bool),
  Yulang.GeneralNominalState.Linked (Yulang.GeneralNominalRefreshFork.state choice)
    Yulang.GeneralNominalRefreshFork.root.demand
Yulang.GeneralNominalRefreshFork.metadata : ∀ (choice : Option Bool),
  Yulang.GeneralNominalRecursiveCandidates.Metadata Yulang.GeneralNominalRefreshFork.registry
    (Yulang.GeneralNominalRefreshFork.context choice)
Yulang.GeneralNominalRefreshFork.initial_source : Yulang.GeneralNominalSourceFormation.InitialSource
  Yulang.GeneralNominalRefreshFork.registry (Yulang.GeneralNominalRefreshFork.context none)
  Yulang.GeneralNominalRefreshFork.root
Yulang.GeneralNominalRefreshFork.initial_reachable : Yulang.B4TargetV5.Reachable
  (Yulang.GeneralDictionaryReachableBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
  Yulang.GeneralNominalRefreshFork.registry Yulang.GeneralNominalRefreshFork.root
  Yulang.GeneralNominalRefreshFork.before
Yulang.GeneralNominalRefreshFork.after_reachable : ∀ (wide : Bool),
  Yulang.B4TargetV5.Reachable
    (Yulang.GeneralDictionaryReachableBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralNominalRefreshFork.registry Yulang.GeneralNominalRefreshFork.root
    (Yulang.GeneralNominalRefreshFork.after wide)
Yulang.GeneralNominalRefreshFork.known_below_four : ∀ (wide : Bool) (source : Nat),
  source < 4 → Yulang.GeneralNominalState.Known (Yulang.GeneralNominalRefreshFork.state (some wide)) source
Yulang.GeneralNominalRefreshFork.no_refresh : ∀ (wide : Bool) (next : Yulang.GeneralNominalCandidates.Context)
  (certified : Yulang.GeneralNominalFeedbackSteps.Refresh (Yulang.GeneralNominalRefreshFork.after wide) next)
  (source : Nat),
  source ∈ Yulang.GeneralNominalState.sources (Yulang.GeneralNominalRefreshFork.state (some wide)) →
    ¬Yulang.GeneralNominalState.Known (Yulang.GeneralNominalRefreshFork.state (some wide)) source →
      ¬Yulang.GeneralNominalState.Known next.state source
Yulang.GeneralNominalRefreshForkCycles.feedback_edge_forward : ∀ (wide : Bool) (first last : Nat),
  Yulang.GeneralNominalFeedbackK2.Edge (Yulang.GeneralNominalRefreshFork.after wide) first last → first < last
Yulang.GeneralNominalRefreshForkCycles.feedback_path_forward : ∀ (wide : Bool) (first last : Nat),
  Yulang.GeneralNominalFeedbackK2.Path (Yulang.GeneralNominalRefreshFork.after wide) first last → first ≤ last
Yulang.GeneralNominalRefreshForkCycles.feedback_acyclic : ∀ (wide : Bool) (source : Nat),
  ¬Yulang.GeneralNominalFeedbackK2.Cycle (Yulang.GeneralNominalRefreshFork.after wide) source
Yulang.GeneralNominalRefreshForkCycles.raw_edge_feedback : ∀ (wide : Bool) (first last : Fin 5),
  Yulang.GeneralNominalMixedRecurrence.Edge (Yulang.GeneralNominalRefreshFork.state (some wide)) first last →
    Yulang.GeneralNominalFeedbackK2.Edge (Yulang.GeneralNominalRefreshFork.after wide) ↑first ↑last
Yulang.GeneralNominalRefreshForkCycles.raw_path_feedback : ∀ (wide : Bool) (first last : Fin 5),
  Yulang.GeneralNominalMixedRecurrence.Path (Yulang.GeneralNominalRefreshFork.state (some wide)) first last →
    Yulang.GeneralNominalFeedbackK2.Path (Yulang.GeneralNominalRefreshFork.after wide) ↑first ↑last
Yulang.GeneralNominalRefreshForkCycles.raw_acyclic : ∀ (wide : Bool) (slot : Fin 5),
  ¬Yulang.GeneralNominalCycleK2.RecursAt (Yulang.GeneralNominalRefreshFork.state (some wide)) slot
Yulang.GeneralNominalRefreshForkCycles.legacy_not_recursive : ∀ (wide : Bool) (slot : Fin 5),
  ¬Yulang.GeneralNominalMixedRecurrence.RecursAt (Yulang.GeneralNominalRefreshFork.state (some wide)) slot
Yulang.GeneralNominalRefreshForkCycles.not_rootK2 : ∀ (wide : Bool)
  (demand : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles),
  ¬Yulang.GeneralNominalFeedbackK2.RootK2 (Yulang.GeneralNominalRefreshFork.after wide) demand
Yulang.GeneralNominalRefreshForkCycles.not_candidateK2 : ∀ (wide : Bool)
  (registry : Yulang.GeneralDeclarations.Registry)
  (demand : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles),
  ¬Yulang.GeneralNominalFeedbackK2.CandidateK2 registry (Yulang.GeneralNominalRefreshFork.after wide) demand
@Yulang.GeneralNominalRefreshForkClassification.list_congr : ∀ {first last : Yulang.CommonNominalFullCarrier.Ty},
  Yulang.CommonNominalFullCarrier.Equivalent first last →
    Yulang.CommonNominalFullCarrier.Equivalent (Yulang.GeneralNominalRefreshFork.list first)
      (Yulang.GeneralNominalRefreshFork.list last)
@Yulang.GeneralNominalRefreshForkClassification.point_nominal : ∀ {choice : Option Bool}
  (m : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models (Yulang.GeneralNominalRefreshFork.state choice) m →
    ∀ (slot target : Fin 5),
      (Yulang.GeneralNominalRefreshFork.state choice).nominals slot =
          some (Yulang.GeneralNominalRefreshFork.descriptor (target, target)) →
        Yulang.CommonNominalFullCarrier.Equivalent (m ↑slot).fst (Yulang.GeneralNominalRefreshFork.list (m ↑target).fst)
Yulang.GeneralNominalRefreshForkClassification.point_report : Yulang.GeneralNominalRecursiveCandidates.report
    (Yulang.GeneralNominalRefreshFork.context (some false)) Yulang.GeneralNominalRefreshFork.declaration [(0, 0)] =
  Yulang.GeneralNominalRefreshForkClassification.calculated
Yulang.GeneralNominalRefreshForkClassification.wide_blocked : (Yulang.GeneralNominalRecursiveCandidates.report
      (Yulang.GeneralNominalRefreshFork.context (some true)) Yulang.GeneralNominalRefreshFork.declaration
      [(0, 0)]).blocked =
  [(2, 4)]
Yulang.GeneralNominalRefreshForkClassification.located : ∀ (choice : Option Bool),
  Yulang.GeneralNominalRecursiveCandidates.arguments (Yulang.GeneralNominalRefreshFork.context choice)
      Yulang.GeneralNominalRefreshFork.root =
    some [(0, 0)]
Yulang.GeneralNominalRefreshForkClassification.children_empty : ∀ (choice : Option Bool)
  (checked :
    Yulang.GeneralDeclarations.DeclarationChecked Yulang.GeneralNominalRefreshFork.registry.constructors
      Yulang.GeneralDeclarationExamples.roles Yulang.GeneralNominalRefreshFork.declaration)
  (bindings : Yulang.GeneralNominalAllocation.Bindings),
  Yulang.GeneralNominalAllocation.children (Yulang.GeneralNominalRefreshFork.state choice)
      Yulang.GeneralNominalRefreshFork.registry Yulang.GeneralNominalRefreshFork.root
      Yulang.GeneralNominalRefreshFork.declaration checked bindings =
    []
Yulang.GeneralNominalRefreshForkClassification.schema_empty : ∀ (choice : Option Bool)
  (checked :
    Yulang.GeneralDeclarations.DeclarationChecked Yulang.GeneralNominalRefreshFork.registry.constructors
      Yulang.GeneralDeclarationExamples.roles Yulang.GeneralNominalRefreshFork.declaration),
  Yulang.GeneralNominalRecursiveCandidates.generated Yulang.GeneralNominalRefreshFork.registry
      (Yulang.GeneralNominalRefreshFork.context choice) Yulang.GeneralNominalRefreshFork.root
      Yulang.GeneralNominalRefreshFork.declaration checked [(0, 0)] =
    { }
Yulang.GeneralNominalRefreshForkClassification.point_projections : ∀ (m : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models (Yulang.GeneralNominalRefreshFork.state (some false)) m →
    Yulang.GeneralNominalRecursiveInspection.ProjectionModels (Yulang.GeneralNominalRefreshFork.state (some false))
      Yulang.GeneralNominalRefreshForkClassification.calculated m
Yulang.GeneralNominalRefreshForkClassification.point_branch : ∀
  (checked :
    Yulang.GeneralDeclarations.DeclarationChecked Yulang.GeneralNominalRefreshFork.registry.constructors
      Yulang.GeneralDeclarationExamples.roles Yulang.GeneralNominalRefreshFork.declaration)
  (m : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models (Yulang.GeneralNominalRefreshFork.state (some false)) m →
    Yulang.GeneralNominalRecursiveCandidates.BranchModels Yulang.GeneralNominalRefreshFork.registry
      (Yulang.GeneralNominalRefreshFork.context (some false)) Yulang.GeneralNominalRefreshFork.root
      Yulang.GeneralNominalRefreshFork.declaration checked [(0, 0)] m
Yulang.GeneralNominalRefreshForkClassification.fresh : ∀ (choice : Option Bool),
  Yulang.GeneralNominalAllocation.Fresh (Yulang.GeneralNominalRefreshFork.state choice)
    Yulang.GeneralNominalRefreshFork.registry Yulang.GeneralNominalRefreshFork.root.identity
Yulang.GeneralNominalRefreshForkClassification.point_prepared : Yulang.GeneralNominalRecursiveCandidates.Prepared
  Yulang.GeneralNominalRefreshFork.registry (Yulang.GeneralNominalRefreshFork.context (some false))
  Yulang.GeneralNominalRefreshFork.root Yulang.GeneralNominalRefreshFork.declaration
  Yulang.GeneralNominalRefreshFork.declaration_checked
Yulang.GeneralNominalRefreshForkClassification.point_survivor : Yulang.GeneralNominalRecursiveCandidates.Survivor
  Yulang.GeneralNominalRefreshFork.registry (Yulang.GeneralNominalRefreshFork.context (some false))
  Yulang.GeneralNominalRefreshFork.root 90 []
Yulang.GeneralNominalRefreshForkClassification.wide_not_prepared : ∀
  (checked :
    Yulang.GeneralDeclarations.DeclarationChecked Yulang.GeneralNominalRefreshFork.registry.constructors
      Yulang.GeneralDeclarationExamples.roles Yulang.GeneralNominalRefreshFork.declaration),
  ¬Yulang.GeneralNominalRecursiveCandidates.Prepared Yulang.GeneralNominalRefreshFork.registry
      (Yulang.GeneralNominalRefreshFork.context (some true)) Yulang.GeneralNominalRefreshFork.root
      Yulang.GeneralNominalRefreshFork.declaration checked
Yulang.GeneralNominalRefreshForkClassification.wide_not_failed : ∀
  (checked :
    Yulang.GeneralDeclarations.DeclarationChecked Yulang.GeneralNominalRefreshFork.registry.constructors
      Yulang.GeneralDeclarationExamples.roles Yulang.GeneralNominalRefreshFork.declaration),
  ¬Yulang.GeneralNominalRecursiveCandidates.Failed Yulang.GeneralNominalRefreshFork.registry
      (Yulang.GeneralNominalRefreshFork.context (some true)) Yulang.GeneralNominalRefreshFork.root
      Yulang.GeneralNominalRefreshFork.declaration checked
Yulang.GeneralNominalRefreshForkClassification.wide_inspection_pending : Yulang.GeneralNominalRecursiveCandidates.InspectionPending
  Yulang.GeneralNominalRefreshFork.registry (Yulang.GeneralNominalRefreshFork.context (some true))
  Yulang.GeneralNominalRefreshFork.root
Yulang.GeneralNominalRefreshDivergence.point_selected : Yulang.GeneralNominalFeedbackK2.Local
  Yulang.GeneralNominalRefreshFork.registry (Yulang.GeneralNominalRefreshFork.after false)
  Yulang.GeneralNominalRefreshFork.root (Yulang.CommonRoleOutermostResolver.Frontier.selected 90 [])
Yulang.GeneralNominalRefreshDivergence.wide_pending : Yulang.GeneralNominalFeedbackK2.Local
  Yulang.GeneralNominalRefreshFork.registry (Yulang.GeneralNominalRefreshFork.after true)
  Yulang.GeneralNominalRefreshFork.root Yulang.CommonRoleOutermostResolver.Frontier.pending
Yulang.GeneralNominalRefreshDivergence.generated_only_root : ∀ (wide : Bool)
  (focus : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles),
  Yulang.GeneralNominalSaturationState.Generated (Yulang.GeneralNominalRefreshFork.after wide)
      Yulang.GeneralNominalRefreshFork.root focus →
    focus = Yulang.GeneralNominalRefreshFork.root
Yulang.GeneralNominalRefreshDivergence.installs_committed : ∀ (wide : Bool)
  (packet : Yulang.GeneralNominalSaturationState.Packet Yulang.GeneralDeclarationExamples.roles),
  packet.site.occurrence = Yulang.GeneralNominalRefreshFork.root →
    Yulang.GeneralNominalFeedbackSteps.Installable Yulang.GeneralNominalRefreshFork.registry
        (Yulang.GeneralNominalRefreshFork.after wide) packet →
      Yulang.GeneralNominalFeedbackSteps.Committed (Yulang.GeneralNominalRefreshFork.after wide) packet
Yulang.GeneralNominalRefreshDivergence.stable : ∀ (wide : Bool),
  Yulang.GeneralNominalFeedbackSteps.Stable Yulang.GeneralNominalRefreshFork.registry
    (Yulang.GeneralNominalRefreshFork.after wide) Yulang.GeneralNominalRefreshFork.root
Yulang.GeneralNominalRefreshDivergence.halted : ∀ (wide : Bool)
  (next : Yulang.GeneralNominalSaturationState.State Yulang.GeneralDeclarationExamples.roles),
  ¬Yulang.GeneralNominalFeedbackSteps.Step Yulang.GeneralNominalRefreshFork.registry
      Yulang.GeneralNominalRefreshFork.root (Yulang.GeneralNominalRefreshFork.after wide) next
Yulang.GeneralNominalRefreshDivergence.point_local : Yulang.B4TargetV3.Local
  (Yulang.GeneralDictionaryFeedbackEvidence.boundary Yulang.GeneralDeclarationExamples.roles)
  Yulang.GeneralNominalRefreshFork.registry (Yulang.GeneralNominalRefreshFork.after false)
  Yulang.GeneralNominalRefreshFork.root (Yulang.CommonRoleOutermostResolver.Frontier.selected 90 [])
Yulang.GeneralNominalRefreshDivergence.wide_local : Yulang.B4TargetV3.Local
  (Yulang.GeneralDictionaryFeedbackEvidence.boundary Yulang.GeneralDeclarationExamples.roles)
  Yulang.GeneralNominalRefreshFork.registry (Yulang.GeneralNominalRefreshFork.after true)
  Yulang.GeneralNominalRefreshFork.root Yulang.CommonRoleOutermostResolver.Frontier.pending
Yulang.GeneralNominalRefreshDivergence.point_tree : Yulang.CommonRoleOutermostResolver.Resolves
  (Yulang.B4TargetV3.Local (Yulang.GeneralDictionaryFeedbackEvidence.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralNominalRefreshFork.registry (Yulang.GeneralNominalRefreshFork.after false))
  Yulang.GeneralNominalRefreshFork.root (Yulang.CommonRoleOutermostResolver.Tree.selected 90 [])
Yulang.GeneralNominalRefreshDivergence.wide_tree : Yulang.CommonRoleOutermostResolver.Resolves
  (Yulang.B4TargetV3.Local (Yulang.GeneralDictionaryFeedbackEvidence.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralNominalRefreshFork.registry (Yulang.GeneralNominalRefreshFork.after true))
  Yulang.GeneralNominalRefreshFork.root Yulang.CommonRoleOutermostResolver.Tree.pending
Yulang.GeneralNominalRefreshDivergence.different_local : ¬∀
    (d : (Yulang.GeneralNominalFeedbackBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles).Demand)
    (f :
      Yulang.CommonRoleOutermostResolver.Frontier
        (Yulang.GeneralNominalFeedbackBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles).Demand),
    Yulang.B4TargetV3.Local (Yulang.GeneralDictionaryFeedbackEvidence.boundary Yulang.GeneralDeclarationExamples.roles)
        Yulang.GeneralNominalRefreshFork.registry (Yulang.GeneralNominalRefreshFork.after false) d f ↔
      Yulang.B4TargetV3.Local
        (Yulang.GeneralDictionaryFeedbackEvidence.boundary Yulang.GeneralDeclarationExamples.roles)
        Yulang.GeneralNominalRefreshFork.registry (Yulang.GeneralNominalRefreshFork.after true) d f
Yulang.GeneralNominalRefreshDivergence.different_diagnostic : ¬Yulang.B4TargetV3.SameDiagnostic
    (Yulang.GeneralDictionaryFeedbackEvidence.boundary Yulang.GeneralDeclarationExamples.roles)
    (Yulang.CommonRoleOutermostResolver.Tree.selected 90 []) Yulang.CommonRoleOutermostResolver.Tree.pending
Yulang.GeneralNominalRefreshDivergence.child_accessible : ∀ (wide : Bool),
  Acc
    (Yulang.CommonRoleOutermostResolver.Child
      (Yulang.B4TargetV3.Local
        (Yulang.GeneralDictionaryFeedbackEvidence.boundary Yulang.GeneralDeclarationExamples.roles)
        Yulang.GeneralNominalRefreshFork.registry (Yulang.GeneralNominalRefreshFork.after wide)))
    Yulang.GeneralNominalRefreshFork.root
Yulang.GeneralNominalRefreshDivergence.point_reader : Yulang.GeneralDictionaryFeedbackExecutor.diagnostic
    Yulang.GeneralDeclarationExamples.roles Yulang.GeneralNominalRefreshFork.registry
    (Yulang.GeneralNominalRefreshFork.after false) Yulang.GeneralNominalRefreshFork.root =
  Yulang.CommonRoleOutermostResolver.Tree.selected 90 []
Yulang.GeneralNominalRefreshDivergence.wide_reader : Yulang.GeneralDictionaryFeedbackExecutor.diagnostic
    Yulang.GeneralDeclarationExamples.roles Yulang.GeneralNominalRefreshFork.registry
    (Yulang.GeneralNominalRefreshFork.after true) Yulang.GeneralNominalRefreshFork.root =
  Yulang.CommonRoleOutermostResolver.Tree.pending
Yulang.GeneralNominalRefreshDivergence.different_reader : ¬Yulang.B4TargetV3.SameDiagnostic
    (Yulang.GeneralDictionaryFeedbackEvidence.boundary Yulang.GeneralDeclarationExamples.roles)
    (Yulang.GeneralDictionaryFeedbackExecutor.diagnostic Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralNominalRefreshFork.registry (Yulang.GeneralNominalRefreshFork.after false)
      Yulang.GeneralNominalRefreshFork.root)
    (Yulang.GeneralDictionaryFeedbackExecutor.diagnostic Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralNominalRefreshFork.registry (Yulang.GeneralNominalRefreshFork.after true)
      Yulang.GeneralNominalRefreshFork.root)
@Yulang.GeneralNominalRefreshDivergence.halted_trace_eq : ∀
  {state final : Yulang.GeneralNominalSaturationState.State Yulang.GeneralDeclarationExamples.roles},
  (∀ (next : Yulang.GeneralNominalSaturationState.State Yulang.GeneralDeclarationExamples.roles),
      ¬Yulang.GeneralNominalFeedbackSteps.Step Yulang.GeneralNominalRefreshFork.registry
          Yulang.GeneralNominalRefreshFork.root state next) →
    Yulang.B4Target.Steps
        (Yulang.GeneralNominalFeedbackSteps.Step Yulang.GeneralNominalRefreshFork.registry
          Yulang.GeneralNominalRefreshFork.root)
        state final →
      final = state
Yulang.GeneralNominalRefreshDivergence.no_observational_join : ¬∃ left right,
    Yulang.B4Target.Steps
        (Yulang.GeneralNominalFeedbackSteps.Step Yulang.GeneralNominalRefreshFork.registry
          Yulang.GeneralNominalRefreshFork.root)
        (Yulang.GeneralNominalRefreshFork.after false) left ∧
      Yulang.B4Target.Steps
          (Yulang.GeneralNominalFeedbackSteps.Step Yulang.GeneralNominalRefreshFork.registry
            Yulang.GeneralNominalRefreshFork.root)
          (Yulang.GeneralNominalRefreshFork.after true) right ∧
        ∀ (d : (Yulang.GeneralNominalFeedbackBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles).Demand)
          (f :
            Yulang.CommonRoleOutermostResolver.Frontier
              (Yulang.GeneralNominalFeedbackBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles).Demand),
          Yulang.B4TargetV3.Local
              (Yulang.GeneralDictionaryFeedbackEvidence.boundary Yulang.GeneralDeclarationExamples.roles)
              Yulang.GeneralNominalRefreshFork.registry left d f ↔
            Yulang.B4TargetV3.Local
              (Yulang.GeneralDictionaryFeedbackEvidence.boundary Yulang.GeneralDeclarationExamples.roles)
              Yulang.GeneralNominalRefreshFork.registry right d f
Yulang.GeneralNominalRefreshDivergence.reachable_halted_divergence : (Yulang.GeneralDictionaryReachableBoundary.boundary
        Yulang.GeneralDeclarationExamples.roles).Checked
    Yulang.GeneralNominalRefreshFork.registry ∧
  (Yulang.GeneralDictionaryReachableBoundary.boundary Yulang.GeneralDeclarationExamples.roles).Initial
      Yulang.GeneralNominalRefreshFork.registry Yulang.GeneralNominalRefreshFork.root
      Yulang.GeneralNominalRefreshFork.before ∧
    Yulang.GeneralNominalFeedbackSteps.Step Yulang.GeneralNominalRefreshFork.registry
        Yulang.GeneralNominalRefreshFork.root Yulang.GeneralNominalRefreshFork.before
        (Yulang.GeneralNominalRefreshFork.after false) ∧
      Yulang.GeneralNominalFeedbackSteps.Step Yulang.GeneralNominalRefreshFork.registry
          Yulang.GeneralNominalRefreshFork.root Yulang.GeneralNominalRefreshFork.before
          (Yulang.GeneralNominalRefreshFork.after true) ∧
        (∀ (wide : Bool) (next : Yulang.GeneralNominalSaturationState.State Yulang.GeneralDeclarationExamples.roles),
            ¬Yulang.GeneralNominalFeedbackSteps.Step Yulang.GeneralNominalRefreshFork.registry
                Yulang.GeneralNominalRefreshFork.root (Yulang.GeneralNominalRefreshFork.after wide) next) ∧
          (∀ (wide : Bool) (m : Yulang.GeneralNominalCommonBridge.Assignment),
              Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralNominalRefreshFork.after wide) m ↔
                Yulang.GeneralNominalSaturationState.Models Yulang.GeneralNominalRefreshFork.before m) ∧
            Yulang.GeneralNominalSaturationState.Models Yulang.GeneralNominalRefreshFork.before
                Yulang.GeneralNominalRefreshFork.model ∧
              Yulang.CommonRoleOutermostResolver.Resolves
                  (Yulang.B4TargetV3.Local
                    (Yulang.GeneralDictionaryFeedbackEvidence.boundary Yulang.GeneralDeclarationExamples.roles)
                    Yulang.GeneralNominalRefreshFork.registry (Yulang.GeneralNominalRefreshFork.after false))
                  Yulang.GeneralNominalRefreshFork.root (Yulang.CommonRoleOutermostResolver.Tree.selected 90 []) ∧
                Yulang.CommonRoleOutermostResolver.Resolves
                    (Yulang.B4TargetV3.Local
                      (Yulang.GeneralDictionaryFeedbackEvidence.boundary Yulang.GeneralDeclarationExamples.roles)
                      Yulang.GeneralNominalRefreshFork.registry (Yulang.GeneralNominalRefreshFork.after true))
                    Yulang.GeneralNominalRefreshFork.root Yulang.CommonRoleOutermostResolver.Tree.pending ∧
                  ¬Yulang.B4TargetV3.SameDiagnostic
                      (Yulang.GeneralDictionaryFeedbackEvidence.boundary Yulang.GeneralDeclarationExamples.roles)
                      (Yulang.CommonRoleOutermostResolver.Tree.selected 90 [])
                      Yulang.CommonRoleOutermostResolver.Tree.pending
Yulang.GeneralDictionaryExecutorOrderResidual.canonicalLocalOrder_of_halted_order : ∀ (roles : Yulang.Roles.RoleDecls)
  (progress : Yulang.GeneralDictionaryFeedbackExecutor.Progress roles),
  Yulang.GeneralDictionaryExecutorOrderResidual.HaltedLocalOrder roles →
    Yulang.GeneralDictionaryCanonicalLocalOrder.CanonicalLocalOrder roles
      (Yulang.GeneralDictionaryFeedbackExecutor.executor roles progress)
Yulang.GeneralDictionaryExecutorOrderResidual.not_halted_local_order : ¬Yulang.GeneralDictionaryExecutorOrderResidual.HaltedLocalOrder
    Yulang.GeneralDeclarationExamples.roles
Yulang.GeneralDictionaryExecutorOrderResidual.remaining : ∀ (roles : Yulang.Roles.RoleDecls)
  (progress : Yulang.GeneralDictionaryFeedbackExecutor.Progress roles),
  Yulang.GeneralDictionaryExecutorOrderResidual.Remaining roles progress →
    Yulang.GeneralDictionaryReachableObligations.Remaining roles
      (Yulang.GeneralDictionaryFeedbackExecutor.executor roles progress)
Yulang.GeneralDictionaryExecutorOrderResidual.bridges : ∀ (roles : Yulang.Roles.RoleDecls)
  (progress : Yulang.GeneralDictionaryFeedbackExecutor.Progress roles),
  Yulang.GeneralDictionaryExecutorOrderResidual.Remaining roles progress →
    Yulang.B4SkeletonV5.B4Bridges (Yulang.GeneralDictionaryReachableBoundary.boundary roles)
      (Yulang.GeneralDictionaryFeedbackExecutor.executor roles progress)
      (Yulang.GeneralDictionaryReachableBoundary.frontiers roles)
```

## Item 5c — canonical observation predicate and additive fork repair (2026-11-12)

**Status: partial.** The maximal certified semantic view, its exact model laws,
and the concrete refresh-fork repair are proved. A general consumer of the
maximal view is not constructed. Consequently neither general old-halted to
new-Stable completion nor final-state confluence nor `canonicalLocalOrder`
from Progress alone is claimed. The R-growth question and progress/descent
remain paused; no language decision was made.

### Source authority and two proved implementation obstructions

Spec §6.3 requires waiting for known inputs and finalizing only after sibling
updates stabilize. Its normalization rules remove hidden fields and merge equal
tags before inspection. The draft/addenda preserve root-pending priority, all
unnamed applicability arguments, and lossless child diagnostics. The K2 decision
is about the known type graph, including nominal arguments and excluding nominal
bodies. These rules require the result to reflect known information independently
of a refresh schedule. The same-input merge decision remains unchanged.

Merely adding “no certified refresh can add a Known source” to old Stable is
insufficient. `GeneralNominalCanonicalViewObstructions.knownMaximal_stable_fork`
proves that **both** old endpoints already satisfy that condition. They are
checked, source-reachable, inhabited, and model-equivalent, but disagree on
Local. `not_knownMaximal_stable_confluence` states the negation with those
premises explicitly. Furthermore `wide_cannot_refine_to_point` and
`wide_cannot_refresh_to_point` prove that the old descriptor-preserving refinement
contract itself prevents the repair, independently of the fresh-Known guard.

The second obstruction is representational. The same state entails both the
point descriptor `(2,2)` and the wider descriptor `(2,4)` for source 0. The theorem
`no_single_descriptor_contains_all` proves that one optional descriptor at that
source cannot literally contain both certified facts. This does **not** exclude
choosing a normalized representative with an appropriate completeness theorem;
it rules out equating literal single-slot containment with the maximal view.

### Maximal certified view, with an exact scope

`GeneralCanonicalObservations.canonical state observation` is the conjunction of:

1. `Certified`: the fact is recorded as a scalar, complete normalized structural
   head, or catalogue-checked nominal descriptor in some checked snapshot;
2. `Compatible`: its source and row-source support is available in this state,
   and any nominal declaration agrees with this state's constructor catalogue;
3. `Entails`: **every full journal model** of this state satisfies the fact.

The base witness carries the explicit type/row source identities. Compatibility
uses the whole witness base support, conservatively stronger than only the free
sources of the individual term. Certification uses the existing normalized
snapshot checker, including its hidden-field/same-tag rules. It is not a new
normalizer, nor a claim that the current state's equations possess a particular
syntactic rewrite derivation. State-specific validity comes from journal
entailment. Unknown/deferred observations are excluded from `Recorded`.

`recorded_in_canonical` includes every current recorded head. `maximal` proves
that every compatible, certified, sound predicate is included. `models_exact`
proves that adjoining the entire predicate preserves exactly the full journal
models. Equality of models **and** source support/catalogue gives equality of
canonical views. The predicate is independent of every executor. On an empty
model set entailment is vacuous; this predicate is not fed directly into a K2
or rejection rule, so no new rejection is inferred from that vacuity.

`Cache`, `Completion`, `completion_exists`, and `completion_halted_iff` give a
one-step completion of a semantic observation cache with identical models.
**This is cache completion, not full role saturation.** It does not establish
that a finite `GeneralNominalState.State` realizes all observations or that its
existing recursive inspector consumes them.

### An actual additive transition and the repaired fork

`GeneralNominalReobservationSteps.Revision` fixes the base, normalized structural
view, source identities, constructor catalogue, allocation state, interpretation,
and journal; it replaces nominal descriptors with the same presence domain.
`Certified.raw` requires new raw models to imply old raw models.
`Certified.exact` requires equivalence of **full journal models**. These are
explicit refresh certificates, not assumptions smuggled into a classifier.
`Improves` preserves all currently point-valued descriptors and makes at least
one additional slot point-valued. It does not claim to cover all possible
nonpoint precision improvements.

The new `At` contains every old feedback transition and this certified
reobservation. The new `Step` still operates only at generated demands.
`Stable` means that neither kind of transition applies there or at any generated
child. `stable_iff` characterizes it exactly as old stability plus absence of
these point improvements. `PointClosed` is a sufficient condition for the
second part, **not** a synonym for full canonicality.

The new relation has actual laws for model inclusion, Known/source support,
generated demands, and committed constraints/edges. `canonical_monotone` and
`canonical_trace` show that its full maximal semantic view only grows.
`stable_committed` preserves the evidence prover's required interface.
No existing Step/Stable/Committed definition or theorem was edited.

For the prior fork, `revision_certified` proves a wide-to-point replacement
with equal models, and `repair_step` is an actual new Step. The old point endpoint
is new-Stable; the old wide endpoint is not. Both old forks extend to the exact
same point endpoint. `GeneralNominalReobservationBoundaryExamples.repaired_fork`
packages checked/initial status, both initial transitions, both extensions,
halting/stability, model equality, the actual new-boundary Local
`selected 90 []`, its diagnostic tree, and `SameDiagnostic`.
This is joinability of the specified two forks, not a theorem about every
execution starting there.

A useful guard against an invalid shortcut is
`canonical_equality_does_not_fix_old_local`: the maximal predicates were already
equal at the old divergent endpoints. A consumer bridge is indispensable.

### Confluence attempt and exact remaining work

`GeneralCanonicalObservationSquares` proves actual merge/merge model equality
and maximal-view equality, without assuming those equalities. Old certified
refreshes and new certified revisions leave the maximal predicate unchanged.
Two such revisions from one start therefore agree on that predicate.

`install_adds` derives the precise information addition of an actual installation
from its current-context premise. `square_models` and `square_observations`
show commutation when both orders have the **same fixed semantic additions**.
`reobservation_add_models` gives the analogous refresh/addition equation.
These theorems leave the second transition's availability explicit. They do
not prove install/install or install/merge diamonds: candidate reinspection,
packet rebasing, allocation/capture identities, children, and gate preservation
must still be connected. In particular, monotonic information alone does not
prove that a frozen packet remains Installable after an arbitrary other update.
Merge/merge model commutation likewise does not by itself prove all transition
novelty/enablement conditions or equality of diagnostic sites.

No Newman's-lemma conclusion is claimed. The missing work is:

- **Canonical inspection:** construct a representative or multi-observation
  consumer whose inspected positions, captures, and emitted children are
  complete for `canonical`, and prove the corresponding Local/K2/pending laws.
  In addition, reconcile full journal Models with the current raw-context
  `Survivor` predicate (`ContextComplete` is not automatic).
- **General completion:** establish actual saturation to a state satisfying
  that inspection contract. Cache completion is insufficient. The requested
  same-model conclusion additionally requires that any installation newly
  enabled by completing observations adds no unentailed constraint. The exact
  necessary condition `same_models_stable_requires_constraints` is proved:
  a new-Stable state with the same models must already satisfy every enabled
  packet's constraints in every original model. No concrete counterexample to
  the universal completion request is asserted here.
- **Local diamonds:** prove installation rebasing/emission preservation and
  compatibility of second updates, not just commutation of supplied semantic
  conditions; then obtain final Local/diagnostic agreement under Progress.

These are implementation/proof obligations under the existing decisions.
No formal semantic update-order divergence was established, so there is no
new owner question. The old R-growth owner question remains untouched.

### V5 field table for the new, explicitly partial boundary

The concrete boundary below is
`GeneralNominalReobservationBoundary.boundary roles`; its executor is
`GeneralNominalReobservationExecutor.executor roles progress`.
It preserves the existing independent Local and evidence judgments while
extending Step/Stable. It is **not** advertised as a completed canonical-view
boundary. `Initial` is the unchanged empty-journal source predicate, and
Reachable uses the actual extended relation.

| V5 field | Status and exact provider |
| --- | --- |
| `progress` | OPEN/PAUSED; exact `GeneralNominalReobservationExecutor.Progress roles`. Old feedback Progress is not substituted for it. |
| `execution` | Conditional only on that Progress; `GeneralNominalReobservationExecutor.execution`. |
| `halted` | Conditional only on that Progress; `GeneralNominalReobservationExecutor.halted`. |
| `closure` | PROVED: `GeneralNominalReobservationBoundary.closure`. |
| `stepModels` | PROVED: `GeneralNominalReobservationBoundary.stepModels`. |
| `frontierLocal` | PROVED: `GeneralNominalReobservationBoundary.frontierLocal`. |
| `localIdentity` | PROVED: `GeneralNominalReobservationBoundary.localIdentity`. |
| `whereAccessible` | OPEN; no new descent/child-accessibility claim. |
| `treeExecution` | Conditional only on Progress, with the target's own explicit `FrontierExact`/child-`Acc` binders; `GeneralNominalReobservationExecutor.treeExecution`. |
| `canonicalLocalOrder` | OPEN; `canonicalLocalOrder_of_halted_order` explicitly additionally assumes `HaltedLocalOrder`. No claim from Progress alone. |
| `dictionaryRefl` | PROVED: `GeneralNominalReobservationBoundary.dictionaryRefl`. |
| `evidenceNode` | OPEN; recorded evidence is not promoted to all current selected nodes. |
| `generatedChildren` | OPEN; no unconditional joint-applicability theorem. |
| `initialReorders` | PROVED: `GeneralNominalReobservationBoundary.initialReorders`. |

Count: **6/14 unconditional; 3 more execution fields conditional on Progress;
Progress itself is open, and 4 other fields remain.**
`GeneralNominalReobservationObligations.Remaining` lists exactly those four after
fixing Progress, and `bridges` fills the actual 14-field structure one for one.
The executor reuses the existing accessibility-to-halted-state existence proof;
its tree fallback does not establish the separate where-accessibility obligation.

### Files, review, and verification

Nine new implementation modules are listed in
[the small module guide](2026-11-12-astra-canonical-view-module-guide.md).
Only import lines were appended to `lean/Yulang.lean`. The audit is the new
`lean/Audit/AstraCanonicalView.lean`; the frozen `lean/Audit.lean` and
`lean/README.md` were not changed. No spec, plan, configuration, or git-ref edits.

The yulang-proofs workflow was used. The requested registered `prover` role and
its repository configuration were unavailable; no prover agent ran. The primary
constructed the bounded derivations. A separate reviewer constructed only the
leased obstruction module, which the primary reviewed; that reviewer then
independently reviewed the primary's other eight modules read-only, including
model directions, quantifiers, residual premises, and the 14-field count. No
blocking finding remained. This does not close the missing general consumer or
confluence proofs.

Verification commands, from `lean/` (final runs):

- `lake build Yulang.GeneralNominalReobservationObligations Yulang.GeneralNominalReobservationBoundaryExamples Yulang.GeneralCanonicalObservationSquares` — exit **0**.
- `lake build Yulang` — exit **0**.
- `lake env lean Audit/AstraCanonicalView.lean` — exit **0**; all **95** new public theorems audited, dependencies confined to `propext`, `Classical.choice`, and `Quot.sound` (or none).

These commands do not claim that the frozen umbrella audit or every historical
audit part was rerun. General maximal-view inspection/completion/confluence and
Progress remain unverified. The result is a repair on the real general carrier,
not another scalar fragment, but a complete Item 5c requires the consumer bridge
and transition diamonds above.

### Full new public theorem statements

The following are Lean's elaborated `#check @...` statements. Definitions and
proofs remain in the modules linked by the guide; all implicit premises are
visible here.

```lean
@Yulang.GeneralCanonicalObservations.recorded_sound : ∀ {observation : Yulang.GeneralCanonicalObservations.Observation}
  (snapshot : Yulang.GeneralNominalState.State) (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models snapshot model →
    Yulang.GeneralCanonicalObservations.Recorded snapshot observation → observation.Holds model
@Yulang.GeneralCanonicalObservations.recorded_compatible : ∀ {roles : Yulang.Roles.RoleDecls}
  {observation : Yulang.GeneralCanonicalObservations.Observation}
  (state : Yulang.GeneralNominalSaturationState.State roles),
  Yulang.GeneralCanonicalObservations.Recorded state.context.state observation →
    Yulang.GeneralCanonicalObservations.Compatible state observation
@Yulang.GeneralCanonicalObservations.recorded_in_canonical : ∀ {roles : Yulang.Roles.RoleDecls}
  {observation : Yulang.GeneralCanonicalObservations.Observation}
  (state : Yulang.GeneralNominalSaturationState.State roles),
  Yulang.GeneralCanonicalObservations.Recorded state.context.state observation →
    Yulang.GeneralCanonicalObservations.canonical state observation
@Yulang.GeneralCanonicalObservations.canonical_sound : ∀ {roles : Yulang.Roles.RoleDecls}
  {observation : Yulang.GeneralCanonicalObservations.Observation}
  (state : Yulang.GeneralNominalSaturationState.State roles),
  Yulang.GeneralCanonicalObservations.canonical state observation →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models state model → observation.Holds model
@Yulang.GeneralCanonicalObservations.canonical_complete : ∀ {roles : Yulang.Roles.RoleDecls}
  {observation : Yulang.GeneralCanonicalObservations.Observation}
  (state : Yulang.GeneralNominalSaturationState.State roles),
  Yulang.GeneralCanonicalObservations.Certified observation →
    Yulang.GeneralCanonicalObservations.Compatible state observation →
      Yulang.GeneralCanonicalObservations.Entails state observation →
        Yulang.GeneralCanonicalObservations.canonical state observation
@Yulang.GeneralCanonicalObservations.maximal : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (view : Yulang.GeneralCanonicalObservations.Observation → Prop),
  (∀ (observation : Yulang.GeneralCanonicalObservations.Observation),
      view observation → Yulang.GeneralCanonicalObservations.Certified observation) →
    (∀ (observation : Yulang.GeneralCanonicalObservations.Observation),
        view observation → Yulang.GeneralCanonicalObservations.Compatible state observation) →
      (∀ (observation : Yulang.GeneralCanonicalObservations.Observation),
          view observation → Yulang.GeneralCanonicalObservations.Entails state observation) →
        ∀ (observation : Yulang.GeneralCanonicalObservations.Observation),
          view observation → Yulang.GeneralCanonicalObservations.canonical state observation
@Yulang.GeneralCanonicalObservations.models_exact : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles) (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralCanonicalObservations.ViewModels state model ↔ Yulang.GeneralNominalSaturationState.Models state model
@Yulang.GeneralCanonicalObservations.compatible_mono : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralNominalSaturationState.State roles}
  {observation : Yulang.GeneralCanonicalObservations.Observation},
  Yulang.GeneralCanonicalObservations.BasisExtends before after →
    Yulang.GeneralCanonicalObservations.Compatible before observation →
      Yulang.GeneralCanonicalObservations.Compatible after observation
@Yulang.GeneralCanonicalObservations.monotone : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralNominalSaturationState.State roles},
  Yulang.GeneralCanonicalObservations.BasisExtends before after →
    (∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
        Yulang.GeneralNominalSaturationState.Models after model →
          Yulang.GeneralNominalSaturationState.Models before model) →
      ∀ (observation : Yulang.GeneralCanonicalObservations.Observation),
        Yulang.GeneralCanonicalObservations.canonical before observation →
          Yulang.GeneralCanonicalObservations.canonical after observation
@Yulang.GeneralCanonicalObservations.equal_of_same_information : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Yulang.GeneralNominalSaturationState.State roles},
  Yulang.GeneralCanonicalObservations.BasisExtends first last →
    Yulang.GeneralCanonicalObservations.BasisExtends last first →
      (∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
          Yulang.GeneralNominalSaturationState.Models first model ↔
            Yulang.GeneralNominalSaturationState.Models last model) →
        Yulang.GeneralCanonicalObservations.canonical first = Yulang.GeneralCanonicalObservations.canonical last
@Yulang.GeneralCanonicalObservations.complete_canonical : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles),
  Yulang.GeneralCanonicalObservations.Canonical (Yulang.GeneralCanonicalObservations.complete state)
@Yulang.GeneralCanonicalObservations.canonical_cache_unique : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles}
  (first last : Yulang.GeneralCanonicalObservations.Cache state),
  Yulang.GeneralCanonicalObservations.Canonical first →
    Yulang.GeneralCanonicalObservations.Canonical last → first.contains = last.contains
@Yulang.GeneralCanonicalObservations.completion_models : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles}
  {first last : Yulang.GeneralCanonicalObservations.Cache state},
  Yulang.GeneralCanonicalObservations.Completion state first last →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      (Yulang.GeneralNominalSaturationState.Models state model ∧
          ∀ (observation : Yulang.GeneralCanonicalObservations.Observation),
            last.contains observation → observation.Holds model) ↔
        Yulang.GeneralNominalSaturationState.Models state model ∧
          ∀ (observation : Yulang.GeneralCanonicalObservations.Observation),
            first.contains observation → observation.Holds model
@Yulang.GeneralCanonicalObservations.completion_exists : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles} (cache : Yulang.GeneralCanonicalObservations.Cache state),
  ∃ final,
    Yulang.B4Target.Steps (Yulang.GeneralCanonicalObservations.Completion state) cache final ∧
      Yulang.GeneralCanonicalObservations.Canonical final
@Yulang.GeneralCanonicalObservations.completion_halted_iff : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles} (cache : Yulang.GeneralCanonicalObservations.Cache state),
  (∀ (next : Yulang.GeneralCanonicalObservations.Cache state),
      ¬Yulang.GeneralCanonicalObservations.Completion state cache next) ↔
    Yulang.GeneralCanonicalObservations.Canonical cache
Yulang.GeneralNominalCanonicalViewObstructions.fork_knownMaximal : ∀ (wide : Bool),
  Yulang.GeneralNominalCanonicalViewObstructions.KnownMaximal (Yulang.GeneralNominalRefreshFork.after wide)
Yulang.GeneralNominalCanonicalViewObstructions.wide_cannot_refine_to_point : ¬Nonempty
    (Yulang.GeneralNominalRefinements.Refines (Yulang.GeneralNominalRefreshFork.state (some true))
      (Yulang.GeneralNominalRefreshFork.state (some false)))
Yulang.GeneralNominalCanonicalViewObstructions.wide_cannot_refresh_to_point : ¬Nonempty
    (Yulang.GeneralNominalFeedbackSteps.Refresh (Yulang.GeneralNominalRefreshFork.after true)
      (Yulang.GeneralNominalRefreshFork.context (some false)))
Yulang.GeneralNominalCanonicalViewObstructions.knownMaximal_stable_fork : (Yulang.GeneralDictionaryReachableBoundary.boundary
        Yulang.GeneralDeclarationExamples.roles).Checked
    Yulang.GeneralNominalRefreshFork.registry ∧
  (Yulang.GeneralDictionaryReachableBoundary.boundary Yulang.GeneralDeclarationExamples.roles).Initial
      Yulang.GeneralNominalRefreshFork.registry Yulang.GeneralNominalRefreshFork.root
      Yulang.GeneralNominalRefreshFork.before ∧
    (∀ (wide : Bool),
        Yulang.B4TargetV5.Reachable
          (Yulang.GeneralDictionaryReachableBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
          Yulang.GeneralNominalRefreshFork.registry Yulang.GeneralNominalRefreshFork.root
          (Yulang.GeneralNominalRefreshFork.after wide)) ∧
      (∀ (wide : Bool),
          Yulang.GeneralNominalCanonicalViewObstructions.KnownMaximal (Yulang.GeneralNominalRefreshFork.after wide) ∧
            Yulang.GeneralNominalFeedbackSteps.Stable Yulang.GeneralNominalRefreshFork.registry
              (Yulang.GeneralNominalRefreshFork.after wide) Yulang.GeneralNominalRefreshFork.root) ∧
        (∀ (wide : Bool) (model : Yulang.GeneralNominalCommonBridge.Assignment),
            Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralNominalRefreshFork.after wide) model ↔
              Yulang.GeneralNominalSaturationState.Models Yulang.GeneralNominalRefreshFork.before model) ∧
          Yulang.GeneralNominalSaturationState.Models Yulang.GeneralNominalRefreshFork.before
              Yulang.GeneralNominalRefreshFork.model ∧
            ¬∀
                (demand :
                  (Yulang.GeneralNominalFeedbackBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles).Demand)
                (frontier :
                  Yulang.CommonRoleOutermostResolver.Frontier
                    (Yulang.GeneralNominalFeedbackBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles).Demand),
                Yulang.B4TargetV3.Local
                    (Yulang.GeneralDictionaryFeedbackEvidence.boundary Yulang.GeneralDeclarationExamples.roles)
                    Yulang.GeneralNominalRefreshFork.registry (Yulang.GeneralNominalRefreshFork.after false) demand
                    frontier ↔
                  Yulang.B4TargetV3.Local
                    (Yulang.GeneralDictionaryFeedbackEvidence.boundary Yulang.GeneralDeclarationExamples.roles)
                    Yulang.GeneralNominalRefreshFork.registry (Yulang.GeneralNominalRefreshFork.after true) demand
                    frontier
Yulang.GeneralNominalCanonicalViewObstructions.not_knownMaximal_stable_confluence : ¬∀
    (first last : Yulang.GeneralNominalSaturationState.State Yulang.GeneralDeclarationExamples.roles),
    Yulang.B4Target.Steps
        (Yulang.GeneralNominalFeedbackSteps.Step Yulang.GeneralNominalRefreshFork.registry
          Yulang.GeneralNominalRefreshFork.root)
        Yulang.GeneralNominalRefreshFork.before first →
      Yulang.B4Target.Steps
          (Yulang.GeneralNominalFeedbackSteps.Step Yulang.GeneralNominalRefreshFork.registry
            Yulang.GeneralNominalRefreshFork.root)
          Yulang.GeneralNominalRefreshFork.before last →
        Yulang.GeneralNominalFeedbackSteps.Stable Yulang.GeneralNominalRefreshFork.registry first
            Yulang.GeneralNominalRefreshFork.root →
          Yulang.GeneralNominalFeedbackSteps.Stable Yulang.GeneralNominalRefreshFork.registry last
              Yulang.GeneralNominalRefreshFork.root →
            Yulang.GeneralNominalCanonicalViewObstructions.KnownMaximal first →
              Yulang.GeneralNominalCanonicalViewObstructions.KnownMaximal last →
                (∀ (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
                    Yulang.GeneralNominalSaturationState.Models first assignment ↔
                      Yulang.GeneralNominalSaturationState.Models last assignment) →
                  ∀
                    (demand :
                      (Yulang.GeneralNominalFeedbackBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles).Demand)
                    (frontier :
                      Yulang.CommonRoleOutermostResolver.Frontier
                        (Yulang.GeneralNominalFeedbackBoundary.vocabulary
                            Yulang.GeneralDeclarationExamples.roles).Demand),
                    Yulang.B4TargetV3.Local
                        (Yulang.GeneralDictionaryFeedbackEvidence.boundary Yulang.GeneralDeclarationExamples.roles)
                        Yulang.GeneralNominalRefreshFork.registry first demand frontier ↔
                      Yulang.B4TargetV3.Local
                        (Yulang.GeneralDictionaryFeedbackEvidence.boundary Yulang.GeneralDeclarationExamples.roles)
                        Yulang.GeneralNominalRefreshFork.registry last demand frontier
@Yulang.GeneralNominalReobservationSteps.revision_known : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles}
  (revision : Yulang.GeneralNominalReobservationSteps.Revision state) (source : Nat),
  Yulang.GeneralNominalState.Known revision.snapshot source ↔
    Yulang.GeneralNominalState.Known state.context.state source
@Yulang.GeneralNominalReobservationSteps.revision_basis : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles}
  (revision : Yulang.GeneralNominalReobservationSteps.Revision state),
  Yulang.GeneralCanonicalObservations.BasisExtends state revision.result ∧
    Yulang.GeneralCanonicalObservations.BasisExtends revision.result state
@Yulang.GeneralNominalReobservationSteps.revision_canonical : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles}
  (revision : Yulang.GeneralNominalReobservationSteps.Revision state),
  Yulang.GeneralNominalReobservationSteps.Certified revision →
    Yulang.GeneralCanonicalObservations.canonical revision.result = Yulang.GeneralCanonicalObservations.canonical state
@Yulang.GeneralNominalReobservationSteps.pointClosed_no_revision : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles},
  Yulang.GeneralNominalReobservationSteps.PointClosed state.context.state →
    ∀ (revision : Yulang.GeneralNominalReobservationSteps.Revision state),
      ¬Yulang.GeneralNominalReobservationSteps.Improves revision
@Yulang.GeneralNominalReobservationSteps.old_step : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralNominalSaturationState.State roles} {registry : Yulang.GeneralDeclarations.Registry}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalFeedbackSteps.Step registry root before after →
    Yulang.GeneralNominalReobservationSteps.Step registry root before after
@Yulang.GeneralNominalReobservationSteps.at_models : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralNominalSaturationState.State roles} {registry : Yulang.GeneralDeclarations.Registry}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalReobservationSteps.At registry before focus after →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models after model → Yulang.GeneralNominalSaturationState.Models before model
@Yulang.GeneralNominalReobservationSteps.stepModels : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralNominalSaturationState.State roles} {registry : Yulang.GeneralDeclarations.Registry}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalReobservationSteps.Step registry root before after →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models after model → Yulang.GeneralNominalSaturationState.Models before model
@Yulang.GeneralNominalReobservationSteps.steps_models : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralNominalSaturationState.State roles} {registry : Yulang.GeneralDeclarations.Registry}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.B4Target.Steps (Yulang.GeneralNominalReobservationSteps.Step registry root) before after →
    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models after model → Yulang.GeneralNominalSaturationState.Models before model
@Yulang.GeneralNominalReobservationSteps.at_known : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralNominalSaturationState.State roles} {registry : Yulang.GeneralDeclarations.Registry}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalReobservationSteps.At registry before focus after →
    ∀ (source : Nat),
      Yulang.GeneralNominalState.Known before.context.state source →
        Yulang.GeneralNominalState.Known after.context.state source
@Yulang.GeneralNominalReobservationSteps.at_extends : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralNominalSaturationState.State roles} {registry : Yulang.GeneralDeclarations.Registry}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalReobservationSteps.At registry before focus after →
    Yulang.GeneralNominalFeedbackProgress.Extends before after
@Yulang.GeneralNominalReobservationSteps.generated_monotone : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralNominalSaturationState.State roles} {registry : Yulang.GeneralDeclarations.Registry}
  {root child : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalReobservationSteps.Step registry root before after →
    Yulang.GeneralNominalSaturationState.Generated before root child →
      Yulang.GeneralNominalSaturationState.Generated after root child
@Yulang.GeneralNominalReobservationSteps.basis_of_refines : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralNominalSaturationState.State roles}
  (refines : Yulang.GeneralNominalRefinements.Refines before.context.state after.context.state),
  Yulang.GeneralCanonicalObservations.BasisExtends before after
@Yulang.GeneralNominalReobservationSteps.at_basis : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralNominalSaturationState.State roles} {registry : Yulang.GeneralDeclarations.Registry}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalReobservationSteps.At registry before focus after →
    Yulang.GeneralCanonicalObservations.BasisExtends before after
@Yulang.GeneralNominalReobservationSteps.canonical_monotone : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralNominalSaturationState.State roles} {registry : Yulang.GeneralDeclarations.Registry}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalReobservationSteps.Step registry root before after →
    ∀ (observation : Yulang.GeneralCanonicalObservations.Observation),
      Yulang.GeneralCanonicalObservations.canonical before observation →
        Yulang.GeneralCanonicalObservations.canonical after observation
@Yulang.GeneralNominalReobservationSteps.canonical_trace : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralNominalSaturationState.State roles} {registry : Yulang.GeneralDeclarations.Registry}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.B4Target.Steps (Yulang.GeneralNominalReobservationSteps.Step registry root) before after →
    ∀ (observation : Yulang.GeneralCanonicalObservations.Observation),
      Yulang.GeneralCanonicalObservations.canonical before observation →
        Yulang.GeneralCanonicalObservations.canonical after observation
@Yulang.GeneralNominalReobservationSteps.stable_iff : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.GeneralNominalReobservationSteps.Stable registry state root ↔
    Yulang.GeneralNominalFeedbackSteps.Stable registry state root ∧
      ∀ (revision : Yulang.GeneralNominalReobservationSteps.Revision state),
        Yulang.GeneralNominalReobservationSteps.Certified revision →
          ¬Yulang.GeneralNominalReobservationSteps.Improves revision
@Yulang.GeneralNominalReobservationSteps.stable_of_pointClosed : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles} {registry : Yulang.GeneralDeclarations.Registry}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalFeedbackSteps.Stable registry state root →
    Yulang.GeneralNominalReobservationSteps.PointClosed state.context.state →
      Yulang.GeneralNominalReobservationSteps.Stable registry state root
@Yulang.GeneralNominalReobservationSteps.halted_stable : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles} {registry : Yulang.GeneralDeclarations.Registry}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles},
  (∀ (after : Yulang.GeneralNominalSaturationState.State roles),
      ¬Yulang.GeneralNominalReobservationSteps.Step registry root state after) →
    Yulang.GeneralNominalReobservationSteps.Stable registry state root
@Yulang.GeneralNominalReobservationSteps.stable_halted : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles} {registry : Yulang.GeneralDeclarations.Registry}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalReobservationSteps.Stable registry state root →
    ∀ (after : Yulang.GeneralNominalSaturationState.State roles),
      ¬Yulang.GeneralNominalReobservationSteps.Step registry root state after
@Yulang.GeneralNominalReobservationSteps.stable_generated : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles} {registry : Yulang.GeneralDeclarations.Registry}
  {root child : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalReobservationSteps.Stable registry state root →
    Yulang.GeneralNominalSaturationState.Generated state root child →
      Yulang.GeneralNominalReobservationSteps.Stable registry state child
@Yulang.GeneralNominalReobservationSteps.closure : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles} {registry : Yulang.GeneralDeclarations.Registry}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles},
  (∀ (after : Yulang.GeneralNominalSaturationState.State roles),
      ¬Yulang.GeneralNominalReobservationSteps.Step registry root state after) →
    Yulang.GeneralNominalReobservationSteps.Stable registry state root ∧
      ∀ (child : Yulang.GeneralSourceDictionaries.Occurrence roles),
        Yulang.GeneralNominalSaturationState.Generated state root child →
          Yulang.GeneralNominalReobservationSteps.Stable registry state child
@Yulang.GeneralNominalReobservationSteps.stable_committed : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles} {registry : Yulang.GeneralDeclarations.Registry}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalReobservationSteps.Stable registry state root →
    ∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
      Yulang.GeneralNominalSaturationState.Generated state root packet.site.occurrence →
        Yulang.GeneralNominalFeedbackSteps.Installable registry state packet →
          Yulang.GeneralNominalFeedbackSteps.Committed state packet
@Yulang.GeneralNominalReobservationSteps.committed_trace : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralNominalSaturationState.State roles} {registry : Yulang.GeneralDeclarations.Registry}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {packet : Yulang.GeneralNominalSaturationState.Packet roles},
  Yulang.B4Target.Steps (Yulang.GeneralNominalReobservationSteps.Step registry root) before after →
    Yulang.GeneralNominalFeedbackSteps.Committed before packet →
      Yulang.GeneralNominalFeedbackSteps.Committed after packet
@Yulang.GeneralNominalReobservationSteps.same_models_stable_requires_constraints : ∀ {roles : Yulang.Roles.RoleDecls}
  {before after : Yulang.GeneralNominalSaturationState.State roles} {registry : Yulang.GeneralDeclarations.Registry}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralNominalReobservationSteps.Stable registry after root →
    (∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
        Yulang.GeneralNominalSaturationState.Models before model ↔
          Yulang.GeneralNominalSaturationState.Models after model) →
      ∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
        Yulang.GeneralNominalSaturationState.Generated after root packet.site.occurrence →
          Yulang.GeneralNominalFeedbackSteps.Installable registry after packet →
            ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
              Yulang.GeneralNominalSaturationState.Models before model → packet.Holds model
@Yulang.GeneralCanonicalObservationSquares.install_adds : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (packet : Yulang.GeneralNominalSaturationState.Packet roles)
  (emission : Yulang.GeneralNominalFeedbackSites.Emission packet),
  packet.context = state.context →
    Yulang.GeneralCanonicalObservationSquares.Adds state
      (Yulang.GeneralNominalFeedbackSites.install state packet emission) packet.Holds
@Yulang.GeneralCanonicalObservationSquares.merge_adds : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (first last : Yulang.GeneralNominalDemandMerging.Site roles),
  Yulang.GeneralCanonicalObservationSquares.Adds state (Yulang.GeneralNominalSaturationState.merge state first last)
    fun model =>
    Yulang.PresenceNormalForm.All Yulang.CommonNominalFullCarrier.model model
      (Yulang.GeneralNominalDemandMerging.outputAtoms first last)
@Yulang.GeneralCanonicalObservationSquares.square_models : ∀ {roles : Yulang.Roles.RoleDecls}
  {start left right finalLeft finalRight : Yulang.GeneralNominalSaturationState.State roles}
  {one two : Yulang.GeneralNominalCommonBridge.Assignment → Prop},
  Yulang.GeneralCanonicalObservationSquares.Adds start left one →
    Yulang.GeneralCanonicalObservationSquares.Adds start right two →
      Yulang.GeneralCanonicalObservationSquares.Adds left finalLeft two →
        Yulang.GeneralCanonicalObservationSquares.Adds right finalRight one →
          ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
            Yulang.GeneralNominalSaturationState.Models finalLeft model ↔
              Yulang.GeneralNominalSaturationState.Models finalRight model
@Yulang.GeneralCanonicalObservationSquares.square_observations : ∀ {roles : Yulang.Roles.RoleDecls}
  {start left right finalLeft finalRight : Yulang.GeneralNominalSaturationState.State roles}
  {one two : Yulang.GeneralNominalCommonBridge.Assignment → Prop},
  Yulang.GeneralCanonicalObservationSquares.Adds start left one →
    Yulang.GeneralCanonicalObservationSquares.Adds start right two →
      Yulang.GeneralCanonicalObservationSquares.Adds left finalLeft two →
        Yulang.GeneralCanonicalObservationSquares.Adds right finalRight one →
          Yulang.GeneralCanonicalObservations.BasisExtends finalLeft finalRight →
            Yulang.GeneralCanonicalObservations.BasisExtends finalRight finalLeft →
              Yulang.GeneralCanonicalObservations.canonical finalLeft =
                Yulang.GeneralCanonicalObservations.canonical finalRight
@Yulang.GeneralCanonicalObservationSquares.merge_merge_models : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles) (a b c d : Yulang.GeneralNominalDemandMerging.Site roles)
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models
      (Yulang.GeneralNominalSaturationState.merge (Yulang.GeneralNominalSaturationState.merge state a b) c d) model ↔
    Yulang.GeneralNominalSaturationState.Models
      (Yulang.GeneralNominalSaturationState.merge (Yulang.GeneralNominalSaturationState.merge state c d) a b) model
@Yulang.GeneralCanonicalObservationSquares.merge_merge_basis : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles) (a b c d : Yulang.GeneralNominalDemandMerging.Site roles),
  Yulang.GeneralCanonicalObservations.BasisExtends
    (Yulang.GeneralNominalSaturationState.merge (Yulang.GeneralNominalSaturationState.merge state a b) c d)
    (Yulang.GeneralNominalSaturationState.merge (Yulang.GeneralNominalSaturationState.merge state c d) a b)
@Yulang.GeneralCanonicalObservationSquares.merge_merge_observations : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles) (a b c d : Yulang.GeneralNominalDemandMerging.Site roles),
  Yulang.GeneralCanonicalObservations.canonical
      (Yulang.GeneralNominalSaturationState.merge (Yulang.GeneralNominalSaturationState.merge state a b) c d) =
    Yulang.GeneralCanonicalObservations.canonical
      (Yulang.GeneralNominalSaturationState.merge (Yulang.GeneralNominalSaturationState.merge state c d) a b)
@Yulang.GeneralCanonicalObservationSquares.refresh_observations : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles) (context : Yulang.GeneralNominalCandidates.Context)
  (certificate : Yulang.GeneralNominalFeedbackSteps.Refresh state context),
  Yulang.GeneralCanonicalObservations.canonical (Yulang.GeneralNominalSaturationState.regenerate state context) =
    Yulang.GeneralCanonicalObservations.canonical state
@Yulang.GeneralCanonicalObservationSquares.reobservation_reobservation : ∀ {roles : Yulang.Roles.RoleDecls}
  {start : Yulang.GeneralNominalSaturationState.State roles}
  (first last : Yulang.GeneralNominalReobservationSteps.Revision start),
  Yulang.GeneralNominalReobservationSteps.Certified first →
    Yulang.GeneralNominalReobservationSteps.Certified last →
      Yulang.GeneralCanonicalObservations.canonical first.result =
        Yulang.GeneralCanonicalObservations.canonical last.result
@Yulang.GeneralCanonicalObservationSquares.enqueue_merge_models : ∀ {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (first last : Yulang.GeneralNominalDemandMerging.Site roles) (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models
      (Yulang.GeneralNominalSaturationState.merge (Yulang.GeneralNominalSaturationState.enqueue state root) first last)
      model ↔
    Yulang.GeneralNominalSaturationState.Models
      (Yulang.GeneralNominalSaturationState.enqueue (Yulang.GeneralNominalSaturationState.merge state first last) root)
      model
@Yulang.GeneralCanonicalObservationSquares.reobservation_add_models : ∀ {roles : Yulang.Roles.RoleDecls}
  {start left right : Yulang.GeneralNominalSaturationState.State roles}
  (revision : Yulang.GeneralNominalReobservationSteps.Revision start),
  Yulang.GeneralNominalReobservationSteps.Certified revision →
    ∀ {condition : Yulang.GeneralNominalCommonBridge.Assignment → Prop},
      Yulang.GeneralCanonicalObservationSquares.Adds start left condition →
        Yulang.GeneralCanonicalObservationSquares.Adds revision.result right condition →
          ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
            Yulang.GeneralNominalSaturationState.Models left model ↔
              Yulang.GeneralNominalSaturationState.Models right model
Yulang.GeneralNominalReobservationExamples.revision_result : Yulang.GeneralNominalReobservationExamples.revision.result =
  Yulang.GeneralNominalRefreshFork.after false
Yulang.GeneralNominalReobservationExamples.revision_certified : Yulang.GeneralNominalReobservationSteps.Certified
  Yulang.GeneralNominalReobservationExamples.revision
Yulang.GeneralNominalReobservationExamples.point_closed : Yulang.GeneralNominalReobservationSteps.PointClosed
  (Yulang.GeneralNominalRefreshFork.state (some false))
Yulang.GeneralNominalReobservationExamples.revision_improves : Yulang.GeneralNominalReobservationSteps.Improves
  Yulang.GeneralNominalReobservationExamples.revision
Yulang.GeneralNominalReobservationExamples.repair_step : Yulang.GeneralNominalReobservationSteps.Step
  Yulang.GeneralNominalRefreshFork.registry Yulang.GeneralNominalRefreshFork.root
  (Yulang.GeneralNominalRefreshFork.after true) (Yulang.GeneralNominalRefreshFork.after false)
Yulang.GeneralNominalReobservationExamples.point_stable : Yulang.GeneralNominalReobservationSteps.Stable
  Yulang.GeneralNominalRefreshFork.registry (Yulang.GeneralNominalRefreshFork.after false)
  Yulang.GeneralNominalRefreshFork.root
Yulang.GeneralNominalReobservationExamples.point_halted : ∀
  (next : Yulang.GeneralNominalSaturationState.State Yulang.GeneralDeclarationExamples.roles),
  ¬Yulang.GeneralNominalReobservationSteps.Step Yulang.GeneralNominalRefreshFork.registry
      Yulang.GeneralNominalRefreshFork.root (Yulang.GeneralNominalRefreshFork.after false) next
Yulang.GeneralNominalReobservationExamples.wide_not_stable : ¬Yulang.GeneralNominalReobservationSteps.Stable
    Yulang.GeneralNominalRefreshFork.registry (Yulang.GeneralNominalRefreshFork.after true)
    Yulang.GeneralNominalRefreshFork.root
Yulang.GeneralNominalReobservationExamples.fork_extension : ∀ (wide : Bool),
  Yulang.B4Target.Steps
    (Yulang.GeneralNominalReobservationSteps.Step Yulang.GeneralNominalRefreshFork.registry
      Yulang.GeneralNominalRefreshFork.root)
    (Yulang.GeneralNominalRefreshFork.after wide) (Yulang.GeneralNominalRefreshFork.after false)
Yulang.GeneralNominalReobservationExamples.fork_join : ∀ (wide : Bool),
  Yulang.B4Target.Steps
      (Yulang.GeneralNominalReobservationSteps.Step Yulang.GeneralNominalRefreshFork.registry
        Yulang.GeneralNominalRefreshFork.root)
      Yulang.GeneralNominalRefreshFork.before (Yulang.GeneralNominalRefreshFork.after false) ∧
    Yulang.B4Target.Steps
        (Yulang.GeneralNominalReobservationSteps.Step Yulang.GeneralNominalRefreshFork.registry
          Yulang.GeneralNominalRefreshFork.root)
        (Yulang.GeneralNominalRefreshFork.after wide) (Yulang.GeneralNominalRefreshFork.after false) ∧
      Yulang.GeneralNominalReobservationSteps.Stable Yulang.GeneralNominalRefreshFork.registry
          (Yulang.GeneralNominalRefreshFork.after false) Yulang.GeneralNominalRefreshFork.root ∧
        ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
          Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralNominalRefreshFork.after wide) model ↔
            Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralNominalRefreshFork.after false) model
Yulang.GeneralNominalReobservationExamples.canonical_fork_equal : Yulang.GeneralCanonicalObservations.canonical
    (Yulang.GeneralNominalRefreshFork.after false) =
  Yulang.GeneralCanonicalObservations.canonical (Yulang.GeneralNominalRefreshFork.after true)
Yulang.GeneralNominalReobservationExamples.canonical_equality_does_not_fix_old_local : Yulang.GeneralCanonicalObservations.canonical
      (Yulang.GeneralNominalRefreshFork.after false) =
    Yulang.GeneralCanonicalObservations.canonical (Yulang.GeneralNominalRefreshFork.after true) ∧
  ¬∀ (d : (Yulang.GeneralNominalFeedbackBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles).Demand)
      (f :
        Yulang.CommonRoleOutermostResolver.Frontier
          (Yulang.GeneralNominalFeedbackBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles).Demand),
      Yulang.B4TargetV3.Local
          (Yulang.GeneralDictionaryFeedbackEvidence.boundary Yulang.GeneralDeclarationExamples.roles)
          Yulang.GeneralNominalRefreshFork.registry (Yulang.GeneralNominalRefreshFork.after false) d f ↔
        Yulang.B4TargetV3.Local
          (Yulang.GeneralDictionaryFeedbackEvidence.boundary Yulang.GeneralDeclarationExamples.roles)
          Yulang.GeneralNominalRefreshFork.registry (Yulang.GeneralNominalRefreshFork.after true) d f
Yulang.GeneralNominalReobservationExamples.point_observation_in_wide : Yulang.GeneralCanonicalObservations.canonical
  (Yulang.GeneralNominalRefreshFork.after true)
  (Yulang.GeneralCanonicalObservations.Observation.nominal Yulang.GeneralNominalRefreshFork.base 0
    (Yulang.GeneralNominalRefreshFork.descriptor (2, 2)))
Yulang.GeneralNominalReobservationExamples.wide_observation_in_wide : Yulang.GeneralCanonicalObservations.canonical
  (Yulang.GeneralNominalRefreshFork.after true)
  (Yulang.GeneralCanonicalObservations.Observation.nominal Yulang.GeneralNominalRefreshFork.base 0
    (Yulang.GeneralNominalRefreshFork.descriptor (2, 4)))
Yulang.GeneralNominalReobservationExamples.no_single_descriptor_contains_all : ¬∃ entries,
    ∀ (descriptor : Yulang.GeneralNominalState.Descriptor Yulang.GeneralNominalRefreshFork.base.slots),
      Yulang.GeneralCanonicalObservations.canonical (Yulang.GeneralNominalRefreshFork.after true)
          (Yulang.GeneralCanonicalObservations.Observation.nominal Yulang.GeneralNominalRefreshFork.base 0 descriptor) →
        entries 0 = some descriptor
Yulang.GeneralNominalReobservationExamples.repaired_diagnostic : (∀ (wide : Bool),
    Yulang.B4Target.Steps
      (Yulang.GeneralNominalReobservationSteps.Step Yulang.GeneralNominalRefreshFork.registry
        Yulang.GeneralNominalRefreshFork.root)
      (Yulang.GeneralNominalRefreshFork.after wide) (Yulang.GeneralNominalRefreshFork.after false)) ∧
  (∀ (next : Yulang.GeneralNominalSaturationState.State Yulang.GeneralDeclarationExamples.roles),
      ¬Yulang.GeneralNominalReobservationSteps.Step Yulang.GeneralNominalRefreshFork.registry
          Yulang.GeneralNominalRefreshFork.root (Yulang.GeneralNominalRefreshFork.after false) next) ∧
    Yulang.B4TargetV3.Local (Yulang.GeneralDictionaryFeedbackEvidence.boundary Yulang.GeneralDeclarationExamples.roles)
        Yulang.GeneralNominalRefreshFork.registry (Yulang.GeneralNominalRefreshFork.after false)
        Yulang.GeneralNominalRefreshFork.root (Yulang.CommonRoleOutermostResolver.Frontier.selected 90 []) ∧
      Yulang.CommonRoleOutermostResolver.Resolves
          (Yulang.B4TargetV3.Local
            (Yulang.GeneralDictionaryFeedbackEvidence.boundary Yulang.GeneralDeclarationExamples.roles)
            Yulang.GeneralNominalRefreshFork.registry (Yulang.GeneralNominalRefreshFork.after false))
          Yulang.GeneralNominalRefreshFork.root (Yulang.CommonRoleOutermostResolver.Tree.selected 90 []) ∧
        Yulang.B4TargetV3.SameDiagnostic
          (Yulang.GeneralDictionaryFeedbackEvidence.boundary Yulang.GeneralDeclarationExamples.roles)
          (Yulang.CommonRoleOutermostResolver.Tree.selected 90 [])
          (Yulang.CommonRoleOutermostResolver.Tree.selected 90 [])
Yulang.GeneralNominalReobservationBoundary.local_iff_old : ∀ (roles : Yulang.Roles.RoleDecls)
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (frontier : Yulang.CommonRoleOutermostResolver.Frontier (Yulang.GeneralSourceDictionaries.Occurrence roles)),
  Yulang.B4TargetV3.Local (Yulang.GeneralNominalReobservationBoundary.boundary roles).toSourceBoundary registry state
      root frontier ↔
    Yulang.B4TargetV3.Local (Yulang.GeneralDictionaryFeedbackEvidence.boundary roles) registry state root frontier
@Yulang.GeneralNominalReobservationBoundary.closure : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry),
  (Yulang.GeneralNominalReobservationBoundary.boundary roles).Checked registry →
    ∀ (state : Yulang.GeneralNominalSaturationState.State roles)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalReobservationBoundary.boundary roles) registry root state →
        (∀ (after : (Yulang.GeneralNominalReobservationBoundary.vocabulary roles).State),
            ¬(Yulang.GeneralNominalReobservationBoundary.boundary roles).Step registry root state after) →
          (Yulang.GeneralNominalReobservationBoundary.boundary roles).Stable registry state root ∧
            ∀ (child : (Yulang.GeneralNominalReobservationBoundary.vocabulary roles).Demand),
              (Yulang.GeneralNominalReobservationBoundary.boundary roles).Generated registry state root child →
                (Yulang.GeneralNominalReobservationBoundary.boundary roles).Stable registry state child
@Yulang.GeneralNominalReobservationBoundary.stepModels : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry),
  (Yulang.GeneralNominalReobservationBoundary.boundary roles).Checked registry →
    ∀ (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
      (before after : Yulang.GeneralNominalSaturationState.State roles),
      Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalReobservationBoundary.boundary roles) registry root before →
        (Yulang.GeneralNominalReobservationBoundary.boundary roles).Step registry root before after →
          ∀ (model : (Yulang.GeneralNominalReobservationBoundary.vocabulary roles).Model),
            (Yulang.GeneralNominalReobservationBoundary.boundary roles).Models after model →
              (Yulang.GeneralNominalReobservationBoundary.boundary roles).Models before model
@Yulang.GeneralNominalReobservationBoundary.frontierLocal : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry),
  (Yulang.GeneralNominalReobservationBoundary.boundary roles).Checked registry →
    ∀ (state : Yulang.GeneralNominalSaturationState.State roles)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalReobservationBoundary.boundary roles) registry root state →
        ∀ (d : Yulang.GeneralSourceDictionaries.Occurrence roles)
          (f : Yulang.CommonRoleOutermostResolver.Frontier (Yulang.GeneralSourceDictionaries.Occurrence roles)),
          (Yulang.GeneralNominalReobservationBoundary.frontiers roles registry state).frontier d = f ↔
            Yulang.B4TargetV3.Local (Yulang.GeneralNominalReobservationBoundary.boundary roles).toSourceBoundary
              registry state d f
@Yulang.GeneralNominalReobservationBoundary.localIdentity : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalReobservationBoundary.boundary roles) registry root state →
    (Yulang.GeneralNominalReobservationBoundary.frontiers roles registry state).Local =
      Yulang.B4TargetV3.Local (Yulang.GeneralNominalReobservationBoundary.boundary roles).toSourceBoundary registry
        state
@Yulang.GeneralNominalReobservationBoundary.dictionaryRefl : ∀ {roles : Yulang.Roles.RoleDecls}
  (dictionary : Yulang.CommonRoleOutermostResolver.Dictionary),
  (Yulang.GeneralNominalReobservationBoundary.boundary roles).DictionaryEquivalent dictionary dictionary
@Yulang.GeneralNominalReobservationBoundary.initialReorders : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry other : Yulang.GeneralDeclarations.Registry),
  (Yulang.GeneralNominalReobservationBoundary.boundary roles).Checked registry →
    (Yulang.GeneralNominalReobservationBoundary.boundary roles).Checked other →
      (Yulang.GeneralNominalReobservationBoundary.boundary roles).Reorders registry other →
        ∀ (state : Yulang.GeneralNominalSaturationState.State roles)
          (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
          (Yulang.GeneralNominalReobservationBoundary.boundary roles).Initial registry root state →
            (Yulang.GeneralNominalReobservationBoundary.boundary roles).Initial other root state
@Yulang.GeneralNominalReobservationBoundary.old_reachable : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
  Yulang.B4TargetV5.Reachable (Yulang.GeneralDictionaryReachableBoundary.boundary roles) registry root state →
    Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalReobservationBoundary.boundary roles) registry root state
Yulang.GeneralNominalReobservationExecutor.final_spec : ∀ (roles : Yulang.Roles.RoleDecls)
  (progress : Yulang.GeneralNominalReobservationExecutor.Progress roles)
  (registry : Yulang.GeneralDeclarations.Registry),
  (Yulang.GeneralNominalReobservationBoundary.boundary roles).Checked registry →
    ∀ (state : Yulang.GeneralNominalSaturationState.State roles)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalReobservationBoundary.boundary roles) registry root state →
        Yulang.B4Target.Steps ((Yulang.GeneralNominalReobservationBoundary.boundary roles).Step registry root) state
            (Yulang.GeneralNominalReobservationExecutor.finalState roles progress registry state root) ∧
          ∀ (next : (Yulang.GeneralNominalReobservationBoundary.vocabulary roles).State),
            ¬(Yulang.GeneralNominalReobservationBoundary.boundary roles).Step registry root
                (Yulang.GeneralNominalReobservationExecutor.finalState roles progress registry state root) next
Yulang.GeneralNominalReobservationExecutor.diagnostic_eq_resolve : ∀ (roles : Yulang.Roles.RoleDecls)
  (registry : Yulang.GeneralDeclarations.Registry) (state : Yulang.GeneralNominalSaturationState.State roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (exact :
    Yulang.CommonRoleOutermostResolver.FrontierExact
      (Yulang.GeneralNominalReobservationBoundary.frontiers roles registry state))
  (accessible :
    Acc
      (Yulang.CommonRoleOutermostResolver.Child
        (Yulang.GeneralNominalReobservationBoundary.frontiers roles registry state).Local)
      root),
  Yulang.GeneralNominalReobservationExecutor.diagnostic roles registry state root =
    Yulang.CommonRoleOutermostResolver.resolve
      (Yulang.GeneralNominalReobservationBoundary.frontiers roles registry state) exact root accessible
Yulang.GeneralNominalReobservationExecutor.execution : ∀ (roles : Yulang.Roles.RoleDecls)
  (progress : Yulang.GeneralNominalReobservationExecutor.Progress roles)
  (r : (Yulang.GeneralNominalReobservationBoundary.vocabulary roles).Registry),
  (Yulang.GeneralNominalReobservationBoundary.boundary roles).Checked r →
    ∀ (s : (Yulang.GeneralNominalReobservationBoundary.vocabulary roles).State)
      (d : (Yulang.GeneralNominalReobservationBoundary.vocabulary roles).Demand),
      Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalReobservationBoundary.boundary roles) r d s →
        Yulang.B4Target.Steps ((Yulang.GeneralNominalReobservationBoundary.boundary roles).Step r d) s
          ((Yulang.GeneralNominalReobservationExecutor.executor roles progress).run r s d).fst
Yulang.GeneralNominalReobservationExecutor.halted : ∀ (roles : Yulang.Roles.RoleDecls)
  (progress : Yulang.GeneralNominalReobservationExecutor.Progress roles)
  (r : (Yulang.GeneralNominalReobservationBoundary.vocabulary roles).Registry),
  (Yulang.GeneralNominalReobservationBoundary.boundary roles).Checked r →
    ∀ (s : (Yulang.GeneralNominalReobservationBoundary.vocabulary roles).State)
      (d : (Yulang.GeneralNominalReobservationBoundary.vocabulary roles).Demand),
      Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalReobservationBoundary.boundary roles) r d s →
        ∀ (next : (Yulang.GeneralNominalReobservationBoundary.vocabulary roles).State),
          ¬(Yulang.GeneralNominalReobservationBoundary.boundary roles).Step r d
              ((Yulang.GeneralNominalReobservationExecutor.executor roles progress).run r s d).fst next
Yulang.GeneralNominalReobservationExecutor.treeExecution : ∀ (roles : Yulang.Roles.RoleDecls)
  (progress : Yulang.GeneralNominalReobservationExecutor.Progress roles)
  (r : (Yulang.GeneralNominalReobservationBoundary.vocabulary roles).Registry),
  (Yulang.GeneralNominalReobservationBoundary.boundary roles).Checked r →
    ∀ (s : (Yulang.GeneralNominalReobservationBoundary.vocabulary roles).State)
      (d : (Yulang.GeneralNominalReobservationBoundary.vocabulary roles).Demand),
      Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalReobservationBoundary.boundary roles) r d s →
        ∀
          (exact :
            Yulang.CommonRoleOutermostResolver.FrontierExact
              (Yulang.GeneralNominalReobservationBoundary.frontiers roles r
                ((Yulang.GeneralNominalReobservationExecutor.executor roles progress).run r s d).fst))
          (accessible :
            Acc
              (Yulang.CommonRoleOutermostResolver.Child
                (Yulang.GeneralNominalReobservationBoundary.frontiers roles r
                    ((Yulang.GeneralNominalReobservationExecutor.executor roles progress).run r s d).fst).Local)
              d),
          ((Yulang.GeneralNominalReobservationExecutor.executor roles progress).run r s d).snd =
            Yulang.CommonRoleOutermostResolver.resolve
              (Yulang.GeneralNominalReobservationBoundary.frontiers roles r
                ((Yulang.GeneralNominalReobservationExecutor.executor roles progress).run r s d).fst)
              exact d accessible
Yulang.GeneralNominalReobservationExecutor.final_reachable : ∀ (roles : Yulang.Roles.RoleDecls)
  (progress : Yulang.GeneralNominalReobservationExecutor.Progress roles)
  (registry : Yulang.GeneralDeclarations.Registry),
  (Yulang.GeneralNominalReobservationBoundary.boundary roles).Checked registry →
    ∀ (state : Yulang.GeneralNominalSaturationState.State roles)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalReobservationBoundary.boundary roles) registry root state →
        Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalReobservationBoundary.boundary roles) registry root
          ((Yulang.GeneralNominalReobservationExecutor.executor roles progress).run registry state root).fst
Yulang.GeneralNominalReobservationExecutor.final_stable : ∀ (roles : Yulang.Roles.RoleDecls)
  (progress : Yulang.GeneralNominalReobservationExecutor.Progress roles)
  (registry : Yulang.GeneralDeclarations.Registry),
  (Yulang.GeneralNominalReobservationBoundary.boundary roles).Checked registry →
    ∀ (state : Yulang.GeneralNominalSaturationState.State roles)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalReobservationBoundary.boundary roles) registry root state →
        (Yulang.GeneralNominalReobservationBoundary.boundary roles).Stable registry
            ((Yulang.GeneralNominalReobservationExecutor.executor roles progress).run registry state root).fst root ∧
          ∀ (child : (Yulang.GeneralNominalReobservationBoundary.vocabulary roles).Demand),
            (Yulang.GeneralNominalReobservationBoundary.boundary roles).Generated registry
                ((Yulang.GeneralNominalReobservationExecutor.executor roles progress).run registry state root).fst root
                child →
              (Yulang.GeneralNominalReobservationBoundary.boundary roles).Stable registry
                ((Yulang.GeneralNominalReobservationExecutor.executor roles progress).run registry state root).fst child
Yulang.GeneralNominalReobservationExecutor.final_models : ∀ (roles : Yulang.Roles.RoleDecls)
  (progress : Yulang.GeneralNominalReobservationExecutor.Progress roles)
  (registry : Yulang.GeneralDeclarations.Registry),
  (Yulang.GeneralNominalReobservationBoundary.boundary roles).Checked registry →
    ∀ (state : Yulang.GeneralNominalSaturationState.State roles)
      (root : Yulang.GeneralSourceDictionaries.Occurrence roles),
      Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalReobservationBoundary.boundary roles) registry root state →
        ∀ (model : (Yulang.GeneralNominalReobservationBoundary.vocabulary roles).Model),
          (Yulang.GeneralNominalReobservationBoundary.boundary roles).Models
              ((Yulang.GeneralNominalReobservationExecutor.executor roles progress).run registry state root).fst model →
            (Yulang.GeneralNominalReobservationBoundary.boundary roles).Models state model
Yulang.GeneralNominalReobservationExecutor.saturationTotal : ∀ (roles : Yulang.Roles.RoleDecls)
  (progress : Yulang.GeneralNominalReobservationExecutor.Progress roles),
  Yulang.B4TargetV5.SaturationTotal (Yulang.GeneralNominalReobservationBoundary.boundary roles)
    (Yulang.GeneralNominalReobservationExecutor.executor roles progress)
Yulang.GeneralNominalReobservationObligations.bridges : ∀ (roles : Yulang.Roles.RoleDecls)
  (progress : Yulang.GeneralNominalReobservationExecutor.Progress roles),
  Yulang.GeneralNominalReobservationObligations.Remaining roles progress →
    Yulang.B4SkeletonV5.B4Bridges (Yulang.GeneralNominalReobservationBoundary.boundary roles)
      (Yulang.GeneralNominalReobservationExecutor.executor roles progress)
      (Yulang.GeneralNominalReobservationBoundary.frontiers roles)
Yulang.GeneralNominalReobservationObligations.canonicalLocalOrder_of_halted_order : ∀ (roles : Yulang.Roles.RoleDecls)
  (progress : Yulang.GeneralNominalReobservationExecutor.Progress roles),
  Yulang.GeneralNominalReobservationObligations.HaltedLocalOrder roles →
    ∀ (r r' : (Yulang.GeneralNominalReobservationBoundary.vocabulary roles).Registry),
      (Yulang.GeneralNominalReobservationBoundary.boundary roles).Checked r →
        (Yulang.GeneralNominalReobservationBoundary.boundary roles).Checked r' →
          (Yulang.GeneralNominalReobservationBoundary.boundary roles).Reorders r r' →
            ∀ (s : (Yulang.GeneralNominalReobservationBoundary.vocabulary roles).State)
              (root : (Yulang.GeneralNominalReobservationBoundary.vocabulary roles).Demand),
              Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalReobservationBoundary.boundary roles) r root s →
                Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalReobservationBoundary.boundary roles) r' root s →
                  ∀ (d : (Yulang.GeneralNominalReobservationBoundary.vocabulary roles).Demand)
                    (f :
                      Yulang.CommonRoleOutermostResolver.Frontier
                        (Yulang.GeneralNominalReobservationBoundary.vocabulary roles).Demand),
                    Yulang.B4TargetV3.Local (Yulang.GeneralNominalReobservationBoundary.boundary roles).toSourceBoundary
                        r ((Yulang.GeneralNominalReobservationExecutor.executor roles progress).run r s root).fst d f ↔
                      Yulang.B4TargetV3.Local
                        (Yulang.GeneralNominalReobservationBoundary.boundary roles).toSourceBoundary r'
                        ((Yulang.GeneralNominalReobservationExecutor.executor roles progress).run r' s root).fst d f
Yulang.GeneralNominalReobservationBoundaryExamples.point_local : Yulang.B4TargetV3.Local
  (Yulang.GeneralNominalReobservationBoundary.boundary Yulang.GeneralDeclarationExamples.roles).toSourceBoundary
  Yulang.GeneralNominalRefreshFork.registry (Yulang.GeneralNominalRefreshFork.after false)
  Yulang.GeneralNominalRefreshFork.root (Yulang.CommonRoleOutermostResolver.Frontier.selected 90 [])
Yulang.GeneralNominalReobservationBoundaryExamples.point_tree : Yulang.CommonRoleOutermostResolver.Resolves
  (Yulang.B4TargetV3.Local
    (Yulang.GeneralNominalReobservationBoundary.boundary Yulang.GeneralDeclarationExamples.roles).toSourceBoundary
    Yulang.GeneralNominalRefreshFork.registry (Yulang.GeneralNominalRefreshFork.after false))
  Yulang.GeneralNominalRefreshFork.root (Yulang.CommonRoleOutermostResolver.Tree.selected 90 [])
Yulang.GeneralNominalReobservationBoundaryExamples.same_diagnostic : Yulang.B4TargetV3.SameDiagnostic
  (Yulang.GeneralNominalReobservationBoundary.boundary Yulang.GeneralDeclarationExamples.roles).toSourceBoundary
  (Yulang.CommonRoleOutermostResolver.Tree.selected 90 []) (Yulang.CommonRoleOutermostResolver.Tree.selected 90 [])
Yulang.GeneralNominalReobservationBoundaryExamples.reachable_point : Yulang.B4TargetV5.Reachable
  (Yulang.GeneralNominalReobservationBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
  Yulang.GeneralNominalRefreshFork.registry Yulang.GeneralNominalRefreshFork.root
  (Yulang.GeneralNominalRefreshFork.after false)
Yulang.GeneralNominalReobservationBoundaryExamples.repaired_fork : (Yulang.GeneralNominalReobservationBoundary.boundary
        Yulang.GeneralDeclarationExamples.roles).Checked
    Yulang.GeneralNominalRefreshFork.registry ∧
  (Yulang.GeneralNominalReobservationBoundary.boundary Yulang.GeneralDeclarationExamples.roles).Initial
      Yulang.GeneralNominalRefreshFork.registry Yulang.GeneralNominalRefreshFork.root
      Yulang.GeneralNominalRefreshFork.before ∧
    (∀ (wide : Bool),
        (Yulang.GeneralNominalReobservationBoundary.boundary Yulang.GeneralDeclarationExamples.roles).Step
          Yulang.GeneralNominalRefreshFork.registry Yulang.GeneralNominalRefreshFork.root
          Yulang.GeneralNominalRefreshFork.before (Yulang.GeneralNominalRefreshFork.after wide)) ∧
      (∀ (wide : Bool),
          Yulang.B4Target.Steps
            ((Yulang.GeneralNominalReobservationBoundary.boundary Yulang.GeneralDeclarationExamples.roles).Step
              Yulang.GeneralNominalRefreshFork.registry Yulang.GeneralNominalRefreshFork.root)
            (Yulang.GeneralNominalRefreshFork.after wide) (Yulang.GeneralNominalRefreshFork.after false)) ∧
        (∀
            (next :
              (Yulang.GeneralNominalReobservationBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles).State),
            ¬(Yulang.GeneralNominalReobservationBoundary.boundary Yulang.GeneralDeclarationExamples.roles).Step
                Yulang.GeneralNominalRefreshFork.registry Yulang.GeneralNominalRefreshFork.root
                (Yulang.GeneralNominalRefreshFork.after false) next) ∧
          (Yulang.GeneralNominalReobservationBoundary.boundary Yulang.GeneralDeclarationExamples.roles).Stable
              Yulang.GeneralNominalRefreshFork.registry (Yulang.GeneralNominalRefreshFork.after false)
              Yulang.GeneralNominalRefreshFork.root ∧
            (∀ (wide : Bool)
                (model :
                  (Yulang.GeneralNominalReobservationBoundary.vocabulary
                      Yulang.GeneralDeclarationExamples.roles).Model),
                (Yulang.GeneralNominalReobservationBoundary.boundary Yulang.GeneralDeclarationExamples.roles).Models
                    (Yulang.GeneralNominalRefreshFork.after wide) model ↔
                  (Yulang.GeneralNominalReobservationBoundary.boundary Yulang.GeneralDeclarationExamples.roles).Models
                    (Yulang.GeneralNominalRefreshFork.after false) model) ∧
              Yulang.B4TargetV3.Local
                  (Yulang.GeneralNominalReobservationBoundary.boundary
                      Yulang.GeneralDeclarationExamples.roles).toSourceBoundary
                  Yulang.GeneralNominalRefreshFork.registry (Yulang.GeneralNominalRefreshFork.after false)
                  Yulang.GeneralNominalRefreshFork.root (Yulang.CommonRoleOutermostResolver.Frontier.selected 90 []) ∧
                Yulang.CommonRoleOutermostResolver.Resolves
                    (Yulang.B4TargetV3.Local
                      (Yulang.GeneralNominalReobservationBoundary.boundary
                          Yulang.GeneralDeclarationExamples.roles).toSourceBoundary
                      Yulang.GeneralNominalRefreshFork.registry (Yulang.GeneralNominalRefreshFork.after false))
                    Yulang.GeneralNominalRefreshFork.root (Yulang.CommonRoleOutermostResolver.Tree.selected 90 []) ∧
                  Yulang.B4TargetV3.SameDiagnostic
                    (Yulang.GeneralNominalReobservationBoundary.boundary
                        Yulang.GeneralDeclarationExamples.roles).toSourceBoundary
                    (Yulang.CommonRoleOutermostResolver.Tree.selected 90 [])
                    (Yulang.CommonRoleOutermostResolver.Tree.selected 90 [])
```

## Item 5d — same-model completion obstruction and an actual merge/reobservation diamond (2026-11-12)

**Status: the requested same-model full-Stable completion is false for the
existing descriptor-replacement relation.** This is proved on the actual checked,
source-reachable carriers. General maximal-view inspection and all transition
confluence are not claimed complete. The task contract clarification is pending:
observation completion can preserve models, while full stabilization must be
allowed to decrease them, as the existing B4 V5 clause (1) already permits.
Progress/descent and the R-growth owner question remain paused.

### Why the completion requirements separate

Spec §6.3 states that the selected implementation's associated definition is
substituted into the fresh output variable. It also requires waiting for known
inputs and finalizing only after sibling updates stabilize. The draft/addenda
make all unnamed inputs needed; the named output is not an applicability input.
Thus an unresolved output cannot prevent a known, uniquely matching implementation
from supplying its output equation. `B4TargetV5.SaturationTotal` requires final
Models to imply initial Models, not equivalence of those predicates.

A schematic Yulang instance of the checked declaration used here is:

```yulang
impl Container (list (list int)):
    type item = int
```

The demand is `Container(list (list int), item = 'out)`, with `'out` initially
unconstrained. The test uses the general declaration carrier, its real checker,
the existing nominal list constructor, normalized state, explicit source
identities, materialization schema, candidate predicates, and feedback Step.
There is no scalar-only substitute boundary or ad-hoc Local judgment.

| Source identity | Information in both pre-install snapshots |
| --- | --- |
| 0 | `list (list int)`, also constrained equal to source 1 |
| 1 | `list (list int)` |
| 2 | `list int` |
| 3 | `int` |
| 4 | top |
| 5 | the unconstrained requested associated output; reserved and linked |

The wide snapshot records source 0's nominal parameter interval as `(2,4)`;
the precise snapshot records `(2,2)`. Both have exactly the same full journal
models. The old wide state is genuinely halted: nested inspection is blocked,
top cannot acquire a certified head, and source 5 has both int and str model
witnesses, preventing a certified head there. There are no other generated
sites, uncommitted packets, or nontrivial merges. It is reached by an actual old
refresh from an empty-journal `InitialSource` state.

The descriptor repair preserves all models, but precise inspection selects key
90 with no children and a materialized `source 5 ≈ int` obligation. The packet
is actually Installable, including the full joint and merge guards. Installation
therefore keeps the int-output model and excludes the str-output model.
`installed_models_exact` proves the stronger exact statement, for every assignment:

```text
Models installed assignment ↔
  Models oldWide assignment ∧ Equivalent (assignment 5).1 (.base .int)
```

This is an information-adding installation required by the selected declaration,
not an order-dependent language choice or a loss caused by normalization.

### The obstruction covers every current transition path

The primary strengthened the concrete example into an all-path theorem:

- `point_descriptor_forced`: with this catalogue and explicit source model, a
  point descriptor at slots 0/1 must be `list(2,2)`, and at slot 2 must be
  `list(3,3)`. The nominal invariant theorem determines the constructor name,
  layout, and argument; distinct source values determine the endpoints.
- `revision_result_forced`: every certified improving Revision of the wide
  snapshot is exactly the precise snapshot. The Revision carrier fixes the
  base and nominal presence domain; slots 1 and 2 are already point-valued,
  so its strict new point must be at slot 0.
- `step_from_wide`: every full new Step from the wide state reaches the precise
  state, because old stability excludes every ordinary update.
- `step_from_point_excludes_bad`: every full new Step from the precise state
  excludes the str-output model. Point closure excludes more descriptor
  replacements; old refresh/enqueue/merge/equality guards exclude the other
  administrative updates; every remaining installation is the same visible
  declaration with the same root and bounds, hence forces the int output.
- `trace_trichotomy`: after **any** finite full new-Step trace from the wide
  state, the final state is wide, precise, or has lost the str-output model.
- `stable_trace_loses_bad`: the first two states are not new-Stable, so every
  stable continuation has lost that model.
- `no_same_models_stable_extension`: there is no stable continuation with the
  same models.
- `not_old_halted_same_models_completion`: the universal claim over checked
  registries and old-reachable, old-halted states is false for the existing
  `GeneralNominalReobservationSteps.Step`.
- `boundary_completion_obstruction`: the same concrete witness uses the public
  `GeneralNominalReobservationBoundary.boundary roles` Step, Stable, Models,
  and Reachable. Its old-halted premise intentionally names the old feedback Step.

These theorems do not merely exhibit one unsuccessful schedule. They also do
not assert failure of every hypothetical future canonical-view relation, refute
cache-only completion, or construct a stable final state after the installation.
The existing Step's entire trace relation is the quantified relation. The separate
`canonical_views_equal` theorem shows that the wide and precise pre-install
snapshots have the same maximal semantic predicate.

A minimal faithful restatement is already available conditionally:
`model_decreasing_completion_of_progress` gives an actual stable continuation
and final-model inclusion for every checked reachable state of the current
boundary, from precisely its Progress field. This is a reuse of the existing
executor laws, not a proof of Progress, a maximal-view consumer, or a new V5 field.
The stronger equality requirement has not been silently replaced.

### A genuine transition diamond, independent of that clarification

`GeneralNominalReobservationMergeDiamond.merge_reobserve_diamond` constructs the
following square for arbitrary general states, sites, and certified improving
revisions:

```text
state ──merge──▶ merge state first last
  │                     │
revision          lifted revision
  │                     │
  ▼                     ▼
revision.result ──merge──▶ merge revision.result first last
```

All four arrows are the actual public Step, including Generated restrictions.
Only the original merge guards and revision certificate/improvement are premises.
Neither second transition is assumed. The final states are literally identical.

The proof supplies the missing preservation facts for this pair:

- Full model equivalence preserves recovered origins and same-input recognition.
- Reobservation leaves sites/aliases unchanged, so merge membership and novelty
  survive. Generated membership follows from the proved actual-Step law.
- A Revision lifts over the merge's ordinary associated-output equations.
  Its raw-model preservation and exact full-model equivalence follow from the
  original certificate and the exact `merge_models` characterization.
- Nominal presence and point improvement are unchanged by that lift.

This closes **merge/this certified descriptor replacement**, not
install/install, install/merge, install/canonical-refresh, arbitrary
refresh/refresh, or full maximal-view consumption. The old model-only commuting
squares have not been promoted to transition diamonds. No application of
Newman's lemma or final-state agreement is claimed. No genuine semantic
update-order divergence was established, so no owner language question was
invented from these implementation gaps.

### V5 14-field table

The current concrete boundary remains
`GeneralNominalReobservationBoundary.boundary roles`, with
`GeneralNominalReobservationExecutor.executor roles progress`.
No existing definition was changed and no completed maximal-view boundary is
claimed.

| V5 field | Status |
| --- | --- |
| `progress` | OPEN/PAUSED; exact current `Progress roles`, not supplied or proved here. |
| `execution` | Previously proved conditional only on that Progress. |
| `halted` | Previously proved conditional only on that Progress. |
| `closure` | PROVED, unchanged `GeneralNominalReobservationBoundary.closure`. |
| `stepModels` | PROVED, unchanged `GeneralNominalReobservationBoundary.stepModels`; model decrease is the correct saturation direction. |
| `frontierLocal` | PROVED, unchanged `GeneralNominalReobservationBoundary.frontierLocal`. |
| `localIdentity` | PROVED, unchanged `GeneralNominalReobservationBoundary.localIdentity`. |
| `whereAccessible` | OPEN; no descent work resumed. |
| `treeExecution` | Previously proved conditional on Progress with the target's explicit frontier-exactness and child-accessibility binders. |
| `canonicalLocalOrder` | OPEN; the one new diamond does not supply all local confluence or the canonical consumer. |
| `dictionaryRefl` | PROVED, unchanged `GeneralNominalReobservationBoundary.dictionaryRefl`. |
| `evidenceNode` | OPEN in the current bridge package. |
| `generatedChildren` | OPEN in the current bridge package. |
| `initialReorders` | PROVED, unchanged `GeneralNominalReobservationBoundary.initialReorders`. |

Count unchanged: **6/14 unconditional; 3 additional execution fields conditional
on Progress; Progress itself and 4 other fields remain open.** The universal
same-model completion request is an additional requested property, not one of
those 14 fields, and is now refuted for this relation. None of the obstruction
or diamond lemmas is counted as an extra bridge field.

### Review, files, and checks

The four new implementation modules are listed in the
[small module guide](2026-11-12-astra-canonical-completion-module-guide.md).
The only existing Lean change is four appended imports in `lean/Yulang.lean`.
`lean/Audit/AstraCanonicalCompletion.lean` is a new audit part. Frozen
`lean/Audit.lean` and `lean/README.md`, spec, plan, configs, and git refs are unchanged.

The yulang-proofs workflow was used. The registered `prover` role/configuration
and the skill's three referenced rule files were unavailable; no prover agent
ran. A complementary reviewer constructed only the two leased counterexample
support modules, which the primary independently reviewed. The primary proved
the all-trace obstruction and the merge/reobservation diamond. A fresh independent
review covered all four modules, including quantifiers, actual source reachability,
model witnesses, the distinction between the current and hypothetical relations,
and the absence of a second-edge premise in the diamond. No blocking issue remained.

Final verification, from `lean/`:

- `lake build Yulang.GeneralNominalCanonicalCompletionObstruction Yulang.GeneralNominalReobservationMergeDiamond` — exit **0**.
- `lake build Yulang` — exit **0**.
- `lake env lean Audit/AstraCanonicalCompletion.lean` — exit **0**. All **72** new public theorems are covered; dependencies are confined to `propext`, `Classical.choice`, and `Quot.sound` (or none).

The frozen umbrella audit and all historical audit parts were not rerun. No
claim is made for general canonical inspection, all transition diamonds,
Newman/final-state agreement, or `canonicalLocalOrder` from Progress alone.
This work is on the real general carriers and closes a concrete contract error
and one actual transition pair; it does not complete Item 5c as originally phrased.

### Full new public theorem statements

These are Lean's elaborated `#check @...` statements, with implicit premises
exposed. The implementation modules contain the definitions and proofs.

```lean
Yulang.GeneralNominalCanonicalOutputFork.declaration_checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDeclarationExamples.roles
  Yulang.GeneralNominalCanonicalOutputFork.declaration
Yulang.GeneralNominalCanonicalOutputFork.registry_checked : Yulang.GeneralDeclarations.Checked
  Yulang.GeneralNominalCanonicalOutputFork.registry
Yulang.GeneralNominalCanonicalOutputFork.state_models : ∀ (choice : Option Bool)
  (m : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models (Yulang.GeneralNominalCanonicalOutputFork.state choice) m ↔
    Yulang.GeneralNominalState.Models (Yulang.GeneralNominalRefreshFork.state choice) m
Yulang.GeneralNominalCanonicalOutputFork.zero_known : ∀ (wide : Bool),
  Yulang.GeneralNominalState.Known (Yulang.GeneralNominalCanonicalOutputFork.state (some wide)) 0
Yulang.GeneralNominalCanonicalOutputFork.refresh_step : ∀ (wide : Bool),
  Yulang.GeneralNominalFeedbackSteps.Step Yulang.GeneralNominalCanonicalOutputFork.registry
    Yulang.GeneralNominalCanonicalOutputFork.root Yulang.GeneralNominalCanonicalOutputFork.before
    (Yulang.GeneralNominalCanonicalOutputFork.after wide)
Yulang.GeneralNominalCanonicalOutputFork.same_models : ∀ (wide : Bool)
  (m : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralNominalCanonicalOutputFork.after wide) m ↔
    Yulang.GeneralNominalSaturationState.Models Yulang.GeneralNominalCanonicalOutputFork.before m
Yulang.GeneralNominalCanonicalOutputFork.initial_models : ∀ (scalar : Yulang.Inference.Base),
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralNominalCanonicalOutputFork.before
    (Yulang.GeneralNominalCanonicalOutputFork.model scalar)
Yulang.GeneralNominalCanonicalOutputFork.after_models : ∀ (wide : Bool) (scalar : Yulang.Inference.Base),
  Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralNominalCanonicalOutputFork.after wide)
    (Yulang.GeneralNominalCanonicalOutputFork.model scalar)
Yulang.GeneralNominalCanonicalOutputFork.source_bound : ∀ (choice : Option Bool) (source : Nat),
  source ∈ Yulang.GeneralNominalState.sources (Yulang.GeneralNominalCanonicalOutputFork.state choice) → source ≤ 5
Yulang.GeneralNominalCanonicalOutputFork.linked : ∀ (choice : Option Bool),
  Yulang.GeneralNominalState.Linked (Yulang.GeneralNominalCanonicalOutputFork.state choice)
    Yulang.GeneralNominalCanonicalOutputFork.root.demand
Yulang.GeneralNominalCanonicalOutputFork.metadata : ∀ (choice : Option Bool),
  Yulang.GeneralNominalRecursiveCandidates.Metadata Yulang.GeneralNominalCanonicalOutputFork.registry
    (Yulang.GeneralNominalCanonicalOutputFork.context choice)
Yulang.GeneralNominalCanonicalOutputFork.initial_source : Yulang.GeneralNominalSourceFormation.InitialSource
  Yulang.GeneralNominalCanonicalOutputFork.registry (Yulang.GeneralNominalCanonicalOutputFork.context none)
  Yulang.GeneralNominalCanonicalOutputFork.root
Yulang.GeneralNominalCanonicalOutputFork.initial_reachable : Yulang.B4TargetV5.Reachable
  (Yulang.GeneralDictionaryReachableBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
  Yulang.GeneralNominalCanonicalOutputFork.registry Yulang.GeneralNominalCanonicalOutputFork.root
  Yulang.GeneralNominalCanonicalOutputFork.before
Yulang.GeneralNominalCanonicalOutputFork.after_reachable : ∀ (wide : Bool),
  Yulang.B4TargetV5.Reachable
    (Yulang.GeneralDictionaryReachableBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralNominalCanonicalOutputFork.registry Yulang.GeneralNominalCanonicalOutputFork.root
    (Yulang.GeneralNominalCanonicalOutputFork.after wide)
Yulang.GeneralNominalCanonicalOutputFork.no_refresh : ∀ (wide : Bool) (next : Yulang.GeneralNominalCandidates.Context)
  (certified : Yulang.GeneralNominalFeedbackSteps.Refresh (Yulang.GeneralNominalCanonicalOutputFork.after wide) next)
  (source : Nat),
  source ∈ Yulang.GeneralNominalState.sources (Yulang.GeneralNominalCanonicalOutputFork.state (some wide)) →
    ¬Yulang.GeneralNominalState.Known (Yulang.GeneralNominalCanonicalOutputFork.state (some wide)) source →
      ¬Yulang.GeneralNominalState.Known next.state source
Yulang.GeneralNominalCanonicalOutputFork.revision_result : Yulang.GeneralNominalCanonicalOutputFork.revision.result =
  Yulang.GeneralNominalCanonicalOutputFork.after false
Yulang.GeneralNominalCanonicalOutputFork.revision_certified : Yulang.GeneralNominalReobservationSteps.Certified
  Yulang.GeneralNominalCanonicalOutputFork.revision
Yulang.GeneralNominalCanonicalOutputFork.revision_improves : Yulang.GeneralNominalReobservationSteps.Improves
  Yulang.GeneralNominalCanonicalOutputFork.revision
Yulang.GeneralNominalCanonicalOutputFork.repair_step : Yulang.GeneralNominalReobservationSteps.Step
  Yulang.GeneralNominalCanonicalOutputFork.registry Yulang.GeneralNominalCanonicalOutputFork.root
  (Yulang.GeneralNominalCanonicalOutputFork.after true) (Yulang.GeneralNominalCanonicalOutputFork.after false)
Yulang.GeneralNominalCanonicalOutputForkClassification.point_report : Yulang.GeneralNominalRecursiveCandidates.report
    (Yulang.GeneralNominalCanonicalOutputFork.context (some false)) Yulang.GeneralNominalCanonicalOutputFork.declaration
    [(0, 0)] =
  Yulang.GeneralNominalCanonicalOutputForkClassification.calculated
Yulang.GeneralNominalCanonicalOutputForkClassification.wide_blocked : (Yulang.GeneralNominalRecursiveCandidates.report
      (Yulang.GeneralNominalCanonicalOutputFork.context (some true))
      Yulang.GeneralNominalCanonicalOutputFork.declaration [(0, 0)]).blocked =
  [(2, 4)]
Yulang.GeneralNominalCanonicalOutputForkClassification.located : ∀ (choice : Option Bool),
  Yulang.GeneralNominalRecursiveCandidates.arguments (Yulang.GeneralNominalCanonicalOutputFork.context choice)
      Yulang.GeneralNominalCanonicalOutputFork.root =
    some [(0, 0)]
Yulang.GeneralNominalCanonicalOutputForkClassification.children_empty : ∀ (choice : Option Bool)
  (checked :
    Yulang.GeneralDeclarations.DeclarationChecked Yulang.GeneralNominalCanonicalOutputFork.registry.constructors
      Yulang.GeneralDeclarationExamples.roles Yulang.GeneralNominalCanonicalOutputFork.declaration)
  (bindings : Yulang.GeneralNominalAllocation.Bindings),
  Yulang.GeneralNominalAllocation.children (Yulang.GeneralNominalCanonicalOutputFork.state choice)
      Yulang.GeneralNominalCanonicalOutputFork.registry Yulang.GeneralNominalCanonicalOutputFork.root
      Yulang.GeneralNominalCanonicalOutputFork.declaration checked bindings =
    []
Yulang.GeneralNominalCanonicalOutputForkClassification.schema_calculated : ∀ (choice : Option Bool)
  (checked :
    Yulang.GeneralDeclarations.DeclarationChecked Yulang.GeneralNominalCanonicalOutputFork.registry.constructors
      Yulang.GeneralDeclarationExamples.roles Yulang.GeneralNominalCanonicalOutputFork.declaration),
  Yulang.GeneralNominalRecursiveCandidates.generated Yulang.GeneralNominalCanonicalOutputFork.registry
      (Yulang.GeneralNominalCanonicalOutputFork.context choice) Yulang.GeneralNominalCanonicalOutputFork.root
      Yulang.GeneralNominalCanonicalOutputFork.declaration checked [(0, 0)] =
    {
      tests :=
        [(Yulang.GeneralNominalRecursiveInspection.Origin.source 5,
            Yulang.GeneralNominalRecursiveInspection.Test.scalar Yulang.Inference.Base.int)] }
Yulang.GeneralNominalCanonicalOutputForkClassification.point_projections : ∀
  (m : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models (Yulang.GeneralNominalCanonicalOutputFork.state (some false)) m →
    Yulang.GeneralNominalRecursiveInspection.ProjectionModels
      (Yulang.GeneralNominalCanonicalOutputFork.state (some false))
      Yulang.GeneralNominalCanonicalOutputForkClassification.calculated m
Yulang.GeneralNominalCanonicalOutputForkClassification.point_branch : ∀
  (checked :
    Yulang.GeneralDeclarations.DeclarationChecked Yulang.GeneralNominalCanonicalOutputFork.registry.constructors
      Yulang.GeneralDeclarationExamples.roles Yulang.GeneralNominalCanonicalOutputFork.declaration)
  (m : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalState.Models (Yulang.GeneralNominalCanonicalOutputFork.state (some false)) m →
    Yulang.CommonNominalFullCarrier.Equivalent (m 5).fst
        (Yulang.CommonNominalSyntax.Layer.base Yulang.Inference.Base.int) →
      Yulang.GeneralNominalRecursiveCandidates.BranchModels Yulang.GeneralNominalCanonicalOutputFork.registry
        (Yulang.GeneralNominalCanonicalOutputFork.context (some false)) Yulang.GeneralNominalCanonicalOutputFork.root
        Yulang.GeneralNominalCanonicalOutputFork.declaration checked [(0, 0)] m
Yulang.GeneralNominalCanonicalOutputForkClassification.branch_output : ∀
  (checked :
    Yulang.GeneralDeclarations.DeclarationChecked Yulang.GeneralNominalCanonicalOutputFork.registry.constructors
      Yulang.GeneralDeclarationExamples.roles Yulang.GeneralNominalCanonicalOutputFork.declaration)
  (m : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalRecursiveCandidates.BranchModels Yulang.GeneralNominalCanonicalOutputFork.registry
      (Yulang.GeneralNominalCanonicalOutputFork.context (some false)) Yulang.GeneralNominalCanonicalOutputFork.root
      Yulang.GeneralNominalCanonicalOutputFork.declaration checked [(0, 0)] m →
    Yulang.CommonNominalFullCarrier.Equivalent (m 5).fst
      (Yulang.CommonNominalSyntax.Layer.base Yulang.Inference.Base.int)
Yulang.GeneralNominalCanonicalOutputForkClassification.fresh : ∀ (choice : Option Bool),
  Yulang.GeneralNominalAllocation.Fresh (Yulang.GeneralNominalCanonicalOutputFork.state choice)
    Yulang.GeneralNominalCanonicalOutputFork.registry Yulang.GeneralNominalCanonicalOutputFork.root.identity
Yulang.GeneralNominalCanonicalOutputForkClassification.point_prepared : Yulang.GeneralNominalRecursiveCandidates.Prepared
  Yulang.GeneralNominalCanonicalOutputFork.registry (Yulang.GeneralNominalCanonicalOutputFork.context (some false))
  Yulang.GeneralNominalCanonicalOutputFork.root Yulang.GeneralNominalCanonicalOutputFork.declaration
  Yulang.GeneralNominalCanonicalOutputFork.declaration_checked
Yulang.GeneralNominalCanonicalOutputForkClassification.point_survivor : Yulang.GeneralNominalRecursiveCandidates.Survivor
  Yulang.GeneralNominalCanonicalOutputFork.registry (Yulang.GeneralNominalCanonicalOutputFork.context (some false))
  Yulang.GeneralNominalCanonicalOutputFork.root 90 []
Yulang.GeneralNominalCanonicalOutputForkClassification.wide_not_prepared : ∀
  (checked :
    Yulang.GeneralDeclarations.DeclarationChecked Yulang.GeneralNominalCanonicalOutputFork.registry.constructors
      Yulang.GeneralDeclarationExamples.roles Yulang.GeneralNominalCanonicalOutputFork.declaration),
  ¬Yulang.GeneralNominalRecursiveCandidates.Prepared Yulang.GeneralNominalCanonicalOutputFork.registry
      (Yulang.GeneralNominalCanonicalOutputFork.context (some true)) Yulang.GeneralNominalCanonicalOutputFork.root
      Yulang.GeneralNominalCanonicalOutputFork.declaration checked
Yulang.GeneralNominalCanonicalOutputForkClassification.generated_only_root : ∀ (wide : Bool)
  (focus : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles),
  Yulang.GeneralNominalSaturationState.Generated (Yulang.GeneralNominalCanonicalOutputFork.after wide)
      Yulang.GeneralNominalCanonicalOutputFork.root focus →
    focus = Yulang.GeneralNominalCanonicalOutputFork.root
Yulang.GeneralNominalCanonicalOutputForkClassification.wide_stable : Yulang.GeneralNominalFeedbackSteps.Stable
  Yulang.GeneralNominalCanonicalOutputFork.registry (Yulang.GeneralNominalCanonicalOutputFork.after true)
  Yulang.GeneralNominalCanonicalOutputFork.root
Yulang.GeneralNominalCanonicalOutputForkClassification.feedback_acyclic : ∀ (wide : Bool) (source : Nat),
  ¬Yulang.GeneralNominalFeedbackK2.Cycle (Yulang.GeneralNominalCanonicalOutputFork.after wide) source
Yulang.GeneralNominalCanonicalOutputForkClassification.raw_acyclic : ∀ (wide : Bool) (slot : Fin 5),
  ¬Yulang.GeneralNominalCycleK2.RecursAt (Yulang.GeneralNominalCanonicalOutputFork.state (some wide)) slot
Yulang.GeneralNominalCanonicalOutputForkClassification.not_rootK2 : ∀ (wide : Bool)
  (demand : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles),
  ¬Yulang.GeneralNominalFeedbackK2.RootK2 (Yulang.GeneralNominalCanonicalOutputFork.after wide) demand
Yulang.GeneralNominalCanonicalOutputForkClassification.not_candidateK2 : ∀ (wide : Bool)
  (r : Yulang.GeneralDeclarations.Registry)
  (demand : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles),
  ¬Yulang.GeneralNominalFeedbackK2.CandidateK2 r (Yulang.GeneralNominalCanonicalOutputFork.after wide) demand
Yulang.GeneralNominalCanonicalOutputForkClassification.point_selected : Yulang.GeneralNominalFeedbackK2.Local
  Yulang.GeneralNominalCanonicalOutputFork.registry (Yulang.GeneralNominalCanonicalOutputFork.after false)
  Yulang.GeneralNominalCanonicalOutputFork.root (Yulang.CommonRoleOutermostResolver.Frontier.selected 90 [])
Yulang.GeneralNominalCanonicalOutputForkClassification.packet_children : Yulang.GeneralNominalCanonicalOutputForkClassification.packet.children =
  []
Yulang.GeneralNominalCanonicalOutputForkClassification.good_packet : Yulang.GeneralNominalCanonicalOutputForkClassification.packet.Holds
  (Yulang.GeneralNominalCanonicalOutputFork.model Yulang.Inference.Base.int)
Yulang.GeneralNominalCanonicalOutputForkClassification.bad_packet : ¬Yulang.GeneralNominalCanonicalOutputForkClassification.packet.Holds
    (Yulang.GeneralNominalCanonicalOutputFork.model Yulang.Inference.Base.str)
Yulang.GeneralNominalCanonicalOutputForkClassification.point_installable : Yulang.GeneralNominalFeedbackSteps.Installable
  Yulang.GeneralNominalCanonicalOutputFork.registry (Yulang.GeneralNominalCanonicalOutputFork.after false)
  Yulang.GeneralNominalCanonicalOutputForkClassification.packet
Yulang.GeneralNominalCanonicalOutputForkClassification.point_not_committed : ¬Yulang.GeneralNominalFeedbackSteps.Committed
    (Yulang.GeneralNominalCanonicalOutputFork.after false) Yulang.GeneralNominalCanonicalOutputForkClassification.packet
Yulang.GeneralNominalCanonicalOutputForkClassification.actual_install : Yulang.GeneralNominalReobservationSteps.Step
  Yulang.GeneralNominalCanonicalOutputFork.registry Yulang.GeneralNominalCanonicalOutputFork.root
  (Yulang.GeneralNominalCanonicalOutputFork.after false)
  Yulang.GeneralNominalCanonicalOutputForkClassification.installed
Yulang.GeneralNominalCanonicalOutputForkClassification.installed_excludes_bad : ¬Yulang.GeneralNominalSaturationState.Models
    Yulang.GeneralNominalCanonicalOutputForkClassification.installed
    (Yulang.GeneralNominalCanonicalOutputFork.model Yulang.Inference.Base.str)
Yulang.GeneralNominalCanonicalOutputForkClassification.installed_good : Yulang.GeneralNominalSaturationState.Models
  Yulang.GeneralNominalCanonicalOutputForkClassification.installed
  (Yulang.GeneralNominalCanonicalOutputFork.model Yulang.Inference.Base.int)
Yulang.GeneralNominalCanonicalOutputForkClassification.point_not_stable : ¬Yulang.GeneralNominalReobservationSteps.Stable
    Yulang.GeneralNominalCanonicalOutputFork.registry (Yulang.GeneralNominalCanonicalOutputFork.after false)
    Yulang.GeneralNominalCanonicalOutputFork.root
Yulang.GeneralNominalCanonicalOutputForkClassification.no_stable_same_models_with_installable : ∀
  (final : Yulang.GeneralNominalSaturationState.State Yulang.GeneralDeclarationExamples.roles),
  Yulang.GeneralNominalReobservationSteps.Stable Yulang.GeneralNominalCanonicalOutputFork.registry final
      Yulang.GeneralNominalCanonicalOutputFork.root →
    (∀ (m : Yulang.GeneralNominalCommonBridge.Assignment),
        Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralNominalCanonicalOutputFork.after true) m ↔
          Yulang.GeneralNominalSaturationState.Models final m) →
      Yulang.GeneralNominalFeedbackSteps.Installable Yulang.GeneralNominalCanonicalOutputFork.registry final
          Yulang.GeneralNominalCanonicalOutputForkClassification.packet →
        False
Yulang.GeneralNominalCanonicalOutputForkClassification.installed_trace_loses_bad : ∀
  (final : Yulang.GeneralNominalSaturationState.State Yulang.GeneralDeclarationExamples.roles),
  Yulang.B4Target.Steps
      (Yulang.GeneralNominalReobservationSteps.Step Yulang.GeneralNominalCanonicalOutputFork.registry
        Yulang.GeneralNominalCanonicalOutputFork.root)
      Yulang.GeneralNominalCanonicalOutputForkClassification.installed final →
    ¬Yulang.GeneralNominalSaturationState.Models final
        (Yulang.GeneralNominalCanonicalOutputFork.model Yulang.Inference.Base.str)
Yulang.GeneralNominalCanonicalOutputForkClassification.concrete_completion_requires_output : Yulang.GeneralDeclarations.Checked
    Yulang.GeneralNominalCanonicalOutputFork.registry ∧
  Yulang.B4TargetV5.Reachable
      (Yulang.GeneralDictionaryReachableBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
      Yulang.GeneralNominalCanonicalOutputFork.registry Yulang.GeneralNominalCanonicalOutputFork.root
      (Yulang.GeneralNominalCanonicalOutputFork.after true) ∧
    Yulang.GeneralNominalFeedbackSteps.Stable Yulang.GeneralNominalCanonicalOutputFork.registry
        (Yulang.GeneralNominalCanonicalOutputFork.after true) Yulang.GeneralNominalCanonicalOutputFork.root ∧
      Yulang.GeneralNominalReobservationSteps.Step Yulang.GeneralNominalCanonicalOutputFork.registry
          Yulang.GeneralNominalCanonicalOutputFork.root (Yulang.GeneralNominalCanonicalOutputFork.after true)
          (Yulang.GeneralNominalCanonicalOutputFork.after false) ∧
        (∀ (m : Yulang.GeneralNominalCommonBridge.Assignment),
            Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralNominalCanonicalOutputFork.after true) m ↔
              Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralNominalCanonicalOutputFork.after false) m) ∧
          Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralNominalCanonicalOutputFork.after true)
              (Yulang.GeneralNominalCanonicalOutputFork.model Yulang.Inference.Base.int) ∧
            Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralNominalCanonicalOutputFork.after true)
                (Yulang.GeneralNominalCanonicalOutputFork.model Yulang.Inference.Base.str) ∧
              Yulang.GeneralNominalFeedbackSteps.Installable Yulang.GeneralNominalCanonicalOutputFork.registry
                  (Yulang.GeneralNominalCanonicalOutputFork.after false)
                  Yulang.GeneralNominalCanonicalOutputForkClassification.packet ∧
                ¬Yulang.GeneralNominalReobservationSteps.Stable Yulang.GeneralNominalCanonicalOutputFork.registry
                      (Yulang.GeneralNominalCanonicalOutputFork.after false)
                      Yulang.GeneralNominalCanonicalOutputFork.root ∧
                  Yulang.GeneralNominalReobservationSteps.Step Yulang.GeneralNominalCanonicalOutputFork.registry
                      Yulang.GeneralNominalCanonicalOutputFork.root
                      (Yulang.GeneralNominalCanonicalOutputFork.after false)
                      Yulang.GeneralNominalCanonicalOutputForkClassification.installed ∧
                    Yulang.GeneralNominalSaturationState.Models
                        Yulang.GeneralNominalCanonicalOutputForkClassification.installed
                        (Yulang.GeneralNominalCanonicalOutputFork.model Yulang.Inference.Base.int) ∧
                      ¬Yulang.GeneralNominalSaturationState.Models
                          Yulang.GeneralNominalCanonicalOutputForkClassification.installed
                          (Yulang.GeneralNominalCanonicalOutputFork.model Yulang.Inference.Base.str)
Yulang.GeneralNominalCanonicalCompletionObstruction.point_descriptor_forced : ∀ (slot : Fin 5)
  (d : Yulang.GeneralNominalState.Descriptor 5),
  ↑slot < 3 →
    Yulang.GeneralDeclarationExamples.constructors d.constructor = some d.declaration →
      Yulang.GeneralNominalReobservationSteps.PointDescriptor d →
        Yulang.GeneralNominalState.Denotes Yulang.GeneralNominalRefreshFork.base Yulang.GeneralNominalRefreshFork.model
            slot d →
          d = Yulang.GeneralNominalRefreshFork.descriptor (if slot = 2 then (3, 3) else (2, 2))
Yulang.GeneralNominalCanonicalCompletionObstruction.revision_pointClosed : ∀
  (change : Yulang.GeneralNominalReobservationSteps.Revision (Yulang.GeneralNominalCanonicalOutputFork.after true)),
  Yulang.GeneralNominalReobservationSteps.Improves change →
    Yulang.GeneralNominalReobservationSteps.PointClosed change.snapshot
Yulang.GeneralNominalCanonicalCompletionObstruction.revision_entries_forced : ∀
  (change : Yulang.GeneralNominalReobservationSteps.Revision (Yulang.GeneralNominalCanonicalOutputFork.after true)),
  Yulang.GeneralNominalReobservationSteps.Certified change →
    Yulang.GeneralNominalReobservationSteps.Improves change →
      change.entries = (Yulang.GeneralNominalCanonicalOutputFork.state (some false)).nominals
Yulang.GeneralNominalCanonicalCompletionObstruction.revision_result_forced : ∀
  (change : Yulang.GeneralNominalReobservationSteps.Revision (Yulang.GeneralNominalCanonicalOutputFork.after true)),
  Yulang.GeneralNominalReobservationSteps.Certified change →
    Yulang.GeneralNominalReobservationSteps.Improves change →
      change.result = Yulang.GeneralNominalCanonicalOutputFork.after false
Yulang.GeneralNominalCanonicalCompletionObstruction.step_from_wide : ∀
  (next : Yulang.GeneralNominalSaturationState.State Yulang.GeneralDeclarationExamples.roles),
  Yulang.GeneralNominalReobservationSteps.Step Yulang.GeneralNominalCanonicalOutputFork.registry
      Yulang.GeneralNominalCanonicalOutputFork.root (Yulang.GeneralNominalCanonicalOutputFork.after true) next →
    next = Yulang.GeneralNominalCanonicalOutputFork.after false
Yulang.GeneralNominalCanonicalCompletionObstruction.point_packet_excludes_bad : ∀
  (p : Yulang.GeneralNominalSaturationState.Packet Yulang.GeneralDeclarationExamples.roles),
  p.site.occurrence = Yulang.GeneralNominalCanonicalOutputFork.root →
    Yulang.GeneralNominalFeedbackSteps.Installable Yulang.GeneralNominalCanonicalOutputFork.registry
        (Yulang.GeneralNominalCanonicalOutputFork.after false) p →
      ¬p.Holds (Yulang.GeneralNominalCanonicalOutputFork.model Yulang.Inference.Base.str)
Yulang.GeneralNominalCanonicalCompletionObstruction.step_from_point_excludes_bad : ∀
  (next : Yulang.GeneralNominalSaturationState.State Yulang.GeneralDeclarationExamples.roles),
  Yulang.GeneralNominalReobservationSteps.Step Yulang.GeneralNominalCanonicalOutputFork.registry
      Yulang.GeneralNominalCanonicalOutputFork.root (Yulang.GeneralNominalCanonicalOutputFork.after false) next →
    ¬Yulang.GeneralNominalSaturationState.Models next
        (Yulang.GeneralNominalCanonicalOutputFork.model Yulang.Inference.Base.str)
Yulang.GeneralNominalCanonicalCompletionObstruction.trace_trichotomy : ∀
  (final : Yulang.GeneralNominalSaturationState.State Yulang.GeneralDeclarationExamples.roles),
  Yulang.B4Target.Steps
      (Yulang.GeneralNominalReobservationSteps.Step Yulang.GeneralNominalCanonicalOutputFork.registry
        Yulang.GeneralNominalCanonicalOutputFork.root)
      (Yulang.GeneralNominalCanonicalOutputFork.after true) final →
    final = Yulang.GeneralNominalCanonicalOutputFork.after true ∨
      final = Yulang.GeneralNominalCanonicalOutputFork.after false ∨
        ¬Yulang.GeneralNominalSaturationState.Models final
            (Yulang.GeneralNominalCanonicalOutputFork.model Yulang.Inference.Base.str)
Yulang.GeneralNominalCanonicalCompletionObstruction.stable_trace_loses_bad : ∀
  (final : Yulang.GeneralNominalSaturationState.State Yulang.GeneralDeclarationExamples.roles),
  Yulang.B4Target.Steps
      (Yulang.GeneralNominalReobservationSteps.Step Yulang.GeneralNominalCanonicalOutputFork.registry
        Yulang.GeneralNominalCanonicalOutputFork.root)
      (Yulang.GeneralNominalCanonicalOutputFork.after true) final →
    Yulang.GeneralNominalReobservationSteps.Stable Yulang.GeneralNominalCanonicalOutputFork.registry final
        Yulang.GeneralNominalCanonicalOutputFork.root →
      ¬Yulang.GeneralNominalSaturationState.Models final
          (Yulang.GeneralNominalCanonicalOutputFork.model Yulang.Inference.Base.str)
Yulang.GeneralNominalCanonicalCompletionObstruction.no_same_models_stable_extension : ¬∃ final,
    Yulang.B4Target.Steps
        (Yulang.GeneralNominalReobservationSteps.Step Yulang.GeneralNominalCanonicalOutputFork.registry
          Yulang.GeneralNominalCanonicalOutputFork.root)
        (Yulang.GeneralNominalCanonicalOutputFork.after true) final ∧
      Yulang.GeneralNominalReobservationSteps.Stable Yulang.GeneralNominalCanonicalOutputFork.registry final
          Yulang.GeneralNominalCanonicalOutputFork.root ∧
        ∀ (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
          Yulang.GeneralNominalSaturationState.Models final assignment ↔
            Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralNominalCanonicalOutputFork.after true) assignment
Yulang.GeneralNominalCanonicalCompletionObstruction.installed_models_exact : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralNominalCanonicalOutputForkClassification.installed
      assignment ↔
    Yulang.GeneralNominalSaturationState.Models (Yulang.GeneralNominalCanonicalOutputFork.after true) assignment ∧
      Yulang.CommonNominalFullCarrier.Equivalent (assignment 5).fst
        (Yulang.CommonNominalSyntax.Layer.base Yulang.Inference.Base.int)
Yulang.GeneralNominalCanonicalCompletionObstruction.canonical_views_equal : Yulang.GeneralCanonicalObservations.canonical
    (Yulang.GeneralNominalCanonicalOutputFork.after true) =
  Yulang.GeneralCanonicalObservations.canonical (Yulang.GeneralNominalCanonicalOutputFork.after false)
Yulang.GeneralNominalCanonicalCompletionObstruction.boundary_completion_obstruction : (Yulang.GeneralNominalReobservationBoundary.boundary
        Yulang.GeneralDeclarationExamples.roles).Checked
    Yulang.GeneralNominalCanonicalOutputFork.registry ∧
  Yulang.B4TargetV5.Reachable
      (Yulang.GeneralNominalReobservationBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
      Yulang.GeneralNominalCanonicalOutputFork.registry Yulang.GeneralNominalCanonicalOutputFork.root
      (Yulang.GeneralNominalCanonicalOutputFork.after true) ∧
    (∀ (next : Yulang.GeneralNominalSaturationState.State Yulang.GeneralDeclarationExamples.roles),
        ¬Yulang.GeneralNominalFeedbackSteps.Step Yulang.GeneralNominalCanonicalOutputFork.registry
            Yulang.GeneralNominalCanonicalOutputFork.root (Yulang.GeneralNominalCanonicalOutputFork.after true) next) ∧
      ¬∃ final,
          Yulang.B4Target.Steps
              ((Yulang.GeneralNominalReobservationBoundary.boundary Yulang.GeneralDeclarationExamples.roles).Step
                Yulang.GeneralNominalCanonicalOutputFork.registry Yulang.GeneralNominalCanonicalOutputFork.root)
              (Yulang.GeneralNominalCanonicalOutputFork.after true) final ∧
            (Yulang.GeneralNominalReobservationBoundary.boundary Yulang.GeneralDeclarationExamples.roles).Stable
                Yulang.GeneralNominalCanonicalOutputFork.registry final Yulang.GeneralNominalCanonicalOutputFork.root ∧
              ∀
                (assignment :
                  (Yulang.GeneralNominalReobservationBoundary.vocabulary
                      Yulang.GeneralDeclarationExamples.roles).Model),
                (Yulang.GeneralNominalReobservationBoundary.boundary Yulang.GeneralDeclarationExamples.roles).Models
                    final assignment ↔
                  (Yulang.GeneralNominalReobservationBoundary.boundary Yulang.GeneralDeclarationExamples.roles).Models
                    (Yulang.GeneralNominalCanonicalOutputFork.after true) assignment
Yulang.GeneralNominalCanonicalCompletionObstruction.not_old_halted_same_models_completion : ¬∀
    (r : Yulang.GeneralDeclarations.Registry),
    (Yulang.GeneralDictionaryReachableBoundary.boundary Yulang.GeneralDeclarationExamples.roles).Checked r →
      ∀ (start : Yulang.GeneralNominalSaturationState.State Yulang.GeneralDeclarationExamples.roles)
        (d : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles),
        Yulang.B4TargetV5.Reachable
            (Yulang.GeneralDictionaryReachableBoundary.boundary Yulang.GeneralDeclarationExamples.roles) r d start →
          (∀ (next : Yulang.GeneralNominalSaturationState.State Yulang.GeneralDeclarationExamples.roles),
              ¬Yulang.GeneralNominalFeedbackSteps.Step r d start next) →
            ∃ final,
              Yulang.B4Target.Steps (Yulang.GeneralNominalReobservationSteps.Step r d) start final ∧
                Yulang.GeneralNominalReobservationSteps.Stable r final d ∧
                  ∀ (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
                    Yulang.GeneralNominalSaturationState.Models final assignment ↔
                      Yulang.GeneralNominalSaturationState.Models start assignment
Yulang.GeneralNominalCanonicalCompletionObstruction.model_decreasing_completion_of_progress : ∀
  (roleDecls : Yulang.Roles.RoleDecls),
  Yulang.GeneralNominalReobservationExecutor.Progress roleDecls →
    ∀ (r : Yulang.GeneralDeclarations.Registry),
      (Yulang.GeneralNominalReobservationBoundary.boundary roleDecls).Checked r →
        ∀ (start : Yulang.GeneralNominalSaturationState.State roleDecls)
          (d : Yulang.GeneralSourceDictionaries.Occurrence roleDecls),
          Yulang.B4TargetV5.Reachable (Yulang.GeneralNominalReobservationBoundary.boundary roleDecls) r d start →
            ∃ final,
              Yulang.B4Target.Steps (Yulang.GeneralNominalReobservationSteps.Step r d) start final ∧
                Yulang.GeneralNominalReobservationSteps.Stable r final d ∧
                  ∀ (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
                    Yulang.GeneralNominalSaturationState.Models final assignment →
                      Yulang.GeneralNominalSaturationState.Models start assignment
@Yulang.GeneralNominalReobservationMergeDiamond.recover_equal_models : ∀ {roles : Yulang.Roles.RoleDecls}
  (before after : Yulang.GeneralNominalSaturationState.State roles),
  (∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models before model ↔
        Yulang.GeneralNominalSaturationState.Models after model) →
    ∀ (site : Yulang.GeneralNominalDemandMerging.Site roles),
      Yulang.GeneralNominalFeedbackSites.recover before site = Yulang.GeneralNominalFeedbackSites.recover after site
@Yulang.GeneralNominalReobservationMergeDiamond.sameInputs_equal_models : ∀ {roles : Yulang.Roles.RoleDecls}
  (before after : Yulang.GeneralNominalSaturationState.State roles),
  (∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
      Yulang.GeneralNominalSaturationState.Models before model ↔
        Yulang.GeneralNominalSaturationState.Models after model) →
    ∀ (first last : Yulang.GeneralNominalDemandMerging.Site roles),
      Yulang.GeneralNominalFeedbackSites.SameInputs before first last ↔
        Yulang.GeneralNominalFeedbackSites.SameInputs after first last
@Yulang.GeneralNominalReobservationMergeDiamond.alias_of_same_edges : ∀ {roles : Yulang.Roles.RoleDecls}
  {first last : Nat} {before after : Yulang.GeneralNominalSaturationState.State roles},
  before.aliases = after.aliases →
    Yulang.GeneralNominalSaturationState.Alias before first last →
      Yulang.GeneralNominalSaturationState.Alias after first last
@Yulang.GeneralNominalReobservationMergeDiamond.merged_result : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles}
  (change : Yulang.GeneralNominalReobservationSteps.Revision state)
  (first last : Yulang.GeneralNominalDemandMerging.Site roles),
  (Yulang.GeneralNominalReobservationMergeDiamond.merged change first last).result =
    Yulang.GeneralNominalSaturationState.merge change.result first last
@Yulang.GeneralNominalReobservationMergeDiamond.merged_certified : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles}
  (change : Yulang.GeneralNominalReobservationSteps.Revision state),
  Yulang.GeneralNominalReobservationSteps.Certified change →
    ∀ (first last : Yulang.GeneralNominalDemandMerging.Site roles),
      Yulang.GeneralNominalReobservationSteps.Certified
        (Yulang.GeneralNominalReobservationMergeDiamond.merged change first last)
@Yulang.GeneralNominalReobservationMergeDiamond.merged_improves : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles}
  (change : Yulang.GeneralNominalReobservationSteps.Revision state),
  Yulang.GeneralNominalReobservationSteps.Improves change →
    ∀ (first last : Yulang.GeneralNominalDemandMerging.Site roles),
      Yulang.GeneralNominalReobservationSteps.Improves
        (Yulang.GeneralNominalReobservationMergeDiamond.merged change first last)
@Yulang.GeneralNominalReobservationMergeDiamond.merge_reobserve_diamond : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles} (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (first last : Yulang.GeneralNominalDemandMerging.Site roles),
  first ∈ state.sites →
    last ∈ state.sites →
      Yulang.GeneralNominalSaturationState.Generated state root first.occurrence →
        Yulang.GeneralNominalFeedbackSites.SameInputs state first last →
          ¬Yulang.GeneralNominalSaturationState.Alias state first.occurrence.identity last.occurrence.identity →
            ∀ (change : Yulang.GeneralNominalReobservationSteps.Revision state),
              Yulang.GeneralNominalReobservationSteps.Certified change →
                Yulang.GeneralNominalReobservationSteps.Improves change →
                  Yulang.GeneralNominalReobservationSteps.Step registry root state
                      (Yulang.GeneralNominalSaturationState.merge state first last) ∧
                    Yulang.GeneralNominalReobservationSteps.Step registry root state change.result ∧
                      Yulang.GeneralNominalReobservationSteps.Step registry root
                          (Yulang.GeneralNominalSaturationState.merge state first last)
                          (Yulang.GeneralNominalSaturationState.merge change.result first last) ∧
                        Yulang.GeneralNominalReobservationSteps.Step registry root change.result
                          (Yulang.GeneralNominalSaturationState.merge change.result first last)
```

### Task-contract clarification (pending; not a language-semantics decision)

For `Container(list (list int), item = 'out)`, should same-model equality
apply to observation completion alone, with full stabilization permitted to add
the selected `item = int` constraint and decrease Models?

1. **Recommended:** complete observations without model loss, then carry out
   model-decreasing saturation under the existing B4 clause (1).
2. Retain same-model equality, but stop at an observation-complete intermediate
   rather than claim full Stable. The checked old-halted domain cannot satisfy
   both properties under the current relation, as proved above.

### Owner answer to the Item 4e recursive associated-output growth question (2026-11-12)

Option 1 (lazy): defer expansion of a where-child whose needed input head is supported only by provisional associated-output equations inside its own unresolved dependency cycle; keep those equations for ordinary constraints, same-input merging and K2; resume when support arrives from outside the cycle (source constraints or discharged demands); final pending at the stable end of file. No declaration-time rejection. Recorded in spec/06-roles.md §6.3 and draft addendum 5.

### Supervisor answer to the Item 5d clarification (2026-11-12)

Yes: model equality is required only for observation completion (refresh/reobservation/descriptor replacement). Full stabilization may decrease Models (installation adds the selected candidate's constraints), as V5 already permits; the earlier "every old-halted state extends to a new-Stable state with the same models" request was too strong and is withdrawn.


## Item 4f — retained support and guarded expansion (2026-11-12)

Status: **partial; general termination is not proved**. This section implements
and checks the first support bridge requested after the owner chose the lazy
answer. It does not claim B4 clause (1), an unconditional executor, or a fully
complete implementation of support resumption.

Authority: spec/06-roles.md §6.3, “自分の出力だけを根拠にした展開は保留する”,
the main-statement draft's addendum 5, and the supervisor answers immediately
above. Observation completion preserves models. Installation and full
stabilization may decrease models; no same-model full-stabilization premise is
used here. Existing Lean definitions, the frozen audit, and the module README
remain unchanged.

### What the support relation means

`GeneralNominalPacketSupport.packet_exact` separates a packet into its old raw
context, new `Inputs`, and new `Outputs`. `Inputs` includes the ordinary self,
cross, and repeated-capture constraints, actual projection constraints, and
compound unnamed child-input materialization. `Outputs` retains the complete
named materialization schema, including cross-equations with input uses. This
intentional overlap preserves the full conjunction. Neither delta contains the
old raw context's model predicate. Thus a refreshed head cannot enter the
support kernel simply because a later packet retained that cached context.

`GeneralNominalSupport.Tracked` adds an immutable initial source context and a
finite fact ledger beside the existing saturation state. It does not replace
the nominal model carrier. Facts are input deltas, output deltas, and same-input
merge equations, with finite lists of producing obligations. An output fact
adds its own producer to the support inherited from the applicability decision.
A merge adds both dictionary obligations and the support of its input equality.

`Slice state support` uses the original source models and precisely those facts
whose entire dependency list is contained in `support`. `Entails` is universal
semantic entailment from that slice; it never reads an executor result.
`HeadSupported` requires an independently certified normalized head observation
entailed by the slice. Its head tag must agree with the head being read, but its
parameter intervals can be broader than the current cached descriptor. This
allows a source-known nominal head to remain supported after later precision.

For a producer `p` used by a focus `d`, `Generated current p d` is the independent
where/alias dependency from the producer to the focus. Using p's provisional
output for d adds the reverse support dependence. `External current d p` holds
when p has a finite `Discharged` derivation, or there is no such generation
path. Inherited support lists retain earlier output dependencies transitively;
a later use cannot erase them by selecting a different packet. `Discharged` is
an inductive finite tree of installed packets with every emitted child
discharged (and registered alias transport). It is not `Committed`: installation
makes a packet committed immediately, while a packet with unresolved children
has no such finite discharge derivation. The no-leaves theorem makes this
separation explicit.

Support alternatives are existential. Installations and merges record **all**
valid supports available at insertion, rather than one chosen witness. The
finite enumeration is the subset list of the current ledger's dependency pool.
`slice_restrict` proves that removing irrelevant identities does not change the
slice; `guard_restrict` and `merge_alternatives_exists` justify completeness of
this finite enumeration for the insertion-time certificates. Arbitrary witness
choice therefore does not affect the resulting ledger. This is a per-state
finiteness result, not a bound on all future installations.

The merge certificate additionally proves endpoint equality under the slice
for every input whose origin was missing before recovery. Without this
`RecoverySupported` condition, recovery using full-journal equality could turn
(L,U) and (L,V) into the same apparent point L, hiding the provisional equations
that justified L≈U≈V. The real same-input merge and K2 continue using the full
journal, as required by the owner.

`reads` follows the recursive inspector's actual decisions. Variables add no
nested reads. A scalar pattern reads only the lower head. A structural pattern
with a scalar lower mismatch does not require the upper head. Nonpoint nominal
inspection reads the upper head, and descends into parameters only when both
outer descriptors pass the corresponding layout checks. `DecisionGuard`
requires support for every unnamed lower-root head and every head read by each
visible same-role declaration. It includes candidates whose inspection ends in
failure: an unsupported mismatch cannot become “all candidates vanish” or make
another candidate selectable early.

`GeneralNominalSupportSteps.Step` restricts installation on the newest
feedback/reobservation relation using this whole-decision certificate. It
retains ordinary updates, merges, equality feedback, and descriptor replacement.
Administrative updates do not add support facts. `step_old` projects every new
step to an actual old reobservation step. `formed_exact` proves, for every new
SourceFormed state, exact agreement between full journal models and the
immutable source plus all ledger deltas. No constraint is discarded by a
support cut in the actual solver state.

The new boundary adds support deferral to **InspectionPending**, not
RootPending. Full-journal RootK2 and CandidateK2 retain priority. `install_selected`
proves the installation guard agrees with the new independent selected
judgment. `stable_committed` retains the additional guard explicitly; the old
unguarded Stable⇒Committed statement is not silently reused.

### Concrete results and limits

* The R-growth fixture starts with the real empty-journal InitialSource,
  performs the real first installation and certified refresh, and retains all
  installed equations. For every admissible support, `finiteModel 0` is a model
  of the cut in which child input 1 is int. Thus no nominal-list head for that
  input has a support witness. The first child cannot pass any declaration's
  guard and has independent Local `.pending`.
* This is a classification at the displayed reachable snapshot. The name
  `child_final_pending` does **not** assert that this snapshot is Stable, or
  prove an EOF trace.
* Display(list int) is selected with exactly the list declaration and child
  [Display int]. Wrap is selected with its Container child and named item
  obligation (numeric output name 1 in the fixture). Both have actual guarded
  installation steps. Their emitted input heads retain direct source support.
* `source_ready`/`source_guard` establish the general source-support route;
  `discharged_support` establishes the route once all supporting producers have
  finite discharge proofs. These results do not prove completeness of every
  future support-resumption scenario.
* `no_modelwise_guarded_rank` shows that even the now-allowed, source-supported
  first installation cannot strictly decrease an arbitrary well-founded rank
  of the input denotation in **every** full journal model. The regular model
  gives equal parent/child denotations. This refutes that proposed measure, not
  accessibility of the guarded Step; the next expansion is blocked.

### Remaining termination work — no new owner question

No `InstallationOrder` is constructed from SourceFormed and Checked. The exact
missing bridge is a finite, interval-sensitive provenance readback for guarded
applicability and emitted inputs, with a well-founded installation order that
cannot increase under refresh, equality feedback, merge, or discharge. It must
handle repeated-capture intervals and compound input materialization and show
that every installed where-child receives the declaration-side substitutions
needed by `DeclarationChecked.captureStable`. Output-only binders remain absent
from that Paterson count. A finite fact list in each snapshot does not prove a
finite bound on the dependency pool across a trace.

Two implementation obligations remain material:

1. The graph/support construction has not been proved sufficient for arbitrary
   unresolved sibling support. A checked-pattern probe is the ladder
   `R(list(list 'a)) where S(list 'a, out='a), R(list 'a)` together with
   `S(list 'a) where T('a, out='b): type out=list 'b`. A provisional sibling can
   expose the next R input without being its generation ancestor. No infinite
   guarded Step trace is claimed or proved. The required connection to the
   existing sibling-stabilization rule and finite source readback remains open.
2. Packet and merge support alternatives are retained at insertion time.
   Completeness when an already committed packet or aliased pair acquires a
   **new independent justification later** is not proved. Novelty currently
   prevents replay solely to add that justification. A provenance rejustification
   bridge and its administrative bound remain to be constructed. Direct source
   support and discharge of already-recorded dependencies work as stated.

These are implementation/proof obligations under the existing owner decisions;
this section makes no new semantic restriction and asks no new owner question.
The older explicit Readback still yields a conditional whereAccessible result,
but is not constructed from the new SourceFormed predicate. In particular, the
parent target is still open.

### SourceBoundary field table

All names below are in `GeneralNominalSupportBoundary` unless qualified.
“Defined” means an independent mathematical judgment; it does not certify
completeness of its source producer or the corresponding V5 bridge.

| Field | Definition / status |
|---|---|
| Checked | `fields.Checked`: inherited role agreement and `GeneralDeclarations.Checked`; defined |
| Models | `fields.Models`: `GeneralNominalSaturationState.Models state.current`; defined; `formed_exact` gives ledger correspondence |
| Step | `GeneralNominalSupportSteps.Step`; defined guarded feedback/reobservation subsystem; progress and later rejustification MISSING |
| Stable | `GeneralNominalSupportSteps.Stable`; defined absence of guarded updates; not claimed maximal provenance |
| Generated | `GeneralNominalSaturationState.Generated state.current`; defined, identities retained |
| RootPending | inherited unresolved unnamed lower-head predicate; defined |
| RootK2 | inherited `GeneralNominalFeedbackK2.RootK2 state.current`; defined, full journal |
| CandidateK2 | inherited `GeneralNominalFeedbackK2.CandidateK2`; defined, full journal |
| InspectionPending | inherited pending or `SupportPending`; defined; support completeness has the limits above |
| Survivor | inherited `GeneralNominalRecursiveCandidates.Survivor`; defined; applicability guard is in pending/installation, alternatives stay separate |
| Evidence | `GeneralDictionaryFeedbackEvidence.evidence roles registry state.current`; defined judgment; new evidenceNode bridge MISSING |
| Reorders | inherited `GeneralRegistryReordering.Reorders`; defined |
| DictionaryEquivalent | inherited `GeneralDictionaryPayloadOrder.Equivalent`; defined |

### V5 fourteen-field accounting

Concrete boundary: `GeneralNominalSupportBoundary.boundary roles`.
Executor: `GeneralNominalSupportExecutor.executor roles progress`.
**Six fields proved without Progress. Three further fields proved conditional
only on Progress. Progress itself remains open; this is not ten unconditional
fields or a completed B4 theorem.**

| V5 field | Result |
|---|---|
| progress | MISSING: construction of the installation order/readback above |
| execution | `GeneralNominalSupportExecutor.execution`, conditional only on `Progress roles` |
| halted | `GeneralNominalSupportExecutor.halted`, same single global premise |
| closure | `GeneralNominalSupportBoundary.closure`, proved |
| stepModels | `GeneralNominalSupportBoundary.stepModels`, proved |
| frontierLocal | `GeneralNominalSupportBoundary.frontierLocal`, proved |
| localIdentity | `GeneralNominalSupportBoundary.localIdentity`, proved |
| whereAccessible | MISSING unconditionally; `whereAccessible_of_readback` retains explicit Readback |
| treeExecution | `GeneralNominalSupportExecutor.treeExecution`, conditional only on Progress, with the target's own exactness/accessibility binders retained |
| canonicalLocalOrder | MISSING for the guarded boundary/executor |
| dictionaryRefl | `GeneralNominalSupportBoundary.dictionaryRefl`, proved |
| evidenceNode | MISSING for the guarded Stable/selected correspondence |
| generatedChildren | MISSING in general; actual initial selected installations emit all children |
| initialReorders | `GeneralNominalSupportBoundary.initialReorders`, proved |

The executor's `saturationTotal` is correspondingly conditional on Progress.
The frontiers remain a classical selection of the independent Local judgment.

### Review and verification

The registered `prover` role was unavailable: the configured role files and the
three skill-referenced orchestration/design-authority rule files are absent in
this checkout. The primary constructed the bounded derivation directly under
[yulang-proofs](/home/momota1029/.codex/skills/yulang-proofs/SKILL.md), with separate
read-only reviews by `confluence_review` and `canonical_review`. No prover agent
ran. Review found and corrected unsupported negative decisions, unnecessary
nominal reads, witness-dependent packet/merge provenance, and recovery of
origins using untracked endpoint equalities. Neither review certified progress.

Final command results are recorded below after the signature catalogue. No
Rust/parser suite, all historical audit parts, end-to-end inference producer,
full confluence, or unconditional termination was verified in this task.

### Full new public theorem statements

The following are the complete source signatures, grouped by namespace. Open
names and local abbreviations are those of the linked modules; the Lean files
contain every proof. Private calculation helpers are omitted. Every listed
public theorem is covered by `lean/Audit/GeneralNominalSupport.lean`.

`Yulang.GeneralNominalPacketSupport` — [module](../../lean/Yulang/GeneralNominalPacketSupport.lean)

```lean
theorem private_exact (packet : Packet roles) (model : Assignment) :
    GeneralNominalState.Models packet.privateContext.state model ↔
      GeneralNominalState.Models packet.context.state model ∧ Ordinary packet model

theorem outputs_inputs (packet : Packet roles) (model : Assignment) (valid : Outputs packet model) :
    GeneralNominalMaterialization.Models packet.context.state packet.declaration (capture packet)
      (report packet) (inputSchema packet) model

theorem packet_exact (packet : Packet roles) (model : Assignment) : packet.Holds model ↔
    GeneralNominalState.Models packet.context.state model ∧ Inputs packet model ∧ Outputs packet model
```


`Yulang.GeneralNominalSupport` — [module](../../lean/Yulang/GeneralNominalSupport.lean)

```lean
theorem head_recorded (head : Head snapshot identity test observation) : Recorded snapshot observation

theorem source_supported (state : Tracked roles) (identity : Nat) (test : Test) (observation : Observation)
    (source : Head state.source.state identity test observation) (support : List (Occurrence roles)) :
    HeadSupported state support identity test

theorem source_ready (state : Tracked roles) (identity : Nat) (test : Test) (old current : Observation)
    (source : Head state.source.state identity test old)
    (seen : Head state.current.context.state identity test current) (support : List (Occurrence roles)) :
    ReadyAt state support identity

theorem source_guard (state : Tracked roles) (root : Occurrence roles) (declaration : Declaration)
    (bounds : List (GeneralNominalInspection.Bounds state.current.context.state))
    (roots : ∀ index, ∃ test old current, Head state.source.state (root.demand.arguments index).1 test old ∧
      Head state.current.context.state (root.demand.arguments index).1 test current)
    (inspected : ∀ slot ∈ readsMany state.current.context.state
      (GeneralNominalInspection.queries state.current.context.state state.current.context.interpretation declaration) bounds,
        ∃ test old current, Head state.source.state (state.current.context.state.base.source slot) test old ∧
          Head state.current.context.state (state.current.context.state.base.source slot) test current) :
    Guard state root declaration bounds []

theorem discharged_external (state : State roles) (focus producer : Occurrence roles)
    (done : Discharged state producer) : External state focus producer

theorem cycle_excluded (state : Tracked roles) (focus producer : Occurrence roles)
    (path : Generated state.current producer focus) (unresolved : ¬ Discharged state.current producer)
    (support : List (Occurrence roles)) (allowed : Admissible state focus support) : producer ∉ support

theorem entails_source (state : Tracked roles) (focus : Occurrence roles) (claim : Assignment → Prop)
    (source : ∀ model, GeneralNominalState.Models state.source.state model → claim model) : Justified state focus claim

theorem refresh_support_unchanged (state : Tracked roles) (context : GeneralNominalCandidates.Context)
    (support : List (Occurrence roles)) (claim : Assignment → Prop) :
    Entails {state with current

theorem all_models_slice (state : Tracked roles) (support : List (Occurrence roles))
    (model : Assignment) (valid : AllModels state model) : Slice state support model

theorem support_sound (state : Tracked roles) (support : List (Occurrence roles)) (claim : Assignment → Prop)
    (entailed : Entails state support claim) (model : Assignment) (valid : AllModels state model) : claim model

theorem discharged_support (state : Tracked roles) (focus : Occurrence roles) (support : List (Occurrence roles))
    (done : ∀ producer ∈ support, Discharged state.current producer) (claim : Assignment → Prop)
    (entailed : Entails state support claim) : Justified state focus claim

theorem unsupported_decision_defers (state : Tracked roles) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (role : declaration.role = root.demand.role)
    (bounds : List (GeneralNominalInspection.Bounds state.current.context.state))
    (located : GeneralNominalRecursiveCandidates.arguments state.current.context root = some bounds)
    (unsupported : ∀ support, Admissible state root support → ¬ Inspection state support declaration bounds) :
    ¬ ∃ support, DecisionGuard state registry root support
```


`Yulang.GeneralNominalSupportChoices` — [module](../../lean/Yulang/GeneralNominalSupportChoices.lean)

```lean
theorem filter_subset (list : List α) (test : α → Bool) : list.filter test ∈ subsets list

theorem restrict_mem (state : Tracked roles) (support : List (Occurrence roles)) (producer : Occurrence roles) :
    producer ∈ restrict state support ↔ producer ∈ dependencyPool state ∧ producer ∈ support

theorem slice_restrict (state : Tracked roles) (support : List (Occurrence roles))
    (model : GeneralNominalCommonBridge.Assignment) : Slice state (restrict state support) model ↔ Slice state support model

theorem ready_restrict (state : Tracked roles) (support : List (Occurrence roles)) (identity : Nat)
    (ready : ReadyAt state support identity) : ReadyAt state (restrict state support) identity

theorem guard_restrict (state : Tracked roles) (root : Occurrence roles) (declaration : GeneralDeclarations.Declaration)
    (bounds : List (GeneralNominalInspection.Bounds state.current.context.state)) (support : List (Occurrence roles))
    (guard : Guard state root declaration bounds support) : Guard state root declaration bounds (restrict state support)

theorem decision_restrict (state : Tracked roles) (registry : GeneralDeclarations.Registry) (root : Occurrence roles)
    (support : List (Occurrence roles)) (guard : DecisionGuard state registry root support) :
    DecisionGuard state registry root (restrict state support)

theorem alternative_guard (member : support ∈ alternatives state packet) : PacketGuard state packet support

theorem alternatives_exists (state : Tracked roles) (packet : Packet roles) (support : List (Occurrence roles))
    (guard : PacketGuard state packet support) : ∃ selected, selected ∈ alternatives state packet

theorem facts_exact (state : Tracked roles) (packet : Packet roles) (support : List (Occurrence roles))
    (guard : PacketGuard state packet support) (model : GeneralNominalCommonBridge.Assignment) :
    (∀ fact ∈ installedFacts state packet, fact.Holds model) ↔
      GeneralNominalPacketSupport.Inputs packet model ∧ GeneralNominalPacketSupport.Outputs packet model

theorem empty_alternatives (state : Tracked roles) (packet : Packet roles) (empty : state.facts = [])
    (guard : PacketGuard state packet []) : installedFacts state packet = [.inputs packet [],.outputs packet []]

theorem merge_alternatives_exists (state : Tracked roles) (first last : GeneralNominalDemandMerging.Site roles)
    (support : List (Occurrence roles)) (guard : MergeGuard state first last support) :
    ∃ selected, selected ∈ mergeAlternatives state first last

theorem merged_facts_exact (state : Tracked roles) (first last : GeneralNominalDemandMerging.Site roles)
    (support : List (Occurrence roles)) (guard : MergeGuard state first last support)
    (model : GeneralNominalCommonBridge.Assignment) :
    (∀ fact ∈ mergedFacts state first last, fact.Holds model) ↔
      PresenceNormalForm.All CommonNominalFullCarrier.model model (GeneralNominalDemandMerging.outputAtoms first last)
```


`Yulang.GeneralNominalSupportSteps` — [module](../../lean/Yulang/GeneralNominalSupportSteps.lean)

```lean
theorem administrative_old (update : Administrative registry before focus after) :
    GeneralNominalReobservationSteps.At registry before focus after

theorem administrative_models (update : Administrative registry before focus after) (model : Assignment) :
    Models after model ↔ Models before model

theorem at_old (update : At registry before focus after) :
    GeneralNominalReobservationSteps.At registry before.current focus after.current

theorem step_old (update : Step registry root before after) :
    GeneralNominalReobservationSteps.Step registry root before.current after.current

theorem stepModels (update : Step registry root before after) (model : Assignment)
    (valid : Models after.current model) : Models before.current model

theorem steps_models (path : B4Target.Steps (Step registry root) before after)
    (model : Assignment) (valid : Models after.current model) : Models before.current model

theorem generated_monotone (update : Step registry root before after) (reached : Generated before.current root child) :
    Generated after.current root child

theorem at_exact (exact : Exact before) (update : At registry before focus after) : Exact after

theorem formed_exact (formed : SourceFormed registry root state) : Exact state

theorem at_source (update : At registry before focus after) : after.source = before.source

theorem closure (halted : ∀ after, ¬ Step registry root state after) :
    Stable registry state root ∧ ∀ child, Generated state.current root child → Stable registry state child

theorem stable_committed {state : Tracked roles} (stable : Stable registry state root) (packet : Packet roles)
    (generated : Generated state.current root packet.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (support : List (Occurrence roles)) (guard : PacketGuard state packet support) :
    GeneralNominalFeedbackSteps.Committed state.current packet
```


`Yulang.GeneralNominalSupportBoundary` — [module](../../lean/Yulang/GeneralNominalSupportBoundary.lean)

```lean
theorem local_correspondence (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (frontier : Frontier (Occurrence roles)) :
    B4TargetV3.Local (boundary roles).toSourceBoundary registry state root frontier ↔ Local registry state root frontier

theorem local_total (registry : Registry) (checked : Checked registry) (state : Tracked roles) (root : Occurrence roles) :
    ∃ frontier, Local registry state root frontier

theorem closure (registry : Registry) (_checked : (boundary roles).Checked registry)
    (state : Tracked roles) (root : Occurrence roles) (_reachable : Reachable (boundary roles) registry root state)
    (halted : ∀ after, ¬ (boundary roles).Step registry root state after) :
    (boundary roles).Stable registry state root ∧
      ∀ child, (boundary roles).Generated registry state root child → (boundary roles).Stable registry state child

theorem stepModels (registry : Registry) (_checked : (boundary roles).Checked registry)
    (root : Occurrence roles) (before after : Tracked roles)
    (_reachable : Reachable (boundary roles) registry root before)
    (step : (boundary roles).Step registry root before after) :
    ∀ model, (boundary roles).Models after model → (boundary roles).Models before model

theorem localIdentity (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (_reachable : Reachable (boundary roles) registry root state) :
    (frontiers roles registry state).Local = B4TargetV3.Local (boundary roles).toSourceBoundary registry state

theorem frontierLocal (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : Tracked roles) (root : Occurrence roles) (_reachable : Reachable (boundary roles) registry root state)
    (demand : Occurrence roles) (frontier : Frontier (Occurrence roles)) :
    (frontiers roles registry state).frontier demand = frontier ↔
      B4TargetV3.Local (boundary roles).toSourceBoundary registry state demand frontier

theorem dictionaryRefl (dictionary : CommonRoleOutermostResolver.Dictionary) :
    (boundary roles).DictionaryEquivalent dictionary dictionary

theorem initialReorders (registry other : Registry) (_checked : (boundary roles).Checked registry)
    (_checkedOther : (boundary roles).Checked other) (order : (boundary roles).Reorders registry other)
    (state : Tracked roles) (root : Occurrence roles) (given : (boundary roles).Initial registry root state) :
    (boundary roles).Initial other root state

theorem reachable_formed (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (reachable : Reachable (boundary roles) registry root state) : GeneralNominalSupportSteps.SourceFormed registry root state

theorem support_pending (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (ready : ¬ GeneralNominalState.RootPending state.current.context.state root.demand)
    (blocked : SupportPending registry state root)
    (noRoot : ¬ GeneralNominalFeedbackK2.RootK2 state.current root)
    (noCandidate : ¬ GeneralNominalFeedbackK2.CandidateK2 registry state.current root) :
    Local registry state root .pending

theorem rootK2_priority (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (cycle : GeneralNominalFeedbackK2.RootK2 state.current root) : Local registry state root .rejected

theorem candidateK2_priority (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (cycle : GeneralNominalFeedbackK2.CandidateK2 registry state.current root) : Local registry state root .rejected

theorem selected_old (selected : Local registry state root (.selected key children)) :
    GeneralNominalFeedbackK2.Local registry state.current root (.selected key children)

theorem selected_supported (selected : GeneralNominalFeedbackK2.Local registry state.current root (.selected key children))
    (support : List (Occurrence roles)) (guard : DecisionGuard state registry root support) :
    Local registry state root (.selected key children)

theorem install_selected {state : Tracked roles} (packet : Packet roles)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (support : List (Occurrence roles)) (guard : GeneralNominalSupportSteps.PacketGuard state packet support) :
    Local registry state packet.site.occurrence (.selected packet.declaration.id packet.children)

theorem whereAccessible_of_readback (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : Tracked roles) (root : Occurrence roles)
    (readback : GeneralNominalCycleReadback.Readback roles registry state.current.context) :
    Acc (Child (B4TargetV3.Local (boundary roles).toSourceBoundary registry state)) root
```


`Yulang.GeneralNominalSupportGrowth` — [module](../../lean/Yulang/GeneralNominalSupportGrowth.lean)

```lean
theorem root_guard : PacketGuard start (packet 0) []

theorem first_install : Step registry (root 0) start added

theorem first_refresh : Step registry (root 0) added observed

theorem formed : SourceFormed registry (root 0) observed

theorem full_models (model : GeneralNominalCommonBridge.Assignment) :
    Models observed.current model ↔ Models (installed 0) model

theorem no_leaves_no_discharge (state : State roleDecls)
    (nonempty : ∀ packet ∈ state.packets, packet.children ≠ []) (focus : Occurrence roleDecls) :
    ¬ Discharged state focus

theorem unresolved (focus : Occurrence roles) : ¬ Discharged observed.current focus

theorem dependency : Generated observed.current (root 0) (child 0)

theorem cut_model (support : List (Occurrence roles)) (allowed : Admissible observed (child 0) support) :
    Slice observed support (finiteModel 0)

theorem child_head_unsupported (support : List (Occurrence roles))
    (allowed : Admissible observed (child 0) support) :
    ¬ HeadSupported observed support 1 (.nominal 0 1)

theorem child_not_ready (support : List (Occurrence roles))
    (allowed : Admissible observed (child 0) support) : ¬ ReadyAt observed support 1

theorem child_guard_blocked (declaration : GeneralDeclarations.Declaration)
    (bounds : List (GeneralNominalInspection.Bounds observed.current.context.state)) (support : List (Occurrence roles)) :
    ¬ Guard observed (child 0) declaration bounds support

theorem child_final_pending : GeneralNominalSupportBoundary.Local registry observed (child 0) .pending

theorem no_modelwise_guarded_rank {Measure : Type u} (less : Measure → Measure → Prop)
    (wellFounded : WellFounded less) (rank : Ty → Measure) :
    ¬ (∀ model, Models added.current model →
      less (rank (model ((child 0).demand.arguments ⟨0,by decide⟩).1).1)
        (rank (model ((root 0).demand.arguments ⟨0,by decide⟩).1).1))
```


`Yulang.GeneralNominalSupportInstallation` — [module](../../lean/Yulang/GeneralNominalSupportInstallation.lean)

```lean
theorem initial_selected_installation (registry : Registry) (context : GeneralNominalCandidates.Context)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry (GeneralNominalSupport.initial context root) root
      (.selected key children)) (nonempty : children ≠ []) :
    ∃ packet : Packet roles, ∃ support,
      packet.site.occurrence = root ∧ packet.declaration.id = key ∧ packet.children = children ∧
      Step registry root (GeneralNominalSupport.initial context root)
        (GeneralNominalSupportSteps.install (GeneralNominalSupport.initial context root) packet support)
```


`Yulang.GeneralNominalSupportExamples` — [module](../../lean/Yulang/GeneralNominalSupportExamples.lean)

```lean
theorem all_source_decisions (root : Occurrence roles) (arguments : ∀ index, root.demand.arguments index = (0,0)) :
    DecisionGuard (start root) registry root []

theorem display_guard : PacketGuard (start displayRoot)
    ⟨registry,context true,GeneralNominalDemandMerging.pointSite displayRoot,display,display_checked,[(0,0)]⟩ []

theorem wrap_guard : PacketGuard (start wrapRoot)
    ⟨registry,context true,GeneralNominalDemandMerging.pointSite wrapRoot,wrap,wrap_checked,[(0,0)]⟩ []

theorem display_exactly_one (key : Nat) (children : List (Occurrence roles)) :
    (GeneralNominalSupportBoundary.boundary roles).Survivor registry (start displayRoot) displayRoot key children ↔
      key = 1 ∧ children = [displayChild]

theorem wrap_child_equation :
    (GeneralNominalSupportBoundary.boundary roles).Survivor registry (start wrapRoot) wrapRoot 2 [wrapChild] ∧
      wrapChild.demand.outputs = [⟨1,itemTarget⟩] ∧
      ¬ GeneralNominalSupportBoundary.SupportPending registry (start wrapRoot) wrapRoot

theorem emitted_inputs_source_supported : Roots (start displayRoot) [] displayChild ∧ Roots (start wrapRoot) [] wrapChild

theorem display_selected : GeneralNominalSupportBoundary.Local registry (start displayRoot) displayRoot
    (.selected 1 [displayChild])

theorem wrap_selected : GeneralNominalSupportBoundary.Local registry (start wrapRoot) wrapRoot
    (.selected 2 [wrapChild])

theorem display_expands : ∃ packet : Packet roles, ∃ support,
    packet.site.occurrence = displayRoot ∧ packet.declaration.id = 1 ∧ packet.children = [displayChild] ∧
    Step registry displayRoot (start displayRoot) (GeneralNominalSupportSteps.install (start displayRoot) packet support)

theorem wrap_expands : ∃ packet : Packet roles, ∃ support,
    packet.site.occurrence = wrapRoot ∧ packet.declaration.id = 2 ∧ packet.children = [wrapChild] ∧
    Step registry wrapRoot (start wrapRoot) (GeneralNominalSupportSteps.install (start wrapRoot) packet support)
```


`Yulang.GeneralNominalSupportExecutor` — [module](../../lean/Yulang/GeneralNominalSupportExecutor.lean)

```lean
theorem final_spec (roles : Roles.RoleDecls) (progress : Progress roles)
    (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : Tracked roles) (root : Occurrence roles)
    (reachable : Reachable (boundary roles) registry root state) :
    B4Target.Steps ((boundary roles).Step registry root) state (finalState roles progress registry state root) ∧
      ∀ next, ¬ (boundary roles).Step registry root (finalState roles progress registry state root) next

theorem diagnostic_eq_resolve (roles : Roles.RoleDecls) (registry : Registry)
    (state : Tracked roles) (root : Occurrence roles)
    (exact : FrontierExact (frontiers roles registry state))
    (accessible : Acc (Child (frontiers roles registry state).Local) root) :
    diagnostic roles registry state root = resolve (frontiers roles registry state) exact root accessible

theorem execution (roles : Roles.RoleDecls) (progress : Progress roles) :
    ∀ r, (boundary roles).Checked r → ∀ s d, Reachable (boundary roles) r d s →
      B4Target.Steps ((boundary roles).Step r d) s ((executor roles progress).run r s d).1

theorem halted (roles : Roles.RoleDecls) (progress : Progress roles) :
    ∀ r, (boundary roles).Checked r → ∀ s d, Reachable (boundary roles) r d s →
      ∀ next, ¬ (boundary roles).Step r d ((executor roles progress).run r s d).1 next

theorem treeExecution (roles : Roles.RoleDecls) (progress : Progress roles) :
    ∀ r (_checked : (boundary roles).Checked r) s d, Reachable (boundary roles) r d s →
      ∀ (exact : FrontierExact (frontiers roles r ((executor roles progress).run r s d).1))
      (accessible : Acc (Child (frontiers roles r ((executor roles progress).run r s d).1).Local) d),
      ((executor roles progress).run r s d).2 =
        resolve (frontiers roles r ((executor roles progress).run r s d).1) exact d accessible

theorem final_reachable (roles : Roles.RoleDecls) (progress : Progress roles)
    (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : Tracked roles) (root : Occurrence roles)
    (reachable : Reachable (boundary roles) registry root state) :
    Reachable (boundary roles) registry root ((executor roles progress).run registry state root).1

theorem final_stable (roles : Roles.RoleDecls) (progress : Progress roles)
    (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : Tracked roles) (root : Occurrence roles)
    (reachable : Reachable (boundary roles) registry root state) :
    (boundary roles).Stable registry ((executor roles progress).run registry state root).1 root ∧
      ∀ child, (boundary roles).Generated registry ((executor roles progress).run registry state root).1 root child →
        (boundary roles).Stable registry ((executor roles progress).run registry state root).1 child

theorem final_models (roles : Roles.RoleDecls) (progress : Progress roles)
    (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : Tracked roles) (root : Occurrence roles)
    (reachable : Reachable (boundary roles) registry root state) :
    ∀ model, (boundary roles).Models ((executor roles progress).run registry state root).1 model →
      (boundary roles).Models state model

theorem saturationTotal (roles : Roles.RoleDecls) (progress : Progress roles) :
    B4TargetV5.SaturationTotal (boundary roles) (executor roles progress)
```

### Item 4f final checks

| Command (repository root unless shown otherwise) | Exit code | Result |
|---|---:|---|
| `cd lean && lake build Yulang.GeneralNominalSupportExamples Yulang.GeneralNominalSupportExecutor` | 0 | Focused dependency closure, all nine new modules; 687 jobs |
| `cd lean && lake build Yulang` | 0 | Full aggregate import build; 1639 jobs |
| `cd lean && lake env lean Audit/GeneralNominalSupport.lean > /tmp/yulang-support-audit.log` | 0 | All 89 new public theorem entries; only propext, Classical.choice, Quot.sound |
| `git diff --check` | 0 | No whitespace errors in tracked changes |

Additional read-only checks confirmed that `lean/Yulang.lean` retains its entire
original byte prefix and adds only nine import lines, and that `lean/Audit.lean`
and `lean/README.md` match HEAD byte-for-byte. The new Lean files contain none of
the prohibited proof escapes. No commit, push, or ref update was performed.

Files added: nine `lean/Yulang/GeneralNominal{PacketSupport,Support,SupportChoices,
SupportSteps,SupportBoundary,SupportGrowth,SupportInstallation,SupportExamples,
SupportExecutor}.lean` modules; `lean/Audit/GeneralNominalSupport.lean`; and
`notes/design/2026-11-12-general-nominal-support-module-guide.md`. Files changed:
append-only imports in `lean/Yulang.lean`, this Item 4f section, and one module-guide
entry in `notes/design/INDEX.md`.

Assessment: this work connects the actual general nominal carriers, checked
registries, packet constraints, emitted identities, feedback steps, and V5 Local;
it is not another scalar or settled-unary substitute. The source examples have
real guarded transitions and the old output-growth fixture now has a supported
pending explanation. That is concrete convergence at the transition interface.
It is not convergence evidence for a completed termination proof until the
finite provenance/readback and sibling-stabilization bridges above are built.

## Item 4g — guarded installation order: administrative closure and a failed rank construction (2026-11-12)

**Status: unconditional progress is not proved.** The guarded boundary remains
`GeneralNominalSupportBoundary.boundary roles`; no existing Step, Stable,
Committed, support, candidate, or evidence definition is changed. This item
closes the administrative accessibility premise for the actual guarded
feedback/reobservation relation. It does not construct its installation order,
prove a necessary cyclic head support, or exhibit a nonterminating Step trace.
The unconditional V5 bridge count remains **6/14**.

### The measure test and the exact results

The proposed source-denotation measure still fails in its “every journal
model” form. The already integrated
`GeneralNominalSupportGrowth.no_modelwise_guarded_rank` applies to a real,
source-supported first installation: a permitted regular model gives the same
parent and child denotation. Passing the support guard does not make every
model finite. K2 tests cycles entailed by the type information, not arbitrary
additional cycles present in one model. This is a failure of that measure,
not of guarded accessibility.

A second candidate was to rank all unresolved external producers. That
relation is not well founded either, even in a very small formed state. The
new fixture uses the existing general declaration, nominal, packet, and
emission definitions:

```yulang
impl Container (list 't):
    type item = 't
impl Wrap (list 't) where Container('t, item = 'b):
    type out = list 'b
impl P (list 'a)
    where Container('a, item = 'z), Wrap('a, out = 'z), P('a)
// Initial demand: P(list(list X)); X's head is unknown.
```

`Wrap` is exactly `GeneralDeclarationExamples.wrap`. The two added declarations
pass the full `GeneralDeclarations.DeclarationChecked`, including universal
capture stability and the output-only check. The binder z appears only in
named child outputs, and each child has the strictly smaller unnamed pattern a.
Thus no new declaration rejection can be inferred from this example. This is
consistent with spec §6.3's normalization, Paterson, and output-only rules.

`GeneralNominalSupportSiblings.first_step` is an actual guarded installation
from an empty-journal InitialSource, not a supplied transition hypothesis.
`first_formed`, `children_generated`, `p_children`, `shared_output`, and
`child_inputs` prove its state formation and exact output. The three children
have the same unnamed interval `(1,1)` (the source node for list X). Container's
item and Wrap's out have the same fresh source identity `out`.

After this one installation the Container and Wrap siblings are both generated
and unresolved. Neither is a generation ancestor of the other, so either
passes `External` as a producer for the other. `Permitted` explicitly collects
all such permitted singleton supports between generated unresolved occurrences.
`sibling_cycle` and `permitted_not_accessible` prove a two-cycle in that
relation. `no_permitted_rank` rules out ranking it with **any** well-founded
order, not just a natural-number depth.

**This is an obstruction only to ranking every permitted edge.** It is not an
obstruction to choosing a useful support explanation. These singleton supports
are redundant: `sibling_heads_source_supported` proves that all three children's
heads already have empty support. In this first snapshot the uninstalled
sibling identities are also absent from the dependency pool; the existing
restriction operation removes them. Consequently these results do **not** show
that the actual guard consumes circular output support, or that progress is
false. Any installation measure must distinguish chosen necessary explanations
from the union of all admissible dependencies.

### Derived administrative accessibility

`GeneralNominalReobservationOrder` extends the old administrative argument to
certified descriptor replacement. The finite basis consists of the old Known,
alias, and ordinary-equality facts, plus `Point source`: an observed nominal
descriptor with coinciding lower/upper endpoints at that source identity.

The basis is computed from the starting snapshot's finite source list and its
already registered named output targets. Merge, refresh, and equality feedback
preserve the site list and keep all sources in this support. Reobservation
preserves the entire base table. Each update establishes a previously false
fact. The new point facts survive every actual update: ordinary refinement
transports them through its source-preserving slot embedding, and descriptor
replacement explicitly preserves every old point descriptor. Injectivity of
source identities turns replacement's new slot fact into a new source fact.
There is no slot-renaming reset, assumed global fact set, or installation bound
in `accessible`.

`GeneralNominalSupportOrder` proves recorded edges and registered generated
occurrences for the exact support-tracked SourceFormed predicate. Hence enqueue
cannot occur in a formed Step. Every such Step is either a `Passive` update
(projecting to the new bounded administrative relation) or one actual enabled,
novel, guarded installation. Passive accessibility lifts through the changing
support ledger; it does not require the ledger itself to stay identical.

`InstallationOrder` now states the precise remaining order obligation for this
relation. Its measure may have any type and any well-founded relation. Passive
steps may preserve or strictly decrease its rank; an enabled guarded
installation at a generated occurrence must strictly decrease it. `accessible`
and `boundary_progress` prove the reduction without assuming a natural-number
budget. The order value itself is still a premise, clearly present in both
statements. Checked and K2 exclusion have not been used to manufacture one.

`empty_models_accessible` proves an additional unconditional case: every formed
state with no Models has Acc for the full guarded Step. Installable contains a
model witness, so no installation can occur; model inclusion preserves
emptiness and the administrative measure handles the remaining updates.

### What still needs proof, and the sibling investigation's limits

The sufficient missing construction is, for every checked registry and root,
an `InstallationOrder registry root` (or a trace-local order with its own proved
accessibility reduction). In particular it must select provenance explanations
that remain bounded across refresh, merge, newly discharged demands, and
installation, and relate every emitted unnamed interval to the substitutions
in `DeclarationChecked.captureStable`. Merely putting a rank on all `External`
edges cannot supply this. Output-only binders must remain excluded from the
Paterson side, as they are in the checked fixture.

The shared-z fixture provides a concrete next test of the stronger grounding
claim, but that test is **not completed** here. After the proved P installation,
the proposed finite continuation is:

1. Install Container(list X,item=out), obtaining out ≈ X and a discharged leaf.
2. Install Wrap(list X,out=out), obtaining out ≈ list B and a pending child
   Container(X,item=B).
3. Install the source-supported P(list X), obtaining a generated P(X).
4. Certify/observe X ≈ list B and test support for P(X) using the unresolved
   Wrap sibling and the discharged Container leaf.

Those three further Installable/PacketGuard/Step derivations, their freshness,
joint-classification and origin obligations, the required refresh, and a proof
that source/discharged-only support is insufficient have **not** been proved.
A suggested continuation by pending Container merges is likewise unverified.
No infinite guarded trace, failure of Acc, or semantic contradiction follows
from the current artifacts.

If this trace is realizable, the implementation bridge to inspect is the
whole unresolved obligation dependency: generation/aliases together with
needed-head support of blocked demands, including provisional equalities
transferred by pending merges. Alternatives must remain existential; taking
all alternatives together creates the false cycle already demonstrated here.
Aliases must be quotiented or treated as equality, not as two strict dependency
edges. This is a proof/implementation investigation under spec §6.3 and draft
addendum 5. It is not evidence for a new language restriction. **No new owner
semantic question is asserted, and no speculative guard replacement is made.**

The existing conditional
`GeneralNominalSupportBoundary.whereAccessible_of_readback` remains available,
with its explicit `GeneralNominalCycleReadback.Readback` premise. This item does
not construct that readback for all reachable states. Progress and
whereAccessible therefore remain open at their required quantifiers.

### V5 fourteen-field table

Boundary: `GeneralNominalSupportBoundary.boundary roles`. Frontiers and executor
are the integrated `GeneralNominalSupportBoundary.frontiers` and
`GeneralNominalSupportExecutor.executor roles progress`.

| Field | Status at the required V5 quantifiers |
|---|---|
| progress | OPEN. `GeneralNominalSupportOrder.boundary_progress` requires an InstallationOrder; empty-model and passive accessibility do not discharge this field. |
| execution | Conditional only on the exact Progress field, via `GeneralNominalSupportExecutor.execution`. |
| halted | Conditional only on Progress, via `GeneralNominalSupportExecutor.halted`. |
| closure | Proved: `GeneralNominalSupportBoundary.closure`. |
| stepModels | Proved: `GeneralNominalSupportBoundary.stepModels`. |
| frontierLocal | Proved: `GeneralNominalSupportBoundary.frontierLocal`. |
| localIdentity | Proved: `GeneralNominalSupportBoundary.localIdentity`. |
| whereAccessible | OPEN. The integrated theorem still requires Readback. |
| treeExecution | Conditional only on Progress, with the exact/accessibility binders present in the target: `GeneralNominalSupportExecutor.treeExecution`. |
| canonicalLocalOrder | OPEN for the guarded executor. |
| dictionaryRefl | Proved: `GeneralNominalSupportBoundary.dictionaryRefl`. |
| evidenceNode | OPEN for this guarded boundary; no new stable emission/evidence bridge is claimed. |
| generatedChildren | OPEN for this guarded boundary; stable guarded installation obligations remain. |
| initialReorders | Proved: `GeneralNominalSupportBoundary.initialReorders`. |

Thus **6/14 unconditional**, with three executor laws conditional only on
Progress. No extra field is counted for an administrative theorem, a fixture,
or a conditional reduction. No SourceBoundary field is newly replaced in this
item; the Item 4f field table still names the concrete thirteen definitions.

### Full new public theorem statements

The signatures below are copied from the new modules. Names and implicit
variables use the namespaces, opens, and concrete fixture definitions in the
linked module; all premises are retained. Proof bodies and private helper
statements are omitted.

`Yulang.GeneralNominalReobservationOrder` — [module](../../lean/Yulang/GeneralNominalReobservationOrder.lean)

```lean
theorem point_sources (point : Point state source) :
    source ∈ GeneralNominalState.sources state.context.state

theorem point_refines (refines : GeneralNominalRefinements.Refines before.context.state after.context.state)
    (point : Point before source) : Point after source

theorem point_at (update : At registry before focus after) (point : Point before source) : Point after source

theorem as_update (update : Update registry before after) : ∃ focus, At registry before focus after

theorem monotone (update : At registry before focus after) (fact : Fact roles) : Holds before fact → Holds after fact

theorem supported_update (start before after : State roles)
    (sites : before.sites = start.sites)
    (sources : GeneralNominalState.sources before.context.state ⊆ support start)
    (update : Update registry before after) :
    after.sites = start.sites ∧ GeneralNominalState.sources after.context.state ⊆ support start ∧
      ∃ fact ∈ facts start, ¬ Holds before fact ∧ Holds after fact

theorem remaining_monotone (basis : List (Fact roles)) (update : At registry before focus after) :
    remaining basis after ≤ remaining basis before

theorem remaining_decreases (basis : List (Fact roles)) (update : At registry before focus after)
    (fact : Fact roles) (member : fact ∈ basis) (old : ¬ Holds before fact) (now : Holds after fact) :
    remaining basis after < remaining basis before

theorem accessible (registry : Registry) (start : State roles) :
    Acc (fun next current => Update registry current next) start
```

`Yulang.GeneralNominalSupportOrder` — [module](../../lean/Yulang/GeneralNominalSupportOrder.lean)

```lean
theorem edges_update (recorded : EdgesRecorded before.current)
    (update : At registry before focus after) : EdgesRecorded after.current

theorem formed_journal (formed : SourceFormed registry root state) :
    EdgesRecorded state.current ∧ ∃ site ∈ state.current.sites, site.occurrence = root

theorem generated_registered (formed : SourceFormed registry root state)
    (generated : Generated state.current root child) : ∃ site ∈ state.current.sites, site.occurrence = child

theorem passive_accessible (registry : Registry) (root : Occurrence roles) (state : Tracked roles) :
    Acc (fun next current => Passive registry root current next) state

theorem formed_step_cases (formed : SourceFormed registry root before) (step : Step registry root before after) :
    Passive registry root before after ∨
      ∃ packet : Packet roles, ∃ support,
        Generated before.current root packet.site.occurrence ∧
        GeneralNominalFeedbackSteps.Installable registry before.current packet ∧
        ¬ GeneralNominalFeedbackSteps.Committed before.current packet ∧
        PacketGuard before packet support ∧ after = GeneralNominalSupportSteps.install before packet support

theorem accessible (order : InstallationOrder registry root)
    (state : Tracked roles) (formed : SourceFormed registry root state) :
    Acc (fun next current => Step registry root current next) state

theorem boundary_progress (roles : Roles.RoleDecls) (registry : Registry) (root : Occurrence roles)
    (order : InstallationOrder registry root) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root state) :
    Acc (fun next current => (GeneralNominalSupportBoundary.boundary roles).Step registry root current next) state

theorem empty_models_accessible (formed : SourceFormed registry root state)
    (empty : ∀ model, ¬ Models state.current model) :
    Acc (fun next current => Step registry root current next) state
```

`Yulang.GeneralNominalSupportSiblings` — [module](../../lean/Yulang/GeneralNominalSupportSiblings.lean)

```lean
theorem p_checked : DeclarationChecked constructors roles p

theorem c_checked : DeclarationChecked constructors roles c

theorem checked : Checked reg

theorem p_query : GeneralNominalInspection.queries src ctx.interpretation p = [.nominal 0 [.variables [0]]]

theorem p_report : report ctx p bs = captured src 0 0 0 (1,1)

theorem sorted : GeneralCanonicalChildOrder.canonicalRequirements p.requirements = [cp,wp,pp]

theorem p_schema : generated reg ctx root p p_checked bs =
    ⟨[⟨2,.source out,.actual⟩,⟨2,.source out,.actual⟩],[],false⟩

theorem p_material (model : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalMaterialization.Models src p
      (GeneralNominalAllocation.capture src reg root.identity p.id (bindings src (report ctx p bs)))
      (report ctx p bs) (generated reg ctx root p p_checked bs) model

theorem p_branch (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models src model) : pk.Holds model

theorem metadata : Metadata reg ctx

theorem initial_source : GeneralNominalSourceFormation.InitialSource reg ctx root

theorem located : arguments ctx root = some bs

theorem p_prepared : Prepared reg ctx root p p_checked

theorem root_ready : ¬ GeneralNominalState.RootPending src root.demand

theorem p_survivor : Survivor reg ctx root p.id pk.children

theorem p_only (d : Declaration) (visible : d ∈ reg.declarations) (role : d.role = root.demand.role) : d=p

theorem selected_old : GeneralNominalFeedbackK2.Local reg start.current root (.selected p.id pk.children)

theorem p_reads : readsMany src (GeneralNominalInspection.queries src ctx.interpretation p) bs = [0]

theorem decisions : DecisionGuard start reg root []

theorem p_guard : PacketGuard start pk []

theorem selected : GeneralNominalSupportBoundary.Local reg start root (.selected p.id pk.children)

theorem p_children : pk.children = [kidC,kidW,kidP]

theorem enabled : GeneralNominalFeedbackSteps.Installable reg start.current pk

theorem first_step : Step reg root start afterP

theorem first_formed : SourceFormed reg root afterP

theorem children_generated : Generated afterP.current root kidC ∧ Generated afterP.current root kidW ∧ Generated afterP.current root kidP

theorem shared_output : kidC.demand.outputs = [⟨1,out⟩] ∧ kidW.demand.outputs = [⟨0,out⟩]

theorem child_inputs :
    (∀ i, kidC.demand.arguments i = (1,1)) ∧
    (∀ i, kidW.demand.arguments i = (1,1)) ∧
    (∀ i, kidP.demand.arguments i = (1,1))
```

`Yulang.GeneralNominalSupportRankObstruction` — [module](../../lean/Yulang/GeneralNominalSupportRankObstruction.lean)

```lean
theorem sibling_generated_identity (first last : Occurrence roles) (above : root.identity < first.identity)
    (reached : Generated afterP.current first last) : last.identity = first.identity

theorem siblings_external : External afterP.current kidC kidW ∧ External afterP.current kidW kidC

theorem siblings_unresolved (focus : Occurrence roles) : ¬ Discharged afterP.current focus

theorem sibling_heads_source_supported : Roots afterP [] kidC ∧ Roots afterP [] kidW ∧ Roots afterP [] kidP

theorem sibling_cycle : Permitted afterP root kidC kidW ∧ Permitted afterP root kidW kidC

theorem permitted_not_accessible : ¬ Acc (Permitted afterP root) kidC

theorem no_permitted_rank {Measure : Type u} (less : Measure → Measure → Prop)
    (wellFounded : WellFounded less) (rank : Occurrence roles → Measure) :
    ¬ (∀ producer focus, Permitted afterP root producer focus → less (rank producer) (rank focus))
```

### Item 4g checks and scope

| Command | Exit code | Result |
|---|---:|---|
| `cd lean && lake build Yulang.GeneralNominalSupportOrder Yulang.GeneralNominalSupportRankObstruction` | 0 | Focused closure of all four new modules; 647 jobs. |
| `cd lean && lake build Yulang` | 0 | Full aggregate build; 1647 jobs. |
| `cd lean && lake env lean Audit/GeneralNominalSupportOrder.lean > /tmp/yulang-support-order-audit.log` | 0 | 52 public theorem entries; dependencies only propext, Classical.choice, Quot.sound. |
| `git diff --check` | 0 | No whitespace errors. |

A separate check verified the entire HEAD byte prefix of `lean/Yulang.lean`,
followed by exactly four new imports; frozen Audit.lean/README.md are unchanged.
The new proof files contain none of the prohibited proof escapes. No commit,
push, or git ref update was performed. The full legacy aggregate audit command
and `tools/verify-lean.sh` were not rerun; the requested new audit part was run.

Files added: the four modules linked above,
`lean/Audit/GeneralNominalSupportOrder.lean`, and
`notes/design/2026-11-12-general-nominal-support-order-module-guide.md`.
Files changed: append-only imports in `lean/Yulang.lean`, this design note, and
a module-guide entry in `notes/design/INDEX.md`.

Workflow: the configured registered prover role/launch surface was unavailable.
The primary constructed a bounded derivation and adjudicated separate read-only
counterexample/probe and review work. No registered prover run is claimed.
Fresh independent reviews accepted the administrative/order reductions and the
fixture's deliberately limited rank obstruction. Kernel checks and the
separate dependency audit are the evidence for the listed theorems.

Assessment: the administrative proof uses the exact general transition relation,
including descriptor replacement and support-ledger changes, so it removes a
real prerequisite rather than proving another scalar fragment. The first-step
fixture also runs on the actual general carrier. These are useful reductions,
but the decisive installation bound has not advanced to a constructed order.
Neither a closed termination theorem nor a concrete divergence has been shown;
Item 4g's primary objective remains unfinished.
