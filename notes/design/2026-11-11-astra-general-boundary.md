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
