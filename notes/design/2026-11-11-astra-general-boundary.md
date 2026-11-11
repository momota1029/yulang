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
