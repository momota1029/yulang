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
