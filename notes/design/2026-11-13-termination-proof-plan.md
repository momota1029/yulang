# Item 4h: termination proof plan and the sibling-output obstruction

Status: **Draft; the unconditional proof plan is blocked.**
Date: 2026-11-13. Baseline: integration `cf730f37e`.
Scope: `GeneralNominalSupportSteps.Step` and
`GeneralNominalSupportBoundary.boundary roles`, with their existing definitions.
No Lean is added in this item. A mathematical counterexecution is distinguished
below from the first prefix already checked in Lean.

## Main theorem and measure in ten lines

1. Target T: Checked(r) and SourceFormed(r,d,s) imply Acc(next,current ↦ Step(r,d,current,next),s).
2. SourceFormed starts at the empty-journal InitialSource; K2 and support exclusion are installation premises, not extra assumptions.
3. The intended measure is μ(s) = the number of false monotone progress facts in a fixed finite basis F derived from the initial source and registry.
4. F must cover semantic packet deltas and emitted edges as well as Known, aliases, ordinary equalities, and point-descriptor facts.
5. A normalized, interval-sensitive Paterson budget must first bound all future invocation and source identities to make F finite.
6. Checked supplies strict child descent for fixed captures; it does not supply that budget across changing captures and supports.
7. Administrative accessibility, including descriptor replacement, is already proved without a global installation bound.
8. A new paper-level sibling-output schedule makes unboundedly many fresh invocations pass the current guard while every finite prefix remains consistent and non-K2.
9. Therefore F cannot be constructed for the current relation by this argument; neither a new Nat rank nor a multiset rank repairs the counterexecution.
10. Stop before new Lean: resolve the downstream-cycle deferral scope, then establish the finite-budget construction for the repaired relation.

## 1. Authority, exact quantifiers, and what is not a premise

The governing sources are [spec §6.3](../../spec/06-roles.md) and the
[approved main statement and addenda 1–5](2026-11-08-b4-main-statement-draft.md).
They require normalized Paterson counting; output-only associated binders;
waiting for every unnamed lower head; conjunction of where children;
sibling-order independence; same-input merging even for pending requests;
K2 at a reached/inspected root on a type cycle through explicit arguments; and
lazy treatment of heads justified only by provisional outputs within an
unresolved dependency cycle. Nominal bodies remain opaque. There is no
user-specified resolution-depth limit.

Write `S` for `GeneralNominalSupport.Tracked roles`, `J(s)` for its `current`
journal state, and `s → s'` for
`GeneralNominalSupportSteps.Step registry root s s'`. The exact desired theorem is:

```text
for every roles, registry r, root occurrence d, and tracked state s:
  GeneralDeclarations.Checked r →
  GeneralNominalSupportSteps.SourceFormed r d s →
  Acc (λ next current, GeneralNominalSupportSteps.Step r d current next) s.
```

SourceFormed is an actual finite transition closure of InitialSource, not a
structure containing a rank or accessibility certificate. Its initial
certificate relates role metadata, a finite source table, interval validity,
the seed, and an empty allocation table. The initial journal and support ledger
are empty. An inference-to-InitialSource producer is not proved by these modules.

The theorem quantifies over **all** permitted steps. Showing that one scheduler
halts, choosing not to refresh, or requiring a fair scheduling hypothesis would
not establish this Acc statement. We do not add such a hypothesis. Models need
not be inhabited: the empty-model case is already covered by
`GeneralNominalSupportOrder.empty_models_accessible`.

For the exact guarded boundary, the previous six unconditional V5 bridge fields
remain proved. This prose item changes that count by zero. In particular, the
integrated conditional executor does not supply its own Progress premise.

## 2. A precise sufficient measure, with its unproved input exposed

### 2.1 The finite-budget construction that would be required

Fix an initial state s₀ and registry r. For this fixed finite-fact proof route,
first construct from that data a finite set U of possible source identities
and a finite set I of possible invocation identities, covering every state
reachable from s₀. This is a sufficient route, not a necessary consequence of
Acc in general: an arbitrary well-founded order need not provide a uniform
finite reachable universe.
It must not define U as “all identities eventually generated” and assume that
set finite. Nor can it assume a fixed finite tree denoting every possible model
of an unresolved source variable.

One sufficient intermediate object would be a **finite generation budget**:
a source-fixed natural height H and a predetermined finite forest of potential
invocation origins, labelled with normalized source-pattern constraints. Each
new where invocation must be a child in this forest with smaller remaining
height. Re-observation, merging, equality feedback, and discharge must not
increase that height budget. Repeated installation of the same invocation must
consume a separate finite delta token or be already Committed.

This is stronger than finite initial tokens, bounded child count, and descent
in an arbitrary well-founded order: a token at ordinal ω could still choose
any finite child height, giving no common finite universe. For the proposed
natural-height route, the alphabet of (declaration ID, clause ID) is finite.
With B such possible child choices, paths of length at most H have at most
1+B+⋯+B^H elements. Deterministic origin allocation maps these paths to a finite
I, and the finite `GeneralNominalAllocation.keys` list at each invocation maps
I to a finite U together with the initial sources. The required theorem is
that every actual new invocation follows such a bounded path; that theorem is
not inferred merely from the finite alphabet or from per-snapshot acyclicity.

For genuinely fixed finite patterns, the declaration-side part has an exact
measure. If h and c are the normalized unnamed head and child arguments, and
ρlo, ρhi are their corresponding captures, put

```text
w(h,ρlo,ρhi) = size(normalize(h[ρlo])) + size(normalize(h[ρhi])).
```

`DeclarationChecked.captureStable` gives
`w(c,ρlo,ρhi) < w(h,ρlo,ρhi)` for each where clause. Replacing a parent token by
any finite number of smaller child tokens decreases the usual multiset
extension of `<` on natural numbers. This statement is about **the same pair of
captures** at parent and child, not independently selected labels before and
after feedback. The semantic producer of suitable labels, and a budget for
later refinements of holes in them, are missing. Section 4 gives a reason they
cannot be supplied for the current Step by merely unpacking its guard.

The alternative “support depth, then Paterson size” does not yet define an
order. It needs a source-derived upper bound H on all useful support depths,
so that H−depth is decreasing when support chains lengthen. Without H, reversing
the natural order on depth is not well founded; using the usual order increases
the measure as depth grows. Per-snapshot acyclicity supplies no such H.

### 2.2 Finite signatures, not finitely many packet values

Even if U and I were available, packets contain cached contexts and cannot
simply be enumerated as raw Lean values. The required finite signature of a
packet consists of its registry declaration identity, invocation/obligation
identities, source-indexed captured intervals, finite inspection/projection
report, input and named-output materialization requests, and exact emitted
child demands/edges. Signature equality must imply semantic equivalence of the
new constraints and equality of the emitted children, modulo the separately
retained cached context.

The decomposition already available is:

```text
packet.Holds model ↔
  Models packet.context.state model ∧ Inputs packet model ∧ Outputs packet model.
```

This is `GeneralNominalPacketSupport.packet_exact`. For a newly enabled packet,
its context is the current context. For an old committed packet, its context's
constraints are retained along the trace. Thus a fixed semantic delta can be
reused without demanding equality of its old and new cached context values.

A finite-signature proof still has to bound report and origin lengths by the
finite declaration patterns, translate slot references to U, handle repeated
captures, and include full named requests. `Fresh` deliberately permits reuse
of already allocated origins. Hence “one installation per (occurrence,key)”
is false as a proof premise: later captures or emitted demands may change.
`¬Committed` excludes an identical semantic replay, not every such revisit.

### 2.3 The actual finite-fact measure

Given the missing finite U, I, and signature family Δ, let F contain:

- `Known i` and `Point i` for every source i in U;
- `Alias a b` for every pair of possible invocation identities in I;
- `RawEqual i j` for every pair in U;
- membership of every possible registered site and generated edge;
- `Entailed δ`, meaning every full journal model satisfies semantic delta δ,
  for every δ in Δ.

Point is the **source-indexed** predicate of
`GeneralNominalReobservationOrder`, not a slot index that can change on refresh.
Define

```text
μF(s) = Σ (f in F) if Holds(s,f) then 0 else 1.
```

F is fixed for the entire trace, not recomputed at each state. The sufficient
proof is short once its construction is available:

1. All facts are monotone: journal constraints only remove models, sites/edges/
   aliases grow, Known persists, raw model entailment persists, and Point
   persists even under slot remapping and descriptor replacement.
2. Every formed step establishes a previously false fact in F. Enqueue is
   unavailable. Merge supplies a new alias; refresh supplies new Known;
   equality feedback supplies new RawEqual; reobservation supplies new Point.
3. For installation, if its delta was not entailed, use `Entailed δ`. Otherwise
   `¬Committed` supplies a missing emitted edge. Coverage of δ and that exact
   child demand is essential here.
4. Thus μF(s') < μF(s) for every step s → s'; induction on μF proves T.

The already proved administrative argument also lets us use only installation
fuel as the outer order and administrative Acc as the inner induction, exactly
as in `GeneralNominalSupportOrder.accessible`. This avoids re-proving the
administrative counting but does not construct the outer fuel.

## 3. Lemma ledger and previously formalized obstructions

“Proved” below means the cited Lean theorem has already been checked/audited on
the integration baseline. A paper argument in this note is not assigned that
status. “Missing” never means it may be assumed in the final theorem.

| ID | Exact role in the proof | Status and source |
|---|---|---|
| L0 | Formed states retain their source kernel; full journal models equal source plus recorded deltas. | **Proved:** `GeneralNominalSupportSteps.at_source`, `formed_exact`, `stepModels`, `steps_models`. |
| L1 | Every generated occurrence is registered; formed Step is passive or an enabled novel guarded installation. | **Proved:** `GeneralNominalSupportOrder.formed_journal`, `generated_registered`, `formed_step_cases`. |
| L2 | Administrative updates are accessible without an installation bound. | **Proved:** `GeneralNominalReobservationOrder.accessible`, `GeneralNominalSupportOrder.passive_accessible`. |
| L3 | For any fixed captures, every checked unnamed where pattern is strictly smaller, after normalization. | **Proved:** `GeneralDeclarations.checked_child_descent`; `GeneralNominalCycleReadback.child_decreases` given its explicit readback. |
| L4 | Capture/child readback is sound for intervals and actual projection origins. | **Proved in part:** `GeneralNominalSourceReadback.packet_capture_exact`, `variable_child_origin`, and `GeneralNominalFeedbackSites.origin_sound`; a cost-preserving finite pattern readback is **missing**. |
| L5 | Each useful support has a source-derived, update-stable generation budget; no provisional sibling chain creates new fuel. | **Missing; contradicted for the current guard by the paper schedule in §4.** `source_ready`, `discharged_support`, and `cycle_excluded` prove only the stated local support routes. |
| L6 | The L3–L5 budget bounds all reachable invocation/source identities. | **Missing; cannot be obtained for the current schedule.** Finite initial source identities and injective allocation alone are insufficient. |
| L7 | A bounded identity universe yields finitely many semantic packet-delta and exact child-demand signatures. | **Missing.** `GeneralNominalPacketSupport.packet_exact` is the semantic decomposition, not the finiteness theorem. |
| L8 | A fixed committed packet remains committed; novel installs must add a delta or edge fact. | Fixed-packet persistence is **proved:** `GeneralNominalReobservationSteps.committed_trace`; a general finite-signature novelty/coverage lemma is **missing**. |
| L9 | A fixed finite fact basis strictly decreases its missing-fact count. | **Proved for existing fact carriers:** `GeneralNominalFeedbackProgress.remaining_decreases`, `accessible_of_finite_basis`, and `GeneralNominalReobservationOrder.remaining_decreases`. The Δ-extended coverage in §2 remains **missing**. |
| L10 | An arbitrary installation order plus administrative accessibility gives exact guarded Acc. | **Proved:** `GeneralNominalSupportOrder.accessible`, `boundary_progress`. The order is an explicit premise there. |
| L11 | Every reachable root has an accessible independent Local child relation. | **Missing:** `GeneralNominalSupportBoundary.whereAccessible_of_readback` still assumes `GeneralNominalCycleReadback.Readback`. Step Acc alone is not this theorem. |
| L12 | Rejustification is complete and finitely bounded if added as a transition. | **Missing, and no such free replay rule exists in the current Step.** The current finite alternative enumeration is insertion-time only. |

### Specific failures that the plan must not conceal

**Output growth (4e).**
`GeneralNominalSupportGrowth.child_guard_blocked` handles the direct R example,
so it must remain a regression. However,
`no_modelwise_guarded_rank` already refutes using arbitrary-model denotations
for even the allowed first installation. The minimum-finite-height variant
also fails in the old example:
`GeneralNominalOutputGrowthMeasures.minimum_does_not_descend`.
Selecting a new smallest model after each update changes the measuring object;
it is not a proof that the old rank decreased. The schedule below repeats
output-driven exposure via siblings rather than the prohibited direct parent.

**Redundant producer supports (4g).**
`GeneralNominalSupportRankObstruction.no_permitted_rank` rules out ranking all
permitted external edges. Its two siblings have empty source support as well
(`sibling_heads_source_supported`); the result is not a necessary cyclic-support
counterexample. A repair must choose valid useful explanations existentially.
Unioning every alternative creates spurious cycles. Merely choosing a minimal
alternative does not fix §4: that schedule uses actual necessary Wrap/merge
facts and ever larger finite dependency sets.

**Interval-sensitive readback.**
`GeneralNominalReadbackCounterexample.endpoint_exact_readback_impossible`
refutes exact endpoint reconstruction. The sound existing fact is containment
of actual projected values in capture intervals. Repeated variables combine
lower bounds by union and upper bounds by intersection, with self/cross checks;
there need not be a single endpoint tree playing both roles. L4 must use these
actual origins and prove a cost correspondence, including compound child
materialization and normalized field/tag handling. Replacing centerless
intervals by a chosen substitution would change the model. The new schedule
already uses point intervals throughout, so solving L4 alone cannot stop it.

**Sibling stabilization.**
Stable EOF classification prevents premature final diagnostics; it does not
bound the number of prior information-adding steps. The present installation
rule requires unique applicability, joint alias consistency, and support, but
has no premise that every sibling has a completed dictionary. In the schedule,
Container demands remain pending while their equal outputs are merged, as the
owner's merging decision permits. Delaying final errors or choosing another
processing order cannot prove Acc for the existing relation. No new “all
siblings must discharge” rule is assumed here.

**Rejustification.**
Support alternatives are retained for packets/merges at insertion. They are
not recomputed simply because a committed packet later obtains a different
independent justification. This may prevent resumption; it is not an extra
unbounded transition already present. A future rejustification rule should add
only a previously absent `(semantic delta, finite dependency subset)` fact.
Its bound would then follow from U, I, and Δ. Counting proofs of Discharged is
not a substitute: reflexive alias proof steps can inflate such proofs without
adding solver information. Actual discharge and alternative certificates must
be quotiented or minimized, and alias equivalence must not be counted as two
strict dependency edges.

**Merges, refresh, reobservation.**
These are genuinely handled by L2, including descriptor precision after Known
has stabilized. Refinement may grow the visible tree, so its current tree size
is not an outer decreasing measure. Only a fixed derived budget or the finite
signature basis could make that growth harmless globally. No bound on future
installations follows merely from the fact that every administrative interval
between installations is finite.

## 4. A mathematical infinite schedule for the current guarded relation

### 4.1 Program and exact formal input

Here is a source-level presentation of the declarations and intended demand:

```yulang
role Container 'a:
    type item

role Wrap 'a:
    type out

role P 'a:
    our a.probe () = ()

impl Container (list 'a):
    type item = 'a

impl Wrap (list 'a) where Container('a, item = 'b):
    type out = list 'b

impl P (list 'a):
    where Container('a, item = 'z), Wrap('a, out = 'z), P('a)

my run (xs: list (list 'x)) = xs.probe ()
```

This spelling illustrates the source obligation `P(list(list X))` with unknown
X. It has not been parser-tested, and no inference-to-snapshot theorem is
claimed. The exact formal input is already fixed independently:
`GeneralNominalSupportSiblings.reg`, `ctx`, `root`, and `start`. That module
proves Checked, InitialSource, the first actual guarded installation, exact
children, and the shared output target. Its source graph has

```text
t₀ ≈ list t₁,    t₁ ≈ list t₂,    t₂ unknown.
```

The numeric source IDs are initially 0, 1, 2. All input intervals are `(tᵢ,tᵢ)`.
The normalized view has no structural edges; every nominal body is opaque.
The role names in this note are presentation names for the module's role IDs.

The declarations are permitted by the full general check. Each where input a
has size one, strictly below `list a` of size two; variable occurrences do not
increase. The output-only z is used only in named outputs. The Wrap output-only
b is used only in its associated definition and its Container child's named
output. No output-only variable appears in an unnamed argument.

### 4.2 Deterministic identities and equations

Let Pₙ be a fresh occurrence of `P(tₙ)`. Its canonical installation emits

```text
Cₙ = Container(tₙ₊₁, item = zₙ)
Wₙ = Wrap(tₙ₊₁, out = zₙ)
Pₙ₊₁ = P(tₙ₊₁).
```

The same zₙ occurs in the two named requests because both refer to the parent's
output-only binder. This is exactly the sharing proved by the existing
`shared_output` theorem for n=0; it is not an equation linking an input binder
to a separately allocated named target.

Installing Wₙ emits

```text
Dₙ = Container(tₙ₊₂, item = bₙ),    zₙ ≈ list bₙ.
```

Define the next tail identity by `tₙ₊₃ := bₙ`. Every zₙ, bₙ, and child occurrence
identity is the existing allocation function of its invocation/declaration/
clause/binder origin. The declaration's own named-output target is zₙ;
its output-only binder b has the independent fresh source bₙ.

### 4.3 The infinite schedule

The base phase is:

```text
install P₀;
install C₀, adding z₀ ≈ t₂;
install W₀, adding z₀ ≈ list b₀ and emitting D₀;
refresh t₂ as list t₃, where t₃ = b₀.
```

For n ≥ 1 repeat:

```text
install Pₙ;
merge Cₙ with Dₙ₋₁, adding zₙ ≈ bₙ₋₁ = tₙ₊₂;
install Wₙ, adding zₙ ≈ list bₙ and emitting Dₙ;
refresh tₙ₊₂ as list tₙ₊₃, where tₙ₊₃ = bₙ.
```

No other Container packet is installed. After stage n the information entails
`tᵢ ≈ list tᵢ₊₁` for all 0 ≤ i ≤ n+2; tₙ₊₃ is still an unconstrained tail.
Before stage n≥1, Pₙ already has a known list head, and its children Cₙ/Wₙ have
the known input head at tₙ₊₁. Thus neither the single-candidate rule nor the
multiargument wait rule is used to infer an unknown input from a candidate.
The newly exposed head is inferred from actual installed output equations and
an actual same-input merge.

### 4.4 Support certificates, including retained origins

For j ≥ 0, write

```text
Sⱼ = {C₀, W₀,…,Wⱼ, C₁,…,Cⱼ, D₀,…,Dⱼ₋₁};
Sⱼ = ∅ for j < 0.
```

Use Sₙ₋₂ for Pₙ and its merge, and Sₙ₋₁ for Wₙ. C₀ uses empty support.
These supports entail the required heads by induction:

- Source facts provide t₀ and t₁'s list heads.
- C₀'s retained output fact provides z₀≈t₂ with producer C₀.
- Wⱼ's retained output fact has dependencies contained in `{Wⱼ} ∪ Sⱼ₋₁`
  and provides zⱼ≈list bⱼ.
- For j≥1, the retained merge fact has dependencies contained in
  `{Cⱼ,Dⱼ₋₁} ∪ Sⱼ₋₂` and provides zⱼ≈tⱼ₊₂.
- Therefore `Slice(s,Sⱼ)` entails tⱼ₊₂≈list tⱼ₊₃. Earlier required heads
  follow from the corresponding smaller support sets.

The recursive inspector for `list a` reads only its known root head; a variable
query does not inspect the head of its captured argument. There is exactly one
declaration of each role, so this covers DecisionGuard as well as the surviving
packet's Guard. The output equations follow from the full named schema;
no output has been relabelled as an empty-dependency input fact.

For the merge, actual site provenance matters. Cₙ, emitted by Pₙ, and Dₙ₋₁,
emitted by Wₙ₋₁, both retain the same origin: explicit nominal argument zero of
source tₙ. There is only one relevant capture in each report, so the source
origin choice is unique. Its existence is source-supported for n=1 and
supported by Sₙ₋₂ thereafter. Hence SameInputs holds under that support slice,
not just under the full journal. RecoverySupported is vacuous: these inputs
have retained origins, not missing origins recovered from untracked equations.
This checks the extra MergeGuard introduced in Item 4f.

The existing alternative enumerator retains a restricted version of each
listed support. `slice_restrict`, `alternatives_exists`, and
`merge_alternatives_exists` justify removing irrelevant identities without
changing the entailment. A witness need not match an arbitrary implementation
choice of support; all valid finite alternatives are stored.

Why are these supports Admissible? The generation graph contains the P spine
and, from each Pₙ, edges to Cₙ and Wₙ. Each Wⱼ has only the child Dⱼ. The only
nontrivial alias class created at stage j+1 is `{Dⱼ,Cⱼ₊₁}`. Those Container
occurrences have no installed children. Thus a Wⱼ's generated cone stops in
that Container class; it never reaches a later P or Wrap focus. The C/D support
producers likewise cannot reach those focuses. C₀ is discharged. Consequently
all listed producers satisfy the current definition

```text
External(s,focus,producer) :=
  Discharged(s,producer) OR NOT Generated(s,producer,focus).
```

The lazy check does block Dⱼ/Cⱼ₊₁ from using their ancestor Wⱼ's output.
The schedule does not install them. It instead uses their permitted pending
merge to transmit their equal named outputs to another Wrap sibling.

### 4.5 Models, K2, and every remaining transition premise

Every finite prefix, and each prospective installation used above, has a finite
separating model. After Wₙ set M=n+3 and interpret

```text
tᵢ = list^(M−i) int       (0 ≤ i ≤ M),
zⱼ = tⱼ₊₂,              bⱼ = tⱼ₊₃       (0 ≤ j ≤ n).
```

Use a sufficiently longer tower before a prospective installation. Assign
remaining unconstrained reserved type sources int and rows the empty row.
Captures are single point captures, so self/cross checks are reflexive;
projection constraints are the displayed nominal equations. P's named schema
only shares z with itself. C₀'s item and each installed Wrap's out equation are
satisfied by the displayed assignment. No constraint from an uninstalled
Container body is assumed. SiteHolds follows from the retained actual origins.
Thus all stored packets, ordinary constraints, and site conditions hold.

Distinct tower heights are not equivalent
(`GeneralNominalOutputGrowth.tower_equivalent`). Hence distinct input levels
are not provably equal in the journal. Moreover every journal-entailed nominal
argument edge must also hold in this finite model and strictly decreases tower
height. Structural edges are absent. A directed cycle would give a strict
self-decrease, which is impossible. This is the argument already used by
`GeneralNominalOutputGrowthModels.feedback_acyclic`; here the sources need a
finite renaming rather than being consecutive numbers. It excludes both raw
and journal K2 at every stage. One may not use a cycle in a possible infinite
model, or at an infinite limit of these states, as a K2 fact of a finite prefix.

| Exact obligation | Reason it holds in the schedule |
|---|---|
| Checked / metadata | The three declarations and initial source are the checked general fixture; installations and nominal refresh retain the catalogue and interpretation. |
| Fresh | All new invocation IDs differ. Injectivity of origin encoding separates each new frame from previous frame reservations; initial source IDs lie at or below the seed. No later ordinary source is introduced except old or reserved identities. |
| Linked / located bounds | Inputs are existing point source slots. Named targets are reserved by the emitting frame. Each reserved new tail is added to the finite slot table by refresh before it is needed as a located input. |
| Prepared / request readiness | Each head is the supported unary nominal pattern `list a`, with one variable capture; the generated schemas use supported nominal and variable forms. The displayed finite model witnesses BranchModels. |
| Unique selected Local | There is one declaration per role. The input head is known, its inspection finishes, interval checks hold, and neither form of K2 holds. |
| Both MergesClosed checks | Every installed P or Wrap has a singleton alias class. Other occurrences of its role have different input levels, separated by the finite model. Only the indicated Container pairs have equal inputs. C₀ is the sole Container when it is installed. |
| ChoiceCompatible / Joint | No old packet is in a new P/Wrap alias class; Joint therefore reduces to its one prospective branch and the common finite model. C₀ is also a singleton at installation. |
| `¬Committed` | Each P/Wrap installation emits a new child edge. Before C₀'s installation, z₀ is unconstrained and can differ from t₂, so its leaf output delta is not already entailed. |
| Merge novelty | The two fresh Container occurrences have not already been aliased; alias classes from earlier stages are disjoint. |
| Refresh certificate | The new descriptor records tₙ₊₂≈list bₙ, already entailed by the journal. It retains all old descriptors, adds only the already reserved bₙ slot, preserves full models, and changes tₙ₊₂ from unknown to Known. |
| Generated focus | All installed occurrences and merged Container sites are on emitted paths from P₀. Refresh can use P₀ itself as focus. |
| Step scheduling | No constructor of At requires later Container discharge, a final diagnostic, or a fair scheduler. The schedule uses no enqueue, reobservation, or rejustification step. |

The identity encoding gives infinitely many distinct P invocations, each with
a new generated edge. The construction therefore supplies an infinite chain
of the current transition rules at the mathematical level. There cannot be an
installation order satisfying strict descent on all these steps, even with an
ordinal or multiset measure. This is stronger than the redundant-permitted-edge
obstruction from Item 4g: the Wrap/merge equations here actually expose the next
needed input head.

**Verification boundary.** The general declarations, first P step, emitted
identities/shared target, and supporting elementary lemmas are kernel-checked
on integration. The uniform state family, the later packet/refresh certificates,
and this infinite schedule have not been encoded in Lean. They have been
reviewed against each transition premise on paper; this is not a claim of a
Lean theorem `¬Acc`. This also does not establish failure of Local-child
accessibility at a fixed finite snapshot: its deeper demands can still be
pending. Dynamic Step accessibility and fixed-snapshot whereAccessible are
different obligations. No new Lean lemma is started because the requested
positive proof plan is not solid.

## 5. Scope of the repair: an owner question, not a hidden restriction

The formal issue is now specific: the ancestry-only External test allows a
consumer **downstream of** another unresolved output cycle to use that cycle's
outputs. It is not caused by missing K2 feedback or by nonpoint intervals.
For example, after the first merge, W₀ waits for D₀~C₁, whose input head was
supplied by W₀. P₂ and W₁ can consume W₀'s output without being in W₀'s
Generated cone.

I classify the remaining policy choice as **(b), a semantic scope question**.
Spec §6.3/addendum 5 says the unresolved cycle *contains that child* and names
ancestors/its own outputs. It also gives source constraints and discharged
demands as examples of outside support. That text does not explicitly say
whether a child outside the cycle may use an unresolved cyclic producer's
output. The current guard's permissive answer is incompatible with the desired
universal termination property on the schedule above. The Item 4g suggestion
that outside support is ultimately source/discharged was a proposed measure
invariant to test, not a proved consequence of External; this schedule tests
precisely that implication. It would nevertheless be
a new restriction to silently replace External by “all producers discharged”.
The implementation's provenance machinery must be repaired after this scope is
settled; no declaration rejection or weaker termination theorem is chosen here.

**Question, with the lazy option first.** In the program above, should
`P(X)` and `Wrap(X,out=...)` remain pending when X's list head is supplied only
by the unresolved `Wrap(list X,...)` / `Container(X,...)` output cycle, even
though these consumers are not themselves members of that cycle?

1. **Lazy, recommended:** propagate output-cycle deferral to consumers whose
   only explanations depend on that unresolved cycle. Keep all equations for
   ordinary constraints, same-input merging, and K2. Resume when an independent
   source or discharged explanation exists. Do not reject these declarations.
2. **Consumer-local cycle rule:** permit such downstream use whenever the
   consumer itself is outside the cycle. The current schedule is then permitted;
   universal Acc cannot be recovered without some other owner-approved change.

If option 1 is confirmed as the intended reading of the existing decision, its
implementation should use alternative-sensitive obligation/output provenance,
including the needed-head dependencies of **blocked, uninstalled** requests.
The graph must quotient aliases and retain named-output equalities. Acyclic
provisional sibling explanations should not be rejected merely because another
irrelevant cyclic explanation exists. A source-supported head must always have
the empty explanation. The old direct-R pending and Display/Wrap source-supported
regressions must remain intact.

This proposal blocks the displayed export of a cyclic producer's output; it is
not yet a termination proof for that repaired relation. In particular, finite
acyclic explanation graphs can grow forever unless the L5 generation budget is
proved. The first missing positive lemma to attempt after the scope is settled
is therefore L5 together with L4's capture-cost correspondence, not another
accessibility wrapper around an assumed rank.

## 6. Next proof packet and checks for this design pass

Before positive termination work resumes:

1. Resolve the question in §5, or supply a specific failed transition premise
   in §4. A uniform formal counterexecution would be the strongest independent
   check of this paper analysis, but is not added in this design-only turn.
2. Write the revised semantic support certificate and prove it blocks §4 while
   retaining independent source/discharged explanations and the existing source
   examples. Specify how changed aliases and newly available explanations
   affect it; do not require a scheduler-specific interpretation.
3. Construct the finite generation budget and interval cost correspondence
   from source data. Only then derive U, I, finite delta signatures, and μF.
4. Prove the root Local-child accessibility separately. Existing Readback is a
   consumer contract; it is not itself the source producer required by V5.

No `.lean` file, aggregate import, audit file, frozen README, specification,
plan inbox, or git ref is changed. Consequently no Lean build or audit is
required for newly added code, and none is claimed for this turn. The requested
plan and an INDEX entry are the only repository changes. Checks completed:
`git diff --check` exited 0; a Python documentation check for local Markdown
links, trailing whitespace, the ten-line summary, the INDEX entry, and the
documentation-only change scope exited 0.

Workflow: no registered prover configuration/launch role is available in this
worktree. The primary performed the design derivation with separate read-only
counterexample and proof-plan reviews. No registered prover or kernel-checked
new theorem is claimed. This document is a proposal and obstruction analysis,
not an Authoritative language decision or a completion of B4 clause (1).

## Owner answer (2026-11-13): option 1 (lazy downstream deferral)

The owner chose option 1: consumers whose only explanation for a needed input head depends on an unresolved output cycle defer, even when they are not members of that cycle; equations remain available to ordinary constraints, same-input merging and K2; resume on independent source or discharged support; no declaration rejection. Recorded in spec/06-roles.md §6.3 and B4 draft addendum 6.
