# Item 4k: captured-value provenance and the remaining execution bridge

Status: **Partial. The requested decision of the six-role stress test is open.**
Date: 2026-11-13. Baseline: integration 04dc49b1b.
Scope: additive definitions on the existing general nominal carriers; all old
Lean definitions remain unchanged. The new value-support boundary is a
candidate extension, not a claim that termination or complete provenance has
been established.

## What is established, and what is not

The exact P/W/G/C/D/Extract registry is now Checked, including descent under
all finite captures. Its eight-slot initial source is InitialSource and
SourceFormed for the existing downstream boundary. The inspection computations
are kernel-checked: C/D read the outer list and box heads and the unresolved U
position; they do not inspect the captured A/B tails. The intended sharing of
associated output-only binders is also proved with the real emitter.

**There is still no actual guarded-Step schedule for that program, no theorem
of unbounded generated demands, and no proof that the current guard blocks
it.** The standalone W invocation's old PacketGuard is proved, but Installable
and a Step are not. Those are separate premises, and are not inferred from
Checked, SourceFormed, Finished, or the guard alone. Thus task (1) is unfinished.

An additive, producer-indexed value-support contract now tracks known subterm
heads of generated child inputs, including source identities identified with
retained actual origins by journal equalities. It has source-preservation,
old-relation embedding, general trap-exclusion, and positive-regression proofs.
The original paired stress has **not** been instantiated into its trap theorem;
this is not a proved repair of that concrete execution. Strict nonpoint origins
without an equivalent existing source identity remain a coverage gap.

For L5, semantic head support persists through every actual update, and
per-head depth zero persists through every Step and finite sequence of Steps.
All depths transport through certified observation-only changes. Positive
provisional depths across installations/merges, L6/L7, InstallationOrder,
progress, and unconditional whereAccessible remain open.

## Exact declaration and source fixtures

[GeneralNominalProvenanceDeclarations](../../lean/Yulang/GeneralNominalProvenanceDeclarations.lean)
uses role IDs P=0, W=1, G=2, C=3, D=4, Extract=5, with arities 3/3/3/2/2/1.
Constructor IDs list=0, box=1, int=2 are distinct. W/G expose out; C/D/Extract
expose item. The carrier represents all clauses and equations; no declaration
is replaced by an ad-hoc classifier. Registry Checked includes output-only
scoping, normalization/count checks and StableSmaller for every finite capture.

The source in
[GeneralNominalProvenanceSource](../../lean/Yulang/GeneralNominalProvenanceSource.lean)
is exactly:

~~~text
0 = list 1;  1 = list 2;  2 = A, unknown
3 = list 4;  4 = list 5;  5 = B, unknown
6 = box 7;                7 = U, unknown
root = P((0,0), (3,3), (6,6))
~~~

Every choice of nominal-carrier values A/B/U gives the displayed source model.
The nominal interpretation recognizes both list and box. InitialSource has
finite source identities, checked observations, no preallocated frames, and
an empty initial journal. It contains no rank or generation-bound premise.

| Declaration at the recorded bounds | Actual head reads | Report |
|---|---|---|
| P on 0,3,6 | 0,1,3,4 | Finished |
| W on 1,4,6 | 1 | Finished |
| G on 4,1,6 | 4 | Finished |
| C on 4,6 | 4,6,7 | blocked exactly at (7,7) |
| D on 1,6 | 1,6,7 | blocked exactly at (7,7) |

Root readiness separately requires every unnamed lower head, including
variable positions; these read lists are not the whole root-readiness test.
The leaves 2,5,7 are unknown in this initial observation. C/D report blocking
is not a final EOF classification theorem.

The standalone wRoot is W((1,1),(4,4),(6,6),out=2), with its own empty-journal
wStart. w_initial_source, w_located, and w_source_guard are proved. It is not
asserted to be a generated occurrence of the P trace. No new Installation
module or execution certificate exists for it.

## Additive value support and its scope

[GeneralNominalValueSupport](../../lean/Yulang/GeneralNominalValueSupport.lean)
defines ProperWaiting as an unresolved waiting path containing at least one
actual generation edge. Waiting before/after that edge may use aliases; paths
stop at discharged demands. The added Need is indexed by both the producer
being justified and the waiting focus.

- Old needed-head obligations remain, including the producer itself.
- Additional value obligations require ProperWaiting. They include every
  available head along the existing normalized journal path from a generated
  child's unnamed lower input.
- Retained input origins are also followed when the journal proves Realizes:
  the observed value equals an existing source identity. The same normalized
  path can then expose its known subterm heads.
- Paths range over certified refresh/reobservation views and use the existing
  structural and actual explicit nominal-argument edges. Nominal bodies supply
  no edges. Unknown subterms supply no head and are not rejection reasons.
- Grounded recursively justifies the producers in a chosen support alternative.
  The alias, source, discharged, and trap results are re-proved for this stronger
  contract. Forgetting extra needs recovers the old Grounded and guard.

This is motivated by spec §6.3 / draft addenda 5–6 and the explicit Item 4k
instruction to retain value provenance through captured binders. In the paired
stress, the intended new dependencies are W→C's input list B→B's G-supported
head, and G→D's input list A→A's W-supported head. These paths and the necessary
cut models must still be constructed on an actual reached prefix. The general
mutual_value_trap theorem does not supply that construction.

A deliberately broader rule was rejected during review: scanning all subterms
of the producer's own input would defer W merely because an unused captured x
later became known from W's output. For example:

~~~yulang
impl W (list 'x, 'm) where C('m, item = 'u):
  type out = list 'u
~~~

The constructor of x is not inspected, passed into C, or used in out. The final
new rule therefore requires the real child-generation edge. It does not use
child != producer as a shortcut, since aliases can return to the same request.
need_without_child_path proves that without such a path the needs are exactly
the old needs. No broader own-input deferral decision is adopted.

### Nonpoint values and source correspondence

Realizes uses the existing SameOrigin relation, with the entire journal's
Models, between a retained origin and an existing source identity. Two sufficient
bridges are proved:

1. A registered site's retained origin plus journal equality of its endpoints
   identifies the value with the lower endpoint.
2. An installed packet's actual-mode materialization equates a named source
   with a retained capture origin, even if the capture interval is not a point.

Neither bridge chooses a center or searches for a substitution. Ordinary Fits
alone is not treated as equality. A strict nonpoint origin for which no source
identity is provably equal to the actual value is **not covered** by the new
source-indexed subterm rule. General coverage would require origin-indexed
head/projection support or a proved producer of the needed correspondences.
No theorem here says every capture has Realizes.

The HeadCertificate helper constructs a finite certified observation witness
from an entailed nominal equation between two existing, distinct identities.
Its private two-slot snapshot is not installed in the solver and allocates no
tracked source. It does not prove a certified refresh exists.

## Transition integration and regressions

[GeneralNominalValueSteps](../../lean/Yulang/GeneralNominalValueSteps.lean)
strengthens only the installation support guard. It retains all old installed
support alternatives, including alternatives not certified by the new Grounded;
future use must pass the new guard. Ordinary equations, named-output merges,
K2, and administrative updates are unchanged. The model law is inherited via
an exact embedding into downstream Step. Formation contains no new budget.

[GeneralNominalValueExamples](../../lean/Yulang/GeneralNominalValueExamples.lean)
proves actual new-relation installations for Display(list int), Wrap(list int),
and the previous three-role P→Container→Wrap prefix. That prefix still blocks
the unsupported downstream head. The earlier R first installation and refresh
are SourceFormed under the new relation, and its child is pending. These are
regressions for the established fixtures, **not** the new six-role P test.

The new boundary preserves full-journal K2 priority, independent Local and
survivors, named equalities and the old evidence predicate. Unsupported
expansion remains inspection-pending. Its laws do not certify complete
value-provenance coverage or termination.

## L5–L7 ledger and V5 count

Define HeadDepth(registry,state,n,identity,test) as existence of a semantic head
support whose producer obligations all have AtDepth n. Depth zero means that
all such producers are already discharged; empty source support also qualifies.
It is independent of pool size and of which observation is cached.

[GeneralNominalValueBudget](../../lean/Yulang/GeneralNominalValueBudget.lean)
proves persistence of semantic HeadSupported and of discharge through every
actual update. Added facts only restrict every fixed support slice; the tracked
source is unchanged. Packets, sites, and aliases persist. Consequently
zero_depth_step and zero_depth_steps preserve this per-head bound through
installations, merges, refreshes, equality feedback, and reobservation.

[GeneralNominalValueObservation](../../lean/Yulang/GeneralNominalValueObservation.lean)
proves transport at arbitrary depths through certified observation-only views.
ProperWaiting transports because the journal is fixed; every after-view need
was already covered by the before-view's quantification over future views.
Neither result bounds newly generated heads or positive provisional depths
through installations/merges.

| Plan item | Status |
|---|---|
| L1 formed-step analysis | Existing downstream analysis remains available through the new step/formation embedding |
| L2 administrative accessibility | PROVED for the new relation: ValueSteps.passive_accessible |
| L3 fixed-capture descent | PROVED on integration and now explicitly for the six stress declarations |
| L4 interval-sensitive finite readback | MISSING; Realizes sufficient cases are not general finite readback |
| L5 per-head generation budget | PARTIAL: depth zero for all Steps; all depths for View; provisional depths/new-head budget MISSING |
| L6 bounded future identities/signatures | MISSING; no source-derived bound or expansion-sharing proof |
| L7 finite semantic packet signatures | MISSING |
| L8 persistence/novelty | Semantic head/discharge persistence proved here; finite-signature coverage remains MISSING |
| L9 finite missing-fact measure | Existing conditional scheme, no global basis constructed |
| L10 installation order / progress | MISSING construction; no new unconditional Acc result |
| L11 root child accessibility | Conditional on explicit Readback in ValueBoundary.whereAccessible_of_readback |
| L12 bounded rejustification | MISSING; no new replay rule introduced |

Exact new boundary: GeneralNominalValueBoundary.boundary roles.
The old GeneralNominalDownstreamBoundary.boundary is unchanged.

| V5 field | New value boundary |
|---|---|
| progress | OPEN |
| execution | OPEN; no executor instantiated for this boundary here |
| halted | OPEN |
| closure | PROVED |
| stepModels | PROVED |
| frontierLocal | PROVED |
| localIdentity | PROVED |
| whereAccessible | OPEN without Readback |
| treeExecution | OPEN |
| canonicalLocalOrder | OPEN |
| dictionaryRefl | PROVED |
| evidenceNode | OPEN for this boundary |
| generatedChildren | OPEN for this boundary |
| initialReorders | PROVED |

The count is six unconditional fields for each boundary; there is no increase
in the original target's field count. Existing progress-conditional executor
results were not silently retagged as theorems for the new boundary.

## Exact next obligation

The immediate missing bridge is a *concrete reached prefix*, not another
abstract support or order structure. Starting from ProvenanceSource.start,
construct the P packet's full Installable certificate, its actual emitted
frames/sites, both Extract leaf installations, W/G installations, and the
journal-certified observation changes. Then either exhibit a failed old guard
premise or construct the induction giving unbounded new demands. On any reached
paired prefix, derive the two value paths, unresolved waiting children and cut
models required by mutual_value_trap; only then claim that the new guard blocks
this specific test.

No further owner question is justified by the present proof status. No actual
counterexecution beyond the existing decisions has been established, and no
new declaration restriction, global merge priority, or scheduling assumption
is adopted. The main requested decision and the general budget remain open.

## Principal theorem statements

Names below use their module namespaces and imported fixture abbreviations.
These are complete hypotheses/conclusions of the principal additions. Every
public theorem, including supporting lemmas, is included in the separate audit.

### GeneralNominalProvenanceDeclarations

~~~lean
theorem checked : Checked registry

theorem p_emitted_outputs (invocation : Nat) (capture : Capture)
    (allocate : (clause : Clause) → Allocation roles clause) :
    ((emitAll invocation p p_checked.signature capture allocate).map (fun emission => emission.demand.outputs)) =
      [[⟨1,capture.outputs 3⟩],[⟨0,capture.outputs 3⟩],
       [⟨1,capture.outputs 4⟩],[⟨0,capture.outputs 4⟩],[]]

theorem w_emitted_inputs (capture : Capture) (allocation : Allocation roles childW) :
    (childDemand p childW (p_checked.signature.2.2.2 childW (by simp)) capture allocation).arguments =
      (fun index => if index.val = 0 then allocation.arguments ⟨0,by decide +kernel⟩
        else if index.val = 1 then allocation.arguments ⟨1,by decide +kernel⟩ else capture.inputs 2)

~~~

### GeneralNominalProvenanceSource

~~~lean
theorem initial_source : GeneralNominalSourceFormation.InitialSource registry context root

theorem formed : GeneralNominalDownstreamSteps.SourceFormed registry root start

theorem source_models (a b u : Ty) : GeneralNominalState.Models state (model a b u)

theorem p_reads : GeneralNominalSupport.readsMany state
    (GeneralNominalInspection.queries state interpretation p) pBounds = [0,1,3,4]

theorem w_reads : GeneralNominalSupport.readsMany state
    (GeneralNominalInspection.queries state interpretation w) wBounds = [1]

theorem g_reads : GeneralNominalSupport.readsMany state
    (GeneralNominalInspection.queries state interpretation g) gBounds = [4]

theorem c_reads : GeneralNominalSupport.readsMany state
    (GeneralNominalInspection.queries state interpretation c) cBounds = [4,6,7]

theorem d_reads : GeneralNominalSupport.readsMany state
    (GeneralNominalInspection.queries state interpretation d) dBounds = [1,6,7]

theorem c_blocked : (GeneralNominalRecursiveCandidates.report context c cBounds).blocked = [(7,7)]

theorem d_blocked : (GeneralNominalRecursiveCandidates.report context d dBounds).blocked = [(7,7)]

theorem w_source_guard : GeneralNominalSupportChoices.PacketGuard wStart wPacket []

~~~

### GeneralNominalValueSupport

~~~lean
theorem need_without_child_path (absent : ¬ ProperWaiting state.current producer focus) :
    Need registry state producer focus identity test ↔
      GeneralNominalDownstreamSupport.Need registry state focus identity test

theorem grounded_old (grounded : Grounded registry state producer) :
    GeneralNominalDownstreamSupport.Grounded registry state producer

theorem point_origin_realizes (state : State roles) (site : GeneralNominalDemandMerging.Site roles)
    (member : site ∈ state.sites) (index : Fin (roles site.occurrence.demand.role).arity)
    (origin : GeneralNominalRecursiveInspection.Origin)
    (recorded : site.inputs[index.val]? = some (some origin))
    (equal : GeneralNominalFeedbackSites.EndpointEqual state (site.occurrence.demand.arguments index)) :
    Realizes state origin (site.occurrence.demand.arguments index).1

theorem materialized_origin_realizes (state : State roles) (packet : Packet roles)
    (member : packet ∈ state.packets) (name identity : Nat)
    (entry : (⟨name,.source identity,.actual⟩ : GeneralNominalMaterialization.Use) ∈
      (GeneralNominalPacketSupport.namedSchema packet).variables)
    (captured : GeneralNominalRecursiveInspection.Capture packet.context.state)
    (present : captured ∈ (GeneralNominalPacketSupport.report packet).captures)
    (same : name = captured.name) (origin : GeneralNominalRecursiveInspection.Origin)
    (recorded : captured.origin = some origin) : Realizes state origin identity

theorem mutual_value_trap (registry : Registry) (state : Tracked roles)
    (first second : Occurrence roles)
    (unresolved : ∀ producer, producer = first ∨ producer = second → ¬ Discharged state.current producer)
    (returns : ∀ producer, producer = first ∨ producer = second → ∃ child,
      Waiting state.current producer child ∧ ¬ Discharged state.current child ∧
      ∃ identity test, Need registry state producer child identity test ∧
        ∀ support, HeadSupported state support identity test →
          ∃ dependency ∈ support, dependency = first ∨ dependency = second) :
    ¬ Grounded registry state first ∧ ¬ Grounded registry state second

theorem child_value_trap (registry : Registry) (state : Tracked roles)
    (producer child : Occurrence roles) (unresolved : ¬ Discharged state.current producer)
    (waiting : Waiting state.current producer child) (openChild : ¬ Discharged state.current child)
    (proper : ProperWaiting state.current producer child)
    (index : Fin (roles child.demand.role).arity) (identity : Nat) (test : Test)
    (path : GeneralNominalFeedbackK2.Path state.current (child.demand.arguments index).1 identity)
    (known : Available state identity test)
    (necessary : ∀ support, HeadSupported state support identity test → producer ∈ support) :
    ¬ Grounded registry state producer

theorem nominal_support_requires_producer (state : Tracked roles) (producer : Occurrence roles)
    (model : GeneralNominalCommonBridge.Assignment) (cut : CutModel state producer model)
    (identity name arity : Nat) (scalar : (model identity).1 = .base .int)
    (support : List (Occurrence roles))
    (supported : HeadSupported state support identity (.nominal name arity)) : producer ∈ support

~~~

### GeneralNominalValueSteps

~~~lean
theorem step_old (update : Step registry root before after) :
    GeneralNominalDownstreamSteps.Step registry root before after

theorem stepModels (update : Step registry root before after) (model : GeneralNominalCommonBridge.Assignment)
    (valid : Models after.current model) : Models before.current model

theorem closure (halted : ∀ after, ¬ Step registry root state after) :
    Stable registry state root ∧ ∀ child, Generated state.current root child → Stable registry state child

theorem passive_accessible (registry : Registry) (root : Occurrence roles) (state : Tracked roles) :
    Acc (fun next current => Passive registry root current next) state

~~~

### GeneralNominalValueBudget

~~~lean
theorem step_head (update : Step registry root before after)
    (supported : HeadSupported before support identity test) : HeadSupported after support identity test

theorem zero_depth_step (update : Step registry root before after)
    (known : HeadDepth registry before 0 identity test) : HeadDepth registry after 0 identity test

theorem zero_depth_steps (path : B4Target.Steps (Step registry root) before after)
    (known : HeadDepth registry before 0 identity test) : HeadDepth registry after 0 identity test

~~~

### GeneralNominalValueObservation

~~~lean
theorem head_depth_nonincreasing (state : Tracked roles) (view : View state.current after)
    (known : HeadDepth registry state depth identity test) :
    HeadDepth registry {state with current := after} depth identity test

~~~

### GeneralNominalValueExamples

~~~lean
theorem actual_sibling_prefix : B4Target.Steps
    (GeneralNominalValueSteps.Step GeneralNominalSupportSiblings.reg GeneralNominalSupportSiblings.root)
    GeneralNominalSupportSiblings.start GeneralNominalBudgetPrefix.afterW

theorem r_child_pending : GeneralNominalValueBoundary.Local GeneralNominalOutputGrowth.registry
    GeneralNominalSupportGrowth.observed (GeneralNominalOutputGrowthPackets.child 0) .pending

~~~

## Checks and changed files

| Command | Exit code | Result |
|---|---:|---|
| cd lean && lake build Yulang.GeneralNominalProvenanceSource Yulang.GeneralNominalValueBudget Yulang.GeneralNominalValueExamples Yulang.GeneralNominalValueHeadCertificate | 0 | Focused closure of all ten new modules, 669 jobs |
| cd lean && lake build Yulang | 0 | Aggregate build, 1846 jobs |
| cd lean && lake env lean Audit/GeneralNominalValueProvenance.lean > /tmp/yulang-value-provenance-audit.log | 0 | 133 public theorem entries; only permitted dependencies |
| git diff --check | 0 | No whitespace errors |

A final scope check confirmed ten additive modules, exact public-theorem/audit
coverage, append-only Yulang imports, permitted audit dependencies, and valid
links in both new notes. Independent read-only review confirmed the theorem
limits and documentation ledger; a truncated displayed theorem statement was
corrected. No existing implementation file was edited.

All new public theorems are listed in
[the audit part](../../lean/Audit/GeneralNominalValueProvenance.lean).
Development builds exposed ordinary elaboration errors; the final commands
above pass. No full legacy audit, tools/verify-lean.sh, Rust/parser tests,
source-inference producer, six-role execution, or unconditional budget was
verified. The actual earlier positive traces are distinguished above from the
new initial fixture and conditional trap theorems.

Added: ten Lean modules, the audit part, this note, and the small
[module guide](2026-11-13-general-nominal-value-provenance-module-guide.md).
Changed: ten appended imports in Yulang.lean, an Item 4k pointer in the main
general-boundary note, and the design INDEX entries. Existing Lean definitions,
frozen Audit.lean/README.md, specification, plan inbox, lake configuration,
and git refs are unchanged.

Workflow: the registered prover configuration and callable prover role remain
unavailable. The primary constructed bounded support/transition/budget
lemmas; a separately leased regression agent constructed declarations and the
source fixture. Independent read-only reviews checked the source paths,
semantics and theorem limits, caught the overbroad own-input rule before it
was retained, and rebuilt the final bounded results. No registered prover run
or closure of the requested stress-test decision is claimed.

Assessment: these additions use the existing general declaration checker,
nominal source model, real emitter, support ledger, and transition constructors.
They are not a parallel scalar classifier. They make the suspected missing
value dependency precise and preserve useful regressions, but are not yet
convergence to a completed termination proof: the decisive execution/cut-model
bridge and generation budget are still absent. The next result must close that
bridge, not count these six unchanged boundary laws again.
