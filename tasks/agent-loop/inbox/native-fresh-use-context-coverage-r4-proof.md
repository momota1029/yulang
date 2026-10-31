# NATIVE-FRESH-USE-CONTEXT-COVERAGE/r4 proof handoff

Assignment `/root/native_fresh_use_context_coverage_proof_r4`, revision 1.
Base contract `a7ed1ad46c45c9a69e4db807f874b709716a7265dbe9d00eaa88275c7fbda11c`;
Amendment 01 `d8f5695ff461270e52d6a27bf0f09593a48a65e5fa2f4c5f5c6b77043730d02f`.
Both were ACKed before their respective source-body reads. Requested Sol/high;
observed model and effort UNKNOWN. Leaf proof role, no descendants or coauthors.

Outcome: **constructed, unchecked partial research; native Context coverage
OPEN.** Nineteen named theorem terms were constructed. Neither native
execution-to-projection interpretation nor every-prepared-image observation
across restoration is established. No reachable successful counterexample is
delivered. No native-coverage or parent-theorem closure is claimed.

## Original source claim and corrections

Read the original source-preservation manuscript §§1,3,5 at
`notes/theory/2026-10-13-intrusion-source-preservation-proof.md`, SHA-256
`3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`;
the authoritative correction `notes/design/2026-10-24-birth-level-scc-intrusion.md`
§§2–6, `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae`;
its admitted theory treatment, `67c2a44b7a4009a96424dc329ed4385fffdbc6d6661bf4155408cfbd62de3bfa`;
the inference progress record, `fd5ff5eb032e3fe276deab0213ede2e073fe0f6bf43c32daca19b6e258ba84b1`;
and `docs/yulang-whole-proof-closure-ja.md` §§1,4,5,6,
`17f7518e72f5977b17ce085523adc788ba72a472041555fd18a24da96b4c79a5`.
These bodies were read only after Amendment 01 authorization.

Original scope: every supported source program and lawful finite Simple-sub
history, exact retained extrusion occurrences and signed pairs, immutable
Value birth and induced-level SCC qualification, original lexical/type/event
scopes, one joint admissible witness strategy, publication and independent
lawful uses, recursive monomorphic sharing, full Call and effect hygiene.
Freshening does not create a source reference or extrusion occurrence.
The manuscript's first missing source completeness premise remains the lawful
joint source strategy at its actual generating rule and allocation scopes.

Actual parent `YulangClosure.SourceProblem.InferenceSoundness`, in the pinned
`Contracts.lean`, remains the proposition

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

It is a definition, not a proved instance. No supported source constructor,
quantifier, shared witness or accepted source behavior was changed. The present
finite control projection cannot instantiate this parent or any `LocalLaws`.

## Construction and source mapping

Artifact `notes/theory/lean/YulangClosure/NativeFreshUseContextCoverageR4.lean`,
SHA-256 `442c41c863e33396ea0759acc2e438d41fa2cd09033c2af18d221a1357bd3ace`.
Namespace: `YulangClosure.NativeFreshUseContextCoverageR4`.

This module imports the admitted r3 research module; that module remains
unchecked. R4 retains its `Expr`, `Children`, `Reach` and `Closed` definitions,
including all six native stored constructors and the logical identity case.

`NativeScan` now retains outer remaining roots, the pending `(id,ready)` stack,
verified membership and map keys separately. Native control at
`candidate_context.rs:1566–1672` projects as follows:

- The outer `for root` push becomes `NativeStep.root`.
- `verified.contains(id)` becomes `skip`, using derived verified/key agreement.
- A non-ready non-leaf push becomes `expand`, retaining the ready parent and
  filtering already verified children exactly as the native loop does.
- Successful constructor reconstruction, child lookups, map publication and
  verified insertion become `publish`. Ready-or-leaf and decreasing-child
  guards are retained. Child lookups are immediate constructor guards, not a
  transitive-domain premise.

The invariants prove verified/key agreement, closure, source reachability and
retention of all marked original roots. A completed finite `NativeRun` from
empty map/verified sets yields exact map domain `keys = Reach(children,roots)`
in membership form, plus identity and empty-domain consequences. Arbitrary
sharing, duplicate roots and successful empty runs are represented. No finite
run's existence, allocation success, native termination or Rust extraction is
proved. Native allocation/interner/payload/checkpoint/rollback guards are
erased from this control relation; success of those operations is not supplied
by the projection theorem. Handwritten transcription is not a verified Rust
execution semantics.

Readback at `candidate_context.rs:1090–1097,1182–1221` omits identity from stored
rows, walks nonzero children and selects each constructor's local weight.
`Readback`, `StoredObservation`, `LogicalObservationR4` and `WeightObservation`
reflect that distinction. No stored identity row is fabricated. The local
monotonicity results establish only that previously selected immutable
constructor/weight observations survive growing readback seeds. They do not
assert the seeds grow across the actual consumer.

`renameExpr` spells out every successful constructor reconstruction from
`candidate_context.rs:1618–1631`; `renamed_children` and `renamed_weight` establish
the immediate projection equations by cases. `selected_renamed_weight` has the
explicit immediate publication equation, nonidentity result and selected-target
premises. These premises are accurately conditional and are not established
for all native map entries. In particular, the selected-target premise is not
used to claim the required all-image observation theorem.

## Restoration investigation and remaining premise

The actual driver `candidate_extrusion.rs:967–1070` inserts an authenticated
FreshUse bound, freezes opposite count, then re-reads live canonical owners
and opposite bound indexes. It starts/owns Replay children and drives their
typed drains to completion. It is not merely an append-only bound loop.

`candidate_context.rs:4042–4050` reads **stored** lower/upper contexts and
interns `Replay(lower,upper)` unless both are identity. Its `relation_with_scoped`
at 3062–3100 can reuse an existing relation on equal pair/context/source/scoped
keys; its Context interner at 2630 also reuses constructors. Thus fresh
operation identity alone does not prove that an old source parent cannot be
processed again. `candidate_context_execute_relation` at 3800–3886 executes
filters before endpoint memoization and publishes discharge/residual state
for the processed relation. `post_check_context` at 3297–3302 reads that state.
Stored relation constructor rows themselves remain unchanged by discharge.

Preparation at baseline `candidate_scheme.rs:4417–4448` captures independent
effective roots and performs one empty-map rename. Admission at 4701–4705
re-reads `relation_context(parent)` and looks up that current root in the map.
`candidate_context_fresh_transport_scoped` at 4278–4296 attaches the chosen
context and retains a Transport dependency. Borrowed readback selects stored
constructor rows through selected relations and touching dependency endpoints.

**First unclosed native premise:** interpret successful native loop branches,
actual finite map/verified sets and immutable source context table as the
`NativeRun` states, including the original checkpoint bounds and constructor
lookup outcomes. Owner: primary/native proof intake. The present theorem
improves the control projection but does not discharge this interpretation.

**Next independent native premise:** show that each root captured at preparation
either remains the effective root at its bound's admission or its entire
prepared image is selected through a compensating real dependency/readback
path. This needs the exact reachable interning/canonicalization/typed-drain
history; neither a noninterference assumption nor a local discharge update
suffices. Owner: primary/restoration-native intake. I found no exact successful
reachable counterexample. A possible interner-reuse shape is a Replay child
whose old pair/context/source/scoped key already denotes an old captured
parent, but no admitted successful whole trace realizes that shape here.
That observation is a search direction only, not a counterexample.

The full `CircuitEvidence` fixed-point implementation, mask bounds, weight/View
validation, actual module/local completion and suspended pre-bound route remain
outside these proved terms. A pre-bound suspension supplies no completed
`NativeRun`/post-bound evidence and must stay Partial/Unavailable at the Rust
instrument. Payload correctness, choice of correct map values, returned root,
source/native correspondence, A/B, complete effect hygiene, principality,
inference termination and production stay OPEN. `H_u` remains AUTHORITY_BLOCKED.

## Inputs and verification receipt

Rechecked actual hashes:

| Input | SHA-256 |
| --- | --- |
| Immutable candidate_scheme baseline overlay | `33235b840c42be38be1df634291e309c0d143fa62f412afa633768be9b40aa0e` |
| r4 candidate_context | `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e` |
| r4 candidate_extrusion | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| NativeFreshUseContextCoverageR3 | `735c0711151c4605d40b338792327f30af80e9740cce346b65517df722543d46` |
| NativeFreshScopeTransport | `1827358830b331ea6c4eafccf83279a1294a3df5b889405cf27ee2f95ff49df5` |
| NativeScopeTransformer | `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6` |
| Contracts | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| OriginalEffectHygiene | `926613078f1f3f2e197bff29793b120128f18d3676657af25db72eca47f2c89f` |

Research base `bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d`; primary baseline
`1d59e3accb3d6c2a6ead91ebc0c6a471c671c981`. Rust bodies read from the clean
r4 dependencies and immutable selected-module overlay, never the live sibling
implementation. Root task/rules and proof skill/source-map/execution guide were
read. The project files were read: pin Lean 4.35.0, no external packages,
`-j1 -M1024`; all retain the contract hashes.

**Actual Lean/Lake/checker invocations: 0. Actual versions: NOT RUN.
Kernel-printed theorem types: NOT RUN. Complete transitive axiom audits:
NOT RUN for each of the nineteen declarations below and the unchecked r3
dependency.** The packet reserves all generated caches/scratch and verification
to the primary after independent acceptance; execution was unavailable to this
leaf under that ownership. No runtime/model/checking receipt is invented.

Read-only shell work used `cat`, focused `sed`, `rg`, and `sha256sum`; exit 0
except one initial `rg` argument named nonexistent `SourceProblem.lean` (exit 2);
the parent definition was then read at its actual admitted `Contracts.lean`
locator. Source search found no proof hole, project axiom or bypass; explanatory
comments mention axiom audits. This search is not a transitive axiom audit.

Only the two exact leased paths were written. No scratch/generated/cache
outputs, compiler edits, expected-output changes, task-state changes, root import
changes, dependencies, Git, tests or descendants. Original 800s grant, no renewal;
wall time was not independently instrumented, exact spent seconds UNKNOWN.
Work stopped within the bound by local estimate; all unused time is relinquished,
remaining usable budget 0, heavy-process time 0. Worker STOPPED; writes stopped
on both leased paths at revision 1. Fresh review/checking/integration pending.

## Complete constructed theorem statements

All names below have prefix `YulangClosure.NativeFreshUseContextCoverageR4.`;
the displayed signatures are source text, not kernel-printed types.

```lean
theorem scheduled_member (children verified : List Nat) (id : Nat) :
    id ∈ (scheduled children verified).map Prod.fst ↔
      id ∈ children ∧ id ∉ verified

theorem step_agrees {children : Children} {before after : NativeScan}
    (step : NativeStep children before after) (old : agrees before) :
    agrees after

theorem step_closed {children : Children} {before after : NativeScan}
    (step : NativeStep children before after)
    (old : Closed children before.keys) : Closed children after.keys

theorem step_marked {children : Children} {before after : NativeScan}
    (step : NativeStep children before after) (same : agrees before)
    {id : Nat} (old : marked before id) : marked after id

theorem step_sound {children : Children} {roots : List Nat}
    {before after : NativeScan} (step : NativeStep children before after)
    (old : ∀ id, marked before id → Reach children roots id) :
    ∀ id, marked after id → Reach children roots id

theorem run_invariants {children : Children} {roots : List Nat}
    {before after : NativeScan} (run : NativeRun children before after)
    (same : agrees before) (closed : Closed children before.keys)
    (sound : ∀ id, marked before id → Reach children roots id) :
    agrees after ∧ Closed children after.keys ∧
      (∀ id, marked after id → Reach children roots id) ∧
      (∀ id, marked before id → marked after id)

theorem completed_native_control_domain (children : Children)
    (roots verified keys : List Nat)
    (run : NativeRun children ⟨roots, [], [], []⟩ ⟨[], [], verified, keys⟩) :
    (∀ id, id ∈ verified ↔ id ∈ keys) ∧
      (∀ id, id ∈ keys ↔ Reach children roots id)

theorem completed_control_identity (children : Children)
    (roots verified keys : List Nat)
    (run : NativeRun children ⟨roots, [], [], []⟩ ⟨[], [], verified, keys⟩)
    (identityRoot : 0 ∈ roots) : 0 ∈ keys

theorem completed_control_empty (children : Children) (verified keys : List Nat)
    (run : NativeRun children ⟨[], [], [], []⟩ ⟨[], [], verified, keys⟩) :
    ∀ id, id ∉ keys

theorem identity_has_no_stored_row (expression : Nat → Expr) (seeds : List Nat) :
    ¬ StoredObservation expression seeds 0

theorem identity_logically_observed (expression : Nat → Expr) (seeds : List Nat) :
    LogicalObservationR4 expression seeds 0

theorem seeded_target_observed (expression : Nat → Expr) (seeds : List Nat)
    (id : Nat) (seeded : id ∈ seeds) : LogicalObservationR4 expression seeds id

theorem observed_child (expression : Nat → Expr) (seeds : List Nat)
    {parent child : Nat} (stored : StoredObservation expression seeds parent)
    (edge : child ∈ (expression parent).children) :
    LogicalObservationR4 expression seeds child

theorem observed_constructor_weight (expression : Nat → Expr) (seeds : List Nat)
    {id weight : Nat} (stored : StoredObservation expression seeds id)
    (payload : (expression id).weight = some weight) :
    WeightObservation expression seeds weight

theorem readback_monotone (expression : Nat → Expr) (before after : List Nat)
    (included : ∀ id ∈ before, id ∈ after) {id : Nat}
    (observed : Readback expression before id) : Readback expression after id

theorem weight_monotone (expression : Nat → Expr) (before after : List Nat)
    (included : ∀ id ∈ before, id ∈ after) {weight : Nat}
    (observed : WeightObservation expression before weight) :
    WeightObservation expression after weight

theorem renamed_children (contextMap weightMap certificateMap : Nat → Nat)
    (expression : Expr) :
    (renameExpr contextMap weightMap certificateMap expression).children =
      expression.children.map contextMap

theorem renamed_weight (contextMap weightMap certificateMap : Nat → Nat)
    (expression : Expr) :
    (renameExpr contextMap weightMap certificateMap expression).weight =
      expression.weight.map weightMap

theorem selected_renamed_weight (source target : Nat → Expr)
    (contextMap weightMap certificateMap : Nat → Nat) (seeds : List Nat)
    {id weight : Nat}
    (published : target (contextMap id) =
      renameExpr contextMap weightMap certificateMap (source id))
    (nonidentity : contextMap id ≠ 0) (seeded : contextMap id ∈ seeds)
    (payload : (source id).weight = some weight) :
    WeightObservation target seeds (weightMap weight)
```
