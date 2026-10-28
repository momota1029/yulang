# NATIVE-IDLE-CHILD-LAUNCH/r5 proof handoff — revision 1

Disposition: **INCOMPLETE, CONSTRUCTED BUT UNCHECKED**. No successful native
Idle/Some-to-Running launch theorem was constructed. The local calculations
below cannot be composed across the first omitted native owner. No parent gate
is closed and no production promotion is supported.

Author: `/root/native_idle_child_launch_r5_proof`, registered `lean_prover`.
Requested model/effort: Sol/high. Observed serving model/effort: UNKNOWN.
Finite grant: 1,000 seconds, no renewal. Exact elapsed worker duration: UNKNOWN;
no duration or unused-budget credit is claimed. No descendants or processes
remain owned by this leaf.

## Contract, inputs and outputs

Contract SHA-256: `dacdb0dac5b36b13d3e1ee3b8ea37d08195668b4e4620a5fba5d7fdd6ca33ecf`.
Amendment 01 SHA-256:
`1f75d1fde7945f7bb937daf26201ca6cb9ffd708182d24186e9fef5b86170687`.
Amendment 02 SHA-256:
`b8be576a1890081f7aa0f8be759e7922941d255a7b1da31ed89a74b1a592c787`.
Each was ACKed before its corresponding body reads/writes. Luna accepted the
initial pin/output ACK; Amendment 02 was admitted at `da169e227`. Source baseline:
`418bde889`. Full contract pin list remains binding; no new dependency is imported.

Changed artifact:
`notes/theory/lean/YulangClosure/NativeIdleChildLaunchR5.lean`, SHA-256
`282e0f68922d3176e0d98aab04e535426cf2558403f2648ee4916ec5bb1644f4`.
The only other changed path is this handoff. No scratch files, root imports,
cache/generated outputs, compiler files, task snapshots, rules or Git refs
were written. The module imports `Std` only. R4 was neither imported nor used
as a transition law or verified evidence.

Verified read pins included:

- `candidate_context.rs`: `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e`.
- `lib.rs`: `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`.
- `NativeDrainOwnership.lean`: `d37edac29dcecc19dd90b91c3095e5385a0657310dcf08d805a8f20672872d18`.
- `Contracts.lean`: `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`.
- Whole-proof manuscript: `17f7518e72f5977b17ce085523adc788ba72a472041555fd18a24da96b4c79a5`.
- Lean README: `8d27e0b90fc04eb8a0a30606a857e564e5269e8e33e72fddbf1190cb6a7072e3`.
- Birth-level correction: `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae`.

## Original parent and corrections

Read the actual original claim in `docs/yulang-whole-proof-closure-ja.md` §1
and actual `YulangClosure.SourceProblem` definitions in `Contracts.lean`
103–155. In particular, `SourceProblem.InferenceSoundness` has unchanged type:

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

`SourceProblem.NativeCorrespondence` separately requires:

```lean
∀ s x n, p.nativeSuccess s x n →
  ∃ d a, p.generates s x d ∧ p.nativeRealizes n d a ∧ p.solves d a
```

These are proposition definitions, not concrete instances. The original whole
source scope includes all accepted constructors, declarations, resolution,
types/effects/profiles, quantifier evidence, generalization/use, complete Call,
protection/release and continuations. No local identity calculation supplies
one shared source witness `e` or a solution `a`.

Read authoritative `2026-10-24-birth-level-scc-intrusion.md` §§1–6: qualification
uses paths entirely inside one immutable-Value-birth induced graph; raw
cross-level reference incidence remains. This correction does not establish
the source-preservation or native-history bridge. Read the pinned annotation
effect-hygiene decision and inference progress note; their open source/native
and effect-policy obligations remain open. No research draft supplies semantic
authority to change them.

## Source audit and exact first omission

`candidate_context_step_replay_child`, context.rs 4097–4121, Idle/Some route:
lookup operation; require Idle, queued=consumed and empty worklist; select child
relation at consumed and construct ack `(id, consumed)`; prepare replay wait;
call start; write frame destination; write operation Running; return More.

The first omitted **successful native branch** is the capacity-growth observer
inside `candidate_prepare_replay_wait`, context.rs 4082–4094. Its
`prepare_replay_ack` helper (2376–2383) may first append an undo snapshot after
fallible reservation. If capacity changed, the caller invokes
`observe_typed_route_capacity(true)` or `sample_f4_resources`. The former,
lib.rs 9253–9266, writes `route_attempt_physical_change` and may write
`incoming_route_event_sample_failed`; sampling also updates execution/resource
observations. These branch writes and fallible prefixes are not modeled by this
module. An appended undo can precede an error. No rollback theorem is supplied.
The local `pushPreparedUndo` starts only at the logical append after successful
reservation and does not assert that the caller reached or passed this boundary.

The remaining launch inventory was inspected to identify downstream owners,
not formalized as a trace:

- `begin_typed_drain`, context.rs 2248–2260: reserve and append 19-field frame,
  return previous vector length. All 19 initializer fields are represented.
  An earlier progress message incorrectly said 22; this handoff and source
  retain the actual count, 19.
- `start_typed_drain`, lib.rs 14186–14231: save processing pair/relation, clear
  both processing fields, clear diagnostics, sample, capture origin index,
  seed relation, retain incoming Some relation, enqueue, then publish receipt.
- Diagnostic clearing, lib.rs 15934–15988, has retained-allocation journal
  replacements, payload counters and scratch-vector clears. Not formalized.
- Seeding, context.rs 3374–3458, may canonicalize pairs, intern source/context/
  transformer/flow/relation, charge scope inventory, update hash heads, link a
  bundle, append an origin, sample resources, and optionally attach formal data.
  The selected caller passes formal=None. No seed-frame preservation is assumed.
- `enqueue_item`, lib.rs 15223–15253, reserves worklist/journal storage, transfers
  the selected replay child (context.rs 2384–2397), updates queued, journals and
  pushes the item. Resource and testing-observer branches also exist. Not proved.
- Passive attribution writes both `frame.source_drain_receipt` and, when its
  predicate matches, `origins[origin_index].source_drain_receipt`, only after
  enqueue success. A seed ID alone is not an authenticated transport witness.
- The final destination and Running writes are local record updates; reaching
  their source program points remains unproved.

## Source-stated theorem surface

All names below have prefix `YulangClosure.NativeIdleChildLaunchR5.`. These are
the source-stated types, **not** Lean-printed or checker-accepted types. Eleven
theorem declarations were constructed. Complete type printing and complete
transitive axiom audit for each: **NOT_RUN**.

1. `selectedItem_of_lookup (id) (op) (relation)`:
   `op.children[op.consumed]? = some relation → selectedItem id op = some
   ⟨op.task, some relation, some ⟨id, op.consumed⟩⟩`.
2. `selectedItem_no_child (id) (op)`:
   `op.children[op.consumed]? = none → selectedItem id op = none`.
3. `preparedUndo_exact (id) (op) (undo)`:
   `pushPreparedUndo id op undo = undo ++
   [⟨id, op.waitingChild, op.queued, op.consumed, op.retired⟩]`.
4. `appendFrame_exact (frames) (task occurrence cause)
   (previousProcessing previousRelation)`:
   `appendFrame frames task occurrence cause previousProcessing previousRelation =
   (frames.length, frames ++
   [initialFrame task occurrence cause previousProcessing previousRelation])`.
5. `initialFrame_saved (task occurrence cause) (previousProcessing previousRelation)`:
   for that computed initializer, conjunction of exact initial/occurrence/cause
   and both saved processing values.
6. `initialFrame_empty (task occurrence cause) (previousProcessing previousRelation)`:
   for that computed initializer, exact current=None, stage=Transport,
   contextConsumed=None, transitions=0, empty replayAcks, completedAcks=0,
   preparedAcks=0, terminalPrepared=false, four dispatch options=None,
   replayDestination=None and sourceDrainReceipt=None.
7. `writeDestination_exact (frame) (ack)`:
   `writeDestination frame ack = { frame with replayDestination := some ack }`.
8. `writeDestination_preserves_payload (frame) (ack)`:
   for the computed destination update, conjunction preserving initial,
   occurrence, cause, both saved processing values and sourceDrainReceipt.
   The exact record equality in declaration 7 exposes every other field too.
9. `writeRunning_exact (op) (ack) (index)`:
   conjunction giving waitingChild=Running ack index and preserving queued,
   consumed, children and retired. The defining update exposes all other fields.
10. `incoming_relation_selected (relation : Nat) (seed : Option Nat)`:
    `selectRelation (some relation) seed = some relation`.
11. `receiptValue_exact (index incoming created selected origin task cause) (ack)`:
    for the computed receipt value, conjunction giving completed=false,
    incomingRelation=some incoming, selectedRelation=selected and replayAck=some ack.

Identity parameters are arbitrary `Nat`; native ownership, task typing, original
source semantics and physical allocator behavior are not interpreted. All 14
native stage tags remain represented. The four dispatch payload options use
identity placeholders; no dispatch body is proved. No accepted source feature
is excluded from the unchanged parent theorem. These are local calculations
with explicit intermediate limitations, not a reduced-language parent result.

## Execution, application and next owner

Read `.agents/skills/yulang-lean-proofs/SKILL.md` and its `sources.md` and
`execution.md` references, root AGENTS/base rules, assigned contract/amendments,
the pinned toolchain/configuration and relevant README instructions. Configured
pin: Lean 4.35.0, `-j1 -M1024`, no external packages. Actual Lean/Lake versions:
**NOT_RUN**. The packet prohibits this leaf from executing Lean/Lake, checker,
builds, tests or formatters; none ran. No checker exit or axiom list is invented.
Read-only `cat`, focused `sed`/`rg`, `sha256sum`, and `apply_patch` succeeded.
No compilation failure evidence exists because no compilation was authorized.

The local calculations identify reusable native initializer/write cuts for a
future authenticated NativeCorrespondence trace. They do not presently apply
to a concrete `SourceProblem` instance. First remaining owner: Luna's next
admitted proof packet must model the capacity-growth resource observation and
its error prefixes inside replay-wait preparation, or authenticate its exact
projection without assuming the desired preservation. Subsequent owners must
prove diagnostic/seed/enqueue/passive-attribution writes before composing the
actual launch. Later Transport/Context/Dispatch completion, restoration,
whole-language inference, effect hygiene, principality and termination remain
OPEN. Independent review and kernel acceptance are pending; no self-certification.

Mutual TODO for Rust lane/primary: keep actual source-driven invocation evidence,
same-ID raw-transformer falsifiers, and successful emission/readback separate
from these local Lean calculations. No Rust result is consumed as a proof.

**Writes stopped:** both exact leased outputs are frozen at this revision.
No further mutation, execution, child launch, scheduling or Git action is pending
from this leaf. Handoff SHA-256 is returned separately to Luna to avoid self-hash.
