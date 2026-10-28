# NATIVE-LAUNCH-PROJECTION/r6 proof handoff

Assignment `native-launch-projection-r6-proof`, revision **1**, frozen on submission.
Author `/root/native_launch_projection_r6_proof`; no contributors or descendants.
Contract SHA-256 `01236acb3ef9134788e58aa888ec7d498ddd24fa9f64250c4f1fc2837f03034a`.
Amendment 01 SHA-256 `770332723483bb646936c71eb4bf7e83e9dfaf5ee6cf9898ff0bbefe98ff5296`.
Baseline label `7b3ad7074`, relying on primary's archive receipt; no Git command ran.
Requested Sol/high; observed effective model/effort **UNKNOWN**. Current identity and
work are evidenced by this tool-backed assignment, not a configuration activation.

Outcome: **constructed, unchecked candidate footprint model; bounded launch incomplete**.
No theorem is reported kernel-accepted, axiom-audited, independently reviewed,
source-corresponding or production-authoritative. There is no parent closure claim.

## Frozen output and scope

Only changed source:
`isolated/native-launch-projection-r6/notes/theory/lean/YulangClosure/NativeLaunchProjectionR6.lean`
SHA-256 `eb4c5c99fee13689b4c7ee4b9cf7668ec39416e3259ed826c44204c78fc7ea13`.
The other write is this handoff. No scratch, generated, compiler, root-import,
manifest, toolchain, question, configuration, other inbox or shared-state writes.

The module imports only `Init`, not R5 or NativeDrainOwnership. Its native handles
are abstract Nat names and opaque record images; an injective native encoding has
not been constructed. Task constructors retain Value and Effect lanes. They are
not a smaller source typing language or a definition of typing as safety.

## Governing source and unchanged parent

Read original whole-closure specification `docs/yulang-whole-proof-closure-ja.md`
§§1,6; actual `YulangClosure.SourceProblem.InferenceSoundness` and
`YulangClosure.SourceProblem.NativeCorrespondence` in `Contracts.lean`; original
source-preservation manuscript `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`
§§1,3,5; accepted immutable Value-birth SCC correction §§2–6; effect-hygiene
policy §1; relevant Lean README and progress boundaries. The original manuscript's
cross-level qualification example is historical under the birth-level correction.
Drafts and prior receipts are not semantic authority.

Original parent type is unchanged:

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

It retains every supported source, lexical/type/event scopes, complete Call,
effects, polymorphism, shared recursive resources and one joint witness. The
manuscript §5 still requires a lawful joint source strategy across demand,
publication and independent uses. Event provenance alone does not supply it.
`SourceProblem` roots are proposition definitions; no concrete instance is
constructed here. NativeCorrespondence remains independently OPEN.

Parent application: the candidate can eventually justify erasing particular
resource-owner writes from a launch-evidence projection while preserving error
exits. It presently yields no concrete source derivation, solved constraint,
shared witness, native success or whole-language theorem. Luna/proof intake owns
all remaining parent/source/native bridges.

## Input authentication and read/write collision

Before source body reads/writes, Python hashlib compared the base contract itself
and all 26 Rust/Lean/proof table entries: every SHA matched, command exit 0.
An explicit ACK was sent to Luna. Three read paths were also Rust output leases.
Luna subsequently ordered a source-read pause because the Rust lane was writing
those paths. No Lean/output had been written at that pause; no mixed interval
was retrospectively authenticated. This was a dependency/read-set defect, not a
mathematical counterexample or proof failure. Initial body observations from
shared context are not treated as baseline evidence.

After amendment 01, a separate hashlib command (exit 0) matched the amendment and
all five added pins BEFORE new body reads; an explicit ACK was sent. Context
helpers, begin frame, Idle branch and seed bodies were then reread exclusively
from the immutable proof-input copy. The mutable R6 Rust outputs were not used
again. Earlier lib/candidate_effect observations were independently pinned and
outside Rust write leases. No baseline/Rust source was mutated by this worker.

Direct immutable dependencies:

- proof-input `candidate_context.rs`: `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e`;
  `candidate_scheme.rs`: `35c58dca3748595e273cd53bfba07da2be3fd340ec63c56f6a18adea5e514fb1`;
  `candidate_extrusion.rs`: `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61`.
- R6 snapshot `lib.rs`: `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`;
  `candidate_effect.rs`: `7c8e4fe5270fd45cecece80dfbbdff81aa8f294546687938bf89212325fc146b`.
- Original scope manuscript: `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`.
- `Contracts.lean`: `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`.
- Snapshot NativeDrainOwnership: `d37edac29dcecc19dd90b91c3095e5385a0657310dcf08d805a8f20672872d18`.
- Birth correction: `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae`;
  effect policy: `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`.
- Frozen Astra handoff: `c8ca2b528fcaf4b62c578535cfbe570db92dfa47cae5d1c025c0fd4b0072482d`,
  read only as a non-authoritative lead. Context claims were independently reread.

Other initial dependency hashes remain the exact 26-entry base-contract table;
ACK does not certify their mathematical content. No dependency installation ran.

## Constructed declarations and precise limits

Namespace prefix for every name below is
`YulangClosure.NativeLaunchProjectionR6.`. The following are **source-stated
types**, not printer output. All seven `#print` and seven `#print axioms` commands
are embedded in the leased module for the verification owner; NONE has run.

```lean
resourceWrite_projection (s : State) (w : ResourceWrite) :
  pi (w.apply s) = pi s
resourceTrace_projection (s : State) (ws : List ResourceWrite) :
  pi (applyWrites s ws) = pi s
sample_projection (s : State) (p : SamplePlan) :
  pi (sample s p).state = pi s
observeCapacity_projection (s : State) (p : SamplePlan) :
  pi (observeCapacity s p).state = pi s
appendUndo_projection (s : State) (id : Nat) (op : Operation) (capacity : Nat) :
  pi (appendUndo s id op capacity) = pi s
prepare_projection (s : State) (id : Nat) (p : PreparePlan) :
  pi (prepare s id p).state = pi s
beginAndClearProcessing_exact (s : State) (item : Item)
    (occurrence cause capacity : Nat) :
  (beginAndClearProcessing s item occurrence cause capacity).operations = s.operations ∧
  (beginAndClearProcessing s item occurrence cause capacity).queue = s.queue ∧
  (beginAndClearProcessing s item occurrence cause capacity).frames =
    s.frames ++ [newFrame s item occurrence cause] ∧
  (beginAndClearProcessing s item occurrence cause capacity).processing = none ∧
  (beginAndClearProcessing s item occurrence cause capacity).processingRelation = none
```

`runPrefix` computes operation lookup, Wait branch, cursor equality, actual child
lookup and queue emptiness, then preparation callback exit, frame reservation,
frame append and processing clears. Missing operation, bad cursor, nonempty
queue, reserve failure, callback Err and callback panic are explicit results;
None child and other Waits end at explicit other-owner boundaries. It never
assumes a desired lookup or successful sample/seed/enqueue/driver return.
**No composed theorem for runPrefix has been constructed.**

ResourceWrite has explicit constructors for physical/failure flags, sample
attempts, TLS peak/trace representation, ledger/counter/sample publication and
matrix-observer take/restore. Preservation is derived from concrete record
updates; there is no callback-purity premise. `prepare` retains the prior undo
append/capacity change on observer failure. Counter/ledger arithmetic,
allocation observations, instrumentation trace encoding and native trace
extraction remain OPEN. SamplePlan overapproximates observations; it does not
prove that any chosen sample result/image is realizable. The candidate therefore
does not establish complete native callback correspondence merely by splitting
records into projected and erased fields. Source inspection found these writes
disjoint, but that inspection and the candidate require fresh independent review.

## Source order, represented and omitted owners

Immutable context:2376 prepare_replay_ack looks up the operation, reserves undo,
then appends `(id,wait,queued,consumed,retired)` transactionally. Context:4082
samples only after capacity changes. Stable lib:9253 sets physical-change before
sampling and failure flag on Err. lib:10774/10821/11017 sample attempt/TLS state,
perform fallible accounting, then publish ledger/counters/sample count. Under
probe configuration lib:20414 takes/modifies/restores the matrix observer;
assertion panic can leave it taken. A projection-preserving write still retains
its failure/panic control edge. The model represents this distinction, while
exact trace extraction and arithmetic outcome correspondence remain unproved.

Context:2249 frame append saves both processing fields and initializes Transport,
empty acknowledgements/current/dispatch fields, zero counters and no destination
or receipt. lib:14186 then clears processing. This is the final modeled write.

**First unmodeled native writer:** `InferenceSession::clear_diagnostic_scratch`,
lib:15934, called by start_typed_drain at lib:14196. Its retained-allocation path
can reserve workspace undo, compute payload, reserve and replace delta, append
undo, and fail in capacity observation BEFORE doing the corresponding index
replacement. Its unjournalled completion clears all diagnostic scratch lists.
A failure here retains the appended frame and cleared processing; the child
entry does not invoke run_candidate_typed_drain's separate unwind wrapper.
Luna/proof intake owns a complete prefix model for this helper and its callees.

Principal later bodies were inspected, not formalized transitively:

- lib:14197 samples again before seed. Context:3374/3444 seed creates/retains
  context/source/scoped/relation/bundle/origin state, then samples; formal is
  None for this branch. Even when `Some(child).or(seed)` selects the child,
  seeding still executes and may fail after earlier writes. No seed-preservation
  lemma is assumed or delivered.
- lib:15223 enqueue skips evidence creation for Some(child), reserves worklist,
  then context:2385 transfer checks Idle, not retired, child/cursor bounds;
  at queued it prepares undo and increments queued before queue insertion.
  Entry Idle/Some alone did not check retired, so success is not automatic.
- lib:14203 publishes passive frame receipt only after enqueue; origin attachment
  has additional index/relation/occurrence/no-prior-receipt checks. Existence and
  matching are not assumed here. Created seed and selected child are distinct.
- Context:4123 writes destination then Running only after start returns success.
  Neither write is reached by a delivered composed theorem. No later drain,
  Transport/Context/Dispatch, completion or driver return is represented.

`R6-PROOF-PREFIX-1`: Luna/proof intake should first check/repair these seven
candidate terms, construct native footprint trace extraction for resource and
prepare, prove runPrefix readback, then model clear_diagnostic_scratch and its
fallible retained-allocation prefixes. Falsifier: any omitted callback write
into projected evidence, or any Err modeled without its prior undo/frame state.
The request supplies no new lease, authority or budget.

## Actual commands, execution status and stop

Executed only read-only `pwd`, `cat`, `sed`, `rg`, `awk`, `wc`, Python hashlib
input verification, Python writes to the two leased outputs, and `sha256sum` for
the artifact. All command exits observed were 0. Clock tool receipts are actual;
last construction clock: 2026-10-28 09:33:58 UTC. Brief bounded waits occurred
while the primary repaired the immutable read set. No nested CLI or network ran.

Read toolchain content pins `leanprover/lean4:v4.35.0`; lakefile has `-j1 -M1024`,
no external manifest packages. These are file observations, **not actual version
command results**. Actual Lean/Lake versions, execution exits, diagnostics,
theorem printer results and complete axiom lists are **NOT_RUN/UNKNOWN** under
this contract's worker prohibition. No Lean/Lake/checker/Cargo/build/test/formatter
command ran. No claim of axiom freedom follows from source inspection. Luna is
the sole authorized post-review verification/cache/generated-output owner.

Resource grant 1000 seconds, no renewal. Exact worker launch wall timestamp,
CPU/RSS and active duration are UNKNOWN; full reservation remains chargeable.
No children, heavy processes or generated outputs exist. The pause/amendment
consumed the existing envelope. No unauthorized source edits or execution;
initial moving read dependency is preserved above as a material input defect.

**Writer STOPPED on freezing this handoff.** No further writes, pending scratch,
processes or descendant leases. Artifact and handoff are pending primary intake
and fresh review; not commit-ready proof closure. This handoff's SHA is returned
separately to avoid self-reference.
