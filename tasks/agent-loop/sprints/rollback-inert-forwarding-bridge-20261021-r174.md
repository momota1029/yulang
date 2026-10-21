# R174 — rollback-inert source attribution and forwarding consumer bridge

Status: **REVISION 2 CANDIDATE** pending exact-hash delta review. Revision 1
remains preserved at SHA-256
`34cd8c4093a8e748a5dccc64ce1ca4113d0238c419aefeaf1c6f4fa4a35ce1cd`; its
prospective review was NOT_CLEAN and its 120-second grant is charged. No proof
or implementation worker lease starts until revision 2 is CLEAN and adopted.

Branch: `research/simple-sub-intrusion`  
Contract revision: 2  
Git HEAD baseline: `e9a7a4fef3d6872fa0596646393a7c0473b3687b`  
Immutable proof baseline: `7ec64a3788175913a2be46331cf0f64c6bd5b407`  
Proof baseline theorem: `notes/theory/2026-10-15-computation-forwarding-preservation.md`
SHA-256 `d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79`  
Source fixture: `tools/inference-playground/examples/r171-formal-name-forwarding.yu`
SHA-256 `cb2fff33a1ab983a932064cc1699d9f4f4a8d5e00d52986525884d42bc58234f`

R173 review outcome and candidate manifest are frozen in
`tasks/agent-loop/current.json` and
`tasks/agent-loop/inbox/20261021-r173-implementation.md` revision 4. The
reviewed R173 code is NOT_CLEAN and must not be represented as integrated or
proof-bearing. R173 baseline-only proof remains distinct. Current working-tree
candidate pins at R174 preparation:

```text
c005b99c1aa6da3c6b203e19c37f8b99700618815528f33d67cbf70941df78f5  crates/yu-solver/src/lib.rs
723cc253090ad2b4a0c67a1a17c57bc0587b26e4dc4d90a642f45ab0d1f468fa  crates/yu-solver/src/candidate_context.rs
48094aff85175ef7b30d1ef8be0e8fc42d6e5282d0c4d562c4a730c13d401b25  crates/yu-solver/src/candidate_scheme.rs
7a4c64d3783496029225be043ea8914543ceff1841caed5fcec19d68dcfb4932  crates/yu-solver/src/shadow_apply.rs
```

## Revision 2: immutable proof inputs and sequential candidate seam

Luna created byte-for-byte, read-only copies of the four R173 candidate owners
and the same four owners from the immutable proof-baseline commit before any
worker starts. The proof worker reads only these exact snapshot paths, never
the mutable checkout. Luna alone created and hash-verified the snapshots;
files are mode 0444 and directories mode 0555. Exact SHA-256 manifest:

```text
c75bf47b3d0d87e99d4365a587e6b90d5d05d05c335db16880cb2943b8b25985  /tmp/r174-inputs/baseline-7ec64a378/lib.rs
d884c20a98140da2a737d65f61faa97491bd9a2af7870bf3f0ea7dd428e9ffeb  /tmp/r174-inputs/baseline-7ec64a378/candidate_context.rs
9569e7cc2ba7152cafe1273fba279a8511fe56aa39358798f3e4586c10ede225  /tmp/r174-inputs/baseline-7ec64a378/candidate_scheme.rs
13ae8de60293b91e24659090649ff84002f5632a8909451d3f7bd8492b61bea5  /tmp/r174-inputs/baseline-7ec64a378/shadow_apply.rs
c005b99c1aa6da3c6b203e19c37f8b99700618815528f33d67cbf70941df78f5  /tmp/r174-inputs/r173-candidate-v4/lib.rs
723cc253090ad2b4a0c67a1a17c57bc0587b26e4dc4d90a642f45ab0d1f468fa  /tmp/r174-inputs/r173-candidate-v4/candidate_context.rs
48094aff85175ef7b30d1ef8be0e8fc42d6e5282d0c4d562c4a730c13d401b25  /tmp/r174-inputs/r173-candidate-v4/candidate_scheme.rs
7a4c64d3783496029225be043ea8914543ceff1841caed5fcec19d68dcfb4932  /tmp/r174-inputs/r173-candidate-v4/shadow_apply.rs
```

During the constructive lane, Luna may edit only the four current checkout
owners and its exact R174 output paths. The proof lane uses immutable R173 and
baseline snapshots while deriving source/lifecycle claims. After Luna stops
implementation writes, she freezes a distinct R174 candidate manifest. The
proof lane may apply its result to those frozen candidate hashes within its
existing assignment grant; Luna performs no further code writes until the
proof worker stops. This ordered handoff is pre-authorized and requires no
per-step dispatcher call. No snapshot is accepted as implementation evidence
merely because its hashes match.

## Original outcome and success evidence

Keep the original forwarding theorem, source domain, quantifiers, shared
satisfying assignment, open incoming E, arbitrary finite chains/repeated calls,
simultaneous entries and every finite prefix unchanged. Preserve the accepted
Simple-sub semantics, A/B claims and all OPEN gates.

Required outcome: make source-drain evidence rollback-inert and observational,
then construct the real ordered bridge from the original source witnesses
through the provider's own Capture and FreshUse restoration to the actual
forwarding Apply demand and ordered Replay/FunctionPort consumer. A specific
first missing owner is useful research progress but does not close the theorem
or authorize production.

R173 falsifiers to resolve:

1. `candidate_context.rs:2229` moves a non-Copy receipt from a borrowed frame;
   the candidate does not pass Rust ownership checking.
2. `lib.rs:12821–12828` mutates a pre-existing Origin's completion receipt,
   while rollback restores frames but not that Origin. Completion then failure
   can make retry return `IdentityExhausted`, violating observational
   noninterference.
3. `shadow_apply.rs:1427–1433` requires the later Apply checking relation inside
   the provider's immutable earlier Capture. Source order creates the provider
   route before the Apply's fresh relation; this does not establish the required
   consumer bridge.

Success evidence must show: (a) an ownership-valid certificate whose unavailable
or rolled-back state cannot change solver decisions, error paths or publication;
(b) a constructor-authenticated source Fact/Cause → selected seed → same
provider Capture/source bound → provider-owned FreshUse mapping/restoration →
callee flow → actual Apply demand → ordered Replay/FunctionPort consumer path;
and (c) the result applied back to the unchanged original theorem with exact
remaining premises. Preserve alternative routes, canonical self-pairs, shared
anchors, residual/scoped payload, repeated invocation ordinals and failure,
unwind, checkpoint and retry paths.

## Two continuing lanes

**Constructive proof — Sol/high:** prove the noninterference claim across
checkpoint, completion, failure, rollback, retry and repeated attempts. Inspect
actual producers and consumers for the ordered forwarding bridge; distinguish
retained facts from generated edges and generated edges from consumed
constraints. Apply every established lemma to the original theorem. Do not
review or certify the combined implementation.

**Implementation — Luna/high:** repair receipt ownership, then use an
append-only or explicitly undoable lifecycle so rollback cannot leave stale
completion evidence. Resource exhaustion/missing evidence must remain
unavailable without a new semantic failure. Replace the backward Capture
membership predicate with the producer-supported FreshUse-to-Apply consumer
bridge; do not weaken its boolean or infer equality from matching endpoints.
Carry the implementation through candidate observation and harness source, but
do not execute it without the review gate below.

No Astra assignment; no descendants. The R173 proof worker remains STOPPED.

## Exact leases

Snapshot input paths are written by Luna during preparation, then frozen for
read-only use by the proof worker. Exact paths:

- `/tmp/r174-inputs/baseline-7ec64a378/lib.rs`
- `/tmp/r174-inputs/baseline-7ec64a378/candidate_context.rs`
- `/tmp/r174-inputs/baseline-7ec64a378/candidate_scheme.rs`
- `/tmp/r174-inputs/baseline-7ec64a378/shadow_apply.rs`
- `/tmp/r174-inputs/r173-candidate-v4/lib.rs`
- `/tmp/r174-inputs/r173-candidate-v4/candidate_context.rs`
- `/tmp/r174-inputs/r173-candidate-v4/candidate_scheme.rs`
- `/tmp/r174-inputs/r173-candidate-v4/shadow_apply.rs`

Luna writes only:

- `crates/yu-solver/src/lib.rs`
- `crates/yu-solver/src/candidate_context.rs`
- `crates/yu-solver/src/candidate_scheme.rs`
- `crates/yu-solver/src/shadow_apply.rs`
- `tools/inference-playground/examples/r174_forwarding_bridge.rs`
- `tasks/agent-loop/inbox/20261021-r174-implementation.md`
- `tasks/agent-loop/current.json`
- this sprint contract, for primary-owned sequential revisions only.

Proof worker writes only:

- `notes/theory/2026-10-21-r174-rollback-and-forwarding-bridge.md`
- `tasks/agent-loop/inbox/20261021-r174-proof.md`

The proof worker owns the theory note exclusively. Luna records implementation
findings only in its handoff. The R171 fixture and all unrelated dirty files
are read-only. No broad directory leases, blanket cleanup, staging or stash.

## Dependencies and excluded work

Use R173 final review findings as exact falsifiers, not as proof. Keep immutable
proof baseline `7ec64a378…`, actual activation HEAD `e9a7a4fef…`, R173 candidate
owner hashes above and unchanged R171 fixture separately identified. Do not
rebase the old proof onto candidate bytes. The `next_action_selector` R174
recommendation is the adopted outcome and work split; Luna owns this activation.

No semantic weakening, change to expected outputs, broad build, unrelated
solver cleanup, Yulang2 run, evaluator run, network, nested CLI or background
service. A single offline inference probe is conditional only after candidate
proof inputs and exact code/harness/command pins receive CLEAN independent
review and the required discriminator is established. Otherwise record
`NOT_RUN` and the missing owner. Tests are not a proof substitute.

## Resources and review gates

Hard cap **4200 seconds**, Astra 0, no carryover. R174 rev1 consumed 240
preparation and one 120-second NOT_CLEAN prospective review. Revision 2 moves
120 unissued implementation seconds to snapshot/revision preparation, reducing
implementation to 1380 seconds. This 120-second prep and 120-second rev2
prospective delta review are now issued; remaining allocation:

| Work | Seconds |
|---|---:|
| Constructive proof | 1200 |
| Luna implementation | 1380 |
| Final proof/code review | 300 |
| Invocation review | 60 |
| Result review | 120 |
| Conditional probe | 300 |
| Closeout | 240 |
| **Remaining after issued R174 rev2 review** | **3600** |

Total is 4200: 360 seconds already charged at R174 rev1, 120 seconds snapshot
prep charged, 120 seconds R174 rev2 review charged, and 3600 seconds remaining.
Review grants are issued sequentially. Charge each issued grant in full if
elapsed is UNKNOWN; never reclaim R173's charged grants or R174 rev1's
120-second review.

The revision 2 delta reviewer must check original scope, immutable snapshot
hashes, read-before-write ordering, exact path ownership and corrected resource
arithmetic. Final review is by an eligible non-author
against a frozen manifest. A probe requires exact review of command, input,
output directory and receipt path. A green probe is finite instance evidence,
not theorem closure.

Stop on solver-behavior dependence on the certificate, unowned/reclaimed state,
unknown writer collision, a bridge counterexample, incomplete required joins,
budget exhaustion or user STOP. Preserve all A/B/F and production gates OPEN
unless their original obligations are independently closed.

Only Luna integrates: exact-path staging, inspect full outbound range, then
commit/push without force. Preserve unrelated R152–R163 work and all unknown
legacy reservations. At sprint end record hashes, review receipts, author/runtime
observations, full accounting, remaining parent premises and next material
dispatcher boundary.
Contract revision: 2
