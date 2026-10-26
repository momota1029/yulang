# NATIVE-DRAIN-OWNERSHIP-20261026/r4 — primary construction handoff

Status: **FROZEN / WRITES STOPPED for this packet; fresh nonauthor review required**.
Producer: `/root`. This is not independent review or whole-parent closure.
Baseline: `37ec9da2aaca2d7b806887d06d9bbd8b0fc5439c`, branch `yulang3`.
Original native accepted correspondence and `SourceProblem.InferenceSoundness`: **OPEN**.

## Constructed result and original application

The accompanying construction paper gives the unchanged original target and
an exact native constructor/consumer map. `Step` joins operation table, worklist,
frame stack, ordered cursor changes, diagnostics and terminal receipts in one
forward history. The conservation and stage predicates are derived from empty
state, not supplied by the caller; no separate cursor/frame history, whole
semantic law, accepted body or successful typing certificate is a premise.
Each child keeps its own task/relation. Immutable admitted work and its separate
canonical processing relation remain distinct through Transport. The complete
acknowledgement vector is exactly `done ++ pending` with completed=`done.length`.

At an empty worklist/frame stack, every issued occurrence has a diagnosed
ReturnReady receipt with empty current/pending fields; every transferred child
ticket has its exact diagnosed acknowledgement. ReturnReady's current/pending
and completed=prepared=vector-length facts follow from the stage transitions.
The witness constructs synchronous allocation, transport to a different relation,
dispatch, diagnostics, acknowledgement, return and delivery without double ack.
Empty-child retirement, saturating completion, Idle reclamation and commit
re-preparation are represented. Standard classical choice is reported below.

This is a successful-forward **control projection**. Original application still
requires one actual committed native history with payload identities, actual
callback/Transport/Derived paths, merge/cancellation/identity-reuse erasure and
completed Context/Value body ownership. Diagnostic completion is not absence
of conflicts. Original row/Context meaning and the entire source/world/Call/
effect/scoped witness remain required. The paper's section 5 identifies these
exact owners. No original source restriction or semantic change is adopted.

## Frozen artifacts

- `notes/theory/lean/YulangClosure/NativeDrainOwnership.lean`: `d37edac29dcecc19dd90b91c3095e5385a0657310dcf08d805a8f20672872d18`.
- `notes/theory/2026-10-26-native-drain-ownership.md`: `1e725751031322517c213662b0e0f1cf7b6e96bef656e2a6e45a40d67aee24e6`.

The module imports only pinned `Std`. The isolated project was extracted from
the supplied Git tree: 146 existing Lean/config entries, including six already
tracked auxiliary audit sources. That is a frozen baseline manifest, not a
claim that every baseline module was rechecked. An initial live-directory scan
was rejected before checker use. The 27 native/source authority inputs below
also match both their baseline snapshots and current repository bytes.

## Verification and preserved failures

Pinned Lake path: `/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake`.
Verified Lake `5.0.0-src+eb6cafb`, Lean `4.35.0`, compiler commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Release. No installation or dependency
change. Authorized normal execution avoids the known sandbox toolchain detection
failure. Ordinary calls use 115-second helper / 119-second outer deadlines,
`LEAN_NUM_THREADS=1`, `-j1 -M1024`, owned project/cache and TMPDIR.

Fifteen of 24 allowed primary calls were used. Calls 1–7 retain actual syntax,
constructor-elimination and enqueue-case repairs. Call 8 built successfully but
was killed at the old 1-GiB aggregate wrapper ceiling during its named audit;
it is not accepted complete verification. Measured wrapper/Lake/Lean overhead
justified a local 1.25-GiB aggregate ceiling; the Lean/project limit remains
1 GiB. Call 9 verified the coherent stage/control milestone. Calls 10–11 retain
witness record-layout repairs. Call 12 successfully checks the final source and
all 17 authored roots with no new warning. Later checks use CPU 8 alone instead
of CPU 0, avoiding sibling checks' affinity. Peak RSS is sampled, not a claim
of continuous kernel enforcement.

Call 13 reported exit zero, but its subsequently observed log is incomplete
(505 BEGIN / 504 END markers, no trailer) and its observed hash differs from
the receipt. Both the log and original JSON are retained; it is **not accepted**
audit evidence. Call 14 drains stdout through EOF and has all balanced blocks,
but the byte-chunk decoder introduced two replacement characters in a printed
non-theorem type. That call is likewise **not accepted** complete-type evidence.
Call 15 uses streaming UTF-8 decoding, reaches EOF, retains all 512 balanced
blocks and the final count, and has zero replacement characters or omitted terms.
No failed source, log or receipt was overwritten. Exact observed mismatch data
are stored in `native-drain-r4/output-collection-failures.json`.

| Call | Exit | Wall seconds | Peak aggregate RSS bytes | Termination |
| --- | ---: | ---: | ---: | --- |
| `check-01` | 1 | 1.682605 | 917712896 | none |
| `check-02` | 1 | 1.809010 | 917307392 | none |
| `check-03` | 1 | 1.790710 | 919760896 | none |
| `check-04` | 1 | 24.512234 | 994729984 | none |
| `check-05` | 1 | 23.249303 | 992780288 | none |
| `check-06` | 1 | 19.674072 | 960073728 | none |
| `check-07` | 1 | 16.794852 | 945885184 | none |
| `check-08` | -9 | 28.408942 | 1085517824 | aggregate RSS budget |
| `check-09` | 0 | 54.066297 | 1144537088 | none |
| `check-10` | 1 | 36.053499 | 972767232 | none |
| `check-11` | 1 | 49.655997 | 970903552 | none |
| `check-12` | 0 | 40.688010 | 1146888192 | none |
| `census-13` | 0 | 2.299366 | 1138712576 | none |
| `census-14` | 0 | 2.115590 | 1139036160 | none |
| `census-15` | 0 | 2.086277 | 1136836608 | none |

Total measured checker wall: **304.886764 seconds**. Peak sampled aggregate RSS: **1146888192 bytes**.

The exact expanded commands/versions/exits are in `native-drain-r4/logs`;
immutable main-source snapshots are in `snapshots`. Final focused invocation
uses the bundled helper with the isolated project, absolute pinned Lake,
`--module YulangClosure.NativeDrainOwnership --timeout 115` and the 17 exact
manifest roots. Final whole-origin census command:

```text
lake --no-cache env lean -j1 -M1024 AuditNativeDrainOwnership.lean
```

The census selects **actual originating module indices**, including private and
generated constants, and rejects originating axioms. It prints every complete
type with explicit proof arguments/deep terms, followed by its complete transitive
axiom set. Independent parsing requires unique matching BEGIN/END blocks, all
roots, complete axiom reports, exact module/final counts, no `⋯` omission and no
replacement character. All dependencies are within `propext`, `Quot.sound`,
`Classical.choice`; no `sorryAx`, project axiom, native-evaluation trust or kernel
bypass occurs. Source scans are supplementary, not the indirect-axiom audit.

## Complete originating census

**512 declarations / 187 theorem constants / 17 authored roots.**

| Complete axiom set | Theorem constants | All declarations |
| --- | ---: | ---: |
| none | 107 | 407 |
| `propext` | 28 | 53 |
| `propext, Quot.sound` | 10 | 10 |
| `propext, Quot.sound, Classical.choice` | 42 | 42 |

Classical choice is a permitted standard Lean axiom and is explicitly reported;
this is not an axiom-free claim. All 187 originating theorem types and exact
axiom lists are appended below. The full 512-declaration census, including
non-theorems, is `native-drain-r4/logs/census-15.log`, SHA-256
`2b06ede11d8d76a3cfd2b637e6eea45bb7865ff400a0637f867f1efae3144758`.

## Frozen source-owner inputs

| Repository path | SHA-256 |
| --- | --- |
| `AGENTS.md` | `ce73e9754ba9fd00bd2c4395d322ce77730a26aafb586d51de8ad169d7f8d48f` |
| `AGENTS.pre-sprint.md` | `34b8b8169696dcc6a0899204226914d250ddecf6782d14be670b7b2d5352c562` |
| `rules/goal-driven-sprints.md` | `e50f5d4f79814c87af56e7dc34ddb6ab968abb523826c72ecdc40a8920397c0a` |
| `rules/design-authority.md` | `e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1` |
| `.agents/skills/yulang-lean-proofs/SKILL.md` | `05346b8c6e3d9cdd1715da1774bb26cf7bce313233782240b3493bd9ee8754a7` |
| `.agents/skills/yulang-lean-proofs/references/sources.md` | `cb3f1009e80f0f9f7a1bf2575b4144e002a72f21e474c66b441e1f626a1e4d4a` |
| `.agents/skills/yulang-lean-proofs/references/execution.md` | `a1d8c47550e8925220623e0401410556d92719aff5590c459ac4c2e88306800b` |
| `.agents/skills/yulang-lean-proofs/scripts/check_lean.py` | `a4f10b70297cbf4d8b5bc0c7526bc29783eaf417f1f70e53eeea341d1150dde6` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/theory/2026-10-26-native-replay-lifecycle.md` | `3ebc78dacc8d3aa68a42094016ff291a3320375f5daf403cc15f3f7f60c7e55b` |
| `notes/theory/2026-10-26-native-replay-current-construction.md` | `ed7a97033d68822ac705bce26064ec590c07934df0c23d6a6761368bc1f6854a` |
| `notes/theory/2026-10-26-native-replay-acknowledgement.md` | `2989aa7ce9dd9bf37cfd847acb3cc21135c9b9a87664041bed2343dae2911dc3` |
| `notes/theory/2026-10-26-native-execution-history.md` | `72714bcfc9c30e34d13d08f3e63d121a5162fa63462dee0c39dc2d61e8fe3de2` |
| `notes/theory/2026-10-26-native-frame-rollback.md` | `001b7d066200024cf1d1cb269c4dd835871246f74d7ced87774f096a26d2fe7c` |
| `notes/theory/lean/YulangClosure/Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `notes/theory/lean/YulangClosure/CoreComposition.lean` | `1527cd3c5961b413ec2b97495744b218aba6247956881318485364d15065294c` |
| `notes/theory/lean/YulangClosure/NativeReplayAcknowledgement.lean` | `5264c6b6d9904a43ec0b50c3ac0100a05612b724f52a8601e3a93c771f8204df` |
| `notes/theory/lean/YulangClosure/NativeExecutionHistory.lean` | `44ad2a6d5b9ac0526ea36adc9180e0ed66e3892e48fa39aa40b20999dc7a1da6` |
| `notes/theory/lean/YulangClosure/NativeFrameRollback.lean` | `274e9a9ac1c43bc81d3b962edb6846dd5e4fa2adb2b645ebd92d6d5f38bd9964` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `cab85ff9a8a7dc5103fe932739dcea0dfc02e6420b1277565449882c802473bd` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-solver/src/candidate_context.rs` | `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_effect.rs` | `70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |

## Authored roots

- `YulangClosure.NativeDrainOwnership.initial_invariant`
- `YulangClosure.NativeDrainOwnership.step_invariant`
- `YulangClosure.NativeDrainOwnership.initial_coherent`
- `YulangClosure.NativeDrainOwnership.step_coherent`
- `YulangClosure.NativeDrainOwnership.run_invariant`
- `YulangClosure.NativeDrainOwnership.reachable_invariant`
- `YulangClosure.NativeDrainOwnership.run_coherent`
- `YulangClosure.NativeDrainOwnership.reachable_coherent`
- `YulangClosure.NativeDrainOwnership.ready_frame_readback`
- `YulangClosure.NativeDrainOwnership.quiescent_work_returned`
- `YulangClosure.NativeDrainOwnership.quiescent_replay_acknowledged`
- `YulangClosure.NativeDrainOwnership.outstanding_ticket_has_owner`
- `YulangClosure.NativeDrainOwnership.frame_prefix_has_real_receipts`
- `YulangClosure.NativeDrainOwnership.frame_split_exact`
- `YulangClosure.NativeDrainOwnership.empty_pending_iff_completed`
- `YulangClosure.NativeDrainOwnership.Witness.synchronous_transport_run`
- `YulangClosure.NativeDrainOwnership.Witness.synchronous_transport_readback`

## Writer cessation

The module, paper and this handoff are now frozen. No checker is running.
Only the primary's separately recorded progress/integration work continues.
No Rust, expected output, dependency, configuration, protected scheduling state
or reserved original public root changed. A fresh nonauthor must review the
exact frozen bytes, source map, complete census and retained failures before
commit. No parent theorem is self-certified by the construction owner.

## Complete originating theorem types and axiom lists

```text
@YulangClosure.NativeDrainOwnership.Child.mk.inj : ∀ {task relation task_1 relation_1 : Nat},
  { task := task, relation := relation } = { task := task_1, relation := relation_1 } →
    task = task_1 ∧ relation = relation_1
'YulangClosure.NativeDrainOwnership.Child.mk.inj' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.quiescent_work_returned : ∀ {s : YulangClosure.NativeDrainOwnership.State},
  YulangClosure.NativeDrainOwnership.Run YulangClosure.NativeDrainOwnership.initial s →
    s.queue = [] →
      s.frames = [] →
        ∀ (w : YulangClosure.NativeDrainOwnership.Work),
          w ∈ s.issued →
            ∃ r,
              r ∈ s.returns ∧
                w ∈ r.frame.processed ∧
                  r.frame.diagnosed = Bool.true ∧
                    r.frame.phase = YulangClosure.NativeDrainOwnership.Phase.returnReady ∧
                      r.frame.pending = [] ∧ r.frame.current = Option.none
'YulangClosure.NativeDrainOwnership.quiescent_work_returned' depends on axioms: [propext, Classical.choice, Quot.sound]

@_private.YulangClosure.NativeDrainOwnership.0.YulangClosure.NativeDrainOwnership.queueTicket_append._simp_1_2 : ∀
  {a b c : Prop}, ((a ∨ b) ∧ c) = (a ∧ c ∨ b ∧ c)
'_private.YulangClosure.NativeDrainOwnership.0.YulangClosure.NativeDrainOwnership.queueTicket_append._simp_1_2' depends on axioms: [propext]

YulangClosure.NativeDrainOwnership.step_coherent._proof_1_8 : ∀ (f : YulangClosure.NativeDrainOwnership.Frame),
  f.done.length ≤ f.done.length + f.pending.length + 1 ∧
    f.done.length + f.pending.length + 1 ≤ f.done.length + (f.pending.length + 1)
'YulangClosure.NativeDrainOwnership.step_coherent._proof_1_8' depends on axioms: [propext, Classical.choice, Quot.sound]

YulangClosure.NativeDrainOwnership.instDecidableEqWait.decEq._proof_12 : ∀
  (a : YulangClosure.NativeDrainOwnership.Ticket) (a_1 a_2 b b_1 : Nat),
  ¬a_1 = b →
    YulangClosure.NativeDrainOwnership.Wait.ready a a_1 a_2 = YulangClosure.NativeDrainOwnership.Wait.ready a b b_1 →
      False
'YulangClosure.NativeDrainOwnership.instDecidableEqWait.decEq._proof_12' does not depend on any axioms

YulangClosure.NativeDrainOwnership.State.mk.sizeOf_spec : ∀
  (operations : Nat → Option YulangClosure.NativeDrainOwnership.Operation) (nextOperation nextBirth nextWork : Nat)
  (queue : List YulangClosure.NativeDrainOwnership.Work) (frames : List YulangClosure.NativeDrainOwnership.Frame)
  (issued : List YulangClosure.NativeDrainOwnership.Work) (transferred : List YulangClosure.NativeDrainOwnership.Ticket)
  (acknowledgements : List YulangClosure.NativeDrainOwnership.AckReceipt)
  (returns : List YulangClosure.NativeDrainOwnership.ReturnReceipt),
  SizeOf.sizeOf
      { operations := operations, nextOperation := nextOperation, nextBirth := nextBirth, nextWork := nextWork,
        queue := queue, frames := frames, issued := issued, transferred := transferred,
        acknowledgements := acknowledgements, returns := returns } =
    1 + SizeOf.sizeOf nextOperation + SizeOf.sizeOf nextBirth + SizeOf.sizeOf nextWork + SizeOf.sizeOf queue +
              SizeOf.sizeOf frames +
            SizeOf.sizeOf issued +
          SizeOf.sizeOf transferred +
        SizeOf.sizeOf acknowledgements +
      SizeOf.sizeOf returns
'YulangClosure.NativeDrainOwnership.State.mk.sizeOf_spec' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.Invariant.acknowledgements : ∀ {s : YulangClosure.NativeDrainOwnership.State},
  YulangClosure.NativeDrainOwnership.Invariant s →
    ∀ (r : YulangClosure.NativeDrainOwnership.AckReceipt), r ∈ s.acknowledgements → r.diagnosed = Bool.true
'YulangClosure.NativeDrainOwnership.Invariant.acknowledgements' does not depend on any axioms

YulangClosure.NativeDrainOwnership.step_coherent._proof_1_12 : ∀ (f : YulangClosure.NativeDrainOwnership.Frame)
  (fs : List YulangClosure.NativeDrainOwnership.Frame) (rest : List YulangClosure.NativeDrainOwnership.Ticket),
  ((f.current = Option.none ∧ f.done.length ≤ f.prepared ∧ f.prepared ≤ f.done.length + (rest.length + 1)) ∧
      ∀ (a : YulangClosure.NativeDrainOwnership.Frame),
        a ∈ fs →
          (¬a.phase = YulangClosure.NativeDrainOwnership.Phase.working → a.current = Option.none) ∧
            (a.phase = YulangClosure.NativeDrainOwnership.Phase.acknowledgements ∨
                  a.phase = YulangClosure.NativeDrainOwnership.Phase.returnReady →
                a.diagnosed = Bool.true) ∧
              (a.phase = YulangClosure.NativeDrainOwnership.Phase.returnReady → a.pending = []) ∧
                a.done.length ≤ a.prepared ∧ a.prepared ≤ a.done.length + a.pending.length) →
    f.done.length < f.prepared → f.done.length + 1 ≤ f.prepared ∧ f.prepared ≤ f.done.length + 1 + rest.length
'YulangClosure.NativeDrainOwnership.step_coherent._proof_1_12' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

YulangClosure.NativeDrainOwnership.initial.eq_1 : YulangClosure.NativeDrainOwnership.initial =
  { operations := fun x => Option.none, nextOperation := 0, nextBirth := 0, nextWork := 0, queue := [], frames := [],
    issued := [], transferred := [], acknowledgements := [], returns := [] }
'YulangClosure.NativeDrainOwnership.initial.eq_1' does not depend on any axioms

YulangClosure.NativeDrainOwnership.instDecidableEqAckReceipt.decEq._proof_5 : ∀
  (a : YulangClosure.NativeDrainOwnership.Ticket) (a_1 a_2 : Nat) (a_3 : Bool)
  (b : YulangClosure.NativeDrainOwnership.Ticket) (b_1 b_2 : Nat) (b_3 : Bool),
  ¬a = b →
    { ticket := a, frameBirth := a_1, frameIndex := a_2, diagnosed := a_3 } =
        { ticket := b, frameBirth := b_1, frameIndex := b_2, diagnosed := b_3 } →
      False
'YulangClosure.NativeDrainOwnership.instDecidableEqAckReceipt.decEq._proof_5' does not depend on any axioms

YulangClosure.NativeDrainOwnership.Operation.mk.sizeOf_spec : ∀ (birth task : Nat)
  (children : List YulangClosure.NativeDrainOwnership.Child) (queued consumed : Nat) (retired : Bool)
  (waiting : YulangClosure.NativeDrainOwnership.Wait),
  SizeOf.sizeOf
      { birth := birth, task := task, children := children, queued := queued, consumed := consumed, retired := retired,
        waiting := waiting } =
    1 + SizeOf.sizeOf birth + SizeOf.sizeOf task + SizeOf.sizeOf children + SizeOf.sizeOf queued +
          SizeOf.sizeOf consumed +
        SizeOf.sizeOf retired +
      SizeOf.sizeOf waiting
'YulangClosure.NativeDrainOwnership.Operation.mk.sizeOf_spec' does not depend on any axioms

YulangClosure.NativeDrainOwnership.step_invariant._proof_1_20 : ∀ (index task relation : Nat)
  (op : YulangClosure.NativeDrainOwnership.Operation),
  op.children[index]? = Option.some { task := task, relation := relation } → index < op.children.length
'YulangClosure.NativeDrainOwnership.step_invariant._proof_1_20' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

YulangClosure.NativeDrainOwnership.instDecidableEqWait.decEq._proof_8 : ∀
  (ticket : YulangClosure.NativeDrainOwnership.Ticket) (frame transitions : Nat),
  YulangClosure.NativeDrainOwnership.Wait.ready ticket frame transitions =
      YulangClosure.NativeDrainOwnership.Wait.idle →
    False
'YulangClosure.NativeDrainOwnership.instDecidableEqWait.decEq._proof_8' does not depend on any axioms

YulangClosure.NativeDrainOwnership.step_invariant._proof_1_38 : ∀ (f : YulangClosure.NativeDrainOwnership.Frame),
  f.prepared + 1 ≤ (f.done ++ f.pending).length → f.prepared < (f.done ++ f.pending).length
'YulangClosure.NativeDrainOwnership.step_invariant._proof_1_38' depends on axioms: [propext]

YulangClosure.NativeDrainOwnership.instDecidableEqReturnReceipt.decEq._proof_1 : ∀
  (a : YulangClosure.NativeDrainOwnership.Frame), { frame := a } = { frame := a }
'YulangClosure.NativeDrainOwnership.instDecidableEqReturnReceipt.decEq._proof_1' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.Invariant.returned : ∀ {s : YulangClosure.NativeDrainOwnership.State},
  YulangClosure.NativeDrainOwnership.Invariant s →
    ∀ (r : YulangClosure.NativeDrainOwnership.ReturnReceipt),
      r ∈ s.returns →
        r.frame.phase = YulangClosure.NativeDrainOwnership.Phase.returnReady ∧
          r.frame.diagnosed = Bool.true ∧ r.frame.pending = [] ∧ r.frame.current = Option.none
'YulangClosure.NativeDrainOwnership.Invariant.returned' does not depend on any axioms

YulangClosure.NativeDrainOwnership.instDecidableEqOperation.decEq._proof_2 : ∀ (a a_1 : Nat)
  (a_2 : List YulangClosure.NativeDrainOwnership.Child) (a_3 a_4 : Nat) (a_5 : Bool)
  (a_6 b : YulangClosure.NativeDrainOwnership.Wait),
  ¬a_6 = b →
    { birth := a, task := a_1, children := a_2, queued := a_3, consumed := a_4, retired := a_5, waiting := a_6 } =
        { birth := a, task := a_1, children := a_2, queued := a_3, consumed := a_4, retired := a_5, waiting := b } →
      False
'YulangClosure.NativeDrainOwnership.instDecidableEqOperation.decEq._proof_2' does not depend on any axioms

YulangClosure.NativeDrainOwnership.AckReceipt.mk.sizeOf_spec : ∀ (ticket : YulangClosure.NativeDrainOwnership.Ticket)
  (frameBirth frameIndex : Nat) (diagnosed : Bool),
  SizeOf.sizeOf { ticket := ticket, frameBirth := frameBirth, frameIndex := frameIndex, diagnosed := diagnosed } =
    1 + SizeOf.sizeOf ticket + SizeOf.sizeOf frameBirth + SizeOf.sizeOf frameIndex + SizeOf.sizeOf diagnosed
'YulangClosure.NativeDrainOwnership.AckReceipt.mk.sizeOf_spec' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.step_invariant._proof_1_35 : ∀ {s : YulangClosure.NativeDrainOwnership.State}
  (f : YulangClosure.NativeDrainOwnership.Frame) (fs : List YulangClosure.NativeDrainOwnership.Frame)
  (w : YulangClosure.NativeDrainOwnership.Work) (ws : List YulangClosure.NativeDrainOwnership.Work),
  (∀ (w_1 : YulangClosure.NativeDrainOwnership.Work),
      w_1 ∈ s.issued →
        (w_1 = w ∨ w_1 ∈ ws) ∨
          (w_1 ∈ f.processed ∨ ∃ x, x ∈ fs ∧ (x.current = Option.some w_1 ∨ w_1 ∈ x.processed)) ∨
            ∃ r, r ∈ s.returns ∧ w_1 ∈ r.frame.processed) →
    ∀ (w_1 : YulangClosure.NativeDrainOwnership.Work),
      w_1 ∈ s.issued →
        w_1 ∈ ws ∨
          ((w = w_1 ∨ w_1 ∈ f.processed) ∨ ∃ x, x ∈ fs ∧ (x.current = Option.some w_1 ∨ w_1 ∈ x.processed)) ∨
            ∃ r, r ∈ s.returns ∧ w_1 ∈ r.frame.processed
'YulangClosure.NativeDrainOwnership.step_invariant._proof_1_35' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

YulangClosure.NativeDrainOwnership.instDecidableEqPhase._proof_1 : ∀ (x y : YulangClosure.NativeDrainOwnership.Phase),
  x.ctorIdx = y.ctorIdx → x = y
'YulangClosure.NativeDrainOwnership.instDecidableEqPhase._proof_1' does not depend on any axioms

YulangClosure.NativeDrainOwnership.Wait.ready.sizeOf_spec : ∀ (ticket : YulangClosure.NativeDrainOwnership.Ticket)
  (frame transitions : Nat),
  SizeOf.sizeOf (YulangClosure.NativeDrainOwnership.Wait.ready ticket frame transitions) =
    1 + SizeOf.sizeOf ticket + SizeOf.sizeOf frame + SizeOf.sizeOf transitions
'YulangClosure.NativeDrainOwnership.Wait.ready.sizeOf_spec' does not depend on any axioms

YulangClosure.NativeDrainOwnership.Frame.coherent.eq_1 : ∀ (f : YulangClosure.NativeDrainOwnership.Frame),
  f.coherent =
    ((f.phase ≠ YulangClosure.NativeDrainOwnership.Phase.working → f.current = Option.none) ∧
      (f.phase = YulangClosure.NativeDrainOwnership.Phase.acknowledgements ∨
            f.phase = YulangClosure.NativeDrainOwnership.Phase.returnReady →
          f.diagnosed = Bool.true) ∧
        (f.phase = YulangClosure.NativeDrainOwnership.Phase.returnReady → f.pending = []) ∧
          f.completed ≤ f.prepared ∧ f.prepared ≤ f.acks.length)
'YulangClosure.NativeDrainOwnership.Frame.coherent.eq_1' does not depend on any axioms

YulangClosure.NativeDrainOwnership.instDecidableEqOperation.decEq._proof_3 : ∀ (a a_1 : Nat)
  (a_2 : List YulangClosure.NativeDrainOwnership.Child) (a_3 a_4 : Nat) (a_5 : Bool)
  (a_6 : YulangClosure.NativeDrainOwnership.Wait) (b : Bool) (b_1 : YulangClosure.NativeDrainOwnership.Wait),
  ¬a_5 = b →
    { birth := a, task := a_1, children := a_2, queued := a_3, consumed := a_4, retired := a_5, waiting := a_6 } =
        { birth := a, task := a_1, children := a_2, queued := a_3, consumed := a_4, retired := b, waiting := b_1 } →
      False
'YulangClosure.NativeDrainOwnership.instDecidableEqOperation.decEq._proof_3' does not depend on any axioms

YulangClosure.NativeDrainOwnership.step_coherent._proof_1_9 : ∀ (f : YulangClosure.NativeDrainOwnership.Frame),
  f.prepared + 1 ≤ (f.done ++ f.pending).length → f.prepared < (f.done ++ f.pending).length
'YulangClosure.NativeDrainOwnership.step_coherent._proof_1_9' depends on axioms: [propext]

YulangClosure.NativeDrainOwnership.instDecidableEqFrame.decEq._proof_8 : ∀ (a a_1 : Nat)
  (a_2 : Option YulangClosure.NativeDrainOwnership.Work) (a_3 : Option Nat)
  (a_4 : List YulangClosure.NativeDrainOwnership.Work) (a_5 a_6 : List YulangClosure.NativeDrainOwnership.Ticket)
  (a_7 : Nat) (a_8 : YulangClosure.NativeDrainOwnership.Phase) (a_9 : Bool)
  (a_10 : Option YulangClosure.NativeDrainOwnership.Ticket) (a_11 : Nat)
  (b b_1 : List YulangClosure.NativeDrainOwnership.Ticket) (b_2 : Nat) (b_3 : YulangClosure.NativeDrainOwnership.Phase)
  (b_4 : Bool) (b_5 : Option YulangClosure.NativeDrainOwnership.Ticket) (b_6 : Nat),
  ¬a_5 = b →
    { birth := a, index := a_1, current := a_2, processing := a_3, processed := a_4, done := a_5, pending := a_6,
          prepared := a_7, phase := a_8, diagnosed := a_9, destination := a_10, transitions := a_11 } =
        { birth := a, index := a_1, current := a_2, processing := a_3, processed := a_4, done := b, pending := b_1,
          prepared := b_2, phase := b_3, diagnosed := b_4, destination := b_5, transitions := b_6 } →
      False
'YulangClosure.NativeDrainOwnership.instDecidableEqFrame.decEq._proof_8' does not depend on any axioms

@_private.YulangClosure.NativeDrainOwnership.0.YulangClosure.NativeDrainOwnership.received_append._simp_1_3 : ∀
  {α : Sort u_1} {p q : α → Prop}, (∃ x, p x ∨ q x) = ((∃ x, p x) ∨ ∃ x, q x)
'_private.YulangClosure.NativeDrainOwnership.0.YulangClosure.NativeDrainOwnership.received_append._simp_1_3' depends on axioms: [propext]

YulangClosure.NativeDrainOwnership.TaskCovered.eq_1 : ∀ (s : YulangClosure.NativeDrainOwnership.State)
  (w : YulangClosure.NativeDrainOwnership.Work),
  YulangClosure.NativeDrainOwnership.TaskCovered s w =
    (w ∈ s.queue ∨
      YulangClosure.NativeDrainOwnership.stackWork w s.frames ∨
        YulangClosure.NativeDrainOwnership.returnedWork w s.returns)
'YulangClosure.NativeDrainOwnership.TaskCovered.eq_1' does not depend on any axioms

YulangClosure.NativeDrainOwnership.Work.mk.sizeOf_spec : ∀ (serial task relation : Nat)
  (ticket : Option YulangClosure.NativeDrainOwnership.Ticket),
  SizeOf.sizeOf { serial := serial, task := task, relation := relation, ticket := ticket } =
    1 + SizeOf.sizeOf serial + SizeOf.sizeOf task + SizeOf.sizeOf relation + SizeOf.sizeOf ticket
'YulangClosure.NativeDrainOwnership.Work.mk.sizeOf_spec' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.AckReceipt.mk.inj : ∀ {ticket : YulangClosure.NativeDrainOwnership.Ticket}
  {frameBirth frameIndex : Nat} {diagnosed : Bool} {ticket_1 : YulangClosure.NativeDrainOwnership.Ticket}
  {frameBirth_1 frameIndex_1 : Nat} {diagnosed_1 : Bool},
  { ticket := ticket, frameBirth := frameBirth, frameIndex := frameIndex, diagnosed := diagnosed } =
      { ticket := ticket_1, frameBirth := frameBirth_1, frameIndex := frameIndex_1, diagnosed := diagnosed_1 } →
    ticket = ticket_1 ∧ frameBirth = frameBirth_1 ∧ frameIndex = frameIndex_1 ∧ diagnosed = diagnosed_1
'YulangClosure.NativeDrainOwnership.AckReceipt.mk.inj' does not depend on any axioms

YulangClosure.NativeDrainOwnership.Child.mk.injEq : ∀ (task relation task_1 relation_1 : Nat),
  ({ task := task, relation := relation } = { task := task_1, relation := relation_1 }) =
    (task = task_1 ∧ relation = relation_1)
'YulangClosure.NativeDrainOwnership.Child.mk.injEq' depends on axioms: [propext]

YulangClosure.NativeDrainOwnership.instDecidableEqAckReceipt.decEq._proof_1 : ∀
  (a : YulangClosure.NativeDrainOwnership.Ticket) (a_1 a_2 : Nat) (a_3 : Bool),
  { ticket := a, frameBirth := a_1, frameIndex := a_2, diagnosed := a_3 } =
    { ticket := a, frameBirth := a_1, frameIndex := a_2, diagnosed := a_3 }
'YulangClosure.NativeDrainOwnership.instDecidableEqAckReceipt.decEq._proof_1' does not depend on any axioms

YulangClosure.NativeDrainOwnership.consumedFrame.eq_1 : ∀ (f : YulangClosure.NativeDrainOwnership.Frame)
  (a : YulangClosure.NativeDrainOwnership.Ticket) (remaining : List YulangClosure.NativeDrainOwnership.Ticket),
  YulangClosure.NativeDrainOwnership.consumedFrame f a remaining =
    { birth := f.birth, index := f.index, current := f.current, processing := f.processing, processed := f.processed,
      done := f.done ++ [a], pending := remaining, prepared := f.prepared,
      phase :=
        if remaining = [] then YulangClosure.NativeDrainOwnership.Phase.returnReady
        else YulangClosure.NativeDrainOwnership.Phase.acknowledgements,
      diagnosed := f.diagnosed, destination := f.destination, transitions := f.transitions }
'YulangClosure.NativeDrainOwnership.consumedFrame.eq_1' does not depend on any axioms

YulangClosure.NativeDrainOwnership.instDecidableEqWork.decEq._proof_3 : ∀ (a a_1 a_2 : Nat)
  (a_3 : Option YulangClosure.NativeDrainOwnership.Ticket) (b : Nat)
  (b_1 : Option YulangClosure.NativeDrainOwnership.Ticket),
  ¬a_2 = b →
    { serial := a, task := a_1, relation := a_2, ticket := a_3 } =
        { serial := a, task := a_1, relation := b, ticket := b_1 } →
      False
'YulangClosure.NativeDrainOwnership.instDecidableEqWork.decEq._proof_3' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.Wait.ready.inj : ∀ {ticket : YulangClosure.NativeDrainOwnership.Ticket}
  {frame transitions : Nat} {ticket_1 : YulangClosure.NativeDrainOwnership.Ticket} {frame_1 transitions_1 : Nat},
  YulangClosure.NativeDrainOwnership.Wait.ready ticket frame transitions =
      YulangClosure.NativeDrainOwnership.Wait.ready ticket_1 frame_1 transitions_1 →
    ticket = ticket_1 ∧ frame = frame_1 ∧ transitions = transitions_1
'YulangClosure.NativeDrainOwnership.Wait.ready.inj' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.step_invariant._proof_1_49 : ∀ {s : YulangClosure.NativeDrainOwnership.State},
  (∀ (a : YulangClosure.NativeDrainOwnership.Ticket),
      a ∈ s.transferred →
        (∃ w, w ∈ s.queue ∧ w.ticket = Option.some a) ∨
          (∃ f, f ∈ s.frames ∧ (a ∈ f.done ∨ a ∈ f.pending)) ∨ ∃ r, r ∈ s.acknowledgements ∧ r.ticket = a) →
    ∀ (a : YulangClosure.NativeDrainOwnership.Ticket),
      a ∈ s.transferred →
        (∃ w, w ∈ s.queue ∧ w.ticket = Option.some a) ∨
          (∃ f,
              (∃ a,
                  a ∈ s.frames ∧
                    { birth := a.birth, index := a.index, current := a.current, processing := a.processing,
                        processed := a.processed, done := a.done, pending := a.pending, prepared := a.done.length,
                        phase := a.phase, diagnosed := a.diagnosed, destination := a.destination,
                        transitions := a.transitions } =
                      f) ∧
                (a ∈ f.done ∨ a ∈ f.pending)) ∨
            ∃ r, r ∈ s.acknowledgements ∧ r.ticket = a
'YulangClosure.NativeDrainOwnership.step_invariant._proof_1_49' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

@YulangClosure.NativeDrainOwnership.quiescent_replay_acknowledged : ∀ {s : YulangClosure.NativeDrainOwnership.State},
  YulangClosure.NativeDrainOwnership.Run YulangClosure.NativeDrainOwnership.initial s →
    s.queue = [] →
      s.frames = [] →
        ∀ (a : YulangClosure.NativeDrainOwnership.Ticket),
          a ∈ s.transferred → ∃ r, r ∈ s.acknowledgements ∧ r.ticket = a ∧ r.diagnosed = Bool.true
'YulangClosure.NativeDrainOwnership.quiescent_replay_acknowledged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

YulangClosure.NativeDrainOwnership.instDecidableEqWait.decEq._proof_5 : ∀
  (a : YulangClosure.NativeDrainOwnership.Ticket) (a_1 b : Nat),
  ¬a_1 = b →
    YulangClosure.NativeDrainOwnership.Wait.running a a_1 = YulangClosure.NativeDrainOwnership.Wait.running a b → False
'YulangClosure.NativeDrainOwnership.instDecidableEqWait.decEq._proof_5' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.step_invariant._proof_1_24 : ∀ {s : YulangClosure.NativeDrainOwnership.State}
  (f : YulangClosure.NativeDrainOwnership.Frame) (fs : List YulangClosure.NativeDrainOwnership.Frame)
  (id index relation : Nat) (op : YulangClosure.NativeDrainOwnership.Operation),
  (∀ (a : YulangClosure.NativeDrainOwnership.Ticket),
      a ∈ s.transferred →
        (∃ w, w ∈ s.queue ∧ w.ticket = Option.some a) ∨
          ((a ∈ f.done ∨ a ∈ f.pending) ∨ ∃ x, x ∈ fs ∧ (a ∈ x.done ∨ a ∈ x.pending)) ∨
            ∃ r, r ∈ s.acknowledgements ∧ r.ticket = a) →
    ∀ (a : YulangClosure.NativeDrainOwnership.Ticket),
      a ∈ s.transferred ∨ a = YulangClosure.NativeDrainOwnership.selectedTicket id op index relation →
        (YulangClosure.NativeDrainOwnership.selectedTicket id op index relation = a ∨
            ∃ x, x ∈ s.queue ∧ x.ticket = Option.some a) ∨
          ((a ∈ f.done ∨ a ∈ f.pending) ∨ ∃ x, x ∈ fs ∧ (a ∈ x.done ∨ a ∈ x.pending)) ∨
            ∃ r, r ∈ s.acknowledgements ∧ r.ticket = a
'YulangClosure.NativeDrainOwnership.step_invariant._proof_1_24' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

@YulangClosure.NativeDrainOwnership.step_invariant._proof_1_36 : ∀ {s : YulangClosure.NativeDrainOwnership.State}
  (f : YulangClosure.NativeDrainOwnership.Frame) (fs : List YulangClosure.NativeDrainOwnership.Frame)
  (ws : List YulangClosure.NativeDrainOwnership.Work) (a : YulangClosure.NativeDrainOwnership.Ticket),
  (∀ (a_1 : YulangClosure.NativeDrainOwnership.Ticket),
      a_1 ∈ s.transferred →
        (a = a_1 ∨ ∃ x, x ∈ ws ∧ x.ticket = Option.some a_1) ∨
          ((a_1 ∈ f.done ∨ a_1 ∈ f.pending) ∨ ∃ x, x ∈ fs ∧ (a_1 ∈ x.done ∨ a_1 ∈ x.pending)) ∨
            ∃ r, r ∈ s.acknowledgements ∧ r.ticket = a_1) →
    ∀ (a_1 : YulangClosure.NativeDrainOwnership.Ticket),
      a_1 ∈ s.transferred →
        (∃ w, w ∈ ws ∧ w.ticket = Option.some a_1) ∨
          ((a_1 ∈ f.done ∨ a_1 ∈ f.pending ∨ a_1 = a) ∨ ∃ x, x ∈ fs ∧ (a_1 ∈ x.done ∨ a_1 ∈ x.pending)) ∨
            ∃ r, r ∈ s.acknowledgements ∧ r.ticket = a_1
'YulangClosure.NativeDrainOwnership.step_invariant._proof_1_36' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

@_private.YulangClosure.NativeDrainOwnership.0.YulangClosure.NativeDrainOwnership.returnedWork_append._simp_1_3 : ∀
  {α : Sort u_1} {p q : α → Prop}, (∃ x, p x ∨ q x) = ((∃ x, p x) ∨ ∃ x, q x)
'_private.YulangClosure.NativeDrainOwnership.0.YulangClosure.NativeDrainOwnership.returnedWork_append._simp_1_3' depends on axioms: [propext]

@YulangClosure.NativeDrainOwnership.step_invariant._simp_1_13 : ∀ {α : Type u_1} {b : α} {l : List α} {a : α},
  (a ∈ b :: l) = (a = b ∨ a ∈ l)
'YulangClosure.NativeDrainOwnership.step_invariant._simp_1_13' depends on axioms: [propext]

YulangClosure.NativeDrainOwnership.TicketCovered.eq_1 : ∀ (s : YulangClosure.NativeDrainOwnership.State)
  (a : YulangClosure.NativeDrainOwnership.Ticket),
  YulangClosure.NativeDrainOwnership.TicketCovered s a =
    (YulangClosure.NativeDrainOwnership.queueTicket a s.queue ∨
      YulangClosure.NativeDrainOwnership.stackTicket a s.frames ∨
        YulangClosure.NativeDrainOwnership.received a s.acknowledgements)
'YulangClosure.NativeDrainOwnership.TicketCovered.eq_1' does not depend on any axioms

YulangClosure.NativeDrainOwnership.step_invariant._proof_1_40 : ∀ (f : YulangClosure.NativeDrainOwnership.Frame),
  f.prepared + 1 ≤ f.done.length → f.prepared < f.done.length
'YulangClosure.NativeDrainOwnership.step_invariant._proof_1_40' depends on axioms: [propext]

@YulangClosure.NativeDrainOwnership.Ticket.mk.inj : ∀
  {birth operation index relation birth_1 operation_1 index_1 relation_1 : Nat},
  { birth := birth, operation := operation, index := index, relation := relation } =
      { birth := birth_1, operation := operation_1, index := index_1, relation := relation_1 } →
    birth = birth_1 ∧ operation = operation_1 ∧ index = index_1 ∧ relation = relation_1
'YulangClosure.NativeDrainOwnership.Ticket.mk.inj' does not depend on any axioms

YulangClosure.NativeDrainOwnership.instDecidableEqFrame.decEq._proof_10 : ∀ (a a_1 : Nat)
  (a_2 : Option YulangClosure.NativeDrainOwnership.Work) (a_3 : Option Nat)
  (a_4 : List YulangClosure.NativeDrainOwnership.Work) (a_5 a_6 : List YulangClosure.NativeDrainOwnership.Ticket)
  (a_7 : Nat) (a_8 : YulangClosure.NativeDrainOwnership.Phase) (a_9 : Bool)
  (a_10 : Option YulangClosure.NativeDrainOwnership.Ticket) (a_11 : Nat) (b : Option Nat)
  (b_1 : List YulangClosure.NativeDrainOwnership.Work) (b_2 b_3 : List YulangClosure.NativeDrainOwnership.Ticket)
  (b_4 : Nat) (b_5 : YulangClosure.NativeDrainOwnership.Phase) (b_6 : Bool)
  (b_7 : Option YulangClosure.NativeDrainOwnership.Ticket) (b_8 : Nat),
  ¬a_3 = b →
    { birth := a, index := a_1, current := a_2, processing := a_3, processed := a_4, done := a_5, pending := a_6,
          prepared := a_7, phase := a_8, diagnosed := a_9, destination := a_10, transitions := a_11 } =
        { birth := a, index := a_1, current := a_2, processing := b, processed := b_1, done := b_2, pending := b_3,
          prepared := b_4, phase := b_5, diagnosed := b_6, destination := b_7, transitions := b_8 } →
      False
'YulangClosure.NativeDrainOwnership.instDecidableEqFrame.decEq._proof_10' does not depend on any axioms

YulangClosure.NativeDrainOwnership.instDecidableEqFrame.decEq._proof_6 : ∀ (a a_1 : Nat)
  (a_2 : Option YulangClosure.NativeDrainOwnership.Work) (a_3 : Option Nat)
  (a_4 : List YulangClosure.NativeDrainOwnership.Work) (a_5 a_6 : List YulangClosure.NativeDrainOwnership.Ticket)
  (a_7 : Nat) (a_8 : YulangClosure.NativeDrainOwnership.Phase) (a_9 : Bool)
  (a_10 : Option YulangClosure.NativeDrainOwnership.Ticket) (a_11 b : Nat)
  (b_1 : YulangClosure.NativeDrainOwnership.Phase) (b_2 : Bool) (b_3 : Option YulangClosure.NativeDrainOwnership.Ticket)
  (b_4 : Nat),
  ¬a_7 = b →
    { birth := a, index := a_1, current := a_2, processing := a_3, processed := a_4, done := a_5, pending := a_6,
          prepared := a_7, phase := a_8, diagnosed := a_9, destination := a_10, transitions := a_11 } =
        { birth := a, index := a_1, current := a_2, processing := a_3, processed := a_4, done := a_5, pending := a_6,
          prepared := b, phase := b_1, diagnosed := b_2, destination := b_3, transitions := b_4 } →
      False
'YulangClosure.NativeDrainOwnership.instDecidableEqFrame.decEq._proof_6' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.Run.brecOn : ∀ {a : YulangClosure.NativeDrainOwnership.State}
  {motive : (a_1 : YulangClosure.NativeDrainOwnership.State) → YulangClosure.NativeDrainOwnership.Run a a_1 → Prop}
  {a_1 : YulangClosure.NativeDrainOwnership.State} (t : YulangClosure.NativeDrainOwnership.Run a a_1),
  (∀ (a_2 : YulangClosure.NativeDrainOwnership.State) (t : YulangClosure.NativeDrainOwnership.Run a a_2),
      YulangClosure.NativeDrainOwnership.Run.below t → motive a_2 t) →
    motive a_1 t
'YulangClosure.NativeDrainOwnership.Run.brecOn' depends on axioms: [propext]

YulangClosure.NativeDrainOwnership.instDecidableEqWait.decEq._proof_1 : ∀
  (ticket : YulangClosure.NativeDrainOwnership.Ticket) (frame : Nat),
  YulangClosure.NativeDrainOwnership.Wait.idle = YulangClosure.NativeDrainOwnership.Wait.running ticket frame → False
'YulangClosure.NativeDrainOwnership.instDecidableEqWait.decEq._proof_1' does not depend on any axioms

YulangClosure.NativeDrainOwnership.instDecidableEqWait.decEq._proof_2 : ∀
  (ticket : YulangClosure.NativeDrainOwnership.Ticket) (frame transitions : Nat),
  YulangClosure.NativeDrainOwnership.Wait.idle =
      YulangClosure.NativeDrainOwnership.Wait.ready ticket frame transitions →
    False
'YulangClosure.NativeDrainOwnership.instDecidableEqWait.decEq._proof_2' does not depend on any axioms

YulangClosure.NativeDrainOwnership.Phase.acknowledgements.sizeOf_spec : SizeOf.sizeOf
    YulangClosure.NativeDrainOwnership.Phase.acknowledgements =
  1
'YulangClosure.NativeDrainOwnership.Phase.acknowledgements.sizeOf_spec' does not depend on any axioms

YulangClosure.NativeDrainOwnership.instDecidableEqOperation.decEq._proof_4 : ∀ (a a_1 : Nat)
  (a_2 : List YulangClosure.NativeDrainOwnership.Child) (a_3 a_4 : Nat) (a_5 : Bool)
  (a_6 : YulangClosure.NativeDrainOwnership.Wait) (b : Nat) (b_1 : Bool)
  (b_2 : YulangClosure.NativeDrainOwnership.Wait),
  ¬a_4 = b →
    { birth := a, task := a_1, children := a_2, queued := a_3, consumed := a_4, retired := a_5, waiting := a_6 } =
        { birth := a, task := a_1, children := a_2, queued := a_3, consumed := b, retired := b_1, waiting := b_2 } →
      False
'YulangClosure.NativeDrainOwnership.instDecidableEqOperation.decEq._proof_4' does not depend on any axioms

YulangClosure.NativeDrainOwnership.Work.mk.injEq : ∀ (serial task relation : Nat)
  (ticket : Option YulangClosure.NativeDrainOwnership.Ticket) (serial_1 task_1 relation_1 : Nat)
  (ticket_1 : Option YulangClosure.NativeDrainOwnership.Ticket),
  ({ serial := serial, task := task, relation := relation, ticket := ticket } =
      { serial := serial_1, task := task_1, relation := relation_1, ticket := ticket_1 }) =
    (serial = serial_1 ∧ task = task_1 ∧ relation = relation_1 ∧ ticket = ticket_1)
'YulangClosure.NativeDrainOwnership.Work.mk.injEq' depends on axioms: [propext]

YulangClosure.NativeDrainOwnership.instDecidableEqWork.decEq._proof_2 : ∀ (a a_1 a_2 : Nat)
  (a_3 b : Option YulangClosure.NativeDrainOwnership.Ticket),
  ¬a_3 = b →
    { serial := a, task := a_1, relation := a_2, ticket := a_3 } =
        { serial := a, task := a_1, relation := a_2, ticket := b } →
      False
'YulangClosure.NativeDrainOwnership.instDecidableEqWork.decEq._proof_2' does not depend on any axioms

YulangClosure.NativeDrainOwnership.Child.mk.sizeOf_spec : ∀ (task relation : Nat),
  SizeOf.sizeOf { task := task, relation := relation } = 1 + SizeOf.sizeOf task + SizeOf.sizeOf relation
'YulangClosure.NativeDrainOwnership.Child.mk.sizeOf_spec' does not depend on any axioms

YulangClosure.NativeDrainOwnership.instDecidableEqFrame.decEq._proof_5 : ∀ (a a_1 : Nat)
  (a_2 : Option YulangClosure.NativeDrainOwnership.Work) (a_3 : Option Nat)
  (a_4 : List YulangClosure.NativeDrainOwnership.Work) (a_5 a_6 : List YulangClosure.NativeDrainOwnership.Ticket)
  (a_7 : Nat) (a_8 : YulangClosure.NativeDrainOwnership.Phase) (a_9 : Bool)
  (a_10 : Option YulangClosure.NativeDrainOwnership.Ticket) (a_11 : Nat) (b : YulangClosure.NativeDrainOwnership.Phase)
  (b_1 : Bool) (b_2 : Option YulangClosure.NativeDrainOwnership.Ticket) (b_3 : Nat),
  ¬a_8 = b →
    { birth := a, index := a_1, current := a_2, processing := a_3, processed := a_4, done := a_5, pending := a_6,
          prepared := a_7, phase := a_8, diagnosed := a_9, destination := a_10, transitions := a_11 } =
        { birth := a, index := a_1, current := a_2, processing := a_3, processed := a_4, done := a_5, pending := a_6,
          prepared := a_7, phase := b, diagnosed := b_1, destination := b_2, transitions := b_3 } →
      False
'YulangClosure.NativeDrainOwnership.instDecidableEqFrame.decEq._proof_5' does not depend on any axioms

YulangClosure.NativeDrainOwnership.empty_pending_iff_completed : ∀ (f : YulangClosure.NativeDrainOwnership.Frame),
  f.pending = [] ↔ f.completed = f.acks.length
'YulangClosure.NativeDrainOwnership.empty_pending_iff_completed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

YulangClosure.NativeDrainOwnership.Phase.working.sizeOf_spec : SizeOf.sizeOf
    YulangClosure.NativeDrainOwnership.Phase.working =
  1
'YulangClosure.NativeDrainOwnership.Phase.working.sizeOf_spec' does not depend on any axioms

YulangClosure.NativeDrainOwnership.instDecidableEqFrame.decEq._proof_11 : ∀ (a a_1 : Nat)
  (a_2 : Option YulangClosure.NativeDrainOwnership.Work) (a_3 : Option Nat)
  (a_4 : List YulangClosure.NativeDrainOwnership.Work) (a_5 a_6 : List YulangClosure.NativeDrainOwnership.Ticket)
  (a_7 : Nat) (a_8 : YulangClosure.NativeDrainOwnership.Phase) (a_9 : Bool)
  (a_10 : Option YulangClosure.NativeDrainOwnership.Ticket) (a_11 : Nat)
  (b : Option YulangClosure.NativeDrainOwnership.Work) (b_1 : Option Nat)
  (b_2 : List YulangClosure.NativeDrainOwnership.Work) (b_3 b_4 : List YulangClosure.NativeDrainOwnership.Ticket)
  (b_5 : Nat) (b_6 : YulangClosure.NativeDrainOwnership.Phase) (b_7 : Bool)
  (b_8 : Option YulangClosure.NativeDrainOwnership.Ticket) (b_9 : Nat),
  ¬a_2 = b →
    { birth := a, index := a_1, current := a_2, processing := a_3, processed := a_4, done := a_5, pending := a_6,
          prepared := a_7, phase := a_8, diagnosed := a_9, destination := a_10, transitions := a_11 } =
        { birth := a, index := a_1, current := b, processing := b_1, processed := b_2, done := b_3, pending := b_4,
          prepared := b_5, phase := b_6, diagnosed := b_7, destination := b_8, transitions := b_9 } →
      False
'YulangClosure.NativeDrainOwnership.instDecidableEqFrame.decEq._proof_11' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.step_invariant : ∀ {s t : YulangClosure.NativeDrainOwnership.State},
  YulangClosure.NativeDrainOwnership.Step s t →
    YulangClosure.NativeDrainOwnership.Invariant s → YulangClosure.NativeDrainOwnership.Invariant t
'YulangClosure.NativeDrainOwnership.step_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]

YulangClosure.NativeDrainOwnership.instDecidableEqFrame.decEq._proof_2 : ∀ (a a_1 : Nat)
  (a_2 : Option YulangClosure.NativeDrainOwnership.Work) (a_3 : Option Nat)
  (a_4 : List YulangClosure.NativeDrainOwnership.Work) (a_5 a_6 : List YulangClosure.NativeDrainOwnership.Ticket)
  (a_7 : Nat) (a_8 : YulangClosure.NativeDrainOwnership.Phase) (a_9 : Bool)
  (a_10 : Option YulangClosure.NativeDrainOwnership.Ticket) (a_11 b : Nat),
  ¬a_11 = b →
    { birth := a, index := a_1, current := a_2, processing := a_3, processed := a_4, done := a_5, pending := a_6,
          prepared := a_7, phase := a_8, diagnosed := a_9, destination := a_10, transitions := a_11 } =
        { birth := a, index := a_1, current := a_2, processing := a_3, processed := a_4, done := a_5, pending := a_6,
          prepared := a_7, phase := a_8, diagnosed := a_9, destination := a_10, transitions := b } →
      False
'YulangClosure.NativeDrainOwnership.instDecidableEqFrame.decEq._proof_2' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.step_invariant._proof_1_18 : ∀ {s : YulangClosure.NativeDrainOwnership.State}
  (f : YulangClosure.NativeDrainOwnership.Frame) (fs : List YulangClosure.NativeDrainOwnership.Frame)
  (task relation : Nat),
  (∀ (w : YulangClosure.NativeDrainOwnership.Work),
      w ∈ s.issued →
        w ∈ s.queue ∨
          ((f.current = Option.some w ∨ w ∈ f.processed) ∨
              ∃ x, x ∈ fs ∧ (x.current = Option.some w ∨ w ∈ x.processed)) ∨
            ∃ r, r ∈ s.returns ∧ w ∈ r.frame.processed) →
    ∀ (w : YulangClosure.NativeDrainOwnership.Work),
      w ∈ s.issued ∨ w = { serial := s.nextWork, task := task, relation := relation, ticket := Option.none } →
        (w = { serial := s.nextWork, task := task, relation := relation, ticket := Option.none } ∨ w ∈ s.queue) ∨
          ((f.current = Option.some w ∨ w ∈ f.processed) ∨
              ∃ x, x ∈ fs ∧ (x.current = Option.some w ∨ w ∈ x.processed)) ∨
            ∃ r, r ∈ s.returns ∧ w ∈ r.frame.processed
'YulangClosure.NativeDrainOwnership.step_invariant._proof_1_18' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

@YulangClosure.NativeDrainOwnership.ready_frame_readback._proof_1_4 : ∀ {f : YulangClosure.NativeDrainOwnership.Frame},
  f.completed ≤ f.prepared →
    f.prepared ≤ f.acks.length → f.acks.length = f.completed → ¬f.prepared = f.acks.length → False
'YulangClosure.NativeDrainOwnership.ready_frame_readback._proof_1_4' depends on axioms: [propext, Quot.sound]

@YulangClosure.NativeDrainOwnership.ReturnReceipt.mk.inj : ∀ {frame frame_1 : YulangClosure.NativeDrainOwnership.Frame},
  { frame := frame } = { frame := frame_1 } → frame = frame_1
'YulangClosure.NativeDrainOwnership.ReturnReceipt.mk.inj' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.step_invariant._proof_1_48 : ∀ {s : YulangClosure.NativeDrainOwnership.State},
  (∀ (w : YulangClosure.NativeDrainOwnership.Work),
      w ∈ s.issued →
        w ∈ s.queue ∨
          (∃ f, f ∈ s.frames ∧ (f.current = Option.some w ∨ w ∈ f.processed)) ∨
            ∃ r, r ∈ s.returns ∧ w ∈ r.frame.processed) →
    ∀ (w : YulangClosure.NativeDrainOwnership.Work),
      w ∈ s.issued →
        w ∈ s.queue ∨
          (∃ f,
              (∃ a,
                  a ∈ s.frames ∧
                    { birth := a.birth, index := a.index, current := a.current, processing := a.processing,
                        processed := a.processed, done := a.done, pending := a.pending, prepared := a.done.length,
                        phase := a.phase, diagnosed := a.diagnosed, destination := a.destination,
                        transitions := a.transitions } =
                      f) ∧
                (f.current = Option.some w ∨ w ∈ f.processed)) ∨
            ∃ r, r ∈ s.returns ∧ w ∈ r.frame.processed
'YulangClosure.NativeDrainOwnership.step_invariant._proof_1_48' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

YulangClosure.NativeDrainOwnership.instDecidableEqWait.decEq._proof_9 : ∀
  (ticket : YulangClosure.NativeDrainOwnership.Ticket) (frame transitions : Nat)
  (ticket_1 : YulangClosure.NativeDrainOwnership.Ticket) (frame_1 : Nat),
  YulangClosure.NativeDrainOwnership.Wait.ready ticket frame transitions =
      YulangClosure.NativeDrainOwnership.Wait.running ticket_1 frame_1 →
    False
'YulangClosure.NativeDrainOwnership.instDecidableEqWait.decEq._proof_9' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.step_invariant._proof_1_21 : ∀ {s : YulangClosure.NativeDrainOwnership.State}
  (f : YulangClosure.NativeDrainOwnership.Frame) (fs : List YulangClosure.NativeDrainOwnership.Frame)
  (id index task relation : Nat) (op : YulangClosure.NativeDrainOwnership.Operation),
  (∀ (w : YulangClosure.NativeDrainOwnership.Work),
      w ∈ s.issued →
        w ∈ s.queue ∨
          ((f.current = Option.some w ∨ w ∈ f.processed) ∨
              ∃ x, x ∈ fs ∧ (x.current = Option.some w ∨ w ∈ x.processed)) ∨
            ∃ r, r ∈ s.returns ∧ w ∈ r.frame.processed) →
    ∀ (w : YulangClosure.NativeDrainOwnership.Work),
      w ∈ s.issued ∨
          w =
            { serial := s.nextWork, task := task, relation := relation,
              ticket := Option.some (YulangClosure.NativeDrainOwnership.selectedTicket id op index relation) } →
        (w ∈ s.queue ∨
            w =
              { serial := s.nextWork, task := task, relation := relation,
                ticket := Option.some (YulangClosure.NativeDrainOwnership.selectedTicket id op index relation) }) ∨
          ((f.current = Option.some w ∨ w ∈ f.processed) ∨
              ∃ x, x ∈ fs ∧ (x.current = Option.some w ∨ w ∈ x.processed)) ∨
            ∃ r, r ∈ s.returns ∧ w ∈ r.frame.processed
'YulangClosure.NativeDrainOwnership.step_invariant._proof_1_21' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

@YulangClosure.NativeDrainOwnership.Invariant.tasks : ∀ {s : YulangClosure.NativeDrainOwnership.State},
  YulangClosure.NativeDrainOwnership.Invariant s →
    ∀ (w : YulangClosure.NativeDrainOwnership.Work), w ∈ s.issued → YulangClosure.NativeDrainOwnership.TaskCovered s w
'YulangClosure.NativeDrainOwnership.Invariant.tasks' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.step_invariant._proof_1_16 : ∀ {s : YulangClosure.NativeDrainOwnership.State}
  (f : YulangClosure.NativeDrainOwnership.Frame) (fs : List YulangClosure.NativeDrainOwnership.Frame)
  (task relation : Nat),
  (∀ (w : YulangClosure.NativeDrainOwnership.Work),
      w ∈ s.issued →
        w ∈ s.queue ∨
          ((f.current = Option.some w ∨ w ∈ f.processed) ∨
              ∃ x, x ∈ fs ∧ (x.current = Option.some w ∨ w ∈ x.processed)) ∨
            ∃ r, r ∈ s.returns ∧ w ∈ r.frame.processed) →
    ∀ (w : YulangClosure.NativeDrainOwnership.Work),
      w ∈ s.issued ∨ w = { serial := s.nextWork, task := task, relation := relation, ticket := Option.none } →
        (w ∈ s.queue ∨ w = { serial := s.nextWork, task := task, relation := relation, ticket := Option.none }) ∨
          ((f.current = Option.some w ∨ w ∈ f.processed) ∨
              ∃ x, x ∈ fs ∧ (x.current = Option.some w ∨ w ∈ x.processed)) ∨
            ∃ r, r ∈ s.returns ∧ w ∈ r.frame.processed
'YulangClosure.NativeDrainOwnership.step_invariant._proof_1_16' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

@YulangClosure.NativeDrainOwnership.frame_prefix_has_real_receipts : ∀ {s : YulangClosure.NativeDrainOwnership.State},
  YulangClosure.NativeDrainOwnership.Run YulangClosure.NativeDrainOwnership.initial s →
    ∀ {f : YulangClosure.NativeDrainOwnership.Frame},
      f ∈ s.frames →
        ∀ (a : YulangClosure.NativeDrainOwnership.Ticket),
          a ∈ f.done → ∃ r, r ∈ s.acknowledgements ∧ r.ticket = a ∧ r.diagnosed = Bool.true
'YulangClosure.NativeDrainOwnership.frame_prefix_has_real_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

YulangClosure.NativeDrainOwnership.step_invariant._proof_1_31 : ∀ (op : YulangClosure.NativeDrainOwnership.Operation),
  op.consumed + 1 ≤ op.children.length → op.consumed < op.children.length
'YulangClosure.NativeDrainOwnership.step_invariant._proof_1_31' depends on axioms: [propext]

YulangClosure.NativeDrainOwnership.instDecidableEqWait.decEq._proof_7 : ∀
  (ticket : YulangClosure.NativeDrainOwnership.Ticket) (frame : Nat)
  (ticket_1 : YulangClosure.NativeDrainOwnership.Ticket) (frame_1 transitions : Nat),
  YulangClosure.NativeDrainOwnership.Wait.running ticket frame =
      YulangClosure.NativeDrainOwnership.Wait.ready ticket_1 frame_1 transitions →
    False
'YulangClosure.NativeDrainOwnership.instDecidableEqWait.decEq._proof_7' does not depend on any axioms

YulangClosure.NativeDrainOwnership.instDecidableEqFrame.decEq._proof_3 : ∀ (a a_1 : Nat)
  (a_2 : Option YulangClosure.NativeDrainOwnership.Work) (a_3 : Option Nat)
  (a_4 : List YulangClosure.NativeDrainOwnership.Work) (a_5 a_6 : List YulangClosure.NativeDrainOwnership.Ticket)
  (a_7 : Nat) (a_8 : YulangClosure.NativeDrainOwnership.Phase) (a_9 : Bool)
  (a_10 : Option YulangClosure.NativeDrainOwnership.Ticket) (a_11 : Nat)
  (b : Option YulangClosure.NativeDrainOwnership.Ticket) (b_1 : Nat),
  ¬a_10 = b →
    { birth := a, index := a_1, current := a_2, processing := a_3, processed := a_4, done := a_5, pending := a_6,
          prepared := a_7, phase := a_8, diagnosed := a_9, destination := a_10, transitions := a_11 } =
        { birth := a, index := a_1, current := a_2, processing := a_3, processed := a_4, done := a_5, pending := a_6,
          prepared := a_7, phase := a_8, diagnosed := a_9, destination := b, transitions := b_1 } →
      False
'YulangClosure.NativeDrainOwnership.instDecidableEqFrame.decEq._proof_3' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.step_invariant._proof_1_43 : ∀ {s : YulangClosure.NativeDrainOwnership.State}
  (f : YulangClosure.NativeDrainOwnership.Frame) (fs : List YulangClosure.NativeDrainOwnership.Frame)
  (a : YulangClosure.NativeDrainOwnership.Ticket),
  ((∀ (a : YulangClosure.NativeDrainOwnership.Ticket), a ∈ f.done → ∃ r, r ∈ s.acknowledgements ∧ r.ticket = a) ∧
      ∀ (a : YulangClosure.NativeDrainOwnership.Frame),
        a ∈ fs →
          ∀ (a_2 : YulangClosure.NativeDrainOwnership.Ticket),
            a_2 ∈ a.done → ∃ r, r ∈ s.acknowledgements ∧ r.ticket = a_2) →
    (∀ (a_1 : YulangClosure.NativeDrainOwnership.Ticket),
        a_1 ∈ f.done ∨ a_1 = a → (∃ x, x ∈ s.acknowledgements ∧ x.ticket = a_1) ∨ a = a_1) ∧
      ∀ (a_1 : YulangClosure.NativeDrainOwnership.Frame),
        a_1 ∈ fs →
          ∀ (a_3 : YulangClosure.NativeDrainOwnership.Ticket),
            a_3 ∈ a_1.done → (∃ x, x ∈ s.acknowledgements ∧ x.ticket = a_3) ∨ a = a_3
'YulangClosure.NativeDrainOwnership.step_invariant._proof_1_43' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

YulangClosure.NativeDrainOwnership.instDecidableEqChild.decEq._proof_2 : ∀ (a a_1 b : Nat),
  ¬a_1 = b → { task := a, relation := a_1 } = { task := a, relation := b } → False
'YulangClosure.NativeDrainOwnership.instDecidableEqChild.decEq._proof_2' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.run_invariant : ∀ {s t : YulangClosure.NativeDrainOwnership.State},
  YulangClosure.NativeDrainOwnership.Run s t →
    YulangClosure.NativeDrainOwnership.Invariant s → YulangClosure.NativeDrainOwnership.Invariant t
'YulangClosure.NativeDrainOwnership.run_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]

YulangClosure.NativeDrainOwnership.instDecidableEqChild.decEq._proof_3 : ∀ (a a_1 b b_1 : Nat),
  ¬a = b → { task := a, relation := a_1 } = { task := b, relation := b_1 } → False
'YulangClosure.NativeDrainOwnership.instDecidableEqChild.decEq._proof_3' does not depend on any axioms

YulangClosure.NativeDrainOwnership.instDecidableEqWait.decEq._proof_6 : ∀
  (a : YulangClosure.NativeDrainOwnership.Ticket) (a_1 : Nat) (b : YulangClosure.NativeDrainOwnership.Ticket)
  (b_1 : Nat),
  ¬a = b →
    YulangClosure.NativeDrainOwnership.Wait.running a a_1 = YulangClosure.NativeDrainOwnership.Wait.running b b_1 →
      False
'YulangClosure.NativeDrainOwnership.instDecidableEqWait.decEq._proof_6' does not depend on any axioms

YulangClosure.NativeDrainOwnership.instDecidableEqTicket.decEq._proof_5 : ∀ (a a_1 a_2 a_3 b b_1 b_2 b_3 : Nat),
  ¬a = b →
    { birth := a, operation := a_1, index := a_2, relation := a_3 } =
        { birth := b, operation := b_1, index := b_2, relation := b_3 } →
      False
'YulangClosure.NativeDrainOwnership.instDecidableEqTicket.decEq._proof_5' does not depend on any axioms

YulangClosure.NativeDrainOwnership.Frame.completed.eq_1 : ∀ (f : YulangClosure.NativeDrainOwnership.Frame),
  f.completed = f.done.length
'YulangClosure.NativeDrainOwnership.Frame.completed.eq_1' does not depend on any axioms

_private.YulangClosure.NativeDrainOwnership.0.YulangClosure.NativeDrainOwnership.stackTicket_cons : ∀
  (a : YulangClosure.NativeDrainOwnership.Ticket) (f : YulangClosure.NativeDrainOwnership.Frame)
  (fs : List YulangClosure.NativeDrainOwnership.Frame),
  YulangClosure.NativeDrainOwnership.stackTicket a (f :: fs) ↔
    a ∈ f.acks ∨ YulangClosure.NativeDrainOwnership.stackTicket a fs
'_private.YulangClosure.NativeDrainOwnership.0.YulangClosure.NativeDrainOwnership.stackTicket_cons' depends on axioms: [propext,
 Quot.sound]

YulangClosure.NativeDrainOwnership.instDecidableEqOperation.decEq._proof_7 : ∀ (a a_1 : Nat)
  (a_2 : List YulangClosure.NativeDrainOwnership.Child) (a_3 a_4 : Nat) (a_5 : Bool)
  (a_6 : YulangClosure.NativeDrainOwnership.Wait) (b : Nat) (b_1 : List YulangClosure.NativeDrainOwnership.Child)
  (b_2 b_3 : Nat) (b_4 : Bool) (b_5 : YulangClosure.NativeDrainOwnership.Wait),
  ¬a_1 = b →
    { birth := a, task := a_1, children := a_2, queued := a_3, consumed := a_4, retired := a_5, waiting := a_6 } =
        { birth := a, task := b, children := b_1, queued := b_2, consumed := b_3, retired := b_4, waiting := b_5 } →
      False
'YulangClosure.NativeDrainOwnership.instDecidableEqOperation.decEq._proof_7' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.step_invariant._simp_1_15 : ∀ {α : Sort u_1} {p q : α → Prop},
  (∃ x, p x ∨ q x) = ((∃ x, p x) ∨ ∃ x, q x)
'YulangClosure.NativeDrainOwnership.step_invariant._simp_1_15' depends on axioms: [propext]

YulangClosure.NativeDrainOwnership.Wait.running.injEq : ∀ (ticket : YulangClosure.NativeDrainOwnership.Ticket)
  (frame : Nat) (ticket_1 : YulangClosure.NativeDrainOwnership.Ticket) (frame_1 : Nat),
  (YulangClosure.NativeDrainOwnership.Wait.running ticket frame =
      YulangClosure.NativeDrainOwnership.Wait.running ticket_1 frame_1) =
    (ticket = ticket_1 ∧ frame = frame_1)
'YulangClosure.NativeDrainOwnership.Wait.running.injEq' depends on axioms: [propext]

YulangClosure.NativeDrainOwnership.Wait.running.sizeOf_spec : ∀ (ticket : YulangClosure.NativeDrainOwnership.Ticket)
  (frame : Nat),
  SizeOf.sizeOf (YulangClosure.NativeDrainOwnership.Wait.running ticket frame) =
    1 + SizeOf.sizeOf ticket + SizeOf.sizeOf frame
'YulangClosure.NativeDrainOwnership.Wait.running.sizeOf_spec' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.step_invariant._proof_1_17 : ∀ {s : YulangClosure.NativeDrainOwnership.State}
  (f : YulangClosure.NativeDrainOwnership.Frame) (fs : List YulangClosure.NativeDrainOwnership.Frame),
  ((∀ (a : YulangClosure.NativeDrainOwnership.Ticket), a ∈ f.done → ∃ r, r ∈ s.acknowledgements ∧ r.ticket = a) ∧
      ∀ (a : YulangClosure.NativeDrainOwnership.Frame),
        a ∈ fs →
          ∀ (a_2 : YulangClosure.NativeDrainOwnership.Ticket),
            a_2 ∈ a.done → ∃ r, r ∈ s.acknowledgements ∧ r.ticket = a_2) →
    ∀ (a : YulangClosure.NativeDrainOwnership.Frame),
      a ∈ fs →
        ∀ (a_1 : YulangClosure.NativeDrainOwnership.Ticket), a_1 ∈ a.done → ∃ r, r ∈ s.acknowledgements ∧ r.ticket = a_1
'YulangClosure.NativeDrainOwnership.step_invariant._proof_1_17' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

_private.YulangClosure.NativeDrainOwnership.0.YulangClosure.NativeDrainOwnership.queueTicket_cons : ∀
  (a : YulangClosure.NativeDrainOwnership.Ticket) (w : YulangClosure.NativeDrainOwnership.Work)
  (ws : List YulangClosure.NativeDrainOwnership.Work),
  YulangClosure.NativeDrainOwnership.queueTicket a (w :: ws) ↔
    w.ticket = Option.some a ∨ YulangClosure.NativeDrainOwnership.queueTicket a ws
'_private.YulangClosure.NativeDrainOwnership.0.YulangClosure.NativeDrainOwnership.queueTicket_cons' depends on axioms: [propext,
 Quot.sound]

YulangClosure.NativeDrainOwnership.Frame.acks.eq_1 : ∀ (f : YulangClosure.NativeDrainOwnership.Frame),
  f.acks = f.done ++ f.pending
'YulangClosure.NativeDrainOwnership.Frame.acks.eq_1' does not depend on any axioms

YulangClosure.NativeDrainOwnership.instDecidableEqChild.decEq._proof_1 : ∀ (a a_1 : Nat),
  { task := a, relation := a_1 } = { task := a, relation := a_1 }
'YulangClosure.NativeDrainOwnership.instDecidableEqChild.decEq._proof_1' does not depend on any axioms

YulangClosure.NativeDrainOwnership.instDecidableEqFrame.decEq._proof_13 : ∀ (a a_1 : Nat)
  (a_2 : Option YulangClosure.NativeDrainOwnership.Work) (a_3 : Option Nat)
  (a_4 : List YulangClosure.NativeDrainOwnership.Work) (a_5 a_6 : List YulangClosure.NativeDrainOwnership.Ticket)
  (a_7 : Nat) (a_8 : YulangClosure.NativeDrainOwnership.Phase) (a_9 : Bool)
  (a_10 : Option YulangClosure.NativeDrainOwnership.Ticket) (a_11 b b_1 : Nat)
  (b_2 : Option YulangClosure.NativeDrainOwnership.Work) (b_3 : Option Nat)
  (b_4 : List YulangClosure.NativeDrainOwnership.Work) (b_5 b_6 : List YulangClosure.NativeDrainOwnership.Ticket)
  (b_7 : Nat) (b_8 : YulangClosure.NativeDrainOwnership.Phase) (b_9 : Bool)
  (b_10 : Option YulangClosure.NativeDrainOwnership.Ticket) (b_11 : Nat),
  ¬a = b →
    { birth := a, index := a_1, current := a_2, processing := a_3, processed := a_4, done := a_5, pending := a_6,
          prepared := a_7, phase := a_8, diagnosed := a_9, destination := a_10, transitions := a_11 } =
        { birth := b, index := b_1, current := b_2, processing := b_3, processed := b_4, done := b_5, pending := b_6,
          prepared := b_7, phase := b_8, diagnosed := b_9, destination := b_10, transitions := b_11 } →
      False
'YulangClosure.NativeDrainOwnership.instDecidableEqFrame.decEq._proof_13' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.Invariant.done : ∀ {s : YulangClosure.NativeDrainOwnership.State},
  YulangClosure.NativeDrainOwnership.Invariant s →
    ∀ (f : YulangClosure.NativeDrainOwnership.Frame),
      f ∈ s.frames →
        ∀ (a : YulangClosure.NativeDrainOwnership.Ticket),
          a ∈ f.done → YulangClosure.NativeDrainOwnership.received a s.acknowledgements
'YulangClosure.NativeDrainOwnership.Invariant.done' does not depend on any axioms

YulangClosure.NativeDrainOwnership.step_invariant._proof_1_39 : ∀ (f : YulangClosure.NativeDrainOwnership.Frame)
  (a : YulangClosure.NativeDrainOwnership.Ticket),
  (f.done ++ f.pending)[f.prepared]? = Option.some a → f.prepared < (f.done ++ f.pending).length
'YulangClosure.NativeDrainOwnership.step_invariant._proof_1_39' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

YulangClosure.NativeDrainOwnership.instDecidableEqFrame.decEq._proof_4 : ∀ (a a_1 : Nat)
  (a_2 : Option YulangClosure.NativeDrainOwnership.Work) (a_3 : Option Nat)
  (a_4 : List YulangClosure.NativeDrainOwnership.Work) (a_5 a_6 : List YulangClosure.NativeDrainOwnership.Ticket)
  (a_7 : Nat) (a_8 : YulangClosure.NativeDrainOwnership.Phase) (a_9 : Bool)
  (a_10 : Option YulangClosure.NativeDrainOwnership.Ticket) (a_11 : Nat) (b : Bool)
  (b_1 : Option YulangClosure.NativeDrainOwnership.Ticket) (b_2 : Nat),
  ¬a_9 = b →
    { birth := a, index := a_1, current := a_2, processing := a_3, processed := a_4, done := a_5, pending := a_6,
          prepared := a_7, phase := a_8, diagnosed := a_9, destination := a_10, transitions := a_11 } =
        { birth := a, index := a_1, current := a_2, processing := a_3, processed := a_4, done := a_5, pending := a_6,
          prepared := a_7, phase := a_8, diagnosed := b, destination := b_1, transitions := b_2 } →
      False
'YulangClosure.NativeDrainOwnership.instDecidableEqFrame.decEq._proof_4' does not depend on any axioms

YulangClosure.NativeDrainOwnership.instDecidableEqWait.decEq._proof_4 : ∀
  (a : YulangClosure.NativeDrainOwnership.Ticket) (a_1 : Nat),
  YulangClosure.NativeDrainOwnership.Wait.running a a_1 = YulangClosure.NativeDrainOwnership.Wait.running a a_1
'YulangClosure.NativeDrainOwnership.instDecidableEqWait.decEq._proof_4' does not depend on any axioms

YulangClosure.NativeDrainOwnership.Wait.idle.sizeOf_spec : SizeOf.sizeOf YulangClosure.NativeDrainOwnership.Wait.idle =
  1
'YulangClosure.NativeDrainOwnership.Wait.idle.sizeOf_spec' does not depend on any axioms

YulangClosure.NativeDrainOwnership.step_coherent._proof_1_11 : ∀ (f : YulangClosure.NativeDrainOwnership.Frame)
  (fs : List YulangClosure.NativeDrainOwnership.Frame) (a : YulangClosure.NativeDrainOwnership.Ticket),
  (((¬f.phase = YulangClosure.NativeDrainOwnership.Phase.working → f.current = Option.none) ∧
        (f.phase = YulangClosure.NativeDrainOwnership.Phase.acknowledgements ∨
              f.phase = YulangClosure.NativeDrainOwnership.Phase.returnReady →
            f.diagnosed = Bool.true) ∧
          (f.phase = YulangClosure.NativeDrainOwnership.Phase.returnReady → f.pending = []) ∧
            f.done.length ≤ f.prepared ∧ f.prepared ≤ f.done.length + f.pending.length) ∧
      ∀ (a : YulangClosure.NativeDrainOwnership.Frame),
        a ∈ fs →
          (¬a.phase = YulangClosure.NativeDrainOwnership.Phase.working → a.current = Option.none) ∧
            (a.phase = YulangClosure.NativeDrainOwnership.Phase.acknowledgements ∨
                  a.phase = YulangClosure.NativeDrainOwnership.Phase.returnReady →
                a.diagnosed = Bool.true) ∧
              (a.phase = YulangClosure.NativeDrainOwnership.Phase.returnReady → a.pending = []) ∧
                a.done.length ≤ a.prepared ∧ a.prepared ≤ a.done.length + a.pending.length) →
    (f.done ++ f.pending)[f.prepared]? = Option.some a →
      f.done.length ≤ f.prepared + 1 ∧ f.prepared + 1 ≤ f.done.length + f.pending.length
'YulangClosure.NativeDrainOwnership.step_coherent._proof_1_11' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

_private.YulangClosure.NativeDrainOwnership.0.YulangClosure.NativeDrainOwnership.queueTicket_append : ∀
  (a : YulangClosure.NativeDrainOwnership.Ticket) (xs ys : List YulangClosure.NativeDrainOwnership.Work),
  YulangClosure.NativeDrainOwnership.queueTicket a (xs ++ ys) ↔
    YulangClosure.NativeDrainOwnership.queueTicket a xs ∨ YulangClosure.NativeDrainOwnership.queueTicket a ys
'_private.YulangClosure.NativeDrainOwnership.0.YulangClosure.NativeDrainOwnership.queueTicket_append' depends on axioms: [propext,
 Quot.sound]

@YulangClosure.NativeDrainOwnership.step_invariant._proof_1_46 : ∀ {s : YulangClosure.NativeDrainOwnership.State}
  (f : YulangClosure.NativeDrainOwnership.Frame) (fs : List YulangClosure.NativeDrainOwnership.Frame),
  (∀ (a : YulangClosure.NativeDrainOwnership.Ticket),
      a ∈ s.transferred →
        (∃ w, w ∈ s.queue ∧ w.ticket = Option.some a) ∨
          (a ∈ f.done ∨ ∃ x, x ∈ fs ∧ (a ∈ x.done ∨ a ∈ x.pending)) ∨ ∃ r, r ∈ s.acknowledgements ∧ r.ticket = a) →
    ((∀ (a : YulangClosure.NativeDrainOwnership.Ticket), a ∈ f.done → ∃ r, r ∈ s.acknowledgements ∧ r.ticket = a) ∧
        ∀ (a : YulangClosure.NativeDrainOwnership.Frame),
          a ∈ fs →
            ∀ (a_2 : YulangClosure.NativeDrainOwnership.Ticket),
              a_2 ∈ a.done → ∃ r, r ∈ s.acknowledgements ∧ r.ticket = a_2) →
      ∀ (a : YulangClosure.NativeDrainOwnership.Ticket),
        a ∈ s.transferred →
          (∃ w, w ∈ s.queue ∧ w.ticket = Option.some a) ∨
            (∃ f, f ∈ fs ∧ (a ∈ f.done ∨ a ∈ f.pending)) ∨ ∃ r, r ∈ s.acknowledgements ∧ r.ticket = a
'YulangClosure.NativeDrainOwnership.step_invariant._proof_1_46' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

@YulangClosure.NativeDrainOwnership.State.mk.inj : ∀
  {operations : Nat → Option YulangClosure.NativeDrainOwnership.Operation} {nextOperation nextBirth nextWork : Nat}
  {queue : List YulangClosure.NativeDrainOwnership.Work} {frames : List YulangClosure.NativeDrainOwnership.Frame}
  {issued : List YulangClosure.NativeDrainOwnership.Work} {transferred : List YulangClosure.NativeDrainOwnership.Ticket}
  {acknowledgements : List YulangClosure.NativeDrainOwnership.AckReceipt}
  {returns : List YulangClosure.NativeDrainOwnership.ReturnReceipt}
  {operations_1 : Nat → Option YulangClosure.NativeDrainOwnership.Operation}
  {nextOperation_1 nextBirth_1 nextWork_1 : Nat} {queue_1 : List YulangClosure.NativeDrainOwnership.Work}
  {frames_1 : List YulangClosure.NativeDrainOwnership.Frame} {issued_1 : List YulangClosure.NativeDrainOwnership.Work}
  {transferred_1 : List YulangClosure.NativeDrainOwnership.Ticket}
  {acknowledgements_1 : List YulangClosure.NativeDrainOwnership.AckReceipt}
  {returns_1 : List YulangClosure.NativeDrainOwnership.ReturnReceipt},
  { operations := operations, nextOperation := nextOperation, nextBirth := nextBirth, nextWork := nextWork,
        queue := queue, frames := frames, issued := issued, transferred := transferred,
        acknowledgements := acknowledgements, returns := returns } =
      { operations := operations_1, nextOperation := nextOperation_1, nextBirth := nextBirth_1, nextWork := nextWork_1,
        queue := queue_1, frames := frames_1, issued := issued_1, transferred := transferred_1,
        acknowledgements := acknowledgements_1, returns := returns_1 } →
    operations = operations_1 ∧
      nextOperation = nextOperation_1 ∧
        nextBirth = nextBirth_1 ∧
          nextWork = nextWork_1 ∧
            queue = queue_1 ∧
              frames = frames_1 ∧
                issued = issued_1 ∧
                  transferred = transferred_1 ∧ acknowledgements = acknowledgements_1 ∧ returns = returns_1
'YulangClosure.NativeDrainOwnership.State.mk.inj' does not depend on any axioms

YulangClosure.NativeDrainOwnership.instDecidableEqOperation.decEq._proof_6 : ∀ (a a_1 : Nat)
  (a_2 : List YulangClosure.NativeDrainOwnership.Child) (a_3 a_4 : Nat) (a_5 : Bool)
  (a_6 : YulangClosure.NativeDrainOwnership.Wait) (b : List YulangClosure.NativeDrainOwnership.Child) (b_1 b_2 : Nat)
  (b_3 : Bool) (b_4 : YulangClosure.NativeDrainOwnership.Wait),
  ¬a_2 = b →
    { birth := a, task := a_1, children := a_2, queued := a_3, consumed := a_4, retired := a_5, waiting := a_6 } =
        { birth := a, task := a_1, children := b, queued := b_1, consumed := b_2, retired := b_3, waiting := b_4 } →
      False
'YulangClosure.NativeDrainOwnership.instDecidableEqOperation.decEq._proof_6' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.outstanding_ticket_has_owner : ∀ {s : YulangClosure.NativeDrainOwnership.State},
  YulangClosure.NativeDrainOwnership.Run YulangClosure.NativeDrainOwnership.initial s →
    ∀ {a : YulangClosure.NativeDrainOwnership.Ticket},
      a ∈ s.transferred →
        ¬YulangClosure.NativeDrainOwnership.received a s.acknowledgements →
          YulangClosure.NativeDrainOwnership.queueTicket a s.queue ∨
            YulangClosure.NativeDrainOwnership.stackTicket a s.frames
'YulangClosure.NativeDrainOwnership.outstanding_ticket_has_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

YulangClosure.NativeDrainOwnership.ReturnReceipt.mk.sizeOf_spec : ∀ (frame : YulangClosure.NativeDrainOwnership.Frame),
  SizeOf.sizeOf { frame := frame } = 1 + SizeOf.sizeOf frame
'YulangClosure.NativeDrainOwnership.ReturnReceipt.mk.sizeOf_spec' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.Frame.mk.inj : ∀ {birth index : Nat}
  {current : Option YulangClosure.NativeDrainOwnership.Work} {processing : Option Nat}
  {processed : List YulangClosure.NativeDrainOwnership.Work}
  {done pending : List YulangClosure.NativeDrainOwnership.Ticket} {prepared : Nat}
  {phase : YulangClosure.NativeDrainOwnership.Phase} {diagnosed : Bool}
  {destination : Option YulangClosure.NativeDrainOwnership.Ticket} {transitions birth_1 index_1 : Nat}
  {current_1 : Option YulangClosure.NativeDrainOwnership.Work} {processing_1 : Option Nat}
  {processed_1 : List YulangClosure.NativeDrainOwnership.Work}
  {done_1 pending_1 : List YulangClosure.NativeDrainOwnership.Ticket} {prepared_1 : Nat}
  {phase_1 : YulangClosure.NativeDrainOwnership.Phase} {diagnosed_1 : Bool}
  {destination_1 : Option YulangClosure.NativeDrainOwnership.Ticket} {transitions_1 : Nat},
  { birth := birth, index := index, current := current, processing := processing, processed := processed, done := done,
        pending := pending, prepared := prepared, phase := phase, diagnosed := diagnosed, destination := destination,
        transitions := transitions } =
      { birth := birth_1, index := index_1, current := current_1, processing := processing_1, processed := processed_1,
        done := done_1, pending := pending_1, prepared := prepared_1, phase := phase_1, diagnosed := diagnosed_1,
        destination := destination_1, transitions := transitions_1 } →
    birth = birth_1 ∧
      index = index_1 ∧
        current = current_1 ∧
          processing = processing_1 ∧
            processed = processed_1 ∧
              done = done_1 ∧
                pending = pending_1 ∧
                  prepared = prepared_1 ∧
                    phase = phase_1 ∧
                      diagnosed = diagnosed_1 ∧ destination = destination_1 ∧ transitions = transitions_1
'YulangClosure.NativeDrainOwnership.Frame.mk.inj' does not depend on any axioms

YulangClosure.NativeDrainOwnership.Phase.returnReady.sizeOf_spec : SizeOf.sizeOf
    YulangClosure.NativeDrainOwnership.Phase.returnReady =
  1
'YulangClosure.NativeDrainOwnership.Phase.returnReady.sizeOf_spec' does not depend on any axioms

YulangClosure.NativeDrainOwnership.Witness.synchronous_transport_readback : Option.map
      YulangClosure.NativeDrainOwnership.Frame.processing
      YulangClosure.NativeDrainOwnership.Witness.transported.frames.head? =
    Option.some (Option.some 99) ∧
  YulangClosure.NativeDrainOwnership.Witness.delivered.issued =
      [YulangClosure.NativeDrainOwnership.Witness.occurrence] ∧
    YulangClosure.NativeDrainOwnership.Witness.delivered.transferred =
        [YulangClosure.NativeDrainOwnership.Witness.ticket] ∧
      YulangClosure.NativeDrainOwnership.Witness.delivered.queue = [] ∧
        YulangClosure.NativeDrainOwnership.Witness.delivered.frames = [] ∧
          YulangClosure.NativeDrainOwnership.Witness.delivered.acknowledgements =
              [YulangClosure.NativeDrainOwnership.receipt YulangClosure.NativeDrainOwnership.Witness.diagnosedFrame
                  YulangClosure.NativeDrainOwnership.Witness.ticket] ∧
            YulangClosure.NativeDrainOwnership.Witness.delivered.acknowledgements =
                YulangClosure.NativeDrainOwnership.Witness.returned.acknowledgements ∧
              YulangClosure.NativeDrainOwnership.Witness.delivered.returns =
                  [{ frame := YulangClosure.NativeDrainOwnership.Witness.completedFrame }] ∧
                YulangClosure.NativeDrainOwnership.Witness.delivered.operations 0 =
                    Option.some
                      (have __src := YulangClosure.NativeDrainOwnership.Witness.completedOp;
                      { birth := __src.birth, task := __src.task, children := __src.children, queued := __src.queued,
                        consumed := __src.consumed, retired := __src.retired }) ∧
                  YulangClosure.NativeDrainOwnership.Witness.completedOp.consumed = 1 ∧
                    YulangClosure.NativeDrainOwnership.Witness.completedOp.queued = 1
'YulangClosure.NativeDrainOwnership.Witness.synchronous_transport_readback' does not depend on any axioms

_private.YulangClosure.NativeDrainOwnership.0.YulangClosure.NativeDrainOwnership.received_append : ∀
  (a : YulangClosure.NativeDrainOwnership.Ticket) (xs ys : List YulangClosure.NativeDrainOwnership.AckReceipt),
  YulangClosure.NativeDrainOwnership.received a (xs ++ ys) ↔
    YulangClosure.NativeDrainOwnership.received a xs ∨ YulangClosure.NativeDrainOwnership.received a ys
'_private.YulangClosure.NativeDrainOwnership.0.YulangClosure.NativeDrainOwnership.received_append' depends on axioms: [propext,
 Quot.sound]

YulangClosure.NativeDrainOwnership.ReturnReceipt.mk.injEq : ∀
  (frame frame_1 : YulangClosure.NativeDrainOwnership.Frame),
  ({ frame := frame } = { frame := frame_1 }) = (frame = frame_1)
'YulangClosure.NativeDrainOwnership.ReturnReceipt.mk.injEq' depends on axioms: [propext]

_private.YulangClosure.NativeDrainOwnership.0.YulangClosure.NativeDrainOwnership.returnedWork_append : ∀
  (w : YulangClosure.NativeDrainOwnership.Work) (xs ys : List YulangClosure.NativeDrainOwnership.ReturnReceipt),
  YulangClosure.NativeDrainOwnership.returnedWork w (xs ++ ys) ↔
    YulangClosure.NativeDrainOwnership.returnedWork w xs ∨ YulangClosure.NativeDrainOwnership.returnedWork w ys
'_private.YulangClosure.NativeDrainOwnership.0.YulangClosure.NativeDrainOwnership.returnedWork_append' depends on axioms: [propext,
 Quot.sound]

YulangClosure.NativeDrainOwnership.AckReceipt.mk.injEq : ∀ (ticket : YulangClosure.NativeDrainOwnership.Ticket)
  (frameBirth frameIndex : Nat) (diagnosed : Bool) (ticket_1 : YulangClosure.NativeDrainOwnership.Ticket)
  (frameBirth_1 frameIndex_1 : Nat) (diagnosed_1 : Bool),
  ({ ticket := ticket, frameBirth := frameBirth, frameIndex := frameIndex, diagnosed := diagnosed } =
      { ticket := ticket_1, frameBirth := frameBirth_1, frameIndex := frameIndex_1, diagnosed := diagnosed_1 }) =
    (ticket = ticket_1 ∧ frameBirth = frameBirth_1 ∧ frameIndex = frameIndex_1 ∧ diagnosed = diagnosed_1)
'YulangClosure.NativeDrainOwnership.AckReceipt.mk.injEq' depends on axioms: [propext]

YulangClosure.NativeDrainOwnership.work.eq_1 : ∀ (s : YulangClosure.NativeDrainOwnership.State) (task relation : Nat)
  (ticket : Option YulangClosure.NativeDrainOwnership.Ticket),
  YulangClosure.NativeDrainOwnership.work s task relation ticket =
    { serial := s.nextWork, task := task, relation := relation, ticket := ticket }
'YulangClosure.NativeDrainOwnership.work.eq_1' does not depend on any axioms

YulangClosure.NativeDrainOwnership.instDecidableEqFrame.decEq._proof_12 : ∀ (a a_1 : Nat)
  (a_2 : Option YulangClosure.NativeDrainOwnership.Work) (a_3 : Option Nat)
  (a_4 : List YulangClosure.NativeDrainOwnership.Work) (a_5 a_6 : List YulangClosure.NativeDrainOwnership.Ticket)
  (a_7 : Nat) (a_8 : YulangClosure.NativeDrainOwnership.Phase) (a_9 : Bool)
  (a_10 : Option YulangClosure.NativeDrainOwnership.Ticket) (a_11 b : Nat)
  (b_1 : Option YulangClosure.NativeDrainOwnership.Work) (b_2 : Option Nat)
  (b_3 : List YulangClosure.NativeDrainOwnership.Work) (b_4 b_5 : List YulangClosure.NativeDrainOwnership.Ticket)
  (b_6 : Nat) (b_7 : YulangClosure.NativeDrainOwnership.Phase) (b_8 : Bool)
  (b_9 : Option YulangClosure.NativeDrainOwnership.Ticket) (b_10 : Nat),
  ¬a_1 = b →
    { birth := a, index := a_1, current := a_2, processing := a_3, processed := a_4, done := a_5, pending := a_6,
          prepared := a_7, phase := a_8, diagnosed := a_9, destination := a_10, transitions := a_11 } =
        { birth := a, index := b, current := b_1, processing := b_2, processed := b_3, done := b_4, pending := b_5,
          prepared := b_6, phase := b_7, diagnosed := b_8, destination := b_9, transitions := b_10 } →
      False
'YulangClosure.NativeDrainOwnership.instDecidableEqFrame.decEq._proof_12' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.step_invariant._proof_1_44 : ∀ {s : YulangClosure.NativeDrainOwnership.State}
  (f : YulangClosure.NativeDrainOwnership.Frame) (a : YulangClosure.NativeDrainOwnership.Ticket),
  (∀ (r : YulangClosure.NativeDrainOwnership.AckReceipt), r ∈ s.acknowledgements → r.diagnosed = Bool.true) →
    ∀ (r : YulangClosure.NativeDrainOwnership.AckReceipt),
      r ∈ s.acknowledgements ∨
          r = { ticket := a, frameBirth := f.birth, frameIndex := f.index, diagnosed := Bool.true } →
        r.diagnosed = Bool.true
'YulangClosure.NativeDrainOwnership.step_invariant._proof_1_44' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

YulangClosure.NativeDrainOwnership.stackWork.eq_1 : ∀ (w : YulangClosure.NativeDrainOwnership.Work)
  (fs : List YulangClosure.NativeDrainOwnership.Frame),
  YulangClosure.NativeDrainOwnership.stackWork w fs = ∃ f, f ∈ fs ∧ YulangClosure.NativeDrainOwnership.frameWork w f
'YulangClosure.NativeDrainOwnership.stackWork.eq_1' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.Work.mk.inj : ∀ {serial task relation : Nat}
  {ticket : Option YulangClosure.NativeDrainOwnership.Ticket} {serial_1 task_1 relation_1 : Nat}
  {ticket_1 : Option YulangClosure.NativeDrainOwnership.Ticket},
  { serial := serial, task := task, relation := relation, ticket := ticket } =
      { serial := serial_1, task := task_1, relation := relation_1, ticket := ticket_1 } →
    serial = serial_1 ∧ task = task_1 ∧ relation = relation_1 ∧ ticket = ticket_1
'YulangClosure.NativeDrainOwnership.Work.mk.inj' does not depend on any axioms

YulangClosure.NativeDrainOwnership.Ticket.mk.injEq : ∀
  (birth operation index relation birth_1 operation_1 index_1 relation_1 : Nat),
  ({ birth := birth, operation := operation, index := index, relation := relation } =
      { birth := birth_1, operation := operation_1, index := index_1, relation := relation_1 }) =
    (birth = birth_1 ∧ operation = operation_1 ∧ index = index_1 ∧ relation = relation_1)
'YulangClosure.NativeDrainOwnership.Ticket.mk.injEq' depends on axioms: [propext]

YulangClosure.NativeDrainOwnership.Coherent.eq_1 : ∀ (s : YulangClosure.NativeDrainOwnership.State),
  YulangClosure.NativeDrainOwnership.Coherent s =
    ∀ (f : YulangClosure.NativeDrainOwnership.Frame), f ∈ s.frames → f.coherent
'YulangClosure.NativeDrainOwnership.Coherent.eq_1' does not depend on any axioms

YulangClosure.NativeDrainOwnership.step_invariant._proof_1_41 : ∀ (f : YulangClosure.NativeDrainOwnership.Frame)
  (a : YulangClosure.NativeDrainOwnership.Ticket),
  (f.done ++ f.pending)[f.prepared]? = Option.some a →
    ¬f.prepared + 1 ≤ f.done.length → f.prepared - f.done.length < f.pending.length
'YulangClosure.NativeDrainOwnership.step_invariant._proof_1_41' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

@YulangClosure.NativeDrainOwnership.run_coherent : ∀ {s t : YulangClosure.NativeDrainOwnership.State},
  YulangClosure.NativeDrainOwnership.Run s t →
    YulangClosure.NativeDrainOwnership.Coherent s → YulangClosure.NativeDrainOwnership.Coherent t
'YulangClosure.NativeDrainOwnership.run_coherent' depends on axioms: [propext, Classical.choice, Quot.sound]

YulangClosure.NativeDrainOwnership.Frame.mk.injEq : ∀ (birth index : Nat)
  (current : Option YulangClosure.NativeDrainOwnership.Work) (processing : Option Nat)
  (processed : List YulangClosure.NativeDrainOwnership.Work)
  (done pending : List YulangClosure.NativeDrainOwnership.Ticket) (prepared : Nat)
  (phase : YulangClosure.NativeDrainOwnership.Phase) (diagnosed : Bool)
  (destination : Option YulangClosure.NativeDrainOwnership.Ticket) (transitions birth_1 index_1 : Nat)
  (current_1 : Option YulangClosure.NativeDrainOwnership.Work) (processing_1 : Option Nat)
  (processed_1 : List YulangClosure.NativeDrainOwnership.Work)
  (done_1 pending_1 : List YulangClosure.NativeDrainOwnership.Ticket) (prepared_1 : Nat)
  (phase_1 : YulangClosure.NativeDrainOwnership.Phase) (diagnosed_1 : Bool)
  (destination_1 : Option YulangClosure.NativeDrainOwnership.Ticket) (transitions_1 : Nat),
  ({ birth := birth, index := index, current := current, processing := processing, processed := processed, done := done,
        pending := pending, prepared := prepared, phase := phase, diagnosed := diagnosed, destination := destination,
        transitions := transitions } =
      { birth := birth_1, index := index_1, current := current_1, processing := processing_1, processed := processed_1,
        done := done_1, pending := pending_1, prepared := prepared_1, phase := phase_1, diagnosed := diagnosed_1,
        destination := destination_1, transitions := transitions_1 }) =
    (birth = birth_1 ∧
      index = index_1 ∧
        current = current_1 ∧
          processing = processing_1 ∧
            processed = processed_1 ∧
              done = done_1 ∧
                pending = pending_1 ∧
                  prepared = prepared_1 ∧
                    phase = phase_1 ∧
                      diagnosed = diagnosed_1 ∧ destination = destination_1 ∧ transitions = transitions_1)
'YulangClosure.NativeDrainOwnership.Frame.mk.injEq' depends on axioms: [propext]

YulangClosure.NativeDrainOwnership.initial_coherent : YulangClosure.NativeDrainOwnership.Coherent
  YulangClosure.NativeDrainOwnership.initial
'YulangClosure.NativeDrainOwnership.initial_coherent' depends on axioms: [propext, Quot.sound]

YulangClosure.NativeDrainOwnership.pushWork.eq_1 : ∀ (s : YulangClosure.NativeDrainOwnership.State)
  (w : YulangClosure.NativeDrainOwnership.Work) (front : Bool),
  YulangClosure.NativeDrainOwnership.pushWork s w front =
    { operations := s.operations, nextOperation := s.nextOperation, nextBirth := s.nextBirth,
      nextWork := s.nextWork + 1, queue := if front = Bool.true then w :: s.queue else s.queue ++ [w],
      frames := s.frames, issued := s.issued ++ [w], transferred := s.transferred,
      acknowledgements := s.acknowledgements, returns := s.returns }
'YulangClosure.NativeDrainOwnership.pushWork.eq_1' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.reachable_invariant : ∀ {s : YulangClosure.NativeDrainOwnership.State},
  YulangClosure.NativeDrainOwnership.Run YulangClosure.NativeDrainOwnership.initial s →
    YulangClosure.NativeDrainOwnership.Invariant s
'YulangClosure.NativeDrainOwnership.reachable_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]

YulangClosure.NativeDrainOwnership.frameWork.eq_1 : ∀ (w : YulangClosure.NativeDrainOwnership.Work)
  (f : YulangClosure.NativeDrainOwnership.Frame),
  YulangClosure.NativeDrainOwnership.frameWork w f = (f.current = Option.some w ∨ w ∈ f.processed)
'YulangClosure.NativeDrainOwnership.frameWork.eq_1' does not depend on any axioms

YulangClosure.NativeDrainOwnership.instDecidableEqWork.decEq._proof_4 : ∀ (a a_1 a_2 : Nat)
  (a_3 : Option YulangClosure.NativeDrainOwnership.Ticket) (b b_1 : Nat)
  (b_2 : Option YulangClosure.NativeDrainOwnership.Ticket),
  ¬a_1 = b →
    { serial := a, task := a_1, relation := a_2, ticket := a_3 } =
        { serial := a, task := b, relation := b_1, ticket := b_2 } →
      False
'YulangClosure.NativeDrainOwnership.instDecidableEqWork.decEq._proof_4' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.step_invariant._simp_1_14 : ∀ {a b c : Prop}, ((a ∨ b) ∧ c) = (a ∧ c ∨ b ∧ c)
'YulangClosure.NativeDrainOwnership.step_invariant._simp_1_14' depends on axioms: [propext]

YulangClosure.NativeDrainOwnership.Ticket.mk.sizeOf_spec : ∀ (birth operation index relation : Nat),
  SizeOf.sizeOf { birth := birth, operation := operation, index := index, relation := relation } =
    1 + SizeOf.sizeOf birth + SizeOf.sizeOf operation + SizeOf.sizeOf index + SizeOf.sizeOf relation
'YulangClosure.NativeDrainOwnership.Ticket.mk.sizeOf_spec' does not depend on any axioms

YulangClosure.NativeDrainOwnership.instDecidableEqOperation.decEq._proof_1 : ∀ (a a_1 : Nat)
  (a_2 : List YulangClosure.NativeDrainOwnership.Child) (a_3 a_4 : Nat) (a_5 : Bool)
  (a_6 : YulangClosure.NativeDrainOwnership.Wait),
  { birth := a, task := a_1, children := a_2, queued := a_3, consumed := a_4, retired := a_5, waiting := a_6 } =
    { birth := a, task := a_1, children := a_2, queued := a_3, consumed := a_4, retired := a_5, waiting := a_6 }
'YulangClosure.NativeDrainOwnership.instDecidableEqOperation.decEq._proof_1' does not depend on any axioms

YulangClosure.NativeDrainOwnership.Phase.ofNat_ctorIdx : ∀ (x : YulangClosure.NativeDrainOwnership.Phase),
  YulangClosure.NativeDrainOwnership.Phase.ofNat x.ctorIdx = x
'YulangClosure.NativeDrainOwnership.Phase.ofNat_ctorIdx' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.step_invariant._simp_1_12 : ∀ {α : Type u_1} {a : α} {s t : List α},
  (a ∈ s ++ t) = (a ∈ s ∨ a ∈ t)
'YulangClosure.NativeDrainOwnership.step_invariant._simp_1_12' depends on axioms: [propext]

YulangClosure.NativeDrainOwnership.instDecidableEqAckReceipt.decEq._proof_2 : ∀
  (a : YulangClosure.NativeDrainOwnership.Ticket) (a_1 a_2 : Nat) (a_3 b : Bool),
  ¬a_3 = b →
    { ticket := a, frameBirth := a_1, frameIndex := a_2, diagnosed := a_3 } =
        { ticket := a, frameBirth := a_1, frameIndex := a_2, diagnosed := b } →
      False
'YulangClosure.NativeDrainOwnership.instDecidableEqAckReceipt.decEq._proof_2' does not depend on any axioms

YulangClosure.NativeDrainOwnership.instDecidableEqAckReceipt.decEq._proof_4 : ∀
  (a : YulangClosure.NativeDrainOwnership.Ticket) (a_1 a_2 : Nat) (a_3 : Bool) (b b_1 : Nat) (b_2 : Bool),
  ¬a_1 = b →
    { ticket := a, frameBirth := a_1, frameIndex := a_2, diagnosed := a_3 } =
        { ticket := a, frameBirth := b, frameIndex := b_1, diagnosed := b_2 } →
      False
'YulangClosure.NativeDrainOwnership.instDecidableEqAckReceipt.decEq._proof_4' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.step_invariant._proof_1_33 : ∀ {s : YulangClosure.NativeDrainOwnership.State}
  (id task relation : Nat) (op : YulangClosure.NativeDrainOwnership.Operation),
  (∀ (w : YulangClosure.NativeDrainOwnership.Work),
      w ∈ s.issued →
        (∃ f, f ∈ s.frames ∧ (f.current = Option.some w ∨ w ∈ f.processed)) ∨
          ∃ r, r ∈ s.returns ∧ w ∈ r.frame.processed) →
    ∀ (w : YulangClosure.NativeDrainOwnership.Work),
      w ∈ s.issued ∨
          w =
            { serial := s.nextWork, task := task, relation := relation,
              ticket := Option.some (YulangClosure.NativeDrainOwnership.selectedTicket id op op.consumed relation) } →
        w =
            { serial := s.nextWork, task := task, relation := relation,
              ticket := Option.some (YulangClosure.NativeDrainOwnership.selectedTicket id op op.consumed relation) } ∨
          (∃ x, x ∈ s.frames ∧ (x.current = Option.some w ∨ w ∈ x.processed)) ∨
            ∃ r, r ∈ s.returns ∧ w ∈ r.frame.processed
'YulangClosure.NativeDrainOwnership.step_invariant._proof_1_33' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

YulangClosure.NativeDrainOwnership.step_invariant._proof_1_19 : ∀ (index : Nat)
  (op : YulangClosure.NativeDrainOwnership.Operation), index + 1 ≤ op.children.length → index < op.children.length
'YulangClosure.NativeDrainOwnership.step_invariant._proof_1_19' depends on axioms: [propext]

YulangClosure.NativeDrainOwnership.instDecidableEqAckReceipt.decEq._proof_3 : ∀
  (a : YulangClosure.NativeDrainOwnership.Ticket) (a_1 a_2 : Nat) (a_3 : Bool) (b : Nat) (b_1 : Bool),
  ¬a_2 = b →
    { ticket := a, frameBirth := a_1, frameIndex := a_2, diagnosed := a_3 } =
        { ticket := a, frameBirth := a_1, frameIndex := b, diagnosed := b_1 } →
      False
'YulangClosure.NativeDrainOwnership.instDecidableEqAckReceipt.decEq._proof_3' does not depend on any axioms

YulangClosure.NativeDrainOwnership.instDecidableEqWork.decEq._proof_1 : ∀ (a a_1 a_2 : Nat)
  (a_3 : Option YulangClosure.NativeDrainOwnership.Ticket),
  { serial := a, task := a_1, relation := a_2, ticket := a_3 } =
    { serial := a, task := a_1, relation := a_2, ticket := a_3 }
'YulangClosure.NativeDrainOwnership.instDecidableEqWork.decEq._proof_1' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.ready_frame_readback : ∀ {s : YulangClosure.NativeDrainOwnership.State},
  YulangClosure.NativeDrainOwnership.Run YulangClosure.NativeDrainOwnership.initial s →
    ∀ {f : YulangClosure.NativeDrainOwnership.Frame},
      f ∈ s.frames →
        f.phase = YulangClosure.NativeDrainOwnership.Phase.returnReady →
          f.current = Option.none ∧
            f.diagnosed = Bool.true ∧ f.pending = [] ∧ f.completed = f.prepared ∧ f.prepared = f.acks.length
'YulangClosure.NativeDrainOwnership.ready_frame_readback' depends on axioms: [propext, Classical.choice, Quot.sound]

@YulangClosure.NativeDrainOwnership.step_invariant._proof_1_34 : ∀ {s : YulangClosure.NativeDrainOwnership.State}
  (id relation : Nat) (op : YulangClosure.NativeDrainOwnership.Operation),
  (∀ (a : YulangClosure.NativeDrainOwnership.Ticket),
      a ∈ s.transferred →
        (∃ f, f ∈ s.frames ∧ (a ∈ f.done ∨ a ∈ f.pending)) ∨ ∃ r, r ∈ s.acknowledgements ∧ r.ticket = a) →
    ∀ (a : YulangClosure.NativeDrainOwnership.Ticket),
      a ∈ s.transferred ∨ a = YulangClosure.NativeDrainOwnership.selectedTicket id op op.consumed relation →
        YulangClosure.NativeDrainOwnership.selectedTicket id op op.consumed relation = a ∨
          (∃ x, x ∈ s.frames ∧ (a ∈ x.done ∨ a ∈ x.pending)) ∨ ∃ r, r ∈ s.acknowledgements ∧ r.ticket = a
'YulangClosure.NativeDrainOwnership.step_invariant._proof_1_34' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

YulangClosure.NativeDrainOwnership.frame_split_exact : ∀ (f : YulangClosure.NativeDrainOwnership.Frame),
  List.take f.completed f.acks = f.done ∧ List.drop f.completed f.acks = f.pending
'YulangClosure.NativeDrainOwnership.frame_split_exact' depends on axioms: [propext]

YulangClosure.NativeDrainOwnership.instDecidableEqWait.decEq._proof_11 : ∀
  (a : YulangClosure.NativeDrainOwnership.Ticket) (a_1 a_2 b : Nat),
  ¬a_2 = b →
    YulangClosure.NativeDrainOwnership.Wait.ready a a_1 a_2 = YulangClosure.NativeDrainOwnership.Wait.ready a a_1 b →
      False
'YulangClosure.NativeDrainOwnership.instDecidableEqWait.decEq._proof_11' does not depend on any axioms

YulangClosure.NativeDrainOwnership.State.mk.injEq : ∀
  (operations : Nat → Option YulangClosure.NativeDrainOwnership.Operation) (nextOperation nextBirth nextWork : Nat)
  (queue : List YulangClosure.NativeDrainOwnership.Work) (frames : List YulangClosure.NativeDrainOwnership.Frame)
  (issued : List YulangClosure.NativeDrainOwnership.Work) (transferred : List YulangClosure.NativeDrainOwnership.Ticket)
  (acknowledgements : List YulangClosure.NativeDrainOwnership.AckReceipt)
  (returns : List YulangClosure.NativeDrainOwnership.ReturnReceipt)
  (operations_1 : Nat → Option YulangClosure.NativeDrainOwnership.Operation)
  (nextOperation_1 nextBirth_1 nextWork_1 : Nat) (queue_1 : List YulangClosure.NativeDrainOwnership.Work)
  (frames_1 : List YulangClosure.NativeDrainOwnership.Frame) (issued_1 : List YulangClosure.NativeDrainOwnership.Work)
  (transferred_1 : List YulangClosure.NativeDrainOwnership.Ticket)
  (acknowledgements_1 : List YulangClosure.NativeDrainOwnership.AckReceipt)
  (returns_1 : List YulangClosure.NativeDrainOwnership.ReturnReceipt),
  ({ operations := operations, nextOperation := nextOperation, nextBirth := nextBirth, nextWork := nextWork,
        queue := queue, frames := frames, issued := issued, transferred := transferred,
        acknowledgements := acknowledgements, returns := returns } =
      { operations := operations_1, nextOperation := nextOperation_1, nextBirth := nextBirth_1, nextWork := nextWork_1,
        queue := queue_1, frames := frames_1, issued := issued_1, transferred := transferred_1,
        acknowledgements := acknowledgements_1, returns := returns_1 }) =
    (operations = operations_1 ∧
      nextOperation = nextOperation_1 ∧
        nextBirth = nextBirth_1 ∧
          nextWork = nextWork_1 ∧
            queue = queue_1 ∧
              frames = frames_1 ∧
                issued = issued_1 ∧
                  transferred = transferred_1 ∧ acknowledgements = acknowledgements_1 ∧ returns = returns_1)
'YulangClosure.NativeDrainOwnership.State.mk.injEq' depends on axioms: [propext]

YulangClosure.NativeDrainOwnership.instDecidableEqFrame.decEq._proof_1 : ∀ (a a_1 : Nat)
  (a_2 : Option YulangClosure.NativeDrainOwnership.Work) (a_3 : Option Nat)
  (a_4 : List YulangClosure.NativeDrainOwnership.Work) (a_5 a_6 : List YulangClosure.NativeDrainOwnership.Ticket)
  (a_7 : Nat) (a_8 : YulangClosure.NativeDrainOwnership.Phase) (a_9 : Bool)
  (a_10 : Option YulangClosure.NativeDrainOwnership.Ticket) (a_11 : Nat),
  { birth := a, index := a_1, current := a_2, processing := a_3, processed := a_4, done := a_5, pending := a_6,
      prepared := a_7, phase := a_8, diagnosed := a_9, destination := a_10, transitions := a_11 } =
    { birth := a, index := a_1, current := a_2, processing := a_3, processed := a_4, done := a_5, pending := a_6,
      prepared := a_7, phase := a_8, diagnosed := a_9, destination := a_10, transitions := a_11 }
'YulangClosure.NativeDrainOwnership.instDecidableEqFrame.decEq._proof_1' does not depend on any axioms

YulangClosure.NativeDrainOwnership.instDecidableEqFrame.decEq._proof_7 : ∀ (a a_1 : Nat)
  (a_2 : Option YulangClosure.NativeDrainOwnership.Work) (a_3 : Option Nat)
  (a_4 : List YulangClosure.NativeDrainOwnership.Work) (a_5 a_6 : List YulangClosure.NativeDrainOwnership.Ticket)
  (a_7 : Nat) (a_8 : YulangClosure.NativeDrainOwnership.Phase) (a_9 : Bool)
  (a_10 : Option YulangClosure.NativeDrainOwnership.Ticket) (a_11 : Nat)
  (b : List YulangClosure.NativeDrainOwnership.Ticket) (b_1 : Nat) (b_2 : YulangClosure.NativeDrainOwnership.Phase)
  (b_3 : Bool) (b_4 : Option YulangClosure.NativeDrainOwnership.Ticket) (b_5 : Nat),
  ¬a_6 = b →
    { birth := a, index := a_1, current := a_2, processing := a_3, processed := a_4, done := a_5, pending := a_6,
          prepared := a_7, phase := a_8, diagnosed := a_9, destination := a_10, transitions := a_11 } =
        { birth := a, index := a_1, current := a_2, processing := a_3, processed := a_4, done := a_5, pending := b,
          prepared := b_1, phase := b_2, diagnosed := b_3, destination := b_4, transitions := b_5 } →
      False
'YulangClosure.NativeDrainOwnership.instDecidableEqFrame.decEq._proof_7' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.reachable_coherent : ∀ {s : YulangClosure.NativeDrainOwnership.State},
  YulangClosure.NativeDrainOwnership.Run YulangClosure.NativeDrainOwnership.initial s →
    YulangClosure.NativeDrainOwnership.Coherent s
'YulangClosure.NativeDrainOwnership.reachable_coherent' depends on axioms: [propext, Classical.choice, Quot.sound]

@_private.YulangClosure.NativeDrainOwnership.0.YulangClosure.NativeDrainOwnership.queueTicket_append._simp_1_3 : ∀
  {α : Sort u_1} {p q : α → Prop}, (∃ x, p x ∨ q x) = ((∃ x, p x) ∨ ∃ x, q x)
'_private.YulangClosure.NativeDrainOwnership.0.YulangClosure.NativeDrainOwnership.queueTicket_append._simp_1_3' depends on axioms: [propext]

YulangClosure.NativeDrainOwnership.receipt.eq_1 : ∀ (f : YulangClosure.NativeDrainOwnership.Frame)
  (a : YulangClosure.NativeDrainOwnership.Ticket),
  YulangClosure.NativeDrainOwnership.receipt f a =
    { ticket := a, frameBirth := f.birth, frameIndex := f.index, diagnosed := f.diagnosed }
'YulangClosure.NativeDrainOwnership.receipt.eq_1' does not depend on any axioms

YulangClosure.NativeDrainOwnership.instDecidableEqPhase._proof_2 : ∀ (x y : YulangClosure.NativeDrainOwnership.Phase),
  ¬x.ctorIdx = y.ctorIdx → x = y → False
'YulangClosure.NativeDrainOwnership.instDecidableEqPhase._proof_2' does not depend on any axioms

YulangClosure.NativeDrainOwnership.instDecidableEqTicket.decEq._proof_3 : ∀ (a a_1 a_2 a_3 b b_1 : Nat),
  ¬a_2 = b →
    { birth := a, operation := a_1, index := a_2, relation := a_3 } =
        { birth := a, operation := a_1, index := b, relation := b_1 } →
      False
'YulangClosure.NativeDrainOwnership.instDecidableEqTicket.decEq._proof_3' does not depend on any axioms

YulangClosure.NativeDrainOwnership.Witness.synchronous_transport_run : YulangClosure.NativeDrainOwnership.Run
  YulangClosure.NativeDrainOwnership.initial YulangClosure.NativeDrainOwnership.Witness.delivered
'YulangClosure.NativeDrainOwnership.Witness.synchronous_transport_run' depends on axioms: [propext]

@YulangClosure.NativeDrainOwnership.ready_frame_readback._proof_1_3 : ∀ {f : YulangClosure.NativeDrainOwnership.Frame},
  f.completed ≤ f.prepared →
    f.prepared ≤ f.acks.length → f.acks.length = f.completed → ¬f.completed = f.prepared → False
'YulangClosure.NativeDrainOwnership.ready_frame_readback._proof_1_3' depends on axioms: [propext, Quot.sound]

@YulangClosure.NativeDrainOwnership.Invariant.tickets : ∀ {s : YulangClosure.NativeDrainOwnership.State},
  YulangClosure.NativeDrainOwnership.Invariant s →
    ∀ (a : YulangClosure.NativeDrainOwnership.Ticket),
      a ∈ s.transferred → YulangClosure.NativeDrainOwnership.TicketCovered s a
'YulangClosure.NativeDrainOwnership.Invariant.tickets' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.Operation.mk.inj : ∀ {birth task : Nat}
  {children : List YulangClosure.NativeDrainOwnership.Child} {queued consumed : Nat} {retired : Bool}
  {waiting : YulangClosure.NativeDrainOwnership.Wait} {birth_1 task_1 : Nat}
  {children_1 : List YulangClosure.NativeDrainOwnership.Child} {queued_1 consumed_1 : Nat} {retired_1 : Bool}
  {waiting_1 : YulangClosure.NativeDrainOwnership.Wait},
  { birth := birth, task := task, children := children, queued := queued, consumed := consumed, retired := retired,
        waiting := waiting } =
      { birth := birth_1, task := task_1, children := children_1, queued := queued_1, consumed := consumed_1,
        retired := retired_1, waiting := waiting_1 } →
    birth = birth_1 ∧
      task = task_1 ∧
        children = children_1 ∧ queued = queued_1 ∧ consumed = consumed_1 ∧ retired = retired_1 ∧ waiting = waiting_1
'YulangClosure.NativeDrainOwnership.Operation.mk.inj' does not depend on any axioms

YulangClosure.NativeDrainOwnership.instDecidableEqReturnReceipt.decEq._proof_2 : ∀
  (a b : YulangClosure.NativeDrainOwnership.Frame), ¬a = b → { frame := a } = { frame := b } → False
'YulangClosure.NativeDrainOwnership.instDecidableEqReturnReceipt.decEq._proof_2' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.Wait.running.inj : ∀ {ticket : YulangClosure.NativeDrainOwnership.Ticket}
  {frame : Nat} {ticket_1 : YulangClosure.NativeDrainOwnership.Ticket} {frame_1 : Nat},
  YulangClosure.NativeDrainOwnership.Wait.running ticket frame =
      YulangClosure.NativeDrainOwnership.Wait.running ticket_1 frame_1 →
    ticket = ticket_1 ∧ frame = frame_1
'YulangClosure.NativeDrainOwnership.Wait.running.inj' does not depend on any axioms

_private.YulangClosure.NativeDrainOwnership.0.YulangClosure.NativeDrainOwnership.Witness.running_wait : YulangClosure.NativeDrainOwnership.completionWait
  YulangClosure.NativeDrainOwnership.Witness.runningOperation YulangClosure.NativeDrainOwnership.Witness.ticket
'_private.YulangClosure.NativeDrainOwnership.0.YulangClosure.NativeDrainOwnership.Witness.running_wait' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.step_invariant._proof_1_45 : ∀ {s : YulangClosure.NativeDrainOwnership.State}
  (f : YulangClosure.NativeDrainOwnership.Frame) (fs : List YulangClosure.NativeDrainOwnership.Frame),
  (∀ (w : YulangClosure.NativeDrainOwnership.Work),
      w ∈ s.issued →
        w ∈ s.queue ∨
          (w ∈ f.processed ∨ ∃ x, x ∈ fs ∧ (x.current = Option.some w ∨ w ∈ x.processed)) ∨
            ∃ r, r ∈ s.returns ∧ w ∈ r.frame.processed) →
    ∀ (w : YulangClosure.NativeDrainOwnership.Work),
      w ∈ s.issued →
        w ∈ s.queue ∨
          (∃ f, f ∈ fs ∧ (f.current = Option.some w ∨ w ∈ f.processed)) ∨
            (∃ x, x ∈ s.returns ∧ w ∈ x.frame.processed) ∨ w ∈ f.processed
'YulangClosure.NativeDrainOwnership.step_invariant._proof_1_45' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

YulangClosure.NativeDrainOwnership.instDecidableEqTicket.decEq._proof_2 : ∀ (a a_1 a_2 a_3 b : Nat),
  ¬a_3 = b →
    { birth := a, operation := a_1, index := a_2, relation := a_3 } =
        { birth := a, operation := a_1, index := a_2, relation := b } →
      False
'YulangClosure.NativeDrainOwnership.instDecidableEqTicket.decEq._proof_2' does not depend on any axioms

YulangClosure.NativeDrainOwnership.step_coherent._proof_1_10 : ∀ (f : YulangClosure.NativeDrainOwnership.Frame)
  (a : YulangClosure.NativeDrainOwnership.Ticket),
  (f.done ++ f.pending)[f.prepared]? = Option.some a → f.prepared < (f.done ++ f.pending).length
'YulangClosure.NativeDrainOwnership.step_coherent._proof_1_10' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

YulangClosure.NativeDrainOwnership.instDecidableEqWait.decEq._proof_3 : ∀
  (ticket : YulangClosure.NativeDrainOwnership.Ticket) (frame : Nat),
  YulangClosure.NativeDrainOwnership.Wait.running ticket frame = YulangClosure.NativeDrainOwnership.Wait.idle → False
'YulangClosure.NativeDrainOwnership.instDecidableEqWait.decEq._proof_3' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.step_invariant._proof_1_42 : ∀ {s : YulangClosure.NativeDrainOwnership.State}
  (f : YulangClosure.NativeDrainOwnership.Frame) (fs : List YulangClosure.NativeDrainOwnership.Frame)
  (a : YulangClosure.NativeDrainOwnership.Ticket) (rest : List YulangClosure.NativeDrainOwnership.Ticket),
  (∀ (a_1 : YulangClosure.NativeDrainOwnership.Ticket),
      a_1 ∈ s.transferred →
        (∃ w, w ∈ s.queue ∧ w.ticket = Option.some a_1) ∨
          ((a_1 ∈ f.done ∨ a_1 = a ∨ a_1 ∈ rest) ∨ ∃ x, x ∈ fs ∧ (a_1 ∈ x.done ∨ a_1 ∈ x.pending)) ∨
            ∃ r, r ∈ s.acknowledgements ∧ r.ticket = a_1) →
    ∀ (a_1 : YulangClosure.NativeDrainOwnership.Ticket),
      a_1 ∈ s.transferred →
        (∃ w, w ∈ s.queue ∧ w.ticket = Option.some a_1) ∨
          (((a_1 ∈ f.done ∨ a_1 = a) ∨ a_1 ∈ rest) ∨ ∃ x, x ∈ fs ∧ (a_1 ∈ x.done ∨ a_1 ∈ x.pending)) ∨
            (∃ x, x ∈ s.acknowledgements ∧ x.ticket = a_1) ∨ a = a_1
'YulangClosure.NativeDrainOwnership.step_invariant._proof_1_42' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

@YulangClosure.NativeDrainOwnership.step_coherent : ∀ {s t : YulangClosure.NativeDrainOwnership.State},
  YulangClosure.NativeDrainOwnership.Step s t →
    YulangClosure.NativeDrainOwnership.Coherent s → YulangClosure.NativeDrainOwnership.Coherent t
'YulangClosure.NativeDrainOwnership.step_coherent' depends on axioms: [propext, Classical.choice, Quot.sound]

YulangClosure.NativeDrainOwnership.received.eq_1 : ∀ (a : YulangClosure.NativeDrainOwnership.Ticket)
  (rs : List YulangClosure.NativeDrainOwnership.AckReceipt),
  YulangClosure.NativeDrainOwnership.received a rs = ∃ r, r ∈ rs ∧ r.ticket = a
'YulangClosure.NativeDrainOwnership.received.eq_1' does not depend on any axioms

YulangClosure.NativeDrainOwnership.Phase.diagnostics.sizeOf_spec : SizeOf.sizeOf
    YulangClosure.NativeDrainOwnership.Phase.diagnostics =
  1
'YulangClosure.NativeDrainOwnership.Phase.diagnostics.sizeOf_spec' does not depend on any axioms

@_private.YulangClosure.NativeDrainOwnership.0.YulangClosure.NativeDrainOwnership.returnedWork_append._simp_1_2 : ∀
  {a b c : Prop}, ((a ∨ b) ∧ c) = (a ∧ c ∨ b ∧ c)
'_private.YulangClosure.NativeDrainOwnership.0.YulangClosure.NativeDrainOwnership.returnedWork_append._simp_1_2' depends on axioms: [propext]

YulangClosure.NativeDrainOwnership.instDecidableEqWait.decEq._proof_13 : ∀
  (a : YulangClosure.NativeDrainOwnership.Ticket) (a_1 a_2 : Nat) (b : YulangClosure.NativeDrainOwnership.Ticket)
  (b_1 b_2 : Nat),
  ¬a = b →
    YulangClosure.NativeDrainOwnership.Wait.ready a a_1 a_2 = YulangClosure.NativeDrainOwnership.Wait.ready b b_1 b_2 →
      False
'YulangClosure.NativeDrainOwnership.instDecidableEqWait.decEq._proof_13' does not depend on any axioms

YulangClosure.NativeDrainOwnership.returnedWork.eq_1 : ∀ (w : YulangClosure.NativeDrainOwnership.Work)
  (rs : List YulangClosure.NativeDrainOwnership.ReturnReceipt),
  YulangClosure.NativeDrainOwnership.returnedWork w rs = ∃ r, r ∈ rs ∧ w ∈ r.frame.processed
'YulangClosure.NativeDrainOwnership.returnedWork.eq_1' does not depend on any axioms

YulangClosure.NativeDrainOwnership.stackTicket.eq_1 : ∀ (a : YulangClosure.NativeDrainOwnership.Ticket)
  (fs : List YulangClosure.NativeDrainOwnership.Frame),
  YulangClosure.NativeDrainOwnership.stackTicket a fs = ∃ f, f ∈ fs ∧ a ∈ f.acks
'YulangClosure.NativeDrainOwnership.stackTicket.eq_1' does not depend on any axioms

YulangClosure.NativeDrainOwnership.newFrame.eq_1 : ∀ (s : YulangClosure.NativeDrainOwnership.State)
  (destination : Option YulangClosure.NativeDrainOwnership.Ticket),
  YulangClosure.NativeDrainOwnership.newFrame s destination =
    { birth := s.nextBirth, index := s.frames.length, destination := destination }
'YulangClosure.NativeDrainOwnership.newFrame.eq_1' does not depend on any axioms

YulangClosure.NativeDrainOwnership.Operation.mk.injEq : ∀ (birth task : Nat)
  (children : List YulangClosure.NativeDrainOwnership.Child) (queued consumed : Nat) (retired : Bool)
  (waiting : YulangClosure.NativeDrainOwnership.Wait) (birth_1 task_1 : Nat)
  (children_1 : List YulangClosure.NativeDrainOwnership.Child) (queued_1 consumed_1 : Nat) (retired_1 : Bool)
  (waiting_1 : YulangClosure.NativeDrainOwnership.Wait),
  ({ birth := birth, task := task, children := children, queued := queued, consumed := consumed, retired := retired,
        waiting := waiting } =
      { birth := birth_1, task := task_1, children := children_1, queued := queued_1, consumed := consumed_1,
        retired := retired_1, waiting := waiting_1 }) =
    (birth = birth_1 ∧
      task = task_1 ∧
        children = children_1 ∧ queued = queued_1 ∧ consumed = consumed_1 ∧ retired = retired_1 ∧ waiting = waiting_1)
'YulangClosure.NativeDrainOwnership.Operation.mk.injEq' depends on axioms: [propext]

YulangClosure.NativeDrainOwnership.Wait.ready.injEq : ∀ (ticket : YulangClosure.NativeDrainOwnership.Ticket)
  (frame transitions : Nat) (ticket_1 : YulangClosure.NativeDrainOwnership.Ticket) (frame_1 transitions_1 : Nat),
  (YulangClosure.NativeDrainOwnership.Wait.ready ticket frame transitions =
      YulangClosure.NativeDrainOwnership.Wait.ready ticket_1 frame_1 transitions_1) =
    (ticket = ticket_1 ∧ frame = frame_1 ∧ transitions = transitions_1)
'YulangClosure.NativeDrainOwnership.Wait.ready.injEq' depends on axioms: [propext]

YulangClosure.NativeDrainOwnership.instDecidableEqTicket.decEq._proof_1 : ∀ (a a_1 a_2 a_3 : Nat),
  { birth := a, operation := a_1, index := a_2, relation := a_3 } =
    { birth := a, operation := a_1, index := a_2, relation := a_3 }
'YulangClosure.NativeDrainOwnership.instDecidableEqTicket.decEq._proof_1' does not depend on any axioms

_private.YulangClosure.NativeDrainOwnership.0.YulangClosure.NativeDrainOwnership.frameWork_cons : ∀
  (w : YulangClosure.NativeDrainOwnership.Work) (f : YulangClosure.NativeDrainOwnership.Frame)
  (fs : List YulangClosure.NativeDrainOwnership.Frame),
  YulangClosure.NativeDrainOwnership.stackWork w (f :: fs) ↔
    YulangClosure.NativeDrainOwnership.frameWork w f ∨ YulangClosure.NativeDrainOwnership.stackWork w fs
'_private.YulangClosure.NativeDrainOwnership.0.YulangClosure.NativeDrainOwnership.frameWork_cons' depends on axioms: [propext,
 Quot.sound]

@YulangClosure.NativeDrainOwnership.step_invariant._proof_1_30 : ∀ {s : YulangClosure.NativeDrainOwnership.State}
  (task relation : Nat),
  (∀ (w : YulangClosure.NativeDrainOwnership.Work),
      w ∈ s.issued →
        (∃ f, f ∈ s.frames ∧ (f.current = Option.some w ∨ w ∈ f.processed)) ∨
          ∃ r, r ∈ s.returns ∧ w ∈ r.frame.processed) →
    ∀ (w : YulangClosure.NativeDrainOwnership.Work),
      w ∈ s.issued ∨ w = { serial := s.nextWork, task := task, relation := relation, ticket := Option.none } →
        w = { serial := s.nextWork, task := task, relation := relation, ticket := Option.none } ∨
          (∃ x, x ∈ s.frames ∧ (x.current = Option.some w ∨ w ∈ x.processed)) ∨
            ∃ r, r ∈ s.returns ∧ w ∈ r.frame.processed
'YulangClosure.NativeDrainOwnership.step_invariant._proof_1_30' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

YulangClosure.NativeDrainOwnership.instDecidableEqFrame.decEq._proof_9 : ∀ (a a_1 : Nat)
  (a_2 : Option YulangClosure.NativeDrainOwnership.Work) (a_3 : Option Nat)
  (a_4 : List YulangClosure.NativeDrainOwnership.Work) (a_5 a_6 : List YulangClosure.NativeDrainOwnership.Ticket)
  (a_7 : Nat) (a_8 : YulangClosure.NativeDrainOwnership.Phase) (a_9 : Bool)
  (a_10 : Option YulangClosure.NativeDrainOwnership.Ticket) (a_11 : Nat)
  (b : List YulangClosure.NativeDrainOwnership.Work) (b_1 b_2 : List YulangClosure.NativeDrainOwnership.Ticket)
  (b_3 : Nat) (b_4 : YulangClosure.NativeDrainOwnership.Phase) (b_5 : Bool)
  (b_6 : Option YulangClosure.NativeDrainOwnership.Ticket) (b_7 : Nat),
  ¬a_4 = b →
    { birth := a, index := a_1, current := a_2, processing := a_3, processed := a_4, done := a_5, pending := a_6,
          prepared := a_7, phase := a_8, diagnosed := a_9, destination := a_10, transitions := a_11 } =
        { birth := a, index := a_1, current := a_2, processing := a_3, processed := b, done := b_1, pending := b_2,
          prepared := b_3, phase := b_4, diagnosed := b_5, destination := b_6, transitions := b_7 } →
      False
'YulangClosure.NativeDrainOwnership.instDecidableEqFrame.decEq._proof_9' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.step_invariant._proof_1_29 : ∀ {s : YulangClosure.NativeDrainOwnership.State},
  (∀ (f : YulangClosure.NativeDrainOwnership.Frame),
      f ∈ s.frames →
        ∀ (a : YulangClosure.NativeDrainOwnership.Ticket), a ∈ f.done → ∃ r, r ∈ s.acknowledgements ∧ r.ticket = a) →
    ∀ (f : YulangClosure.NativeDrainOwnership.Frame),
      f ∈ s.frames →
        ∀ (a : YulangClosure.NativeDrainOwnership.Ticket), a ∈ f.done → ∃ r, r ∈ s.acknowledgements ∧ r.ticket = a
'YulangClosure.NativeDrainOwnership.step_invariant._proof_1_29' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

@YulangClosure.NativeDrainOwnership.step_invariant._proof_1_22 : ∀ {s : YulangClosure.NativeDrainOwnership.State}
  (f : YulangClosure.NativeDrainOwnership.Frame) (fs : List YulangClosure.NativeDrainOwnership.Frame)
  (id index relation : Nat) (op : YulangClosure.NativeDrainOwnership.Operation),
  (∀ (a : YulangClosure.NativeDrainOwnership.Ticket),
      a ∈ s.transferred →
        (∃ w, w ∈ s.queue ∧ w.ticket = Option.some a) ∨
          ((a ∈ f.done ∨ a ∈ f.pending) ∨ ∃ x, x ∈ fs ∧ (a ∈ x.done ∨ a ∈ x.pending)) ∨
            ∃ r, r ∈ s.acknowledgements ∧ r.ticket = a) →
    ∀ (a : YulangClosure.NativeDrainOwnership.Ticket),
      a ∈ s.transferred ∨ a = YulangClosure.NativeDrainOwnership.selectedTicket id op index relation →
        ((∃ x, x ∈ s.queue ∧ x.ticket = Option.some a) ∨
            YulangClosure.NativeDrainOwnership.selectedTicket id op index relation = a) ∨
          ((a ∈ f.done ∨ a ∈ f.pending) ∨ ∃ x, x ∈ fs ∧ (a ∈ x.done ∨ a ∈ x.pending)) ∨
            ∃ r, r ∈ s.acknowledgements ∧ r.ticket = a
'YulangClosure.NativeDrainOwnership.step_invariant._proof_1_22' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

YulangClosure.NativeDrainOwnership.instDecidableEqWork.decEq._proof_5 : ∀ (a a_1 a_2 : Nat)
  (a_3 : Option YulangClosure.NativeDrainOwnership.Ticket) (b b_1 b_2 : Nat)
  (b_3 : Option YulangClosure.NativeDrainOwnership.Ticket),
  ¬a = b →
    { serial := a, task := a_1, relation := a_2, ticket := a_3 } =
        { serial := b, task := b_1, relation := b_2, ticket := b_3 } →
      False
'YulangClosure.NativeDrainOwnership.instDecidableEqWork.decEq._proof_5' does not depend on any axioms

YulangClosure.NativeDrainOwnership.queueTicket.eq_1 : ∀ (a : YulangClosure.NativeDrainOwnership.Ticket)
  (xs : List YulangClosure.NativeDrainOwnership.Work),
  YulangClosure.NativeDrainOwnership.queueTicket a xs = ∃ w, w ∈ xs ∧ w.ticket = Option.some a
'YulangClosure.NativeDrainOwnership.queueTicket.eq_1' does not depend on any axioms

@_private.YulangClosure.NativeDrainOwnership.0.YulangClosure.NativeDrainOwnership.received_append._simp_1_2 : ∀
  {a b c : Prop}, ((a ∨ b) ∧ c) = (a ∧ c ∨ b ∧ c)
'_private.YulangClosure.NativeDrainOwnership.0.YulangClosure.NativeDrainOwnership.received_append._simp_1_2' depends on axioms: [propext]

@YulangClosure.NativeDrainOwnership.step_invariant._proof_1_37 : ∀ {s : YulangClosure.NativeDrainOwnership.State}
  (f : YulangClosure.NativeDrainOwnership.Frame) (fs : List YulangClosure.NativeDrainOwnership.Frame)
  (w : YulangClosure.NativeDrainOwnership.Work),
  (∀ (w_1 : YulangClosure.NativeDrainOwnership.Work),
      w_1 ∈ s.issued →
        w_1 ∈ s.queue ∨
          ((w = w_1 ∨ w_1 ∈ f.processed) ∨ ∃ x, x ∈ fs ∧ (x.current = Option.some w_1 ∨ w_1 ∈ x.processed)) ∨
            ∃ r, r ∈ s.returns ∧ w_1 ∈ r.frame.processed) →
    ∀ (w_1 : YulangClosure.NativeDrainOwnership.Work),
      w_1 ∈ s.issued →
        w_1 ∈ s.queue ∨
          ((w_1 ∈ f.processed ∨ w_1 = w) ∨ ∃ x, x ∈ fs ∧ (x.current = Option.some w_1 ∨ w_1 ∈ x.processed)) ∨
            ∃ r, r ∈ s.returns ∧ w_1 ∈ r.frame.processed
'YulangClosure.NativeDrainOwnership.step_invariant._proof_1_37' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

YulangClosure.NativeDrainOwnership.instDecidableEqWait.decEq._proof_10 : ∀
  (a : YulangClosure.NativeDrainOwnership.Ticket) (a_1 a_2 : Nat),
  YulangClosure.NativeDrainOwnership.Wait.ready a a_1 a_2 = YulangClosure.NativeDrainOwnership.Wait.ready a a_1 a_2
'YulangClosure.NativeDrainOwnership.instDecidableEqWait.decEq._proof_10' does not depend on any axioms

YulangClosure.NativeDrainOwnership.instDecidableEqTicket.decEq._proof_4 : ∀ (a a_1 a_2 a_3 b b_1 b_2 : Nat),
  ¬a_1 = b →
    { birth := a, operation := a_1, index := a_2, relation := a_3 } =
        { birth := a, operation := b, index := b_1, relation := b_2 } →
      False
'YulangClosure.NativeDrainOwnership.instDecidableEqTicket.decEq._proof_4' does not depend on any axioms

YulangClosure.NativeDrainOwnership.instDecidableEqOperation.decEq._proof_5 : ∀ (a a_1 : Nat)
  (a_2 : List YulangClosure.NativeDrainOwnership.Child) (a_3 a_4 : Nat) (a_5 : Bool)
  (a_6 : YulangClosure.NativeDrainOwnership.Wait) (b b_1 : Nat) (b_2 : Bool)
  (b_3 : YulangClosure.NativeDrainOwnership.Wait),
  ¬a_3 = b →
    { birth := a, task := a_1, children := a_2, queued := a_3, consumed := a_4, retired := a_5, waiting := a_6 } =
        { birth := a, task := a_1, children := a_2, queued := b, consumed := b_1, retired := b_2, waiting := b_3 } →
      False
'YulangClosure.NativeDrainOwnership.instDecidableEqOperation.decEq._proof_5' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.step_invariant._proof_1_47 : ∀ {s : YulangClosure.NativeDrainOwnership.State}
  (f : YulangClosure.NativeDrainOwnership.Frame),
  (∀ (r : YulangClosure.NativeDrainOwnership.ReturnReceipt),
      r ∈ s.returns →
        r.frame.phase = YulangClosure.NativeDrainOwnership.Phase.returnReady ∧
          r.frame.diagnosed = Bool.true ∧ r.frame.pending = [] ∧ r.frame.current = Option.none) →
    f.phase = YulangClosure.NativeDrainOwnership.Phase.returnReady →
      f.pending = [] →
        f.current = Option.none →
          f.diagnosed = Bool.true →
            ∀ (r : YulangClosure.NativeDrainOwnership.ReturnReceipt),
              r ∈ s.returns ∨ r = { frame := f } →
                r.frame.phase = YulangClosure.NativeDrainOwnership.Phase.returnReady ∧
                  r.frame.diagnosed = Bool.true ∧ r.frame.pending = [] ∧ r.frame.current = Option.none
'YulangClosure.NativeDrainOwnership.step_invariant._proof_1_47' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

YulangClosure.NativeDrainOwnership.initial_invariant : YulangClosure.NativeDrainOwnership.Invariant
  YulangClosure.NativeDrainOwnership.initial
'YulangClosure.NativeDrainOwnership.initial_invariant' depends on axioms: [propext, Quot.sound]

YulangClosure.NativeDrainOwnership.instDecidableEqOperation.decEq._proof_8 : ∀ (a a_1 : Nat)
  (a_2 : List YulangClosure.NativeDrainOwnership.Child) (a_3 a_4 : Nat) (a_5 : Bool)
  (a_6 : YulangClosure.NativeDrainOwnership.Wait) (b b_1 : Nat) (b_2 : List YulangClosure.NativeDrainOwnership.Child)
  (b_3 b_4 : Nat) (b_5 : Bool) (b_6 : YulangClosure.NativeDrainOwnership.Wait),
  ¬a = b →
    { birth := a, task := a_1, children := a_2, queued := a_3, consumed := a_4, retired := a_5, waiting := a_6 } =
        { birth := b, task := b_1, children := b_2, queued := b_3, consumed := b_4, retired := b_5, waiting := b_6 } →
      False
'YulangClosure.NativeDrainOwnership.instDecidableEqOperation.decEq._proof_8' does not depend on any axioms

@YulangClosure.NativeDrainOwnership.step_invariant._proof_1_23 : ∀ {s : YulangClosure.NativeDrainOwnership.State}
  (f : YulangClosure.NativeDrainOwnership.Frame) (fs : List YulangClosure.NativeDrainOwnership.Frame)
  (id index task relation : Nat) (op : YulangClosure.NativeDrainOwnership.Operation),
  (∀ (w : YulangClosure.NativeDrainOwnership.Work),
      w ∈ s.issued →
        w ∈ s.queue ∨
          ((f.current = Option.some w ∨ w ∈ f.processed) ∨
              ∃ x, x ∈ fs ∧ (x.current = Option.some w ∨ w ∈ x.processed)) ∨
            ∃ r, r ∈ s.returns ∧ w ∈ r.frame.processed) →
    ∀ (w : YulangClosure.NativeDrainOwnership.Work),
      w ∈ s.issued ∨
          w =
            { serial := s.nextWork, task := task, relation := relation,
              ticket := Option.some (YulangClosure.NativeDrainOwnership.selectedTicket id op index relation) } →
        (w =
              { serial := s.nextWork, task := task, relation := relation,
                ticket := Option.some (YulangClosure.NativeDrainOwnership.selectedTicket id op index relation) } ∨
            w ∈ s.queue) ∨
          ((f.current = Option.some w ∨ w ∈ f.processed) ∨
              ∃ x, x ∈ fs ∧ (x.current = Option.some w ∨ w ∈ x.processed)) ∨
            ∃ r, r ∈ s.returns ∧ w ∈ r.frame.processed
'YulangClosure.NativeDrainOwnership.step_invariant._proof_1_23' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

YulangClosure.NativeDrainOwnership.step_invariant._proof_1_32 : ∀ (task relation : Nat)
  (op : YulangClosure.NativeDrainOwnership.Operation),
  op.children[op.consumed]? = Option.some { task := task, relation := relation } → op.consumed < op.children.length
'YulangClosure.NativeDrainOwnership.step_invariant._proof_1_32' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

YulangClosure.NativeDrainOwnership.Frame.mk.sizeOf_spec : ∀ (birth index : Nat)
  (current : Option YulangClosure.NativeDrainOwnership.Work) (processing : Option Nat)
  (processed : List YulangClosure.NativeDrainOwnership.Work)
  (done pending : List YulangClosure.NativeDrainOwnership.Ticket) (prepared : Nat)
  (phase : YulangClosure.NativeDrainOwnership.Phase) (diagnosed : Bool)
  (destination : Option YulangClosure.NativeDrainOwnership.Ticket) (transitions : Nat),
  SizeOf.sizeOf
      { birth := birth, index := index, current := current, processing := processing, processed := processed,
        done := done, pending := pending, prepared := prepared, phase := phase, diagnosed := diagnosed,
        destination := destination, transitions := transitions } =
    1 + SizeOf.sizeOf birth + SizeOf.sizeOf index + SizeOf.sizeOf current + SizeOf.sizeOf processing +
                    SizeOf.sizeOf processed +
                  SizeOf.sizeOf done +
                SizeOf.sizeOf pending +
              SizeOf.sizeOf prepared +
            SizeOf.sizeOf phase +
          SizeOf.sizeOf diagnosed +
        SizeOf.sizeOf destination +
      SizeOf.sizeOf transitions
'YulangClosure.NativeDrainOwnership.Frame.mk.sizeOf_spec' does not depend on any axioms

```
