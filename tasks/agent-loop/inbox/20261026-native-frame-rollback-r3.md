# Native frame rollback r3 — frozen handoff revision 1

Assignment: `/root/native_frame_r3`, generic inherited-model `lean_prover` leaf.
Governing packet: the primary's direct bounded native-frame continuation packet,
baseline `60e8684224a8a911a5627b845312750a192be777`, supplied branch `yulang3`.
No separate versioned sprint-contract hash was supplied in that packet. The
read-only `current.json` snapshot still names the ended source-relay-return r1
sprint; it is not used to infer live ownership or change this assignment's scope.
Requested model/effort: inherit. Independently observed runtime model/effort:
UNKNOWN. Actual current worker identity: `/root/native_frame_r3`.

Authorship: this worker authored the Lean module and two leased Markdown files.
No descendants, coauthors of the construction, Git actions, production edits,
configuration changes, public-root imports, shared-state changes, or network use.
The repository checker was copied unchanged. The census script adapts the
existing originating-module audit pattern; no concurrent proof file is imported.

## Outcome and parent application

Outcome: **kernel-checked constructive stack/journal projection; independent
review pending**. The original `SourceProblem.InferenceSoundness` and complete
native-history authentication remain OPEN. See the exact original scope in
`Contracts.lean:128–130,147–149`, the unchanged original A/B obligation and its
governing source corrections; no source subset or semantic weakening is adopted.

The new module computes a chronological sequence of top-frame creation,
preparation, mutation and pop events. Preparation reads the actual top frame and
deduplicates the entire journal by native numeric index. It derives a contiguous
old-frame snapshot range, every reverse-restore no-gap guard, and the exact whole
checkpoint stack. Its all-prefix theorem includes arbitrary removal and reuse
of old numeric indices. A computed witness also interleaves a new index.

This removes a separately assumed frame-restoration premise once the native
history is authenticated. It does not obtain authentication, accepted drain,
recursive current obligations, original record/Call meaning or source witnesses
from the mere existence of the interpreter.

## Exact inputs and source mapping

Only `Std` is imported by `YulangClosure.NativeFrameRollback`. In particular,
the live `NativeExecutionHistory.lean` file and its proof results are not inputs.
The native logical frame payload is arbitrary `α : Type`; all frame content is
represented opaquely, with allocation identity/capacity outside this projection.
Frames are top first; undo is newest first; indices remain native bottom-based.

Native owners inspected:

- `candidate_context.rs:2249–2278`: push and **first** snapshot per numeric
  index. Both complete-frame readback and deduplication are retained.
- `lib.rs:14260–14285,14881–14945`: exactly two direct preparation callers,
  both enforcing the top-frame guard. The nonterminal caller is itself called
  by the general step and all four dispatch-step families.
- `lib.rs:14185–14258`; `candidate_context.rs:4097–4120,4160–4182`: new-frame
  initialization, replay destination, synchronous failure pop, and helper
  failure truncation. Truncation projects to top pops.
- `candidate_context.rs:2044–2074,2085–2094`: checkpoint lengths, reverse
  suffix traversal, old-index filtering, replace/push guard, final truncation.
- `candidate_context.rs:913–914,2211–2217`; `lib.rs:9271–9273,9424,9498–9543,
  9664–9681`: default-empty frame journal, nonnested route boundaries,
  commit/rollback and preparation reset. `candidate_intrusion.rs:177–202` and
  `candidate_effect.rs:278–279,313–339` connect the checkpoint and rollback.

The note records the source census, including the early candidate dispatch
that bypasses the later legacy synchronous drain body. Full native refinement
is not claimed from source inspection alone.

The empty frame journal at route start is explicit in `initial base`. The
module does not claim arbitrary nested checkpoints with older undo entries,
because native deduplication sees the whole vector. Authenticating that empty
boundary and the source's preparation/terminal flag discipline is still part
of the parent native-history owner obligation.

## Main checked declarations and exact independent premises

All names below have prefix `YulangClosure.NativeFrameRollback`.

`checked_snapshot_structure`, `checked_no_gaps`, and `checked_rollback` all
quantify over **every** `α : Type`, `base : List α`, `events : List (Event α)`
and `s : State α`, with only the computational input

```lean
run base.length (initial base) events = some s
```

Their respective conclusions are:

```lean
∃ untouched live,
  s.frames = live ++ untouched ∧ untouched.length ≤ s.frames.length ∧
  base = (oldUndo base.length s.undo).reverse.map Prod.snd ++ untouched ∧
  (oldUndo base.length s.undo).map Prod.fst =
    List.range' untouched.length (base.length - untouched.length)

NoGaps base.length s.undo s.frames.reverse

(∃ extra, nativeUnwind base.length s.undo s.frames.reverse =
  some (base.reverse ++ extra)) ∧ rollback base.length s = some base
```

`checked_all_prefixes` has the same computational input, and for every natural
`count` constructs a `t` satisfying

```lean
run base.length (initial base) (events.take count) = some t ∧
  Invariant base t ∧
  (∃ extra, nativeUnwind base.length t.undo t.frames.reverse =
    some (base.reverse ++ extra)) ∧ rollback base.length t = some base
```

No final journal shape, original snapshot equality, rollback success, or
no-gap inequality is an independent root hypothesis. `Invariant` and `Saved`
are derived by the execution induction. `write`/`pop` compute the storage guard
that an old index is already protected; native source-to-event authentication
must show this guard for every projected successful action.

All 24 authored roots and every originating private/generated theorem have
complete types and axiom audits in the complete census, not only these roots.
The complete authored list is `native-frame-r3/authored-roots.json`.

## Exact write leases and frozen files

1. `notes/theory/lean/YulangClosure/NativeFrameRollback.lean`
2. `notes/theory/2026-10-26-native-frame-rollback.md`
3. `tasks/agent-loop/inbox/20261026-native-frame-rollback-r3.md`

All retained scratch files are below
`/workspace/scratch/f98087c7ac1a/native-frame-r3/`:

- `project/`: isolated pin/config, module, complete audit source, owned `.lake`
  cache and generated artifacts.
- `inputs/`: four frozen native source owners.
- `logs/`: all seven exact command/exit/time receipts and logs, plus setup receipt.
- `failed/`: calls 01/02 proof sources, call 05 audit source and imported module
  source. The latter was reconstructed by reversing the sole recorded later
  local proof edit; the audit itself failed only on option names.
- `tmp/`: final helper temporary-directory root.
- `authored-roots.json`, `audit-summary.json`, `dependency-hashes.json`,
  `review-inputs.json`, and unchanged copied `check_lean.py`.

`review-inputs.json` freezes 42 source/config/native/audit/log/generated entries.
`dependency-hashes.json` covers 7,294 interface/source/IR/tool files across all
1,459 modules in the audit import closure, a superset of the proof's `Std`
dependency closure. No imported project proof is omitted from the manifest;
there is only this authored module plus standard toolchain modules.

| Frozen item | SHA-256 |
| --- | --- |
| Lean module | `274e9a9ac1c43bc81d3b962edb6846dd5e4fa2adb2b645ebd92d6d5f38bd9964` |
| Theory note | `001b7d066200024cf1d1cb269c4dd835871246f74d7ced87774f096a26d2fe7c` |
| Complete audit source | `d04715e74a734e493c450a683281c2805a13d78b202b4e3ab7c4b059db34063d` |
| Complete audit log, call 07 | `69c21f480a9036aad5fb7006befebad70545d6a17c9cc39ea29d37c81f2bee0c` |
| Review manifest | `0ebc550c54c8fd4760efac9f0f0f2aeafbecd8e61487776137b58b82c3e1499d` |
| Dependency manifest | `cf341a623fc66983436b29c102bed10de73e86dda25b2fea6481e88c816aa76c` |
| Native `candidate_context.rs` | `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e` |
| Native `lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| Native `candidate_effect.rs` | `70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f` |
| Native `candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |

Final reads confirm all four native files, the three project pin/config files,
and the copied/leased Lean module exactly match the frozen inputs. The handoff's
own hash is returned separately to avoid a self-hash cycle.

## Actual verification and resource receipts

Fixed Lake: `/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake`.
Actual version: Lake `5.0.0-src+eb6cafb`; Lean `4.35.0`, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. No installation or network access.
All calls use `LEAN_NUM_THREADS=1`, project `-j1 -M1024`, total timeout 120 s,
`PYTHONDONTWRITEBYTECODE=1`, and one owned project/cache. Final helper temp output
uses the owned `TMPDIR`.

| Call | Exit | Measured elapsed seconds | Result |
| --- | --- | --- | --- |
| 01 | 1 | 1.502718 | Preserved elaboration failures; no claim of success. |
| 02 | 1 | 1.932947 | Preserved structure-update/identifier/simplification failures. |
| 03 | 0 | 3.003931 | Focused build plus reconstruction/all-prefix/witness audits. |
| 04 | 0 | 3.528327 | Focused build plus snapshot-order/no-gap/all-prefix audits. |
| 05 | 1 | 1.244352 | Complete audit rejected two unsupported printer option names. |
| 06 | 0 | 3.171498 | Final focused build and named-root audit. |
| 07 | 0 | 1.353165 | Final complete originating-module census and axiom whitelist. |

Total measured checker/audit wall time: **15.736938 s**. Budget used:
**7 of 14** focused calls, no call over 120 s. First clock receipt was
09:15:03 UTC; write-stop declaration is issued before 09:30 UTC, within the
1800-second envelope. No Cargo/native tests or broad/default build was run.
The primary owns public import integration and any full-project gate.

Final complete audit: **110 distinct originating theorem constants, 205
declarations, all 24 authored roots**. It includes private/generated helpers,
prints complete types, and contains no truncated type markers. Distribution:
61 no axioms; 10 `propext`; 28 `propext, Quot.sound`; 11
`propext, Classical.choice, Quot.sound`. No project axiom, `sorryAx`, proof hole,
unchecked native evaluation or kernel bypass. Final changed module: zero
warnings. The proof source search for holes/bypasses returns no matches.

Tooling deviation disclosed to primary: before correction, helper calls 03–04
created automatically deleted temporary audits at
`/tmp/yulang-lean-audit-87h6vwgy` and `/tmp/yulang-lean-audit-yk07s5_u`, outside
the precise scratch lease. Both paths are now absent. Call 06 fixes `TMPDIR`;
the complete audit always used the owned project. No undeclared repository
path was written. The first setup copy-path and Lake sandbox-detection failures
are also preserved; authorized native-environment version/check calls succeeded.

## Required next owner and stop status

Remaining native owner task: construct one actual route event projection shared
with operation/restoration/worklist history, establish empty frame undo at the
route boundary and logical payload reads, and authenticate protection for all
old-frame writes/pops including terminal-prepared skips and helper cleanup.
Then instantiate `checked_rollback` / `checked_no_gaps`; no extra stack
reconstruction law is required. Full native resource/fixed-width behavior,
commit resets/reclamation, nontransactional phases, accepted drain and original
source semantic evidence remain with their existing owners.

The frozen component is ready for primary-assigned fresh independent review.
This is not self-certification, parent closure, production approval, or Git
integration. No descendants or unresolved descendant leases exist.

**WRITES STOPPED.** The three leased repository outputs and all retained scratch
evidence are frozen at handoff revision 1. No further edits will occur without
a primary-issued follow-up and an explicitly superseding receipt.
