# Native frame rollback r3 — independent M3 review, revision 1

Date: 2026-10-26. Reviewer: `/root/native_frame_review_r3`.
Assignment: the primary's direct frozen-packet mathematical/source review;
900-second envelope, static review by default, at most two focused checker
calls if a concrete unresolved gap requires them. No children.

**Verdict: ACCEPT at the stated computed legal-history projection boundary.**
No new BLOCKING, major, or minor finding. This independently accepts the
rollback component and its bounded source mapping. It does not authenticate
all native executions or close `SourceProblem.InferenceSoundness`, native
correspondence, accepted drain, original source/Call, or production gates.

## Authority, independence, and frozen inputs

The supplied baseline is `60e8684224a8a911a5627b845312750a192be777`, branch
`yulang3`. The primary reported the later unrelated NativeExecutionHistory
checkpoint `9589fe3cea1632ab095df549aa7254514dba044f`; this review does not
depend on that module or inspect/change Git state. Exact target bytes, not a
moving branch tip, delimit this acceptance.

I did not author, repair, or suggest the reviewed construction. The only
repository write is this review receipt. Other writes are exclusively in
`/workspace/scratch/f98087c7ac1a/native-frame-review-r3/`. No producer file,
shared import/audit/status file, compiler source, test, toolchain, manifest,
Git index, or ref was changed. No descendants were launched. Requested
model/effort: inherit; independently observed runtime model/effort: UNKNOWN.

Read authority includes root `AGENTS.md` and `AGENTS.pre-sprint.md`, the
goal-driven sprint contract, design/review rules, `yulang-lean-proofs` and
its source/execution references, the 2026-10-11 inference principles, the
original source-preservation obligation and birth-level SCC correction,
`Contracts.lean`, project pins/configuration, relevant README and handoff.
The stale ended sprint in `current.json` is not treated as live ownership or
as a superseding assignment. No separate versioned sprint hash was supplied
for this direct packet.

| Reviewed artifact | Verified SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/NativeFrameRollback.lean` | `274e9a9ac1c43bc81d3b962edb6846dd5e4fa2adb2b645ebd92d6d5f38bd9964` |
| `notes/theory/2026-10-26-native-frame-rollback.md` | `001b7d066200024cf1d1cb269c4dd835871246f74d7ced87774f096a26d2fe7c` |
| Producer handoff `20261026-native-frame-rollback-r3.md` | `c046ddb8b6fa88bcc087e1808cc5133fc0108bc0a5f2048f978c0d2d87ac6618` |
| `native-frame-r3/review-inputs.json` | `0ebc550c54c8fd4760efac9f0f0f2aeafbecd8e61487776137b58b82c3e1499d` |
| `native-frame-r3/logs/check07-full-audit.log` | `69c21f480a9036aad5fb7006befebad70545d6a17c9cc39ea29d37c81f2bee0c` |
| `native-frame-r3/dependency-hashes.json` | `cf341a623fc66983436b29c102bed10de73e86dda25b2fea6481e88c816aa76c` |

## Exact theorem and mathematical review

All four principal roots are in `YulangClosure.NativeFrameRollback`. They
quantify over every `α : Type`, `base : List α`, event list, and computed
endpoint, with the single independent execution premise

```lean
run base.length (initial base) events = some s
```

`initial base` has exactly `base` and an empty undo list. `step` computes
push, preparation, replacement, and pop; an old numeric slot can be written
or popped only when its index is already in the journal. Preparation reads
the actual top payload and checks the entire journal by numeric index. It
does not receive an original snapshot from a caller.

I read the complete module and all complete originating theorem types. The
decisive argument is valid:

1. `Saved` (line 46) records successive exposure of the original top frames.
   It supplies exact original payloads and the increasing contiguous old
   index range, but is a **derived** invariant. `initial_invariant` and
   `step_preserves` establish it rather than assuming its final instance.
2. In the preparation case with no live prefix, the actual top is the next
   untouched original frame. `Saved.seen_iff` proves its index is absent,
   so preparation records that exact payload and advances the untouched cut.
   With a nonempty live prefix, an unseen top index must be new; any old
   reused index is already covered. This is the substantive first-snapshot
   argument, including pop/reuse histories.
3. A successful write or pop cannot remove the next untouched original
   frame: both alternatives of its storage guard are false. Operations on
   the live prefix preserve the old bottom portion. Push preserves it
   without an extra assumption.
4. `checked_snapshot_structure` (line 252) therefore derives witnesses
   `untouched` and `live`, `s.frames = live ++ untouched`, the original
   payload reconstruction, and
   `oldUndo.map Prod.fst = List.range' untouched.length
   (base.length - untouched.length)`. There is no supplied final snapshot
   shape or reconstruction law.
5. `restoreAt_success_iff` (line 284) correctly characterizes success by
   `index ≤ frames.length`, with strict inequality replacing and equality
   appending. `Saved.reconstruct` fills original frames in increasing native
   index order from the unchanged bottom portion. It also handles a current
   stack shorter than the checkpoint and preserves surplus until truncation.
6. `nativeUnwind_filter` preserves the native reverse-journal order while
   skipping new indices. `checked_rollback` (line 390) derives an actual
   successful unwind to `base.reverse ++ extra` and exact rollback to
   `some base`. `checked_no_gaps` (line 396) derives the guard at **each
   intermediate restore state**, using `NoGaps`, not just a final length
   comparison.
7. `checked_all_prefixes` (line 413) factors the successful computation at
   every natural `count`, constructs that prefix's endpoint and invariant,
   and derives successful unwind and exact restoration. Applying
   `nativeUnwind_no_gaps` also gives the intermediate guards for each such
   prefix. Counts beyond the history length and an empty prefix are covered.

The explicit witness removes both original frames, reuses both old slots,
and interleaves a new slot. The first payloads remain `(0,10)` and `(1,20)`;
the final newest-first journal is `[(2,60),(0,10),(1,20)]`. The empty-stack
intermediate prefix is covered. `duplicated_reuse_gap` correctly concerns a
fabricated snapshot-on-every-reuse journal; neither the note nor handoff
mislabels it as a native execution or compiler defect.

## Native source correspondence and retained boundary

All four copied Rust files match the current corresponding source bytes and
the frozen hashes. The source search and inspected owning paths support
the stated local projection:

| Native owner | Review result |
| --- | --- |
| `candidate_context.rs:85–123,2249–2278` | The opaque payload can represent the complete logical frame, including all four dispatch payloads, acknowledgement state, replay destination, and source receipt. Push uses the vector length. Preparation's line 2264 scans the **entire** undo vector for the numeric index; the content-preserving replacement retains the **first** original frame in undo. |
| `lib.rs:14260–14285,14881–14945` | Exactly two direct calls to `prepare_typed_drain_update`; both callers enforce top-frame and acknowledgement guards. Nonterminal preparation precedes its counter changes. Terminal preparation may be skipped by `terminal_prepared`; the necessary earlier protection is explicitly left for native-history authentication. |
| `lib.rs:14288–14420,14576,14638,14689,14847,14955–15055` | The general step prepares before nonterminal mutation, including dispatch installation through `dispatch_live_item`. All four dispatch-step families prepare before payload changes. The search confirms five calls to `prepare_nonterminal_drain` outside its definition. |
| `lib.rs:13999–14180` | With the candidate present, the early return selects `run_candidate_typed_drain`; the later legacy conditional frame body is not used to justify unprepared old-frame changes. |
| `lib.rs:14185–14258`; `candidate_context.rs:4097–4120,4160–4182` | New-frame attribution/replay-destination writes, synchronous failure pop, and replay-helper failure truncation are present. Their projection requires legal top writes/pops, including protection when a numeric old slot has been reused. The note correctly retains these authentication obligations. |
| `candidate_context.rs:2044–2094` | Checkpoint records both lengths. Rollback drains the undo suffix in reverse, skips indices at/above checkpoint length, replaces or asserts equality and pushes, then truncates. This agrees with the Lean logical branches under an empty route-start journal. |
| `candidate_context.rs:913–914,2211–2217`; `lib.rs:9271–9273,9424,9498–9543,9664–9681`; checkpoint plumbing in `candidate_intrusion.rs` and `candidate_effect.rs` | Default is empty; route nesting is rejected; route completion selects commit/rollback; commit clears the route journal suffix and resets preparation state. These facts support the intended boundary, but the complete route induction establishing it remains unproved. |

The theorem does not cover an arbitrary checkpoint inside an older nonempty
frame journal. That exclusion is material because native deduplication sees
older entries whereas rollback drains only the checkpoint suffix. It is
clearly disclosed and is not silently removed from the native parent gate.

Likewise, `run`'s successful storage guard is a premise to native application,
not a proof that arbitrary Rust stage transitions satisfy it. Actual routes
still need one shared frame/operation/worklist/restoration history, complete
logical payload readbacks, the empty journal boundary, preserved top ownership
through recursive calls, every old-write/pop protection fact, terminal-skip
justification, and helper cleanup correspondence. The allocation identity,
capacity, resource failure and fixed-width aspects are outside this logical
frame theorem. Commit reset/reclamation and nontransactional phases require
their own application boundary.

The original `Contracts.lean:128–130,147–149` source/native quantifiers are
unchanged. Original source evidence, record/Call meaning, accepted drain,
recursive current dispositions, and one same-scoped source witness remain
OPEN. The work does not turn complete failure restoration into an additional
inference requirement contrary to the governing top-level principles.

## Audit and evidence integrity

I rehashed **all 42 review-manifest entries** (6,119,125 bytes) and **all
7,294 dependency-manifest entries** (1,056,537,904 bytes): zero missing files,
size mismatches, or hash mismatches. Every one of the 1,459 audit-import
modules is represented. The four native source inputs, three project
pin/configuration files, copied Lean module, and unchanged checker agree
with their live counterparts. `Std` is the module's sole import.

I inspected the complete census auditor: it enumerates by originating module,
includes private/generated constants, rejects originating project axioms,
requires every authored root to be a theorem, prints full types and transitive
axioms, and enforces the standard whitelist. I independently parsed and read
all **110 distinct theorem types and axiom reports**, including **12 private
constants**, across **205 declarations**, with all **24 authored roots**.
There are no missing audit blocks, printed-type truncation markers, final
warnings, or unapproved axioms. The producer's summary matches exactly.

| Transitive axioms | Theorem constants |
| --- | ---: |
| none | 61 |
| `propext` | 10 |
| `propext`, `Quot.sound` | 28 |
| `propext`, `Classical.choice`, `Quot.sound` | 11 |

The four principal generic roots use all three listed standard axioms; this
is not described as axiom-free. The source contains no `sorry`, `admit`,
project axiom, unchecked native decision procedure, unsafe override, or
kernel-check bypass.

The seven retained command/exit/time receipts agree with their logs:
01/02 failed elaboration; 03/04 passed focused builds/audits; 05 failed on
the two unsupported printer options; 06 passed the final focused build and
named-root audit; 07 passed the complete census. Aggregate measured checker
time is **15.736938 seconds**. The preserved call-05 audit differs by exactly
the two corrected option settings. Its reconstructed old module differs
from the final module only in the disclosed `Saved.seen_iff` proof edit.
The final build trace records the pinned Lean 4.35.0 commit and `-j1 -M1024`.
The setup/version failures are retained and are not counted as proof passes.

The producer's disclosed calls 03/04 temporary-path lease deviation remains
visible; both named `/tmp/yulang-lean-audit-*` directories are absent, and
the final helper uses the owned `TMPDIR`. This is a previously disclosed
process issue, not concealed as a wider lease or a mathematical conclusion.

Reviewer verification was static plus hash/receipt parsing: **0 of 2 focused
checker calls**, no native tests, no broad/default build, and no network.
There was no concrete remaining gap requiring a redundant checker run.
The initial local parser misread printed universe suffixes as axiom-name
tokens; its retained receipt records that ordinary parsing error. The
corrected parser removes universe annotations and exactly matches the
producer census. Neither attempt ran Lean or changed a producer artifact.

Own evidence:

- `native-frame-review-r3/integrity-receipt.json`, SHA-256
  `210ae71e58aa77893b397b9fc485a07ca78ec95ca34da6a9c47fb23c41296a01`.
- `native-frame-review-r3/census-types.txt`, the complete reviewed extracted
  types/axioms, SHA-256
  `0e79a968aba40581d2095f418413c52946498d0d7e8bc3f1377a0059a7322c0f`.
- `native-frame-review-r3/census.json`, SHA-256
  `c74f4ed4824fc705198d54d4cbf64fb46bf4e8c8c582452572a92770d9a5b73e`.
- `native-frame-review-r3/initial-parser-receipt.json`, retained local parsing
  attempt; superseded by the corrected integrity receipt.

## Parent application and stop receipt

The accepted reduction is concrete: authenticating one legal native event
history now supplies first original snapshots, the untouched bottom portion,
contiguous old indices, every no-gap restore guard, and exact rollback of
the entire logical checkpoint stack, including old-slot removal and reuse.
A separate assumed final-stack reconstruction law is unnecessary.

The primary/native-history owner must next supply the actual shared route
projection and the explicit boundary/protection facts above, then instantiate
`checked_rollback` and `checked_no_gaps`. This review grants no independent
status or production promotion beyond the frozen component. Full integration
imports, broader checker gates, status synchronization, and Git remain with
the primary.

First reviewer clock: 10:05:22 UTC. Review completed within the 900-second
envelope. The receipt hash is returned separately to avoid a self-hash cycle.
No background checker, helper process, child, or unresolved child lease remains.

**WRITES STOPPED.** This review revision and all owned scratch evidence are
frozen. No further edits without a primary-issued follow-up and superseding
receipt.
