# Local-use restoration continuation: acknowledgement-frontier falsifier

Date: 2026-10-11
Status: unreviewed research checkpoint; conditional operational witness and bounded characterization.
Baseline: `18f13d938be7e7c85df8525c5dd2fb6a4c999671`.
Producer: complementary falsification leaf `/root/restore_chain_falsifier`; no delegation or implementation authority.
Exclusive lease: this note only. Scratch model: `/tmp/yulang-local-use-restore-falsifier.py`.

## Objective, authority and method

Attack the proposed local-use → freshening → physical bound restoration → replay child → typed terminal continuation, especially transaction boundaries and retained child ownership. Governing authority is the private candidate suspension contract §§3–6: exact owned continuation, parent advancement after child completion, original saved count with live indexed lookup, incidence-changing external mutation deferral, and whole-route rollback. User approval is recorded in that contract. The previous conditional resumed-restoration correspondence and latest typed-drain terminal handoff supply historical facts and exclusions, not an established suspension theorem.

Method: inspect pinned owning source, then execute a small transaction/cursor model with a full-state rollback oracle. This does not repeat the earlier external merge/direct-vector drift attack or construct the primary's conditional aligned-schedule proof. No external vector mutation is used. The witness instead crosses a successful suspension commit while a typed drain is still collecting acknowledgements.

## Result and exact premise

**Conditional integration falsifier:** retaining the existing pre-pop acknowledgement append rule when enabling a successful suspension commit during dispatch can invalidate its preparation frontier. One pending old acknowledgement, one later popped acknowledgement, and two distinct replay handles suffice. Debug execution fails its preparation assertion. With that assertion absent, terminal processing can consume the old child without current-route undo; an injected route failure then loses its consumed cursor.

The exact added premise is that a future `Suspended` route can commit a retained typed drain before diagnostics/acknowledgements, and resume that drain by the existing append and terminal rules. The baseline does not provide that outward suspension path. This is not an existing compiler failure or a source-program counterexample. It identifies a necessary integration condition before those rules may be reused for interruptible dispatch. A suspension limited to terminal stages does not satisfy the witness premise.

The missing source premise is authentic construction of the two retained child handles and an admitted suspend/resume route through that dispatch seam. The source contains the relevant queue producers, but this lane has not supplied a HIR/source program, real certificate, recognizer or lifecycle event establishing that route.

## Owning source evidence

All reads below used committed blobs at the pinned baseline, excluding concurrent working edits.

| Responsibility | Pinned source locator | Relevant fact |
| --- | --- | --- |
| Local use and fresh identity | `candidate_scheme.rs:900–906,1265–1303` | Local use captures and freshens inside a route transaction; freshening starts `begin_use` and owns its remaps on the Rust stack. It has no resumable entrypoint at this baseline. |
| Restore accepted physical bound | `candidate_extrusion.rs:655–721` | Begin inserts once and saves opposite count; drive uses retained emission, next index and active replay. New lookup canonicalizes endpoints and reads live vectors. |
| Collect typed acknowledgements | `lib.rs:11891–11925` | Pre-pop prepares completion undo for the front item's exact handle. After pop, append asserts `prepared_acks == replay_acks.len()`, pushes at the tail and increments `prepared_acks`. |
| Successful route commit | `lib.rs:9162–9186`; `candidate_context.rs:1674–1682` | Commit discards route undo and resets every retained frame's `prepared_acks` to `completed_acks`, irrespective of dispatch/terminal stage. |
| Terminal consumption | `lib.rs:12255–12307` | It prepares the next acknowledgement only when `completed_acks == prepared_acks`; otherwise it consumes the next acknowledgement using the assumed prepared prefix. |
| Per-handle undo and completion | `candidate_context.rs:1811–1864` | Undo records one replay handle's queued/consumed/retired state. Completion validates that handle's consumed cursor against the exact child index. |
| Rollback and reclamation | `candidate_context.rs:1568–1592,1660–1667,1789–1795` | Rollback restores recorded handle updates. A retired replay remains retained while its live restoration points at it. |
| Multiple replay producers | `candidate_extrusion.rs:724–771`; `candidate_context.rs:2937–2971`; `lib.rs:12351–12374` | Ordinary bound replay with `provenance=None` can queue children into the worklist, with per-handle transfer. This supplies a plausible operation producer, not proof of the witness's source reachability. |

## Smallest witness

Let replay handles `Q0` and `Q1` each have one child, child index zero. Both are retained and queued, with `consumed=0, retired=false`. A live typed drain has already popped `Q0`'s child, retained its acknowledgement, and reached a dispatch stage; `Q1`'s child remains queued. Diagnostics have not completed. The hypothetical pause keeps this frame and worklist.

1. Before the pause commits: `acks=[Q0]`, `completed=0`, `prepared=1`. Old-route completion undo exists for `Q0`.
2. Successful suspension commit clears that undo and resets `prepared=completed=0`. The frame remains nonterminal and `acks=[Q0]`.
3. Resumed dispatch preflights `Q1`'s completion, recording only `Q1` undo. Before append, `prepared=0` but `len(acks)=1`: the existing debug assertion fails.
4. In release semantics, append yields `acks=[Q0,Q1]`, `completed=0`, `prepared=1`. This counter no longer describes a prepared prefix: the prepared entry is at position one, whereas position zero lacks undo.
5. After successful diagnostics, terminal processing sees `completed < prepared` and skips completion preparation for `Q0`. It consumes `Q0`, giving `consumed(Q0)=1, retired(Q0)=true`.
6. Inject a route failure before completing `Q1`. Reversing the route's replay undo restores `Q1`, but contains no entry for `Q0`. Thus the replay part of rollback differs from the pre-route state: `Q0` remains consumed/retired. Frame rollback cannot restore that separate replay map entry.

The debug witness needs one old and one new acknowledgement. Two distinct handles are necessary for this particular consumed-cursor loss: if both acknowledgements refer to the same replay operation, preparing the later child can incidentally journal the earlier consumed state too. The model intentionally removes that incidental protection. This does not claim minimality over every possible compiler state or failure class.

A standalone reproduction of the released-assertion cursor witness is:

```python
from copy import deepcopy

ops = {0: [1, 0, False], 1: [1, 0, False]}  # queued, consumed, retired
acks = [0]
completed, prepared = 0, 1
journal = [(0, ops[0].copy())]

# Commit the old route with a retained Dispatch frame.
journal.clear()
prepared = completed
route_start = deepcopy(ops)

# Pre-pop the second child, then use the baseline tail-append rule.
journal.append((1, ops[1].copy()))
assert prepared != len(acks)  # Source debug assertion would fail here.
acks.append(1)
prepared += 1

# Terminal consumes the purportedly prepared prefix without Q0 undo.
assert completed < prepared
ops[acks[completed]][1:] = [1, True]
completed += 1

# Inject failure and reverse the recorded replay updates.
for handle, old in reversed(journal):
    ops[handle] = old
assert ops[0] == [1, 1, True]
assert route_start[0] == [1, 0, False]
assert ops != route_start
```

## Executable envelope and oracle limits

The scratch checker enumerated terminal-only acknowledgement lists of lengths `N=0..4`, initial completed prefixes `c=0..N`, and every Boolean commit/no-commit schedule after each of the `N-c` remaining acknowledgement steps. Each acknowledgement used a distinct retained one-child replay handle; no handle allocation, transfer, nesting, representative change, vector mutation or lifecycle invalidation occurred inside this terminal envelope. Initial prepared frontier was reset on entry to a new route. For every step, reverse-journal rollback was compared with a deep copy taken at the latest route commit.

Result: **57 terminal schedules, 144 terminal acknowledgement/rollback checks; no counterexample in that envelope.** This is bounded characterization only. It agrees with the terminal handoff's limited scope and is not an independent certification of its Rust implementation or tests.

The same checker produced the one-old/one-new/two-handle witness above, with the source debug assertion enabled and disabled. Two negative controls detected named shortcuts: omit the commit frontier reset (one pending terminal child loses rollback), and omit the live parent's retired-replay retention predicate (a live restoration points to a missing replay). The latter is a direct ownership-state mutation check, not execution of the Rust reclamation loop.

The rollback oracle is independent of the candidate's journal decision: it stores the full pre-route replay state instead of relying on `prepared_acks`. Both sides still share supplied transition rules, operation identity, acknowledgement order, allocation success and exact child indices. The model does not execute Rust source, reproduce its allocator/resource accounting or prove its transitions from source. Its independent value is detecting that a prefix counter and tail-only preparation disagree across this proposed stage boundary.

No seeds were used. Search limits are finite and exhaustive within the stated terminal domain; there was no source-program search, random testing, or hidden larger search. The minimized dispatch witness is a directed experiment, not an exhaustive search over all dispatch states. No real duplicate fresh-use/emission, skipped replay child, live-vector drift, publication loss or source-owned failure was demonstrated.

## Checks, resources and frozen dependencies

Commands: pinned `git show` range/caller reads; committed-blob SHA256 comparison; twice run the following lightweight scratch command after correcting its route-baseline bookkeeping and making the second child explicitly prequeued:

```text
/usr/bin/time -f 'elapsed=%e maxrss_kib=%M' timeout 30s bash -c 'ulimit -v 131072; exec python3 /tmp/yulang-local-use-restore-falsifier.py'
```

Both runs returned the stated characterization and witness. Probe process count: two sequential single-process Python runs. Aggregate measured wall time: `0.22s`; peak reported RSS: `11,200 KiB`. Per-run caps: 30 seconds / 128 MiB, below the assigned 90-second aggregate. Read processes and reasoning memory/time were not measured. No Cargo, compiler tests, builds, formatting, Git mutation or delegation occurred.

All seven committed HEAD dependency blobs matched baseline when checked; working edits were excluded. Direct SHA256 values:

```text
f2e8c33ac3e0a61ec6611285adbb866a055ae791cebf5a7440de1f8795fa822e  crates/yu-solver/src/candidate_scheme.rs
beebddb214b80335a33a6e307e7809b98a21a286bbe73aef0fdfab4bfa7c570c  crates/yu-solver/src/candidate_extrusion.rs
085f98e667c47648986c052e2a3411f39361fe85017f8bc3ec2d5ca74e0e64f3  crates/yu-solver/src/candidate_context.rs
97a2fed4e4be960b9fbf0d97adb454dc72cc8d4683cef2963234f2cc22e76fca  crates/yu-solver/src/lib.rs
734d94cb02c3d2a101ab21435b4377ed06952ab384815da73636bcfbc986033d  notes/design/2026-10-11-private-candidate-suspension-contract.md
032e5877d28e60cce2955a15bfffd1761dbc22f75975223f9ee4a396d51271e5  notes/progress/2026-10-11-resumed-restoration-source-correspondence.md
1f2df0b82beecd62572a1a5d9ae384627403beadcc3dd6e05fbeb148a8d706f8  notes/progress/2026-10-11-typed-drain-terminal-handoff.md
```

## Handoff and commit packet

One recommended next action: before enabling commits from a retained nonterminal drain, make acknowledgement preparation preserve the actual current-route prepared prefix across later worklist pops, and exercise this exact two-handle rollback boundary under the primary's separately authorized implementation/test lease. Keeping suspension terminal-only avoids this witness but does not discharge the broader contract's dispatch continuation requirement.

This note is frozen for primary adjudication; it supplies no independent review or gate closure. The constructive theorem, actual suspended scheduler, full dependency footprint/deferral proof, freshening frame construction, lifecycle recomputation, accounting, source/SCC publication and §7 authentic source regression remain unverified here. Active callback mutation must continue using saved-count/live-lookup behavior; external incidence mutation during a pause remains deferred while its footprint proof is open.

Commit packet: exact leased path `notes/progress/2026-10-11-local-use-restoration-continuation-falsifiers.md`; baseline `18f13d938be7e7c85df8525c5dd2fb6a4c999671`; changed dependency hashes: none in checked committed HEAD, concurrent working dependencies require primary revalidation; status: producer-only unreviewed conditional witness/bounded characterization; checks: pinned source reads, dependency SHA256 comparison, two bounded scratch runs, leased-note whitespace check. Proposed checkpoint message: `Record dispatch-resume acknowledgement frontier rollback witness`. Shared-record delta intentionally left for primary/curator: record the nonterminal commit/append preparation condition as open integration work, without reopening the reviewed synchronous terminal slice or closing any suspension/source gate. Scratch outputs remain outside the commit packet.
