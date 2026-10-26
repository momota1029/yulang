# Independent review: original drain and Replay boundaries

Reviewer: `/root/principality`; producer: `/root`. The reviewer did not author
or edit either target. This review is limited to the new local control bridge;
it does not certify the whole native/source interpretation or original goals.

**Verdict: ACCEPT the local conditional proof and its stated application
boundary.** No blocking finding. The frozen producer note was also read in
full and matches the checked theorem scope. Whole-language soundness, Effect
hygiene, principality, inference termination, and full native/source trace
extraction remain OPEN.

## Frozen targets

| Target | SHA256 verified before and after checking |
| --- | --- |
| `notes/theory/lean/YulangClosure/OriginalDrainBoundary.lean` | `d11f5c4e5550702c0796c45076408b0c038e4bc204ec05354b83db8ad7b04ab9` |
| `notes/theory/lean/YulangClosure/OriginalReplayBoundary.lean` | `894f0008c7cf62a43a80c82eb75c5ae08c2a0aa84c0fbadae4dcec07529544c8` |
| `notes/theory/2026-10-27-original-replay-boundary.md` | `31c18ba0ca2a9d3a05582f94112350aa6e2a0824fca5425446ca9e7c431412b0` |

All target source and all authored/generated theorem types were read. The
review followed `NativeDrainOwnership.Step`, `OriginalReplayDrain`'s actual
ordinary loop, pending-work invariant and first-empty theorem,
`NativeValueDrain.Active` and its constructed enqueue run, the physical
`NativeValueRelationExecution.drive`, and the full `NativeValuePorts` key and
Function-port definitions. Native source checks used
`crates/yu-solver/src/candidate_context.rs` and `crates/yu-solver/src/lib.rs`.
Their hashes remain respectively
`57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e`
and `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`,
matching the source-qualified NQ manuscript's recorded Rust owners.

## Independent findings

1. **The owner and prefix predicates do not contain the desired result.**
   `Working` asserts only that a frame with the specified birth/index is in
   working phase. `EmptyBoundary` requires that same frame at the top, working
   phase, no current work, and an empty common queue. `BeforeBoundary` stores
   actual `Step` edges and absence of that owner's boundary at each
   predecessor. None asserts `Processed`, child completion, a consumed cursor,
   diagnostics, fairness, or a future successful return.

2. **Working preservation covers every unchanged control constructor.**
   Begin/startReplay preserve a suspended owner in the tail. Take, Transport,
   Dispatch and preparation preserve the updated frame's birth/index and
   phase. EnterDiagnostics can leave working phase for this owner only from
   its own specified boundary. Diagnostics/acknowledgement/return-ready and
   pop transitions cannot remove a working head; a different working owner
   remains in the tail. Commit changes only preparation cursors. The wildcard
   cases allocate/reserve/enqueue/deliver/noChild/reclaim leave frames unchanged.
   `losing_working_has_boundary` derives a prior boundary from an actual run
   and actual loss; it does not assume one exists on every run.

3. **The old stack-floor condition is derived at every step.**
   `first_boundary_before_return` combines the previous preservation theorem
   with the existing `Indexed` invariant to prove
   `owner.index < middle.frames.length` at each predecessor. At the final
   boundary, indexing and the same owner's identity establish
   `rest.length = owner.index`. The queued-work conservation theorem then
   rules out both an unprocessed queued item and a current item hidden below
   that floor. It does not require the entire stack to be empty.

4. **Birth/index and nested Some-provenance drains remain distinct.**
   Birth is retained alongside the stack index through all updates; a reused
   position is not identified solely by its index. Birth is an existing ghost
   identity in `C.State`, not an asserted field of Rust `TypedDrainFrame`.
   The Rust frame is allocated at vector length and carries occurrence/cause
   and destination; the full trace extraction owns its ghost annotation.
   Nested normal `startReplay`, terminal acknowledgement, popReplay and
   delivery transitions are included. Processed work can reside in a nested
   frame's returned receipt. The new proof does not assume nested drains
   terminate, nor does it include Some-error cleanup or rollback.

5. **Ordinary Replay retains actual queue generation.**
   `ordinaryDrive` is the existing executable loop with the actual remaining
   child-vector measure. Its newly allocated operation produces every child
   before a normal `complete` or `queued` return. The new theorem obtains
   those queued occurrences from `ordinary_return_issues_all`, rather than
   assuming their completion. `queued` is explicitly allowed: it need not
   mean `consumed = children.length`. The production specialization keeps one
   task, the raw relation vector, and each exact birth/operation/index/relation
   ticket.

6. **Physical admission and both Effect ports are preserved.**
   `physical_drive_frames` obtains its frame equality from the same computed
   drive's refinement and enqueue-run invariant. `Active` is the native top
   working frame/current processing-parent/readback/cursor guard; it contains
   no successful child or semantic typing condition. The child result retains
   `AdmissionResult`, the raw relation ID and physical readback of the whole
   `Key`: pair, context, sources and full scoped flow/demand. The deferred
   demand's five fields and the original Function stamp/protect behavior are
   not replaced with Value endpoints. The four-port specialization retains
   argument, argumentEffect, resultEffect, result, length four, the original
   variances and the actual renamed task pair. Native Function admission and
   enqueue remain separate events.

## Acceptance boundary

The precise new result is conditional: **if a finite normal control prefix
reaches the same working owner's first empty boundary, every specified
previously queued child has a recorded dispatch exit by that cut**. The final
`EmptyBoundary` is still an explicit premise. `Processed` means a dispatch
exit recorded in an active or returned frame, not semantic subtyping,
diagnostic acceptance, acknowledgement, or successful global inference.

NQ §§4–5.2 define the real boundary as `Stage::Transport`, `current = None`,
empty worklist, before settlement. The new control projection has the coarser
`phase = working`. Its intended match follows the actual normal stage
discipline: Context/Dispatch/structured admission/enqueue retain current
work; finishing them clears current and restores Transport. A complete
formal extraction of that stage discipline and the whole Rust trace remains
outside these modules. The Rust `dirty`/settlement branch is not silently
turned into a guarantee of entry to Diagnostics.

The physical driver still has a successful computed-execution premise and
local fuel witness. No availability error is promoted to successful
admission. Context/Flow preparation resources, dependency publication and
sampling, the entire dispatch semantic body, source initialization, NQ's
producer/fresh-endpoint/deduplication argument, and whole-language inference
accessibility remain with their existing owners. Abort/rollback can remove
frames without a normal empty boundary and are expressly outside `C.Step`.

The review found no hidden completion premise, narrowed Value-only child
vector, replaced key equality, invented principal ordering, or theorem of
unconditional termination in the target code.

The frozen handoff explicitly retains ghost birth versus native frame data,
the coarse working phase versus the precise pre-settlement Rust stage cut,
successful physical execution premises, and the remaining original `Acc`
obligation. Its scope statements are accepted. One nonblocking locator
shorthand is that its `drive_replay_operation` refers to the actual native
symbol `candidate_context_drive_replay`; the concrete owner inspected here
is that function together with `candidate_context_consume_replay_child`.

## Independent verification

Both frozen source files independently passed:

```text
timeout 120 env LEAN_NUM_THREADS=1 <pinned-lake> env lean -j1 -M1024 <target>
```

Both exited **0** with empty diagnostics. The pinned executable is
`/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake`
(Lean 4.35.0). The reviewer did not build or emit `.olean` files.

A separate imported audit also exited **0**, under the same 1 GiB bound; the
authorized 2 GiB allowance was not needed. It used originating module indices,
printed every declaration type and transitive axiom list with deep printing
enabled, and rejected project axioms and any dependency beyond
`propext`, `Classical.choice`, `Quot.sound`. Its log has no errors or elisions.

| Module | Originating declarations | Theorem declarations | Authored / generated theorems |
| --- | ---: | ---: | ---: |
| `OriginalDrainBoundary` | 51 | 17 | 9 / 8 |
| `OriginalReplayBoundary` | 8 | 8 | 8 / 0 |
| Total | 59 | 25 | 17 / 8 |

`step_keeps_working`, `before_boundary_working` and
`first_boundary_before_return` use `propext`, `Quot.sound`.
`losing_working_has_boundary`, `removal_has_boundary` and the processing
application theorems additionally use `Classical.choice`. No project axiom,
hole or checker bypass was found.

Artifacts in `/tmp/yulang-principality-replay-boundary-review/`:

| Artifact | SHA256 |
| --- | --- |
| `Audit.lean` | `0c2e680afd2a231f57c1f9798939ebf590431a612883d361fe20763d4995c06c` |
| `audit.log` | `b1d6abf1d9eeb9f7d3f4bdb89f900e8cb17c1cd6a754021d1246a3c72163b263` |
| `drain-source.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `replay-source.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |

All independent Lean checking and audit processes have exited. No target,
cache, root import, shared status, compiler, or Git write was made; no child
agent was used. The review artifact is frozen and reviewer writes have
stopped. Acceptance does not certify unrelated declarations in the producer's
larger four-module audit.
