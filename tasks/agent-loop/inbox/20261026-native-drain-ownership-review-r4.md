# Native drain ownership r4 — independent M3 review

Date: 2026-10-26. Assignment/handoff revision: 1.
Reviewer: `/root/native_drain_review_r4`, fresh independent nonauthor, using
the supported generic reviewer capability with inherited model/effort. No
custom-role or separately observed model claim is made. The reviewer made no
construction, repair or counterexample contribution to the frozen targets and
started no descendants.

## Verdict

**ACCEPT at the stated successful-forward control-ownership boundary.** No
BLOCKING, major or minor finding requires repair of the frozen bytes.

The accepted result is the shared event-model construction, its derived
conservation/stage facts, its nonvacuous synchronous witness, and the accuracy
of its explicitly bounded source mapping. This is not acceptance of a complete
Rust execution refinement, accepted-native soundness, or the original
`SourceProblem.InferenceSoundness`. All three remain OPEN. The model permits
more histories than the native implementation, and a map from actual committed
native execution to this `Run` has not been proved.

The primary supplied baseline `37ec9da2aaca2d7b806887d06d9bbd8b0fc5439c`, branch
`yulang3`, a 900-second wall budget, and at most two focused 120-second,
one-thread, `-M1024` checks only for concrete unresolved risks. The exact live
assignment and frozen handoff governed the lease. Root `AGENTS.md`, its
proof-closure contract in `AGENTS.pre-sprint.md`, the sprint and authority
rules, the `yulang-lean-proofs` skill and its two reference guides, and the
Authoritative 2026-10-11 inference principles were read. No Git command was
used to reconstruct or change the supplied baseline.

## 1. Frozen identity and independently reconciled evidence

All three repository outputs match the supplied SHA-256 values. All 27 source
inputs match both current repository bytes and their frozen copies. All 146
entries of the producer's baseline manifest match the isolated project. The
Git extraction provenance is the primary's receipt; this reviewer independently
checked manifest-to-file identity without invoking Git. The 146 entries are
not a claim that all those modules were built by this packet.

| Object | Verified SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/NativeDrainOwnership.lean` | `d37edac29dcecc19dd90b91c3095e5385a0657310dcf08d805a8f20672872d18` |
| `notes/theory/2026-10-26-native-drain-ownership.md` | `1e725751031322517c213662b0e0f1cf7b6e96bef656e2a6e45a40d67aee24e6` |
| `tasks/agent-loop/inbox/20261026-native-drain-ownership-r4.md` | `2f95685b1e828535f2df8ac26371f308fb01e480e4f474dabe69af5ef202108d` |
| Producer `freeze.json` | `63d90fb2699d8981f2fa85fe0731d28c13af60258c0b794057a92796e9802dbd` |
| Producer `logs/check-12.log` | `c403082cd97a86a8c0414fa0965819d510523e9524d87f55dc9135932720b1b3` |
| Producer `logs/census-15.log` | `2b06ede11d8d76a3cfd2b637e6eea45bb7865ff400a0637f867f1efae3144758` |

Producer scratch paths are under
`/workspace/scratch/f98087c7ac1a/native-drain-r4`. Reviewer evidence is confined
to `/workspace/scratch/f98087c7ac1a/native-drain-review-r4`:

- `audit_frozen_evidence.py`, SHA-256
  `7adaf0ee74f619262a076009c55f02c09d16d8b0b73e9f60207bcbe402fef263`:
  independent hash reconciliation and strict census/appendix parsing.
- `evidence-summary.json`, SHA-256
  `b7dc4c66893c13561f55b971c502a839cf3ea1cd2309bb964fe5826ce81c06e8`:
  all 15 receipt outcomes, actual log hashes, counts and retained collection
  failures. The reconciliation command exited zero.
- `root-types-and-axioms.txt`, SHA-256
  `1576fc09552729c52027e2adfcfeb1894ddcbe82125cafdf8c24143892a8baf5`:
  the complete printed types and exact axiom lists of all 17 authored roots,
  extracted independently from the verified final census.

## 2. Mathematical review and actual theorem premises

The complete 516-line Lean module and complete construction paper were read.
Its only import is pinned `Std`; no `LocalLaws`, project soundness axiom,
semantic child-success premise, independent cursor history, or independent
frame history is an input to the reachable-state conclusions.

1. **Occurrence identity survives Transport.** A `Work` records its serial,
   task, admitted relation and optional ticket. `transport` changes the
   frame's separate `processing` field. `dispatch` moves the original work
   into `processed`. The proof does not silently replace the issued occurrence
   by its canonical relation or require those relations to be equal.
2. **One history supplies conservation.** `Step` changes the operation table,
   queue and frame stack in the same state. Replay transfer constructs the
   ticket from the selected operation and the exact indexed child payload;
   successful dequeue attaches that same ticket to the frame. `Invariant`
   expresses the coverage obligation, but `initial_invariant` and
   `step_invariant` establish it. `reachable_invariant` therefore requires
   only `Run initial s`, not the desired coverage as an external assumption.
3. **The vector split is literal.** `acks = done ++ pending` and
   `completed = done.length`. `consumedFrame` removes the first pending entry
   and appends it to `done`. The representation preserves vector order and
   duplicates. `frame_split_exact` proves both slices; it is not a set-valued
   replacement for native acknowledgement storage.
4. **Return facts are derived.** `Frame.coherent` includes the stage/current,
   diagnostic and pending implications and the prepared-cursor interval.
   `initial_coherent` and `step_coherent` derive these properties from the
   empty state. `ready_frame_readback` then obtains empty current/pending,
   completed diagnostics, and `completed = prepared = acks.length` from an
   actual reachable ReturnReady frame. Although pop constructors repeat some
   guards, the public reachable-state conclusion does not assume them as a
   separate terminal-success certificate.
5. **Completion and delivery stay separate.** `acknowledge` requires the
   exact next consumed index and the matching wait state, writes a diagnosed
   receipt, and uses the native saturating completion expression. `popReplay`
   retains Ready only after the exact consumed/queued boundary. `delivered`
   changes only the operation's wait state. Empty-child completion, retired
   Idle reclamation and commit's prepared-to-completed reset are represented.
6. **The model is inhabited along the relevant path.** The explicit ten-step
   witness allocates, starts synchronously, takes, transports from relation 42
   to 99, dispatches, enters/completes diagnostics, acknowledges, returns and
   delivers. Its readback has one immutable issued occurrence, one exact
   ticket, one unchanged acknowledgement on delivery, and both cursors equal
   to one. Ordinary `decide` here is kernel computation, not native evaluation
   used as an unchecked proof oracle.

All names below have prefix `YulangClosure.NativeDrainOwnership`:

| Roots | Exact input and conclusion |
| --- | --- |
| `initial_invariant`, `initial_coherent` | No hypotheses; establish the two predicates at `initial`. |
| `step_invariant`, `step_coherent` | One `Step s t` and the corresponding predicate at `s` preserve it at `t`. |
| `run_invariant`, `run_coherent` | One `Run s t` and the predicate at its starting state preserve it at the endpoint. |
| `reachable_invariant`, `reachable_coherent` | `Run initial s` alone yields the corresponding derived endpoint predicate. |
| `ready_frame_readback` | `Run initial s`, membership of frame `f`, and `f.phase = returnReady` give the five terminal facts above. |
| `quiescent_work_returned` | `Run initial s`, empty queue and empty stack imply that every member of `issued` occurs in a returned frame's processed list, with diagnosed, ReturnReady, empty-pending and empty-current fields. |
| `quiescent_replay_acknowledged` | The same three inputs imply an exact-ticket diagnosed receipt for every member of `transferred`. |
| `outstanding_ticket_has_owner` | `Run initial s`, transferred-ticket membership and absence of its receipt imply queue ownership or live-frame-vector ownership. |
| `frame_prefix_has_real_receipts` | `Run initial s` and live-frame membership imply an exact-ticket diagnosed receipt for each member of `done`. |
| `frame_split_exact`, `empty_pending_iff_completed` | Any frame, without reachability: exact prefix/suffix slices, and empty pending iff completed equals vector length. |
| `Witness.synchronous_transport_run`, `Witness.synchronous_transport_readback` | No hypotheses: the concrete trace and the stated computed endpoint/readback equations. |

The coverage conclusions are existential membership claims. They do not claim
a bijection between slots and receipts, a general exactly-once theorem, or that
every allocated operation child has already been transferred. An allocated
operation with untransferred children can coexist with an empty queue/stack
in this model. Nor does the packet prove that execution eventually reaches
quiescence. These are limits of the exact statements, not counterexamples to
the accepted theorems; the paper's quantified conclusions stay within them.

## 3. Inspection against the actual native bodies

The cited source bodies were read directly, not inferred from the paper's
mapping. Paths in this table are under `crates/yu-solver/src` at the frozen
source hashes.

| Native body | Reviewed correspondence and boundary |
| --- | --- |
| `candidate_context.rs:3992–4076` | Replay allocation retains its actual child relation sequence and zero/Idle cursors. Native currently assigns the operation task to each child; allowing explicit per-child task fields in Lean generalizes the payload without identifying distinct tasks or narrowing the parent. |
| `lib.rs:14185–14258`; `candidate_context.rs:2249–2261` | Successful start allocates a new top frame and enqueues the initial occurrence from an empty queue. Native allocation and fallible preflight must still be authenticated at the successful cut. |
| `lib.rs:15223–15250`; `candidate_context.rs:2369–2396` | Enqueue obtains evidence and capacity before transfer and infallible queue insertion. Transfer checks Idle/live, child index, consumed lower bound and queued upper bound; re-enqueue does not advance queued again. |
| `lib.rs:14260–14343,15166–15171` | Prior slots and the actual next Replay owner are prepared before pop. The popped item's acknowledgement is appended to the same frame and its preparation count advances. |
| `lib.rs:14344–14420`; `candidate_context.rs:3767–3887` | Transport may create a different relation with a retained Derived edge. Context can publish `discharged` before Dispatch finishes. The clearing cut follows ordinary or structured Function/Tuple/Record/Variant completion. The model's `processed` mark correctly refers to that later cut, while the actual Derived/Context/body graph remains an unproved supplier. |
| `lib.rs:14395–14420,14881–14945`; `candidate_context.rs:2405–2453` | Diagnostics precede terminal acknowledgements. Prepared bounds, ordered consumption, exact Running destination, Ready retention and top-frame removal match the represented successful cuts. Diagnostics may retain conflicts. |
| `candidate_context.rs:4097–4228` | Synchronous Running/Ready delivery and asynchronous Queued outcomes are distinct. Delivery releases Ready without another acknowledgement. No-child handling invokes saturating completion. Rust `Ok` or a Queued outcome alone does not imply the theorem's empty-stack/empty-queue premises. |
| `candidate_context.rs:2190–2247` | Actual reclamation also checks that no live restoration retains the Replay. Lean `reclaim` drops that extra guard, an overapproximation harmless to these conservation claims; it is not an operational equivalence theorem. Commit resets every surviving frame's prepared cursor to completed. |

The candidate early return at `lib.rs:14001–14004` was also checked; the later
legacy synchronous loop is not a second reachable candidate stage machine.
The callback batch adapter at `candidate_context.rs:3938–3991` is explicitly
test-only. No test harness is substituted for the production shared history.

Mathematical `Nat` identities, ghost birth/work serials, unrestricted processing
relation updates, omitted capacity/dirty-settlement tests, and the relaxed
reclamation guard all reinforce the stated one-way application boundary. The
paper does not claim that every Lean step can be executed by Rust.

## 4. Checker evidence and complete axiom census

The frozen final module is identical to the isolated project's source and to
the source snapshots used by `check-12` and `census-15`. The exact current
checker evidence was reused as instructed. **New Lean/checker calls: 0 of 2.**
No remaining concrete checker risk justified another build or a broad suite.

`check-12` verifies Lake `5.0.0-src+eb6cafb` and Lean `4.35.0`, compiler commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, then successfully builds the exact
module and checks all 17 roots. The source imports only `Std`; the project's
default target does not supply this proof's coverage. `census-15` uses the
same absolute Lake path with `--no-cache env lean -j1 -M1024
AuditNativeDrainOwnership.lean`, exits zero, and has a complete EOF trailer.

The census program was inspected. It selects the actual originating module
index, including private/generated constants, rejects originating axioms,
prints every complete type, and checks each declaration's transitive axiom set.
Independent parsing confirms 512 unique matching BEGIN/END blocks, 187 theorem
constants, all 17 required roots, the exact final counts, strict valid UTF-8,
zero replacement characters and zero `⋯` omissions. Every one of the 187
theorem blocks in the tracked handoff exactly matches the verified census.

| Complete transitive axiom set | All declarations | Theorem constants |
| --- | ---: | ---: |
| none | 407 | 107 |
| `propext` | 53 | 28 |
| `propext, Quot.sound` | 10 | 10 |
| `propext, Quot.sound, Classical.choice` | 42 | 42 |

For the 17 authored roots: the witness readback has no axioms; `frame_split_exact`
and the witness run use `propext`; the two initial-state roots use `propext`
and `Quot.sound`; the other 12 use all three permitted standard axioms. This
is not an axiom-free claim. Source inspection finds no proof hole, project
axiom, native-evaluation trust or kernel-checking bypass.

All 15 receipts retain their corresponding source snapshots and logs. Their
recorded source hashes match those snapshots. All log hashes match except the
explicitly rejected `census-13`. The observed failures agree with the handoff:

- Calls 1–7 and 10–11 retain actual construction/elaboration failures.
- Call 8 built the module but was killed by the 1-GiB aggregate wrapper bound;
  it is not complete root-audit evidence. Call 9 is an earlier successful
  milestone, not substituted for the final source.
- Call 13 has 505 BEGIN and 504 END markers, no final trailer, and observed
  hash `afc4bf097377d1b714339cda0dadf0d3f2eb2eefbdbc57de7e77f61e064176c5`
  rather than its recorded hash. It remains rejected despite exit zero.
- Call 14 has balanced 512 blocks but two U+FFFD characters; it remains
  rejected as complete-type evidence.
- Call 15 resolves those collection defects. Its observed log hash matches
  the receipt and freeze manifest exactly.

The local aggregate allowance is 1.25 GiB; the Lean process limit and project
configuration remain `-j1 -M1024`. The final source/root call's reported peak
is 1,146,888,192 bytes. The wrapper samples descendant RSS, so this is sampled
resource evidence, not continuous kernel memory enforcement.

## 5. Application to the unchanged original parent

`Contracts.lean:128–130` still asks, for every supported original source,
scope, generated constraints and solution, for an original source judgment
and one witness satisfying the same full `sameScoped` relation. Independently,
`NativeCorrespondence` at lines 147–149 must turn actual native success into
generated constraints and a native-realized solution. `CoreComposition.lean`'s
`native_success_elaborates` explicitly consumes both obligations and an
elaboration proof; it does not establish any of them.

This packet supplies the following genuine reduction: once a **single actual
committed history** is mapped to `Run initial s` and its accepted outer return
is shown to have empty queue and stack, the two quiescence roots supply
diagnosed returned-work and exact transferred-ticket receipts from that same
history. An independently chosen cursor history or terminal frame certificate
is no longer needed for those conclusions.

The first remaining supplier is owned by the native-history/correspondence
lane: construct that common execution map, with complete payload encoding,
actual allocation/frame identities, callback cuts and admissible successful
native paths. Its cancellation, merges and reused numeric IDs must be erased
through the same operation/worklist/frame history. The separate R3 mutable-owner
and frame-rollback theorems do not automatically identify those histories.
The application must also establish which allocated children must actually be
transferred; empty queues alone do not supply this enrollment fact.

The Context/Value owners must then connect the admitted relation, actual
Transport Derived path, early Context publication and completed dispatch body,
including duplicate/discharged cases with their previous complete owner or
active dependency. Diagnostic acceptance must establish the absence of the
rejecting conflicts, rather than merely the stage's completion. The semantic
and source lane still owes the original row/Context interpretation, optional
record adaptation, method selection, complete Call/effect behavior and the
same entire scope/world/`nu,K,D` witness through generalization and uses.

These remain original class-A/B and source/native obligations. No supported
input, source constructor, effect or shared witness is removed; no stronger
conclusion is moved into a new semantic premise and called proved. The bounded
proof component is ready for primary integration at this accepted scope.
Default/import integration, Git commits/pushes and all status changes belong
to the primary. Production or full-parent promotion is not authorized by this
review.

## Writer cessation

**WRITES STOPPED.** The sole repository write is this review file. Scratch
writes are confined to `native-drain-review-r4/**`; no build/cache or process
is running. No producer output, shared status, import, Rust source, expected
output, configuration or dependency was edited. No Git or descendant action
was performed. Frozen producer hashes were rechecked at cessation.
