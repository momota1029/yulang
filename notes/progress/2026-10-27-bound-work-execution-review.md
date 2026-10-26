# Independent review: original selected Bound execution

Verdict: **ACCEPT for scoped Value insertion through the first executable-fiber
loop, at the stated origin-metadata cut.** No blocking source-fidelity or
proof-circularity finding. All four original whole-language goals remain
**OPEN**; this receipt gives no full Work, extrusion, drain, NQ, or global
termination credit.

## Frozen targets and review coverage

| Target | SHA-256 |
| --- | --- |
| [OriginalBoundWorkExecution.lean](../theory/lean/YulangClosure/OriginalBoundWorkExecution.lean) | `b6d3d2e7c9f14b87cce55f69e2cb8fd87269e282732bdefa685fb1bfeaf099f0` |
| [Paired theory note](../theory/2026-10-27-original-bound-work-execution.md) | `120ebdcc78f6781ec9ca3194ef7cf6e1e7312f2552accc68beab10c400ab4e01` |

I did not author either target. I read all **802 source lines**, the complete
note, the relevant Work/fiber/transfer definitions and theorem interfaces, and
the original native owners. The source correspondence was checked against
`candidate_extrusion.rs` Work::Bound and copied-bound insertion,
`candidate_effect.rs` scoped admission/capture/transfer, and
`candidate_context.rs` evidence, linked cursor, and same-parent transport.
The original destination is NQ section 6.1's selected copied-bound edge;
the surrounding source-specific execution remains a separate obligation.

## Findings supporting acceptance

**The selected request and the physical state are connected by computation.**
`selected_bound_execution` uses the actual `select` result and rows-first memo
lookup to reduce `execute` to `continueBound` on the popped Work state and
`W.boundRequest` constructed from that state. It retains the original raw
bound, insertion endpoints, complete operation/caller, and capture flag.
`canonicalRequest` replaces only the destination with the canonicalization
of those insertion endpoints. No arbitrary post-insertion state enters the
interface.

**The native ordering is preserved at the represented cuts.**

| Native sequence | Reviewed construction |
| --- | --- |
| Graph/mode check, original snapshot import with relation absent | `insert`, then the snapshot `Observation`; unscoped insertion stops at its external owner. |
| Canonical endpoint/kind/range checks, origin admission | `canonicalRequest`, `locate`, computed `boundPair`, and `scopedAdmission`; the actual typed-pair scope or bound-pair fallback is retained. |
| Emission reservation, journal, capacity, physical push | The corresponding staged calls precede `W.physicalInsert`; physical addressing uses the selected Value row/atom vector. |
| Flags/counters, exact readback, capture, dirty, emission, sample | `appendValue` and `finishValue` retain this order and require actual slot readback to equal the complete destination bound. |
| Capture source head, read each next pointer before its body | `continueBound` invokes the frozen `TF.transferBound` with its own insertion result; the imported loop retains the captured linked order. |
| Later origin-metadata loop | Still external. `.originMetadata` means the first loop has completed and the later loop is next. |

The native scoped `BoundTransport` case explicitly assigns `relation=None`.
Its evidence/origin operations do not invoke executable relation publication.
The actual Value capture branch is a no-op because capture registration only
matches an Effect-row/negative/Allowance bound. Consequently the modeled
unchanged transfer-state result has a source owner. It is not extended to the
unscoped `OwnerEmission` branch, which can publish before the append, or to
Effect capture. `insert_fibers_unchanged` also holds at these early external
stops; it does not describe execution of their omitted bodies.

**The main proof derives the first-loop premise from the entire result.**
`bound_at_metadata` assumes only that the composed
`continueBound calls inputs state request` returns `.originMetadata`.
It destructs that computation, derives actual insertion readiness and its
physical-slot equality, derives the retained transfer state, and then obtains
completion of that specific `TF.transferBound` call. Neither an independently
completed loop nor a `Delivered` certificate is supplied. Rewriting the
retained state identifies the captured list with the pre-insertion source
head. `AtOriginMetadata` is proved from these facts, not stored in an input.
This is a successful-execution result; it does not prove arbitrary readouts
will make the composition succeed.

**Representatives, raw identity, and complete keys survive the join.**
`physical_representatives` derives preservation of both representative
functions from `W.physicalInsert`. `loopInputs` overwrites both transfer
representatives with those of the retained Work state, preventing an unrelated
pair of representative functions at this join. `TF.Delivered` retains actual
parent readback, computed bound pair and scoped-root remapping, the same-parent
post-check Context, complete source set, full Flow, and the native readback at
the same child ID attached to the destination fiber. The transformer and four
non-root demand fields remain intact; root changes follow the existing
two-position remapping. No endpoint quotient or idempotence assumption is used.

**The nonempty instance and both failure cuts are substantive computations.**
The existing three-step Visit/Visit/Bound producer supplies the row request.
The fixture constructs source relations through actual `publish` calls from
the empty native/fiber state, deriving formation and native history. It proves
source fiber `[1, 0]`, earlier source-link fiber `[2]`, calls
`[(1, 3), (0, 4)]`, and destination fiber `[4, 3]`. Child 3 has the complete
second-parent key with pair `row 2 < row 1` and its computed Context 0;
child 4 has the complete first-parent key with the same new pair. Source sets
42/43 and all five demand fields are retained in these row-only transports.
The kernel-checked reductions establish these IDs and memberships rather than
receiving them as premises.

The final insertion sample failure retains the physical upper vector `[1]`,
dirty flag, bookkeeping, and emission receipt, reports native sample error 17,
and starts no transfer calls. The transfer sample failure retains the same
append and raw child 3's complete key and attachment; child 4 is absent. The
failed first body is not recorded as a completed call. Neither branch replaces
the partial result by its pre-call state.

## Exact acceptance boundary

- `Calls M` exposes named external metadata/resource readouts. Its
  `Observation M A` is retained bookkeeping plus `Except Nat A`, not a safety,
  coverage, or final-membership proposition. Nevertheless authentic snapshot,
  admission, journal/capacity, evidence, and resource extraction remains
  required. The proof does not reconstruct those private tables from opaque
  integer readouts.
- After transfer begins, the `bookkeeping` component is a **before-loop
  checkpoint**. The result does not assert that the imported transfer's
  evidence/dependency operations leave the real metadata state unchanged.
  Its physical native/fiber writes, including partial failures, are retained
  by the separate `TF.State` result.
- `rowExecution` supplies the native/fiber projection at the selected Bound
  cut while computing the Work request from the earlier three-step producer.
  It does not extract all earlier source-link metadata from one Rust history
  or prove that that earlier prefix is inert. The constructed source-link
  fixture is a local instance, not such an extraction theorem. In particular,
  `Operation.processing = some 52` is not authenticated against the fixture's
  small generated relation history.
- `TF.State`'s linked-table validity and native history are formation
  requirements of the input representation. They are constructed for the
  fixture; correspondence for every original native state is still open.
- Unscoped emission, Effect insertion/capture, the later metadata loop,
  surrounding eight-variant extrusion, all selected copied-path operations,
  four-port enqueue/replay, and the full anchored-successor argument remain
  separate owners. No theorem equates the metadata cut with full Work
  completion or closes an original whole-language root.

## Independent verification and complete axiom census

The pinned toolchain reports Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, and Lake
`5.0.0-src+eb6cafb`. From `notes/theory/lean`, the independent direct check used
the resolved Lake path, `timeout 120`, `LEAN_NUM_THREADS=1`, and
`env lean -j1 -M1024`, without `-o`. It exited **0 in 8.314 seconds**, with
an empty log. The independent all-origin audit used `-M2048` solely for the
complete type/axiom printer and exited **0 in 1.576 seconds**.

The audit selects actual declaration origin, including private/generated
constants. All **545** begin/end records match: **286 definitions, 196 theorem
constants, 37 constructors, 13 inductives, and 13 recursors**. There are
**33 private declarations**. All **37 authored roots** are present, leaving
**159 generated theorem constants**. No target axiom or opaque declaration,
diagnostic, elision, `sorryAx`, or unapproved transitive axiom occurs.

The authored axiom distribution is: **2 empty; 17 `{propext}`; 8
`{propext, Quot.sound}`; 10 `{propext, Classical.choice, Quot.sound}`**.
Every declaration's complete type and axiom set is retained in the log;
the census records each set individually. No authored proof hole, unsafe
declaration, native-evaluator axiom, or kernel-checker bypass was found.

| Independent artifact under `/tmp/yulang-bound-work-root-review/` | SHA-256 |
| --- | --- |
| `direct-01.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `AuditFull.lean` | `02e5b4a6a6634c2af4b86b54ba8ba96dcce6e267497a4d83887567571ba748a1` |
| `audit-01.log` | `10fe05e990105cf54fd4af758d636a6d6e746eb1596287a7d23ff8ae00f93f63` |
| `census.json` | `557e436fd960912737979499e080e4196e574911631c0af263726dee70f9dd75` |
| `input-hashes.json` | `8115ee65deea07d2c906face4e62dc2274d4385f3bec789b369e22c39f70f908` |

All seven frozen Lean/native input hashes and the producer's three audit
artifact hashes and final direct-log hash match the paired note. The review
also fingerprints both targets and the additional native/NQ owners, for
15 checked inputs in total. The combined 42-job build log was read; no review
build was run. Historical producer failures remain outside this acceptance
receipt. A postprocessing parser initially matched `opaque` inside a doc
comment; the retained parser failure and comment-aware repair changed neither
Lean evidence nor target source and required no checker retry.

Review budget used: **one direct check and one all-origin audit**, no checker
retry. Only this receipt and its leased scratch directory were written.
Frozen targets and inputs are unchanged. All review checker processes have
stopped; writes stop at this review's frozen handoff.
