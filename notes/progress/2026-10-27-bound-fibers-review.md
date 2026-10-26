# Independent review: original bound fibers

Reviewer: `/root/principality`, independent of target production.
Verdict: **ACCEPT local conditional proof; no blocking finding.** Original
inference termination/NQ extraction and all four whole-language goals remain
OPEN. This review does not certify the reviewer's separate Carrier artifact.

## Frozen targets

| Target | Verified SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/OriginalBoundFibers.lean` | `1a512b23a55936e30088763d46d3f71458cec953b58edbf794e28bb13eaf0ca5` |
| `notes/theory/2026-10-27-original-bound-fibers.md` | `d31a6019b8913b37bdbd578e38c1ce6eebb0efecce8791c779ccc64e9cd127ea` |
| `notes/theory/lean/AuditOriginalBoundFibers.lean` | `249e8c4a458c7d116e57a1601d1a46c3e569bd3dbd15b95328cd75fb82871f31` |

I read all 575 source lines and the complete paired note, the relevant native
owners, `NativeRelationInterner.Native.call`/`NativeHistory`/readback theorem,
and `NativeValuePorts.Key`/`Allowed`. Native source hashes match the note:
`candidate_context.rs` is
`57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e`;
`candidate_effect.rs` is
`70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f`.

## Independent findings

1. **Actual linked chain and formed-state invariant.** `Store` retains the
   complete key, raw relation ID, and stored previous pointer. `Valid` requires
   formed same-key heads/links and strictly smaller predecessor indices. These
   are proved at empty initialization and preserved by actual append/attach
   cases. `walk` follows stored pointers with a proved index decrease; it does
   not replace the chain by an unordered graph or supplied fuel. Its absent
   index branch is excluded for formed captured heads by `heads`, `links`, and
   `head_bounded`; it is not a statement about safe Rust indexing on malformed
   stores.

2. **Read-before-body order is authentic.** Native
   `candidate_transfer_bound_origins` captures the source head once, obtains
   `(parent,next)`, assigns `cursor = next`, and then calls transport. The Lean
   `CursorAdvance` uses the entry read from the **before** store and that same
   saved `previous` for the after cursor. `run_captured_head` and
   `captured_head_entries` preserve the exact ordered entries below the old
   length even if body calls attach to the source key itself. No live head is
   recomputed for continuation.

3. **The accessibility statement is local.** `cursor_accessible` proves
   `Acc (fun next previous => CursorAdvance previous next) start` by the actual
   saved pointer's rank. `CursorAdvance` contains a finite `Run` of represented
   attach calls in its body. It does not prove that the interner,
   dependency/evidence routines, metadata-origin loop, whole drain, or original
   inference step returns. `Valid` itself contains no completion premise. The
   paired note makes this distinction correctly.

4. **Attachment and partial errors follow the source order.** Native `attach`
   checks duplicate raw relation identity, reserves the head map, reserves the
   vector, then updates head/vector. Lean reproduces that decision order and
   preserves represented table contents on reserve failure. Capacity changes
   from an earlier successful reserve are deliberately outside the projection.
   Duplicate success requires no new reserve; new success prepends exactly
   one raw ID at that exact complete key.

5. **One actual interner result is published.** `publish` executes the existing
   `Native.call`; it does not assume a matching result ID/readback. The order is
   interner, dependency result, evidence result, attach, sample, matching
   `candidate_context_transport_witness_with_evidence` after its snapshot and
   key construction. An interner error retains its partial native store.
   Dependency/evidence failure occurs before attachment; sampling failure
   retains the completed attachment. `publish_complete` derives the same
   `.ok relation` and exact successful attach from the computed normal outcome.
   `published_fiber_exact` then derives `Allowed key`, complete stored native
   readback `some key`, and membership of that identical raw relation in the
   destination fiber. It does not assume post-call membership or readback.

6. **No key quotient or Effect omission.** `B` remains a full parametric bound
   key; native `BoundKey` has owner, polarity and endpoint. The relation `Key`
   retains the Value/Effect pair, Context, source set and full scoped Flow,
   including deferred Function demand. `Allowed` is the existing native guard,
   not subtype truth or a semantic equivalence class. The result makes no
   endpoint-only or Value-only substitution.

## Acceptance boundary and residual owners

Dependency, evidence transformation, and sampling are observed external
outcomes in this projection. I inspected their source call sites and the
dependency/transform paths: their separate tables, coverage gaps, accounting
and failure effects are not proved by these Boolean observations. The paired
note retains those owners explicitly.

The suffix starts **after** the source snapshot, witness/target check,
transported scoped Flow, post-check Context and complete key construction.
Authenticity of that input key and its association with the source/destination
bounds remains a separate extraction. `Store.Valid` establishes physical
linked-table formation; it does not establish that every pre-existing fiber ID
has an authentic transported-key meaning in the native store. The new theorem
derives exact readback for its own returned child only.

The subsequent origin metadata loop retains the native
`MissingOriginAssociation` gap and is not converted into an executable source
fiber. Rollback/external mutation is excluded from the append-only segment.
These restrictions do not change the original supported source language; they
limit the proved local projection. Full native/source trace extraction,
selected-copy successor production, first-empty obstruction application and
global `inferStep` accessibility remain open.

## Independent verification

I used two of the authorized four checks, both with the pinned Lean 4.35.0
(`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`),
`timeout 120`, `LEAN_NUM_THREADS=1`, and
`/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake env lean -j1 -M1024`.
The direct frozen-source check and independent rerun of the frozen originating
module audit each exited 0. Neither emitted diagnostics; the audit had no type
elisions. No `-o`, build, cache mutation or Rust execution was used.

The independent census matches the producer: **329 originating declarations,
143 theorem constants = 33 authored + 110 generated**, with 329 matched
begin/end records. All types and all transitive axioms were printed and the
audit rejects project axioms and nonpermitted dependencies. Across all
declarations, 227 use no axioms, 41 only `propext`, 60
`propext, Quot.sound`, and one all three standard axioms. In particular
`cursor_accessible` uses `propext, Quot.sound`; `published_fiber_exact` uses
`propext, Classical.choice, Quot.sound`. No `sorryAx` or checker bypass occurs.

Independent logs are
`/tmp/yulang-principality-bound-fibers-review/source-check.log` and
`/tmp/yulang-principality-bound-fibers-review/audit-check.log`.
Their SHA-256 values are respectively
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`
and `05235808e8bd738e2f196cfd543938be1ba5360bacf75f687bbb64e68f639ca7`;
the independent audit output is byte-identical to the frozen producer audit.
The frozen targets remained byte-identical after verification. All review
checker processes exited; no owned process remains. Only this review file and
the uniquely named scratch directory were written. No target, shared status,
Git or build/cache file changed. Review writes stopped at handoff.

## Primary integration record: nonsemantic audit formatting

After this independent review froze, the primary removed one final blank
line from the reusable audit so the staged whitespace gate passes. The Lean
command stream is unchanged byte-for-byte after trimming trailing whitespace;
the proof source remains at the reviewed hash above. The integrated audit
SHA-256 is `bb9e11273eaa015bf56b8bdc8ec220bbef7e3e10ba83fc3545064f8124ffed23`.
The producer note only updates that checksum and records the normalization;
its integrated SHA-256 is
`ee9dc3686d743768b53ad49b06d41ba2543e232ff7336abb4a2cbacefb19822c`.
No theorem, premise, audit command, verdict or semantic boundary changed.
The independently executed log and its original input hash above remain the
actual verification evidence; no broad recheck was required for this delta.
