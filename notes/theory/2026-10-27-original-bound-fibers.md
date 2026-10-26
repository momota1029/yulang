# Original bound fibers: captured cursors and physical publication

Date: 2026-10-27. Producer: `/root`. Branch: `yulang3`.
The parent is the original native first-empty obstruction, especially its
selected-copy transport step in §6, and ultimately the unchanged original
inference-accessibility obligation. Neither parent is closed by this packet.

`YulangClosure.OriginalBoundFibers` constructs the physical linked bound
table, proves persistence of already captured source cursors through actual
attachment calls, and joins a physical publication suffix to the existing
native relation interner. The result retains the same raw relation ID and
complete relation key, rather than a graph edge modulo semantic equivalence.

## Native owners and represented state

The governing source owners are:

- `candidate_context.rs::bound_cursor`, `bound_entry`, `attach` (around
  3269–3296): a head map plus append-only `(BoundKey, RelationId, next)` vector;
  duplicate raw relation detection precedes head-map and vector reservation.
- `candidate_effect.rs::candidate_transfer_bound_origins` (685 onward):
  capture the source head once, read the current entry and save `next` before
  transporting that parent, then continue from the captured pointer.
- `candidate_context.rs::candidate_context_transport_witness_with_evidence`
  (4320 onward): after snapshot, complete Context/Flow/key construction,
  call the real interner, publish the dependency, record the evidence
  transform, attach the exact child, then sample resources.
- `candidate_context.rs::dependency` and evidence `transform`: their internal
  evidence, dependency, index and accounting tables remain outside this
  physical projection. Their failure positions are retained.

The first two source hashes are respectively
`57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e`
and `70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f`,
matching the source-qualified
[native obstruction](2026-10-26-native-copy-quiescence-obstruction.md).

The bound key type `B` is parametric. Instantiating it with the complete raw
native BoundKey retains owner, polarity and endpoint of either kind. No
endpoint-only equivalence or Value-only restriction is introduced. The
stored relation is the native raw integer; its meaning comes from the
separate physical interner readback, not from its numeric equality to a task.

`Store` keeps the actual head map and vector. `Valid` records only physical
formation: heads address same-key entries, links address same-key predecessors,
and each predecessor index is strictly smaller. `valid_empty` constructs it
at initialization. `append_valid`, `attach_valid` and `run_valid` preserve it
through every represented update, including duplicates and reserve failures.
It contains no semantic typing, completed Replay, or future success premise.

## Captured cursor construction

`walk` follows the actual stored links. Its recursion is justified by
`cursorRank none = 0`, `cursorRank (some i) = i + 1` and the proved older-index
property; there is no caller fuel or global identity bound. The raw absent
entry branch is still representable, but `Valid.heads` and `Valid.links`
prove it unreachable from a formed stored head. This does not assert that
Rust's unchecked vector indexing accepts malformed states safely.

`attach` computes duplicate detection from that same linked readout. It
returns immediately for an existing raw relation, tests the head-map reserve
then the vector reserve, and only then appends and replaces the head. Capacity
changes caused by a reserve before a later reserve fails are not represented
as logical table writes. Every failure retains the represented entries/heads.

`run_captured_cursor` and `run_captured_head` prove equality of the complete
ordered `(index, Entry)` lists before and after any finite sequence of these
actual calls. This applies even when the target is the source bound itself:
the new live head may move, but the previously captured head and every old
next pointer retain their original readback. No recomputed live head is
substituted at the recursive call.

`captured_head_entries` strengthens this equality: every selected entry has
an index below the initial vector length, identical old/new physical
readback, and the complete original source key. `run_fiber_prefix` derives
that the current fiber list is a newly added prefix followed by the old list.
`run_preserves_fiber` follows without any graph saturation assumption.

`CursorAdvance` records one control advance with its read-before-body order
and a finite sequence of represented table calls in that body. The next
cursor decreases even when those calls append arbitrarily many other fibers.
`cursor_accessible` therefore proves `Acc` for this linked-loop **control
relation**. It does not establish termination of the intervening interner,
dependency/evidence calls, the subsequent origin-metadata loop, a whole drain,
or the original inference machine. A finite `Run` body is explicit; it is
not a theorem that all real bodies return normally.

## Same interner result and attached fiber

`Physical` contains the existing `NativeRelationInterner.Native` and this
physical fiber table. `publish` starts after the preceding snapshot and
authentic complete-key calculation. It calls the actual executable
`Native.call` and retains its partial store on failure. It then tests the
observed dependency/evidence results in their native order, calls the actual
`attach`, and finally tests resource sampling. An error after attachment
retains that attachment; it is not silently rolled back or reported as success.

`published_fiber_exact` assumes the existing native interner history and the
computed normal outcome. It derives all of the following for the same result:

1. the existing interner's complete `Allowed key` guard;
2. actual stored readback of the returned raw ID equal to the **entire Key**;
3. membership of that exact ID in the target's actual linked fiber list.

The key retains its Value/Effect pair, Context, source set and full scoped
flow, including all deferred Function demand fields. No caller supplies the
post-call readback, selected child membership or a matching-ID certificate.
`publish_captured_source` applies captured-head preservation to this same
physical computation, including its partial-error outcomes.

The booleans for dependency/evidence/sample are observed results of those
external operations, not their implementation or a promise of semantic
success. Their internal tables and authentic native readback still need an
extraction. The source-to-target transported key, post-check Context, scoped
root remapping, source snapshot and original/destination bound association
are inputs owned before this suffix. No claim that an arbitrary supplied
Key is the authentic transport key is made here.

## Remaining parent applications

The new extrusion Work producer can instantiate `B` with its full `RawBound`
and apply this packet at its exact `BoundRequest` destination. A further join
must compute the authentic transport key from the source fiber's stored
relation and its witness, and connect all normal physical suffixes to that
same Work execution. The metadata origin loop must not be treated as a
source relation fiber; the native code deliberately retains its association
gap. Replay quadrant/dependency deduplication, pre-settlement graph retention,
the NQ successor argument and whole Rust/source trace extraction remain open.

Rollback and external mutation are not added to this append-only segment.
The original supported-source scope, instance order and global
`Acc (fun next prev => p.inferStep prev next)` target are unchanged. All four
whole-language soundness, Effect hygiene, principality and termination gates
remain OPEN.

## Checks, audit and frozen artifacts

The fixed toolchain is Lean 4.35.0,
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. The final direct check used
`-j1 -M1024`, exited 0, and emitted no diagnostics. The parent-owned focused
build then passed **10 jobs**, also without diagnostics.

Ten bounded source invocations were used while constructing the module.
The real local failures involved missing explicit type annotations, reserved
identifier spellings, dependent-match elimination, the recursion proof's
cursor equality, and publication-result case splitting. Two intermediate
fragments and the final source passed. The complete numbered logs are
`/tmp/yulang-bound-fibers-01.log` through `-10.log`; earlier failures were
retained rather than counted as success. The build log is
`/tmp/yulang-bound-fibers-build.log`.

`AuditOriginalBoundFibers.lean` imports the compiled frozen module, selects
every declaration by originating module index, checks required application
roots are theorems, prints complete types and transitive axiom sets, and
rejects project axioms or dependencies beyond the three permitted standard
axioms. The first run passed at **1 GiB**, with no diagnostics or printer
elisions: **329 declarations, 143 theorem constants, 33 authored theorems**.
There are 329 matched begin/end records. The remaining 110 theorem constants
are generated auxiliaries and are included in that audit.

| Artifact | SHA-256 |
| --- | --- |
| `OriginalBoundFibers.lean` | `1a512b23a55936e30088763d46d3f71458cec953b58edbf794e28bb13eaf0ca5` |
| `AuditOriginalBoundFibers.lean` | `bb9e11273eaa015bf56b8bdc8ec220bbef7e3e10ba83fc3545064f8124ffed23` |
| `/tmp/yulang-bound-fibers-audit-01.log` | `05235808e8bd738e2f196cfd543938be1ba5360bacf75f687bbb64e68f639ca7` |

The reusable audit received a one-byte final-blank-line normalization at integration; its Lean command stream is unchanged from the audited copy.

All checker processes exited. The source and reusable audit are frozen for
independent nonauthor review; no full original theorem is claimed here.
