# Resumed restoration: bounded incidence mutation search

Status: **unreviewed research-only source characterization**. No qualifying
source-level resumed-versus-uninterrupted counterexample was constructed.
The conditional indexing example below attacks frozen enumeration, not the
current live-index restoration implementation. No theorem or production gate
is closed by this note.

## Objective, authority, and frozen dependencies

Search actual mutation owners that can change a saved restoration's remaining
opposite enumeration or exact contextual fiber. This complements the constructive
resumption lane with a static mutation/owner attack. The granted budget is one
bounded pass, at most 20 minutes, no Cargo, executable probe, benchmark, or
delegation. Exclusive write lease:
`notes/progress/2026-10-11-resume-incidence-falsifier.md`.

Baseline: `abdec245c9efc3d8a02c0f5e0865af1d5163a643`. Every compiler read used
`git show` or `git grep` against this commit; no implementer's working compiler
files were consumed. Governing authority is the private suspension contract
§4 (saved count/index, live canonical opposite lookup, representative changes)
and §6 (atomic rollback and retry), together with contextual-attachment admission
design §4 (ordered contextual replay, qualifying recorded parent/copy intrusion).
The accepted user decision authorizes the private lifecycle implementation;
it supplies no new language restriction or source rejection rule.

SHA-256 of pinned committed contents:

| Dependency | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_extrusion.rs` | `83ebfc4b1fc917d842209a0d46e22188427a0b6523291073858bace0863055fb` |
| `crates/yu-solver/src/candidate_context.rs` | `bc7e25c14e913d5f1c487723ead0fbbaf696bce80a1e6b756b7af4c04d6ebadc` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `crates/yu-solver/src/candidate_scheme.rs` | `7d3169a68d2413b58228f122c1e92a21d828e1a44e41743f4458eabb90ca580c` |
| `crates/yu-solver/src/candidate_effect.rs` | `7e8e077f13c4a094565cc199a0e643fad2d04c920b449058b33ebb4d048cd360` |
| `crates/yu-solver/src/lib.rs` | `42bb81741d129cca8d9cf64a25f0a54c11fcf4cccc022f66c131c321752aa9de` |
| `notes/design/2026-10-11-private-candidate-suspension-contract.md` | `734d94cb02c3d2a101ab21435b4377ed06952ab384815da73636bcfbc986033d` |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| `notes/progress/2026-10-11-suspension-observation-owner-audit.md` | `1d064f4a4fe81edfad7207fc50eeee995e66df1ec084b1e46bbd239580931614` |

The observation audit is a supplied bounded inventory, not independent review
of this output. Its lifecycle omissions were used as context, and the mutation
and restoration paths relevant here were inspected at the pinned commit.

## Consumer boundary

Locators below are pinned line numbers; compiler filenames are under
`crates/yu-solver/src/`.

`candidate_begin_bound_restoration` (`candidate_extrusion.rs:655–674`)
inserts the accepted bound once, canonicalizes owner/bound, and saves the
opposite count. `candidate_drive_bound_restoration` (677–723) retains the
active replay operation; only after that operation drains does it advance
the opposite index. Before constructing a new replay it canonicalizes the
retained owner/bound and calls `candidate_opposite_bound` at the saved index.

`candidate_opposite_count` (567–590) counts **direct rows plus exact endpoints**.
`candidate_opposite_bound` (592–628) reads the current representative's direct
vector first and its exact vector second, using the current direct length as
the split. The physical opposite enumeration is not an immutable list and
does not enumerate contextual fibers directly.

`candidate_context_begin_replay` (`candidate_context.rs:2705–2786`) freezes
the selected lower/upper fiber heads and generates that operation's exact
ordered child list. Incoming-use replay uses `old=(None,None)`; ordinary
propagation instead uses previously recorded heads and skips duplicate Replay
dependencies. The generated list remains owned while children are queued and
consumed separately (1722–1776, 2788–2819). A later opposite index starts a
new operation with then-current fiber heads. A mutation after a batch was
generated is therefore a different seam from mutation before the next opposite
lookup.

## Mutation inventory and eligibility

| Owner class | Actual producer and condition | Effect on saved restoration |
| --- | --- | --- |
| Same-owner physical append | `candidate_insert_bound_with_evidence`, extrusion 406–565, canonicalizes owner/item then pushes one direct or exact slot; no physical deduplication occurs here. `candidate_apply_value` (769–798) and `candidate_apply_effect` (801–830) choose owner/side by the existing levels and endpoint forms, then insert and replay. | Exact append extends the end of the concatenation. Direct append moves its split and can change an unread index's endpoint. Saved count stays original. No arbitrary vector sort/removal was found in this path. |
| Extrusion one-sided link | `candidate_extrude`, extrusion 85–123: when original level exceeds target, allocate a copy, retain actual parent/copy provenance, and insert the copy into the original's opposite side. Selected bound lengths are saved before that insertion. | Supplies a real direct append producer and actual parent/copy provenance. Whether a specific source callback reaches this producer on the suspended owner's opposite side is a separate reachability premise. |
| Qualifying parent/copy intrusion | `settle_candidate_intrusion`, intrusion 358–506: require dirty state, a recorded parent/copy pair, distinct representatives, and equality of their current dependency-SCC labels. Dependency edges include physical row/endpoint incidence, view tails, and Function ports; the parent provenance record itself is not an adjacency edge. | Eligibility is actual parent/copy plus SCC membership, not arbitrary endpoint equality. No other `merge_candidate_rows` caller was found by committed-source search. This SCC check is not the certificate dependency-disjointness or suspended-frame deferral check. |
| Intrusion append then redirect | `merge_candidate_rows`, intrusion 513–603: append both copy bound sides into parent, transfer origins/fibers, splice Effect capture incidence, redirect copy to parent, canonicalize bound fibers, advance intrusion generation, then replay all parent lowers. | Parent vectors can have a different prefix from copy vectors. A frame retaining raw copy observes parent at its next lookup. Old physical copy storage remains; it is not the next canonical lookup owner. |
| Fiber transport without a new physical opposite slot | Context `candidate_context_canonicalize_bounds` (2822–2840), `candidate_context_transport_witness_with_evidence` (2879–2893), and effect `candidate_transfer_bound_origins` (462–501). Transport creates/reuses a canonical relation and attaches it to its target key; canonicalization scans third-owner keys as well as merged-owner keys. | Can extend an exact contextual fiber and add derived/transport evidence while physical count is unchanged. This is incidence mutation, not merely an intrusion-generation stamp. Missing origin-to-fiber association is explicitly retained as a coverage gap (effect 491–497). |
| Evidence-only admission | Effect `candidate_bound_origin_with_evidence` (341–395) first runs context-bound admission even for a duplicate origin; context `candidate_context_bound` (2608–2650) attaches the resulting relation. `attach` (2203–2215) omits an already attached relation. Imports/transforms retain evidence independently of physical emission. | A duplicate origin can add evidence without a new physical slot. If the relation is already attached, its fiber order does not change; a distinct post-check/context relation can instead prepend a fiber. These cases must not be collapsed into one "no mutation" classification. |
| Source fresh use | Scheme graph-bound loop (1131–1180) maps each captured bound, transports its relation/context and bundle incidence, then invokes restoration with FreshUse evidence. Transport is per bound, immediately before that bound's restore, rather than one pretransport of all captured bounds. | Later graph bounds cannot execute between indices of the current synchronous restoration. Nested typed drain mutations can. The paused freshening continuation and independent-component admission policy are absent from this baseline. |

The callback-to-intrusion connection is actual source code:
`constrain_live_item_with_inferred_entry` (`lib.rs:11869–11871`) settles
intrusion when the typed worklist becomes empty, and continues if the intrusion
state is still dirty (11895–11898). This places qualifying merges inside a
restoration child's synchronous drain, before its caller reads the next
opposite index. It does not show that an arbitrary hand-built parent/copy
configuration is generated by a grammar-valid source program.

## Small conditional discriminator

This is a minimized arithmetic trace of the actual consumer/append rules,
**conditional on the callback appending the indicated direct slot**. It is
not a source-reachable failure witness.

Take a positive restoration at owner O with upper direct vector `[]` and
upper exact vector `[A,B]`, where A and B are admissible exact upper endpoints.
The saved count is 2. Index 0 selects A. During that child's drain, suppose
the canonical owner remains O and a qualifying operation appends direct upper
row U. The current vectors are `[U]` and `[A,B]`. Saved index 1 now selects A,
because `1 - direct.len() = 0`. The physical outer enumeration is A,A;
B is outside its original saved count.

Both the uninterrupted loop and saved-index restoration select A,A under
that same mutation schedule. Incoming-use replay can revisit the selected
fiber, although typed memo/diagnostic handling may omit some later work;
the trace claims only physical selections. A frozen endpoint implementation
would select A,B and would violate §4. This explains why append-only storage
does not imply a stable unread prefix. It establishes neither lost terminal
obligations nor observable source divergence in the existing implementation.

An owner redirect has an analogous prefix issue: parent storage is its own
direct/exact vectors followed within each lane by transferred copy slots.
Saving copy count does not make parent indices denote the original copy slots.
That also occurs synchronously and cannot itself falsify resumption.

Context fibers have a separate ordering issue. `attach` prepends its new entry
to the key's linked fiber; transfer iterates the source fiber from its head
and repeatedly attaches to the destination. Distinct transferred contexts can
therefore appear in reversed relative order at an initially empty destination.
Existing destination fibers and relation deduplication affect the final order.
This is a concrete source-operation property, not a statement that suspended
transport differs from uninterrupted transport. Canonical endpoint equality
alone does not prove fiber-order correspondence.

## Result and exact unresolved join

**Bounded characterization:** the audited owners can change physical index
meaning, representative ownership, exact fiber head/order, and evidence while
preserving the saved count. The inspected synchronous driver re-reads live
ownership for each new opposite product and preserves an already generated
batch. These facts defeat a frozen-endpoint or stable-prefix assumption, but
do not supply a current resumed-versus-uninterrupted counterexample.

The pinned consumer paths have no `Suspended` outcome, independent-component
resume admission, lifecycle dependency registry, or cross-component incidence
deferral predicate. Thus there is no implemented pause window here in which
to establish the requested extra mutation's eligibility. A parent/copy SCC
qualifier answers a different question from whether a route may modify the
dependencies of a paused continuation.

For an operational `C → P` redirect proposed during a pause, the source owner
identified here requires an actual recorded extrusion parent/copy pair and a
current shared dependency SCC before merge. Those necessary conditions alone
do not establish the source prefix or route eligibility. If the proposed merge
is a cross-component mutation that alters the paused frame's incidence, §4
requires deferral while correspondence remains open; §5 permits independent
components to continue only with disjoint dependencies. Such an interleaving
is not a contract-permitted counterexample merely because the merge function
can perform its state change. The same redirect inside the original child's
synchronous drain remains existing live-index behavior.

The unresolved join is exact: construct a source-generated accepted mutation
that is eligible to run while the frame is paused, identify its intersection
with the frame's physical owner or retained bound/context dependencies, and
show whether it is a callback mutation that the uninterrupted schedule would
also perform at that seam or a newly interleaved mutation. For a generated
batch, additionally identify which children/observations its incidence change
invalidates and how recomputation precedes the saved continuation. Without
that join, a supplied state transition cannot establish source reachability,
and another numeric trace would leave the same premise untouched.

Negative-result scope: the three assigned mutation/consumer files, plus the
narrow fresh-use, typed-drain, origin/capture transport call paths above.
No exhaustive source-constructor search, q113 construction, diagnostic
discharge proof, certificate recognizer proof, all-source completeness,
soundness/principality, or newly implemented resume code was inspected or
claimed. This pass does not certify that all future admission owners defer
cross-component mutations.

Recommended next action: have the primary pin the implemented resume admission
and dependency-deferral owner, then assign a source trace that crosses exactly
that owner with a saved restoration dependency. Preserve the current gate
until that source/eligibility join is discharged.

## Checks, resources, and commit packet

- Read checks: pinned `git show <baseline>:<path>`, targeted `sed`/`rg`,
  `git grep -n` for restoration/intrusion call sites and representative writes,
  and `git show <baseline>:<path> | sha256sum` for the dependency table.
  Commands completed successfully. The lease path was absent before writing.
- Oracle independence: no executable oracle or synthetic checker was used.
  The independent criterion is the approved §4 behavior. The conditional
  discriminator shares the actual lookup/append rules and consequently does
  not prove that source constructors generate its required callback.
- Seeds/ranges: none; static bounded pass, no random or exhaustive enumeration.
  No builds, tests, benchmarks, or heavyweight processes. Reads/hashing used
  lightweight shell utilities; peak RSS/CPU and total elapsed wall time were
  not instrumented. The 20-minute lease was not expanded.
- Changed path: only the exclusive note above. No compiler, test, shared
  task/index/theory/authority, manifest, lockfile, or question-board edits;
  no Git mutation or delegation. Dependency contents were not changed.
- Artifact frozen after the final text/scope inspection. Review status:
  **unreviewed research; producer has not independently certified it**.
- Exact commit paths: `notes/progress/2026-10-11-resume-incidence-falsifier.md`.
- Baseline SHA: `abdec245c9efc3d8a02c0f5e0865af1d5163a643`.
  Changed dependency hashes: **none**; pinned hashes are recorded above.
- Checks already run: pinned source/call-site inspection and dependency SHA-256;
  final leased-note diff/whitespace inspection. No execution evidence.
- Proposed one-line checkpoint message:
  `research: bound resumed restoration incidence mutation search`.
- Shared-record deltas intentionally left for primary/curator: record the
  stable-prefix/frozen-endpoint assumption as invalid for live opposite lookup;
  retain source mutation eligibility, cross-component deferral, and generated
  batch invalidation/recomputation as open premises. Do not promote the
  conditional discriminator to a source failure or close the resumption gate.
