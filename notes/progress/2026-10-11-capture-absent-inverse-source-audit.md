# Capture splice inverse: source owner and rollback classification

Date: 2026-10-11
Status: unreviewed, non-authoritative static source characterization.
Producer: leaf `retained_local_capture_probe`; no delegation.
Assigned baseline: pushed `1607eef94d661d8b30fbfb628a1bf767e080ee61`, supplied
by the primary; this packet forbids Git commands, so the ref was not
independently resolved.
Lease: this note only.
Authority: private suspension contract §6 and the accepted correction to use
Oracle-valid syntactic function bindings for any source witness.

## Objective and steering

The original packet asked which operations can reach absent-key `Some` capture
inversion after the occupied-key repair, and whether their one-credit forward
reserve supplies condition (I). During the read-only audit, the primary passed
the user's architectural concern that rollback might be an inappropriate part
of inference. The packet then stopped at enough source mapping to distinguish
inference backtracking from failure-atomicity transactions. No implementation,
storage repair, probe, test or semantic adoption was attempted.

**Result:** capture splice rollback is a transaction failure inverse in the
inspected production call graph. It is not used to try another inference
choice. This classification does not establish that this transaction mechanism
is necessary or that its current resource contract is desirable. Those remain
primary-owned architectural questions. W/A3 and broad effect hygiene stay OPEN.

## Source chain and error boundary

The production inverse chain is:

```text
finish_route_transaction_with_candidate_accounting: Err(SolveAvailabilityError)
  -> rollback_route_transaction
     -> candidate_intrusion::State::rollback
        -> candidate_effect::State::rollback
           -> reverse capture bucket snapshots
```

`lib.rs:9245` is the production invocation of `rollback_route_transaction` in
the inspected inventory. Direct calls later in that file are within the
cfg(test) module beginning at line 18,399. The intrusion inverse calls the
effect inverse at `candidate_intrusion.rs:104`; the outer route inverse calls
intrusion at `lib.rs:9391`. No alternative production caller of these two
capture inverse owners was found.

The successful branch (`lib.rs:9215–9242`) releases undo, commits the store
route, and publishes a completed Local use. It does not reverse capture
splices. The error branch restores the route and returns the error. The
availability error variants (`lib.rs:3947`) are ArtifactMismatch,
CauseMismatch, ReceiptMismatch and IdentityExhausted. IdentityExhausted also
represents resource/construction unavailability in the inspected private
owners; this audit does not classify every producer of that variant.

Ordinary effect mismatch is different: `candidate_effect_mismatch`
(`candidate_effect.rs:604–657`) records an exact conflict and returns its
resource-sampling result. A mismatch alone is not an Err-triggered instruction
to undo the graph and choose another type. A resource error while recording it
can still fail the transaction.

The transaction entrypoints include:

- Local Name routing: `candidate_scheme.rs:1361` opens the route around
  capture, fresh-use construction, LocalUse bound restoration/replay and the
  final link. Its test-only pause returns Ok(Paused), which commits the route;
  the pause does not call capture rollback.
- Open internal and incoming definition uses: `lib.rs:15762` and `:16476`
  wrap their route owners in `with_route_transaction`.

The private suspension contract §6 likewise distinguishes failure restoration
from successful suspension, which retains accepted edges and unfinished
obligations. The code/source classification is consistent with that current
contract; it is not authority to preserve or remove the contract after the
user's new concern. Full solver error handling and every diagnostic owner are
outside this bounded audit.

## Exactly which map operation leaves an absent saved key

The writer search finds two production forward mutators and the inverse:
admission at `candidate_effect.rs:507`, splice removal/insertion at
`:549–550`, and rollback at `:272–275`. The other direct insertion found at
`:1591` belongs to a synthetic test. No forward clear, shrink, whole-map
replacement, or third production remover was found in `crates/yu-solver/src`.

After the occupied-key repair, a saved Some uses `get_mut` if its key exists;
only an absent saved key reaches HashMap::insert. Under successful logical
LIFO restoration of all later operations:

| Logged snapshot | Key at its inverse | Reason |
| --- | --- | --- |
| Admission `(tail, Some(old))` | Present | Admission leaves tail present; later operations restore their own entry states first. |
| Splice `(to, Some(old))` | Present | Forward splice publishes to; later operations are undone before this destination snapshot. |
| Splice `(from, Some(source))` | **Absent** | Forward splice removes from; destination reversal changes only distinct to. |
| Any None snapshot | Removal inverse | It does not call the Some insertion path. |

Thus the remaining absent-key Some insertion is the removed **source** of a
capture splice. This is a conditional logical characterization, assuming
normal return of prior inverse operations. It is not a proof that those
operations return normally under allocation failure. Later admissions that
recreate from are reversed before the earlier splice source snapshot, and do
not eliminate this absent-key owner.

## Real forward splice and source bridge

The sole production splice caller is effect-row `merge_candidate_rows`
(`candidate_intrusion.rs:578`). The merge canonicalizes copy and parent,
transports the copy's bounds to the parent without capture registration,
splices capture incidence, then redirects the representative forest and
replays bounds. The splice saves from first and to second, removes from,
publishes to, and samples resources. That sample can fail after mutation.
An active route journal then restores to before from, using saved raw keys;
forest restoration occurs after the effect-algebra inverse.

`settle_candidate_intrusion` selects a retained copy/parent pair only when its
current representatives are distinct and in the same dependency SCC
(`candidate_intrusion.rs:473–485`). Settlement is reached when the typed
worklist is empty in the synchronous drain (`lib.rs:11996`) or retained typed
drain (`:12229`). This is deterministic parent-copy equality settlement, not
speculative unification followed by inference backtracking.

The parent pair originates in `candidate_extrude` (`candidate_extrusion.rs:121`).
A level-crossing Function-to-row comparison calls that extrusion through
`lib.rs:12418` or `:12431`; Function ports recurse into Effect rows and views.
Physical negative EffectRow/Allowance bounds with a symbolic tail register
capture incidence through `candidate_register_capture_bound`. Formal function
annotations and local fresh-use bound restoration are source constructors for
those bounds. Capture incidence itself is metadata, not the SCC equality edge.

Positive incoming-incidence extrusion starts from an occupied original tail
and can populate its copied tail (`candidate_extrusion.rs:164–180,291–307`).
General view/physical-bound copying has no corresponding original-bucket
occupancy guard. Neither parent retention nor SCC selection checks splice
destination occupancy. These caller facts do not establish a complete
Oracle-qualified source execution that reaches an allocating absent inverse.

## Headroom observation retained from the partial audit

Import the reviewed condition-(I) derivation for Rust 1.95.0 / hashbrown
0.16.1: with live count n, internal growth credit g and raw table capacity c,
the HashMap insert path reserves before key lookup. Its backing-allocation
branch is excluded when `g >= 1 OR n + 1 <= floor(c / 2)`. A removal may leave
DELETED and return no credit. No raw table layout is inferred from public
capacity in this note.

The splice's successful `try_reserve(1)` establishes g >= 1 at that forward
point. If to was absent, removing from and inserting to can spend the credit;
inverse removal of to may return none. If to was occupied and there are no
later capture mutations, the splice leaves at least one credit and the repaired
destination inverse uses get_mut. That isolated case supplies credit for the
source inverse.

Intervening mutations prevent importing that isolated conclusion as a history
invariant: a later new-tail admission can spend the remaining credit, and its
inverse removal can leave a tombstone. Then destination get_mut supplies no
credit before the absent from inverse. Conditional example:
`g=1,n=N` before occupied-destination splice; removal gives `g=1,n=N-1`;
later new-tail insertion consumes EMPTY, giving `g=0,n=N`; its inverse
removal gives `g=0,n=N-1`; destination replacement leaves that state. The
source insertion needs condition (I), which fails if `N > floor(c/2)`.
This arithmetic imports library transitions; actual native key/hash placement,
SCC qualification and source action order are not established by it.

The missing bridge is an Oracle-valid syntactic function binding whose actual
route reaches an occupied copied-tail splice selected by native parent/copy
SCC settlement, followed by a failure at a history with no reverse credit and
high occupancy. No new source witness, seed range, mutation or execution was
produced. A possible future evidence target is to observe the native splice,
its destination snapshot, subsequent admissions and absent-source inverse in
one actual Local transaction. **That target is deferred pending the primary's
architectural adjudication; this note recommends no probe or storage repair
while the direction is paused.**

## Checks, dependencies and limits

Checks: bounded rg writer/caller searches, targeted sed/cat reads of the five
assigned code inputs and governing/previous notes, and SHA-256 dependency
checks. No Git command, Cargo/build/test, executable probe, Oracle run,
measurement, seed enumeration, mutation testing, code edit or delegation.
Resource use was sequential lightweight reads; CPU/RSS/wall time unmeasured.
Prior rules and skill reads from the continuing leaf remain applicable.

| Dependency | SHA-256 |
| --- | --- |
| `candidate_effect.rs` | `ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df` |
| `candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| condition-(I) note | `b765a6cbbf3061b8ef5c7bc3bfe67122cd5c599b243bfaa00b9e4ce8e7db3569` |
| private suspension contract | `734d94cb02c3d2a101ab21435b4377ed06952ab384815da73636bcfbc986033d` |
| occupied rollback repair note | `54269cc2fc3b3e438146cc893be9afe7de948b3db8f3f946a834c6e1cd6e1970` |

Oracle independence: no new Oracle evidence was obtained. The accepted earlier
function-binding observation validates that earlier source only. No arbitrary
expansive annotated value or synthetic cycle fixture is promoted to an
Oracle-qualified source witness here. The static characterization shares the
implementation and reviewed library assumptions; it is not independent review
or a checker proving source rules. Complete rollback, retained accounting,
paused Local entry, all-source inference behavior and effect hygiene remain
unverified and OPEN.

Recommended next action: primary adjudicate the architectural role of
transaction failure recovery separately from inference backtracking, using
this owner/error boundary, before reopening absent-inverse storage work.

## Commit packet

- Exact lease: `notes/progress/2026-10-11-capture-absent-inverse-source-audit.md`.
- Assigned baseline: `1607eef94d661d8b30fbfb628a1bf767e080ee61`
  (primary-supplied full SHA; ref not independently resolved).
- Dependency hashes changed during this packet: none observed or authored.
- Review: unreviewed frozen static characterization; no theorem closure.
- Checks already run: source writer/caller/error-boundary inventory, targeted
  reads, dependency hashes and note integrity inspection; no executable checks.
- Proposed message: `research: classify capture splice rollback as transaction failure recovery`.
- Shared deltas left to primary/curator: capture splice inversion is
  transaction-only in this source cone; absent-source headroom and W/A3 remain
  OPEN; storage/probe direction is paused for the user's architectural concern.
  No shared task/index/authority file was edited.
