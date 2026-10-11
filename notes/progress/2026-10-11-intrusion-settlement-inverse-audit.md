# Intrusion settlement: focused forward/inverse correspondence

Date: 2026-10-11
Status: unreviewed bounded source characterization and conditional local derivation; no constructor-qualified counterexample. Original W/A3 remains OPEN.
Producer: leaf `/root/intrusion_inverse_audit`; no delegation or compiler authority.
Baseline: `6c130940e077853672954640325b034b287a1e96`; inspected compiler sources equal `d7e87c63723213550ac28ddab45e2ef47ce17f6e`.
Exclusive lease: this note only. Budget: static focused pass, at most 20 minutes wall; no code, tests, builds, Cargo, Git mutation or shared-record writes.

## Objective, authority and claim boundary

Trace `InferenceSession::settle_candidate_intrusion` into its actual forest,
memo/completion, diagnostic, context and outer rollback owners. Stop at the
first constructor-qualified escape or exact missing atomic inverse premise.
This follows the residual-owner handoff in
[postrepair adversarial audit](2026-10-11-retained-wa3-postrepair-adversarial-audit.md),
“Exact residual owner and stopping point”; it does not repeat that inventory.

Authority is the user-approved [private suspension contract](../design/2026-10-11-private-candidate-suspension-contract.md)
§6, especially exact pre-route restoration and reservation before mutation.
Approval is “承認して実装を進めて”. Preserve the original statement and
quantifiers in [nonterminal composition](2026-10-11-nonterminal-drain-owner-composition-proof.md),
“Frozen objects, statement and exclusions” and H1/W; [handoff](2026-10-11-retained-parent-handoff-proof.md)
A3/A4; and [rollback premise proof](2026-10-11-retained-parent-rollback-premise-proof.md),
“Remaining rollback and original-parent premises”. In particular, L/G/U,
B/emission/raw endpoints/m/n, R/H/q/c, a=(R,i), F/j, ordered finite Q/A,
`0≤d≤p≤|A|`, diagnostic projection D, both P scopes and C retain their original
binders. Terminal acknowledgement consumes before Ready; Ready delivery does
not consume again. No language meaning or supported source envelope changes.

The local derivation below assumes an active route journal, constructor-valid
acyclic forests and IDs, no concurrent mutation of this session, ordinary owned
collection operations, and normal/exact reversal by imported store/context/
effect/replay/workspace primitives. It identifies which of these imported
premises first becomes unresolved. It is neither a theorem of every original
admitted scheduler state nor a successful rollback assumption disguised as a
source reachability result. Exact equality means the named semantic projection;
identical hash buckets, allocator addresses and historical capacity peaks are
not claimed.

## Direct settlement correspondence

Locators are in `crates/yu-solver/src/` at the pinned baseline.

| Mutation / failure boundary | Actual undo and local derivation |
| --- | --- |
| `candidate_intrusion.rs:358–374`: dirty guard; empty parents clears dirty | `State::begin`, 85–101, saves dirty and generation even when no forest event occurs. `rollback`, 114–115, restores those entry scalars. |
| Compression, 305–356 | Reserve the forest log for `values.len+effects.len` before rewrites. Each rewrite records the actual old parent immediately before assignment (335–352), with no intervening fallible operation. In a fixed valid forest, once rewritten to its root a vertex is never rewritten again during this compression, so the reserved bound suffices. Reverse chronological assignments at 105–110 recover the exact prior forest, rather than merely equivalent representatives. New forest entries are truncated only afterward (111–112). |
| Dependency graph/SCC/merge-list construction, 375–493 | These are local allocations after compression. Any `?` here leaves only the already-journaled compression persistent. `Dependencies::intern`, 622–648, reserves all of its local owners before insertion; no persistent SCC cache is installed. SCC correctness is outside this inverse claim. |
| Scratch charge and dirty reset, 494–510 | Checked scratch addition occurs before assignment. After assignment, resource sampling and every merge run inside the result closure; every ordinary Result exit drops the local graph and subtracts this charge. Dirty is covered by the scalar checkpoint. Panics/unwinding inside the closure are not proved safe here. |
| Merge admission, 520–547 | Recanonicalize both endpoints, return if equal, check generation and row kind before mutation. `state.rep(copy)` is a root, so the undo value `from` at 541 is its actual old self edge. The parent row snapshot is admitted before bound/metadata changes. An error reserving that snapshot leaves only a harmless recorded self-edge inverse. |
| Bound append/transport and metadata, 548–592 | Both sides append through the ordinary insertion owner; old physical source storage is retained. `journal_value_row`/`journal_effect_row` cover parent lengths/flags/level/non_generic, restored at `lib.rs:9429–9469`. New rows are removed afterward. Effect capture splicing is the separate atomic seam below. Forest assignment follows these helpers and uses the already-recorded root edge. |
| Canonicalization, generation and replay, 593–604 | Canonicalization transports the pre-call bound-entry prefix (`candidate_context.rs:3125–3143`); failure may occur after the forest assignment but before generation advance. Forest undo still applies. Generation/dirty writes use entry scalars. Root reopening and each replay remain inside this same route transaction; no nested commit is introduced by settlement. Full helper inverse laws remain imported, not proved by their call ordering. |

Outer route entry records `intrusion.begin()` at `lib.rs:9134`; failure calls
`rollback_route_transaction` at 9234–9236. The inverse takes the journal, then
reverses store at 9371 and intrusion at 9374. Intrusion first reverses
effect/context, then forests, scalars, completion records, diagnostic-edge keys
and saved memos (`candidate_intrusion.rs:103–129`). Outer row restoration and
removal of newly admitted typed-pair keys occur afterward (`lib.rs:9429–9494`).
Thus the new-key frontier is not destroyed before an old-memo inverse reads it.
The reviewed Local/census lemma addresses the separate earlier outer return
sites; this note does not reprove it. Ordered Q/D reversal occurs later, under
the existing workspace owner.

## Memo, completion and diagnostic handoff

`mark_candidate_pair` (`candidate_intrusion.rs:223–255`) reserves completion
storage, then saves each relation's entry `Option<u64>` once before its write.
Failure before publication leaves either no mutation or an extra harmless
entry snapshot. The direct source never removes an old completion key on the
forward path; restoring `Some(old)` replaces a present key, and restoring
`None` removes a newly admitted key. This derives map membership equality for
the inspected owner, conditional on ordinary replacement/removal semantics.

`journal_candidate_memo` (257–302) distinguishes new pairs from old memos and
saves an old memo once before mutation, including children, direct witness and
completion. It reserves/copies the children and computes their charge before
installing undo; a sample error after installation has an owned inverse. The
inspected old keys remain present until intrusion restoration. Root reopening
(`lib.rs:11438–11443`) prepares memo undo and diagnostic admission before
marking completion Pending. Typed replacement (12931–12940) and diagnostic
completion (13408–13414) use the same memo owner.

Replay invokes `record_diagnostic_edge` through
`candidate_extrusion.rs:763–803`. At `lib.rs:12969–12983`, duplicate edges return
before mutation; old memo undo, edge-set capacity and undo-vector capacity are
prepared before child append. Fallible child-capacity/accounting/sample checks
finish before `children.push` and edge/undo insertion (13057–13071). There is
no intervening fallible call in that publication segment. The edge set removes
only these newly recorded keys; the saved old memo reinstates ordered children.
New pair memos are removed by the outer new-key journal. D admission and Q
enqueue use the pre-existing workspace events; their complete inverse proof is
outside this atomic settlement pass.

Context transport has actual producer logs, rather than only saved lengths:
`relation` (2232–2249), `attach` (2409–2421), `replay_progress` (2402–2407) and
`edge` (2342–2376) reserve their owning storage and publish matching log entries
before returning. Context rollback restores bound/pair/replay heads in reverse
order (1636–1662) and pops logged edges (1666–1673). An edge may finish before
the next edge or bundle propagation fails; its separate edge log survives
that partial dependency admission. This is useful correspondence evidence,
not an exhaustive evidence/bundle/replay constructor induction.

## Exact stopping premise: capture-map reinsertion storage

The first unresolved atomic normal-return premise is the effect merge's
`candidate_splice_capture_incidence` (`candidate_effect.rs:428–450`), reached
at `candidate_intrusion.rs:578`. With a source bucket, it reserves two undo
entries and an optional link entry, calls `capture_incidence.try_reserve(1)`,
records `(from,Some(source))` and `(to,destination)`, optionally records and
changes the destination tail link, then **removes `from`** and inserts the
merged `to` bucket. A subsequent resource sample can return an error after
these writes. This is an actual mutation/failure seam; no MAX ledger or
corrupted identity is needed to describe it.

Its abstract inverse is exact: reverse all capture links while records still
exist, then restore `to` before `from` (181–205). If `destination=None`, remove
`to` and reinsert `from`; if it was Some, replace `to` and reinsert `from`.
Reverse chronological bucket snapshots also handle repeated splices. New
capture records are truncated only after both link and bucket restoration.

The **unproved operational premise** is narrower than that abstract inverse:

> For every constructor-valid retained route history reaching this splice,
> including any later capture admissions/splices before failure, every reverse
> `capture_incidence.insert(row, old_bucket)` at 201 completes without allocating
> or failing, although the forward splice removed that key, and prior reverse
> operations can leave map tombstones.

Unlike memo/completion replacement, this inverse inserts an absent key. Unlike
retained stack/allocation restoration, it has no separately retained original
map allocation or entry object to move back. The visible `try_reserve(1)` is a
forward check; converting it into this all-history reverse guarantee needs a
specific collection/source-history argument. A bound on live entry count or
entry capacity alone does not establish it. `lib.rs:12797–12804` explicitly
recognizes inverse-removal tombstones for the separate diagnostic index owner;
its clear/rebuild mechanism does not automatically prove this map's inverse.

This is **not a failure witness**: no constructor-valid history causing an
allocation, panic or state mismatch was produced. The two-bucket splice schema
is the smallest useful local case for the missing premise, not a minimized
counterexample to W/A3. Under a separately established allocation-free map
inverse premise, its stored buckets/links give a straightforward semantic
inverse. Stop here rather than broaden into another absence inventory or
assume a transition model proves Rust map behavior.

Recommended next action: assign a bounded collection/source bridge for this
specific removed-key restoration, using the actually linked HashMap insertion
behavior and native capture admission/splice histories. If executable evidence
is needed, the primary should authorize a focused allocation-observation probe
around the real forward/rollback owner; its oracle should observe allocations
and exact entry buckets/links, independently of the assumed inverse rules.
Keep this allocation premise, imported context/store laws and original W/A3
OPEN until separately established and reviewed.

## Independence, coverage and resources

There is no executable oracle, random seed, range enumeration, mutation run or
new test in this packet. Source controls the operational trace; its intended
rollback behavior is not an independent oracle. The argument shares valid Rust
collections, valid IDs and nonconcurrent session ownership with the prior
proofs. The unavailable collection premise is stated explicitly above.

Coverage: direct dirty/compression/graph rebuild/merge writes; completion and
old-memo snapshot owners; root reopen and replay diagnostic-edge publication;
capture-splice forward/reverse order; selected context log constructors; outer
store→intrusion→row/new-key order. Omitted: full context evidence/bundle/replay
and store term constructors, all-source reachability of qualifying capture
merges, scheduler admission of every original state, allocator/stdlib details,
late accounting, panic recovery, §4 external incidence, §7 lifecycle,
withdrawal/recomputation/publication, Call, hygiene, soundness, principality and
cutover. No theorem promotion or independent review is claimed.

Commands: `cat` governing rules/skill/records; bounded `rg -n` symbol/write
searches; targeted `nl -ba`/`sed -n` forward/inverse reads; read-only
`git rev-parse HEAD`, `git status --short`, scoped
`git diff d7e87c637 -- <five compiler dependencies>` and `sha256sum`.
Compiler dependency diff was empty. Some initial multi-file captures truncated;
the governing statements and direct owners used here were reread narrowly.
No test/build/Cargo/formatter/Git mutation. One leaf, short read processes,
zero sustained compute and zero performance samples. CPU/RSS and total process
count are unmeasured; wall time stayed within the assigned ceiling.

| Dependency | SHA-256 |
| --- | --- |
| `candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `candidate_effect.rs` | `e6d485b3b7d468fa01a283d8710affd64f836ddac2613262e6e6b29e4c2b4cd4` |
| `candidate_context.rs` | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987` |
| `candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `lib.rs` | `31c66d1bc9cc101c6174424f5f11b7cbeb6eb497448e0a4b09b683adbacb9dd9` |
| Suspension contract | `734d94cb02c3d2a101ab21435b4377ed06952ab384815da73636bcfbc986033d` |
| Original composition | `4344694f4b8a8c4a225aae83d3c39fcf242f92c2ff32f0ae059d84ad85ff9222` |
| Handoff | `052ac8e6499b116f4ec7adc8e9c935ee04f02c8a27419428a4659514a7c12357` |
| Rollback premise proof | `b675d0eece6437b83bfffcb78f261568e6239fa796a0cd7ef9581960d9322bc3` |
| Postrepair adversarial audit | `3af82c5fece63b74390c795ba8c56d678969e2c4f11e0b9c7feef9ef0d8a8f0e` |

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-11-intrusion-settlement-inverse-audit.md`.
- Baseline SHA: `6c130940e077853672954640325b034b287a1e96`.
- Changed dependency hashes: none authored or observed relative to baseline; five compiler inputs also match `d7e87c637`.
- Claim/review status: unreviewed bounded source characterization and conditional local inverse derivation; no counterexample, closure or production conformance claim.
- Checks already run: narrow source/authority reads and correspondence searches, baseline/compiler equality and hashes; final note whitespace and lease inspection. No executable verification; primary owns verification and fresh review.
- Proposed one-line research-checkpoint commit message: `research: trace intrusion settlement inverses and capture reinsertion premise`.
- Shared-record deltas intentionally left to primary/curator: record direct forest/scalar/memo correspondence as bounded evidence; name capture-map absent-key reinsertion normal return as a specific residual atomic premise; preserve imported context/store/replay inverse and original W/A3 OPEN. No shared records edited.

Artifact frozen after final dependency/lease checks; no further writes planned.
