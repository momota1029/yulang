# Context map rollback: native head owners and first replacement premise

Date: 2026-10-11
Status: unreviewed bounded source characterization and conditional reduction. Native allocation-free rollback and original W/A3 remain OPEN. No native counterexample, production change or authority promotion.
Producer: leaf `/root/context_map_native_headroom`; no delegation.
Exclusive lease: this note only.
Baseline: `0adbcb6fecf1937a75e35c6bf03971c436e2e389`, branch `research/simple-sub-intrusion`.

## Objective, authority and method

Investigate the native reverse insertions in `candidate_context::State`'s `bundle_incidence_heads`, `replay_heads`, `pair_heads`, `bounds`, and the separately owned `BundleTransports::heads`. The original parent W/A3 stays unchanged. Authority is the user-approved [private suspension contract](../design/2026-10-11-private-candidate-suspension-contract.md) §6: transaction failure restores the checkpoint and storage is fallibly reserved before the mutation that relies on it. No source restriction or changed language meaning is selected.

Method: static inventory of each map's declarations, forward writes, reservations, append certificates, constructor callers and rollback block; then per-key reverse-log induction. The [context transport proof](2026-10-11-context-transport-rollback-proof.md) supplies prior local logical inverses, the [capture-map capacity proof](2026-10-11-capture-map-inverse-capacity-proof.md) supplies its reviewed std/hashbrown condition (I), and the [retained-parent rollback premise proof](2026-10-11-retained-parent-rollback-premise-proof.md) keeps global inverse normal return explicit. The capture map's native history or headroom is not imported into any of these five collections.

All source locators below refer to the pinned commit. `candidate_context.rs` was unchanged at its pinned hash during this packet. Ancillary live `candidate_effect.rs` changed during reads; its live snippets were replaced by `git show 0adbcb6fe:<path>` reads for final source correspondence. No mixed live source snapshot is certified.

Freeze the local quantifier as follows: for each of the five particular maps, every finite constructor-valid suffix of its actual emitted append records after a valid checkpoint, and every reverse `Some` encountered when its owner is reached. Owned collections and IDs are valid; no direct synthetic field mutation, concurrent map writer, forged checkpoint, user Hash/Eq/Drop callback, or continuing execution after UB/panic is admitted. Other inverse owners returning normally is a prerequisite for reaching this owner's block, rather than a result of this note. Built-in keys and copied head values do not call user code. Full source/retained-driver reachability of a chosen map suffix remains separate.

## Imported library premise

Use the capture proof's exact selected Rust 1.95.0 / hashbrown 0.16.1 source correspondence, without claiming linkage of a previously built solver executable. Let `n` be live entries, `g` the actual table's growth credit, and `c` its raw bucket capacity. Its std `HashMap::insert` reserves **before** looking up an existing key. The exclusion of a new backing allocation is:

```text
g >= 1  OR  n + 1 <= floor(c / 2).                    (I)
```

On the second arm it rehashes in place and supplies positive credit. Removing an entry decreases `n`; it increases `g` only when erase writes EMPTY, and leaves `g` unchanged when erase writes DELETED. Replacing an existing key, after a successful no-allocation reserve, changes neither `n` nor `g`. Exposed `capacity()` and key presence alone do not establish (I). This note imports the independently reviewed library derivation; it does not independently review that dependency or rerun its source/archive comparison.

## Distinct source owners

All five maps default to empty (`State` derives Default at `636–637`; `BundleTransports` at `278–282`). The inventories find no forward per-key removal, clear or shrink of these head maps. Their removals occur only in their own reverse loops. The transport index additionally has whole-owner installation/drop, described separately below. Every head publication records exactly the value returned by that publication's `insert`, and each rollback traverses the corresponding log in reverse.

### 1. `bundle_incidence_heads: HashMap<RelationId, usize>`

Declaration `658`; publication `bundle_incidence_insert`, `2128–2136`; inverse `1625–1629`; checkpoint saves incidence-log length at `1561`.

The admission guard is exact `(relation,bundle)` membership in `bundle_incidence`. A repeated exact incidence is read-only. A distinct bundle on an already incident relation is a head replacement, even though the exact incidence is new. Reserve the incidence set, incidence log and head map before any logical write; then replace/insert the relation head, insert exact set membership, and push `{ relation, bundle, previous_on_relation }`. There is no fallible production operation between these writes. Failures in earlier reserves have no new logical head record, although storage/layout may already have changed.

Constructors: `bundle_link` (`2138–2162`) activates the transport index, admits the seed, and uses the append log as its queue through diagnostic edges and qualifying transport successors. `bundle_edge` (`2164–2172`) links each retained parent bundle to a child; dependency Derived/FunctionPort/Replay edges enter it through `edge` (`2342–2376`). Direct entry routes are source seed anchors at local slots 40/41 and 45/46 (`2515–2523`) and fresh-use bundle reconstruction (`3157–3161`, scheme `1257–1259`). The declared `candidate_context_transport_bundle` (`3164–3171`) is an unused/dead-code-allowed route, not evidence of a native call.

Rollback removes each exact incidence, then restores its saved relation head with `insert` for Some or removes that relation head for None. A Some head's key is present at its inverse: newer incidences for that same relation have already been reversed to this record's head, and no other owner removes it. Both replacement and new-key admissions are permitted by these guards; their source/hash placement and interleaving in a failing retained route are not established here.

### 2. `BundleTransports::heads: HashMap<RelationId, usize>`

Separate owner `279–300`; publication `285–288`; reverse `291–295`; index checkpoint `1562`; owner rollback/drop `1630–1631`.

`insert(parent,child)` reserves heads and log, then records `(parent,child,previous)` after publishing the parent head. Distinct qualifying dependencies can replace one parent's head; this helper has no independent pair deduplication. The outer `dependency` guard deduplicates the complete Dependency (`2284–2287`). For Transport with an Extrusion, ParentCopy or EqualityCanonicalization witness, an existing index is updated before `bundle_edge` and before dependency publication (`2321–2339`); failure in `bundle_edge` leaves the head log available even if the dependency itself was never appended. FreshUse and witness None do not enter this index.

Activation (`2118–2126`) builds a **local** default index by scanning existing qualifying dependencies, then installs it only after every insertion succeeds. Activation failure drops the local candidate. If the checkpoint stored None, rollback drops the whole installed index and performs **no reverse insertion in this map**, including any updates after its installation. If the checkpoint stored Some(length), the retained index reverses only its suffix and its saved Some parent keys remain present by that index's own LIFO records. This distinction prevents incorrectly demanding (I) for a newly activated owner that will simply be dropped.

Native qualifying witness routes include effect bound-origin transfer (`candidate_effect.rs:462–472`) and equality canonicalization (`3134`); their concrete provenance/evidence is retained at `candidate_context_transport_witness_with_evidence`, `3182–3196`. No inference from capture-map splicing is used.

### 3. `replay_heads: HashMap<(BoundKey, BoundKey), (Option<usize>, Option<usize>)>`

Declaration `674`; `replay_progress` at `2402–2408`; log frontier `1570`; inverse `1636–1639`.

This map records generation heads for an ordered lower/upper bound-input pair, not replay-operation ownership or a child completion cursor. `replay_progress` reserves map and log, then publishes the head tuple and logs its previous **map membership**. A present value `(None,None)` is distinct from absent membership in its inverse log.

The only production caller is `candidate_context_begin_replay` (`2911–2993`). It reads current bound cursors and recorded heads (`2928–2929`), generates the two delta quadrants using the saved inputs, and invokes `replay_progress` only if `heads != recorded` (`2974–2975`). Incoming use resets the generation loop's prior heads to `(None,None)` but still compares publication to the original recorded value. Consequently incoming replay alone does not force a repeated head write; changed retained bound heads do. An absent pair publishes only when its head tuple differs from `(None,None)`; an existing pair replaces only when its cursors changed.

Native outer callers are retained bound restoration (`candidate_extrusion.rs:758`, incoming use true) and ordinary opposite-bound replay (`802`, false). After progress publication there is checked child-byte accounting, operation publication, and a fallible resource sample (`2978–2989`); generation failures before progress may already affect other owners but add no replay-head record. Reverse Some retains the ordered input key because there is no forward removal and later writes for that key reverse first. Neither the changed-head guard nor incoming-use selection establishes raw table credit.

### 4. `pair_heads: HashMap<TypedPairKey, RelationId>`

Declaration `668`; constructor `relation`, `2232–2253`; relation frontier `1565`; inverse `1647–1654`.

The guard deduplicates the complete `RelationKey { pair, context }`, **not** the pair alone. A second context on the same typed pair is a head replacement. New admission checks context validity and u32 relation length, reserves relation Vec, exact key map and pair-head map, then saves the previous pair head, pushes the Relation and inserts its exact key. This sequence has no intervening fallible production operation. The saved `previous_on_pair` is independent of endpoint canonicalization and relation identity.

Constructor routes are source seed (`2514`), ordinary admission and fallback parent (`2546,2550`), Function ports with inherited/local context (`2597`), canonical task transport (`2725`), ordinary bound origin/child (`2847,2852`), replay child (`2962`), canonical bound transport (`3137`), fresh scheme transport (`3151`), and witness transport (`3190,3212`). Source caller locators include `lib.rs:11980,12148` (seed), `12661` (Function admission), and `12048,12261` (task transport). These branches retain potentially different contexts; this note does not assert every abstract pair/context combination is parsed-source reachable.

Rollback first removes the exact RelationKey, then restores/removes the pair head. Relations for a fixed pair form the recorded previous-head chain; reverse order restores the next older relation while the pair remains present for Some. Removing exact keys in the **different** `keys` map supplies no credit to `pair_heads`. Full inverse storage cannot be deduced from relation Vec capacity or endpoint equality.

### 5. `bounds: HashMap<BoundKey, usize>`

Declaration `672`; `attach`, `2410–2422`; bound-log frontier `1568`; inverse `1659–1662`.

Admission tests whether the exact relation is already in the linked fiber for this BoundKey (`2415`). A duplicate relation is read-only; a distinct relation on an existing BoundKey is a head replacement. Reserve heads and bound-log Vec, publish the new log index and append `(key,relation,previous)` without an intervening fallible operation. The BoundKey's owner, polarity and item remain distinct.

Production attachment routes are ordinary `candidate_context_bound` (`2854`), fresh transport (`3153`), evidence-bearing witness transport (`3193`), and the generic witness path (`3219`). `candidate_bound_origin_with_evidence` (`candidate_effect.rs:341–399`) calls the ordinary context constructor before later origin reservations/evidence admission/resource sampling, so later failure can leave a completed attachment for reversal. Scheme fresh reconstruction (`candidate_scheme.rs:1254`) and transferred/equality bounds use the transport routes above. A Some reverse key remains present under its own linked-fiber LIFO chain. Canonicalization adds/attaches a canonical key without deleting the old BoundKey (`3125–3142`); no destructive map transfer is hidden there.

## Reduced derivation and exact obstruction

The owner inventories establish the following **logical** invariant separately for each map: immediately before reversing a record with Some(previous), that record's key is present, and the value being replaced is the newest unreversed head for that key. Proof is per-key induction: forward publication extends the chain with the exact old head; later records for that key reverse first; None is only the original absent-key admission, and is reversed after that key's Some records. Other keys cannot remove this key. Partial publication suffixes are covered because each head mutation has its completed log before the next fallible production action. The lazy transport owner-drop case is outside this inverse loop.

This invariant does **not** prove allocation-free `insert`. It does enable a smaller conditional storage result. For each particular map rollback block, let S be its **first** reversed Some record. If there is no S, this block makes no insertion. Otherwise require (I) for that map immediately before S. Then:

1. S has a present key. If `g>=1`, its replacement reserves without changing layout and retains that credit. If the other arm of (I) holds, in-place rehash establishes `g=c-n>=1`, and replacement consumes none.
2. Every following None inverse removes one key; `n` decreases and `g` does not decrease. Every following Some replaces an existing key and consumes no credit.
3. Therefore all later inserts in this block have `g>=1` and exclude backing allocation. This conclusion is conditional on the imported library bridge and ordinary valid built-in collection operations; it does not prove preceding unrelated rollback blocks return normally.

Thus the unproved native premise can be checked at **one first Some per map per rollback invocation**, rather than restating it at every insert. The maps have separate tables and separate S points. Checking one map cannot discharge another.

Forward `try_reserve(1)` establishes local `g>=1` before its head publication. Existing-key publication retains that credit. New-key publication can consume the final EMPTY credit and leave `g=0`. Later reverse None removes are not guaranteed to replenish it. A shortest logical suffix exposing the unresolved distinction has two publications: replace an existing head k, then admit an absent head u consuming the last credit; reverse u's None, then reach k's Some. If reverse removal writes DELETED, `g` stays zero. This is an **obstruction pattern**, not a native counterexample: it additionally needs source-valid keys/contexts/bundles/changed cursors or bound fibers for the particular owner, actual native hashing/placement with `n+1>floor(c/2)` at S, a retained checkpoint whose suffix includes both records, and a later real failing route that reaches this block. No such joint source/history witness was constructed. No arbitrary layout from the capture note is substituted for those missing facts.

Useful certified subsets are immediate: a suffix with no Some needs no map insertion; a reached S with positive actual credit is safe; and a reached S with zero credit but sufficiently small actual live count is safe by the in-place arm. If the final head publication in a map was a replacement and no later operation changed that map, it retains positive credit into rollback. These subsets do not restrict or close the original all-native statement.

## Result and next owner

Result: existing-key presence is established by source logs for all five Some inverses, with the distinct lazy transport drop case excluded. Condition (I) is **not established for every native history**. The exact remaining current-code premise is (I) at each map's first reversed Some, or a constructor-qualified route/history witness violating it. Source API permission for the two-publication pattern is weaker than native reachability. Full W/A3, accounting equality/publication, linked binary applicability, other context/evidence maps and all effect/intrusion inverse owners remain OPEN or outside this packet.

This is class A rollback storage/correctness. The owner already retains the previous head and has a source-derived present-key invariant. Repeating a live-length proof or a generic one-credit argument would leave the same control-table premise untouched. Recommended next action: primary assigns the context rollback owner a narrowly authorized construction check/repair using in-place present-key value restoration for these five Some branches, with fresh independent review of the per-owner presence invariant. That is a proposed handoff, not production authorization; this leaf makes no compiler edit. The capture map's genuinely absent-key restoration needs its separate owner and is not solved by this proposal.

## Frozen dependencies and checks

| Dependency | SHA-256 |
| --- | --- |
| Pinned `candidate_context.rs` (also unchanged live input) | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987` |
| Pinned `lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| Pinned `candidate_effect.rs` | `e6d485b3b7d468fa01a283d8710affd64f836ddac2613262e6e6b29e4c2b4cd4` |
| Pinned `candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| Pinned `candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| Pinned `candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| Context transport proof | `c0e5659fa28553c3d64aa4622c9c32e716d056488c5ef95314723ba5b17933e0` |
| Imported capture-map/std proof | `b765a6cbbf3061b8ef5c7bc3bfe67122cd5c599b243bfaa00b9e4ce8e7db3569` |
| Retained-parent rollback premise proof | `563e1b5c92288c2521481b8389de438c8104e412cf4ed11ce09c8da82051f061` |
| Suspension contract | `734d94cb02c3d2a101ab21435b4377ed06952ab384815da73636bcfbc986033d` |

Checks: read requested authority/research/concurrency rules, compiler economy/orchestration rules and yulang-proofs skill; bounded `rg -n` inventories and `sed` owner/caller reads; read-only `git rev-parse`, branch/status, and `git show` pinned dependency reads/hashes; final note whitespace, source/dependency hashes and lease inspection. Initial broad task/policy captures were truncated; decisive rule/contract/source regions were reread narrowly. Source inventory covers the five private map writers and the named direct native constructor routes, not every parsed source program or scheduler path. There is no independent executable oracle: evidence is actual source plus the separately reviewed library dependency, not two implementations sharing supplied transitions.

No tests, experiments, seeds/ranges, mutations, compiler/Cargo builds, formatting, allocator observations, Git mutation, child launch, production/test edit or shared-record edit. Only short read/hash processes; zero sustained compute workloads or performance samples. CPU/RSS and exact aggregate wall time were not measured; no numerical process/RAM/wall-time budget was supplied in this packet. Effective runtime model/effort metadata is unknown; no routing or override claim. Main constructive W/A3 work and independent review remain with the primary's assigned lanes.

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-11-context-map-native-headroom-research.md` only.
- Baseline: `0adbcb6fecf1937a75e35c6bf03971c436e2e389`.
- Dependency changes: none authored. Live effect instrumentation changed during the packet; final ancillary evidence uses pinned blobs and the hashes above. Primary must compare any future production delta before applying this source characterization.
- Review status: frozen unreviewed research checkpoint; no independent review of this note, no native counterexample and no parent closure.
- Checks already run: bounded owner/write/caller inventories, pinned source hashes/reads, per-key logical and first-Some conditional derivation, final note/lease/whitespace inspection. No executable verification.
- Proposed checkpoint message: `research: reduce context rollback headroom to first replacement per owner`.
- Shared-record deltas left to primary/curator: retain W/A3 OPEN; record each collection's distinct first-Some premise, the retained transport-index versus whole-drop distinction, and source-derived present-key restoration handoff. No task/index/theory/authority or question-board path changed.

Artifact frozen after final checks; no further writes planned.
