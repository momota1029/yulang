# Native capture-map rollback headroom: source audit

Date: 2026-10-11
Status: unreviewed research; bounded source characterization and conditional falsification target. No native counterexample, all-history proof, implementation authority or W/A3 closure.
Producer: leaf `/root/capture_map_native_headroom`; no delegation.
Exclusive lease: this note only.
Baseline: `befbe308fb123915385b3ec54a2e1fc3668a279e`, branch `research/simple-sub-intrusion`.

## Objective and exact premise

Investigate the source-history premise left by [capture-map inverse capacity](2026-10-11-capture-map-inverse-capacity-proof.md), §3 and “Exact result, remaining owner and economy”, and [intrusion inverse audit](2026-10-11-intrusion-settlement-inverse-audit.md), “Exact stopping premise: capture-map reinsertion storage”. Authority is the user-approved [private suspension contract](../design/2026-10-11-private-candidate-suspension-contract.md) §6: exact pre-route restoration, reservation before mutation, retained/rollback accounting, and no new source rejection. This packet preserves the original W/A3 parent and its binders; it investigates only capture-map storage during its inverse.

Imported reviewed library result: for the pinned Rust 1.95.0 / hashbrown 0.16.1 insertion path, let `n` be live items, `g` growth credit and `c` raw table maximum capacity. `HashMap::insert` reserves before lookup, including replacement. Excluding its backing-allocation branch requires

```text
(I)  g >= 1  OR  n + 1 <= floor(c / 2).
```

The original question quantifies over every constructor-valid native capture admission/splice suffix and every reversed `Some(bucket)` snapshot, including later mutations before failure. It requires (I) at the actual inverse insertion, not merely at forward reservation. Ordinary valid u32 keys, default `RandomState`, valid records/indices and one session owner are shared assumptions. This note imports the library derivation; it does not independently reprove or certify that derivation, executable linkage, or other map inverses.

Method: bounded static trace from all capture-map writers to real annotation, operation, extrusion, fresh-use, merge and route-rollback owners; inspect existing fixtures for constructor provenance. No executable search was run.

## Complete capture-map write inventory at this baseline

Production references across `crates/yu-solver/src` locate three writers. There is no forward clear/shrink/whole-map replacement, direct writer in `candidate_context`, or separate capture-key deletion route in this inventory.

| Owner | Native trigger and log | Relevant storage consequence |
| --- | --- | --- |
| `candidate_effect.rs:398`, `candidate_capture_incidence` | A new `(source,view)` pair; save `(canonical_tail, old_bucket)`, optional old link, and new pair before publishing a record and bucket. Duplicate pairs return unchanged. | Reserve one map credit; new tail can consume it. Existing tail logs `Some` even though its eventual inverse is a replacement. Fallible sample at :426 follows publication. |
| `candidate_effect.rs:428`, `candidate_splice_capture_incidence` | Different row IDs and occupied source; save `(from,Some(source))` then `(to,destination)`, optional destination link; remove source and insert merged destination. Equal/absent source is unchanged. | Reserve one map credit. Nothing in this function requires destination occupancy. Fallible sample at :450 follows publication. |
| `candidate_effect.rs:181`, `State::rollback` | Restore context first; reverse links while records exist; reverse bucket snapshots at :200, `Some -> insert`, `None -> remove`; then delete new pair keys and truncate records/views. | No reserve, retained old map allocation, or control-byte restoration accompanies inverse insertion. Logical bucket inversion does not restore growth credit. |

The context rollback at `candidate_context.rs:1581` restores its own relations, replay/restoration progress, bundles, bound/pair heads, evidence and edges. It cannot replenish this independent capture map. Its other reverse HashMap insertions belong to separate owner gates, outside this packet.

At baseline `lib.rs:9191`, route operation errors invoke `rollback_route_transaction` (:9339); that calls intrusion rollback (:9374), which calls effect-algebra rollback before restoring forests (`candidate_intrusion.rs:103`). Consequently map restoration occurs while old capture records exist, before row representative restoration. Inverses use saved raw bucket keys rather than re-canonicalizing them. Logical snapshot correspondence is imported from the reviewed audit; normal return of the context inverse and the other outer helpers remains a separate assumption.

## Real construction routes and what they establish

`candidate_register_capture_bound` (`candidate_effect.rs:452`) is the only production caller of admission. Its trigger is exactly an effect-row owner with a negative `Allowance(view)` bound whose view has a tail. It canonicalizes the view tail, retains the physical bound owner as `source`, and deduplicates `(source,view)`. Support, concrete membership, positive bounds and closed views do not admit capture buckets.

`candidate_insert_bound_with_evidence` (`candidate_extrusion.rs:406`) canonicalizes owner/bound, admits evidence and installs the physical bound, then calls the capture registration when its `capture` flag is true (:560). Ordinary insertion (:389) uses true. Merge transport (:400) explicitly uses false. Fresh-bound restoration (:659–680) uses true. Capture admission is therefore a native byproduct of accepted bounds; it is not an arbitrary map-key API.

The bound sources are:

- Annotation/signature construction: `candidate_signature_effect` (:1346–1476) obtains each named tail through scoped `candidate_formal_effect_variable` (:878–896) or operation-local variables, constructs a view, allocates its effect port, and inserts Support/Allowance according to polarity. `candidate_signature_view` (:632–684) alone creates no capture bucket. Formal paired ports (:933–970), local annotation (:1025–1076), and operation signatures (:685–704) reach this same signature owner. Repeated variable spelling in the same annotation scope shares the tail; distinct scopes or names allocate separately. View/source identity remains distinct, so shared tails can receive nonduplicate admissions and `Some` snapshots.
- Positive extrusion: `candidate_extrusion.rs:113–124` creates and retains the copy/parent pair. Its incidence traversal (:164–180) starts from an occupied original tail. `Work::IncomingAllowance` (:291–307) remaps the view to the copied tail and inserts a negative Allowance on the mapped source. This specific copied-incidence route has an occupied original at discovery; it does not establish destination occupancy for every later merge.
- General extrusion of a view/physical bound: `Work::EffectView` (:259–288) copies a view after mapping its tail; `Work::Bound` (:308 onward) installs the mapped bound. A copied view does not carry a map bucket until a negative Allowance is installed. No test for original-tail map occupancy guards these general view/bound branches.
- Capture and fresh use: baseline `candidate_scheme.rs:616–626` reads tail incidence as exact negative Allowance bounds. Freshening (:1005–1027) allocates generic local rows and retains shared rows according to the existing level/non-generic rule; view remapping (:1047–1065, :1089–1105) maps their tails. `begin_candidate_fresh_bound` (:1221–1266) reaches ordinary restoration with capture enabled. Freshening does not synthesize a retained-growth-credit certificate, and its canonical-row deduplication is not table-layout evidence.
- Intrusion: the only production splice caller is `merge_candidate_rows` (`candidate_intrusion.rs:509–610`). A retained parent/copy pair qualifies by equal dependency SCC (:475–483). The merge appends/transports copy bounds without capture (:569–574), then splices (:578) before redirecting its forest. Neither parent retention (:171–221), SCC qualification nor this transfer tests destination capture-map membership. Reverse bucket keys remain exactly those logged before forest redirection.

These are source correspondences, not a proof that every syntactically imaginable order occurs in the retained-Local scheduler. In particular, “every splice destination is occupied” is still an unproved candidate assumption. The occupied-original discovery in the positive-extrusion special route is insufficient to establish it for general bound/view copying, subsequent representative changes and later admissions.

## Smaller conditional falsification target: admission-only suffix

An absent-destination splice is not required to expose the unresolved storage premise. Consider this two-entry suffix of an otherwise constructor-valid route journal:

```text
1. Admit a new (source,view) pair on occupied tail A: log (A,Some(old_A)).
2. Admit a pair on new tail B: log (B,None); sample/failure before another reserve.
rollback: remove B, then insert(A,old_A).
```

Conditional hypotheses: immediately before step 2, `n=c-1,g=1`; its insertion consumes EMPTY; inverse removal of B yields DELETED; `c-1+1>floor(c/2)`. Step 1's reserve establishes forward credit but replacement does not consume it. Step 2 gives `n=c,g=0`; reversing B gives `n=c-1,g=0`; the next inverse replacement violates (I) and reaches the library resize branch before key lookup. This is a conditional derivation, not a minimized native witness. It specifies no invented Hash/Eq or predetermined u32 placement.

The source ingredients for repeated-tail admissions are concrete. The parsed-source fixture `distinct_covariant_formal_positions_share_only_the_scoped_tail_and_freshen_independently` (`candidate_effect.rs:1807–1865`) uses

```text
act io
act other
my bridge (consume:(int -> [io, 'e] ()) -> (int -> [other, 'e] ()) -> ()) = consume
```

It selects the real HIR FormalAnnotation action, invokes the real annotation constructor transaction, and asserts four distinct incidence records on one scoped tail. Another parsed fixture (:1747–1804) checks two records per paired view plus rollback at selected publication failures. These are checked-in fixture assertions, not results newly executed by this packet. Mixed-row construction creates a direct Allowance; subsequent typed matching can add the exposed-port incidence. This note does not infer that both records are consecutive direct signature-constructor calls.

Extending such source construction with distinct scoped tail names is a candidate way to generate new buckets after a repeated-tail admission. The large source shape, exact action/restoration order, actual native row IDs, and failure placement have not been executed or exhaustively derived. The first useful table regime is larger than the SSE2 group width: the selected library explicitly explains why tables smaller than width 16 cannot retain DELETED on erase (`raw/mod.rs:3290–3306`). Thus a tiny few-bucket fixture is a poor falsifier. The prior 32-bucket raw arrangement is not assumed reachable here.

The 64-tail merge-chain regression (:2172–2208) manually calls test-only view construction and direct splice, merges into occupied destinations, and checks logical restoration. It neither uses the native SCC merge entrypoint nor observes allocation/headroom. Its size and success cannot close this source-qualified premise.

## Result, precise residual and next evidence

Established by static inventory: no source constructor in the traced dependency cone reserves reverse insertion credit beyond the ordinary one-credit forward guards, records HashMap control state, or bounds native capture-map occupancy to a tombstone-free table. Deduplication, lexical tail sharing, representative ownership, linked-record acyclicity and physical-bound provenance establish logical incidence facts; none independently yields (I). This is absence of a demonstrated invariant in these owners, not proof that no such invariant exists.

No native counterexample or all-history proof was found. The narrow missing premise is now: **a real native route can (or cannot) order an occupied-tail admission before a credit-exhausting new-tail admission, fail before its next reserve, and erase that new tail to DELETED before reversing the earlier `Some`, using actual row IDs and the actual default hasher**. This admission-only target removes the additional absent-destination splice/SCC obligation. A splice-specific theorem would still need every qualifying copy/parent history, not just positive-incidence extrusion.

Recommended next action: primary authorize one targeted observation packet at the actual admission/rollback owner, driven by parsed annotation or retained fresh-use actions, and inspect test resource behavior before one build. Observe native map `len/capacity` and allocator requests immediately around each inverse insertion; preserve actual u32 IDs and default `RandomState`. Log the real action/bound/undo sequence and failure seam. A capacity increase supplies resize evidence independent of assumed inverse transitions; allocator events distinguish backing allocation from in-place rehash and unrelated context inverse allocations. Read-only map observation gives `g=capacity-len`, but raw `c` must come from a separately verified table/resize observation, not a guessed live-capacity axiom. First try bounded fresh session counts and source-tail counts near capacity transitions; report actual counts and RandomState seed reproducibility limits. No such range or seed was sampled here.

Probe failure conditions: if constructors cannot produce the required order, return that exact scheduling obstruction; if all observed removals return EMPTY, the finite run is inconclusive; if the driver bypasses HIR actions/retained ownership, changes Hash/Eq, or assumes a control layout, it is not a native witness. An injected failure establishes the rollback storage seam for a genuine successful constructor prefix, but needs separate correspondence to the original retained-Local failure domain before refuting its parent claim. The expected-state snapshot oracle and allocator observer share the successful prefix and runtime, but do not implement the candidate's inverse rules. This is an A storage/rollback obligation. Another logical-key/count checker would leave the same physical premise untouched. Source-owned storage repair, if selected, remains the primary's separate authorized implementation gate.

## Dependencies, checks and resource boundary

| Frozen dependency | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_effect.rs` | `e6d485b3b7d468fa01a283d8710affd64f836ddac2613262e6e6b29e4c2b4cd4` |
| `crates/yu-solver/src/candidate_context.rs` | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| baseline `crates/yu-solver/src/candidate_scheme.rs` | `b15d72a5be0f82b2dba37b12fdc3e11a555253ff92ae7aa615b05aaa00380768` |
| baseline `crates/yu-solver/src/lib.rs` | `31c66d1bc9cc101c6174424f5f11b7cbeb6eb497448e0a4b09b683adbacb9dd9` |
| Capture-map inverse capacity note | `b765a6cbbf3061b8ef5c7bc3bfe67122cd5c599b243bfaa00b9e4ce8e7db3569` |
| Intrusion settlement audit | `d986ed3c9f53f88bf55904eb09ee7fa0c2217f816ab0183efedba175179ea71d` |
| Suspension contract | `734d94cb02c3d2a101ab21435b4377ed06952ab384815da73636bcfbc986033d` |

Concurrent implementation edits appeared in `lib.rs`, `candidate_scheme.rs` and `candidate_context_tests.rs` during this pass. Baseline `git show` reads were used to recheck the relevant lib/scheme constructors, hashes and line locators; the report uses pinned baseline behavior, including its simple error-to-rollback exit. The live edits are neither dependencies nor this producer's changes. Stable effect/context/extrusion/intrusion inputs were hashed. The primary must revalidate the implementation delta before applying this evidence to a later revision.

Commands/checks: full governing rule/skill/role reads; narrow `rg -n` writer/caller searches; targeted `sed -n` source/fixture reads; read-only HEAD/status and baseline `git show` reads; `sha256sum`; selected hashbrown erase/capacity-source read; note whitespace/lease inspection. No Cargo/build/test, execution experiment, allocator observer, performance samples, mutation testing, enumeration, Git mutation or child launch. No output beyond the exclusive note was authored. Sequential lightweight read processes only; CPU/RSS and elapsed start time were not measured. Clock observed `2026-10-11 02:11:21 UTC` before drafting. Stop: bounded source inventory complete; actual hash-layout/scheduler evidence needs the proposed different method.

Unverified scope: general all-source route scheduling, actual library linkage, real failure timing, native hash placement, other context-map inverse headroom, retained accounting, full logical rollback across other owners, lifecycle recomputation/publication, Call, hygiene, soundness, principality, production cutover and W/A3.

## Commit packet

- Exact leased path: `notes/progress/2026-10-11-capture-map-native-headroom-research.md` only.
- Baseline SHA: `befbe308fb123915385b3ec54a2e1fc3668a279e`.
- Dependency changes authored: none. Concurrent lib/scheme changes excluded; pinned hashes above govern the artifact.
- Review status: unreviewed non-authoritative source characterization and conditional target; no independent review or parent closure claimed.
- Checks run: static writer/caller/constructor trace, baseline dependency hashes/locators, fixture provenance and selected library erase read; note integrity checks. No executable checks.
- Proposed checkpoint message: `research: trace native capture histories and admission rollback headroom`.
- Shared deltas left to primary/curator: add admission-only inverse replacement as a specific falsification target alongside removed-key splice; keep native condition (I), linked-runtime correspondence and W/A3 OPEN; record exact observation-owner packet. No shared task/index/authority/question files edited.

Artifact frozen after final integrity checks; no further writes planned.
