# Native physical inventory — independent M3 review

Date: 2026-10-26
Reviewer: `/root/native_inventory_review`, fresh nonauthor generic leaf fallback for compiler_referee/spec_auditor
Producer: `/root/native_inventory_construction`
Baseline supplied: `bf81a1bd444b3bcbecca6b754ea6fb603262f368`, branch `yulang3`
Verdict: **REPAIR_REQUIRED — one narrow paper cost-accounting correction.**

The finite physical-address correspondence, native owner comparisons and frozen
test evidence are accepted at their stated scope. No Rust repair, additional
fixture, Cargo run or Lean check is requested. The only finding is the
overstated extraction-cost sentence below. This review does not promote
`SourceProblem.InferenceSoundness`, original inference A/B, source acceptance,
principality, termination, production or cutover.

## 1. Finding and exact repair

**NI-1 — paper cost bound omits traversed inputs (record-only, P2).**

`notes/theory/2026-10-26-native-bound-inventory-construction.md:89–92`
states expected `O(B+E+R+T)` hash-table operations, plus copied dependency
records and structural child arrays, for the extraction. The concrete adapter
also iterates every retained relation at
`candidate_native_inventory_tests.rs:159–163` and pushes its structural root
handles into `work`. The `seen.insert` at line 168 runs for each such occurrence,
including duplicate roots. A count of distinct reachable terms T does not bound
that root multiplicity. No stated premise bounds the number of retained
relations by B, E, R, T or the dependency-copy size.

If the paragraph is intended as an overall extraction bound, it also needs to
account for the two operation-map traversals and sorts at lines 182–185, group
and reuse enumeration at line 193, source-event qualification enumeration at
lines 195–196, and representative/canonicalization traversal at lines 135,
142 and 151. `candidate_intrusion.rs::representative` follows forest parent
links; those calls are not established constant-time lookups here. The
enumeration terminates, but these costs are absent from the stated formula.

Minimal repair: qualify the linear bound as applying only to the physical
vector/emission enumeration, and explicitly list the additional relation-root,
structural-child, operation-map/sorting, group/reuse/source-event and
representative-traversal costs. Alternatively provide a corrected parameterized
bound. Do not change the adapter to make the old sentence true. Update the
paper/producer receipt and hash manifest consistently. This is a paper-only
delta and needs no native rerun; a focused text/hash delta review suffices.

## 2. Source, domain and premise comparison

The authority comparison used root `AGENTS.md`, relevant
`AGENTS.pre-sprint.md` rules, design authority, orchestration budget, the
2026-10-11 inference principles, the new progress contract, the original
2026-10-13 preservation statement §1, and the 2026-10-24 birth-level SCC
decision. The packet preserves the original supported source domain, lexical
scopes, shared witness, generalization, complete Call and effects. It does not
replace them with the fixture's native constructor domain.

| Claim under review | Actual owner comparison and conclusion |
| --- | --- |
| Complete raw physical universe | Both `bounds` and `effect_bounds` are enumerated without a representative filter; each has four distinct append calls and per-vector index enumeration. The independent eight-case `physical_read` plus cardinality and address uniqueness establishes the claimed finite bijection. Raw endpoint equality does not collapse duplicate slots. |
| Correct orientation | `candidate_apply_value` and `candidate_apply_effect` choose upper storage on the lower row when the upper level is no greater, otherwise lower storage on the upper row. Both are normalized correctly: positive/lower means item ≤ owner; negative/upper means owner ≤ item. Canonical copies remain separate from raw addresses and keys. |
| Physical/admission/emission identity | `candidate_insert_bound_with_evidence` chooses the native lane, records the pre-push index, checks immediate raw readback, then calls `evidence_emit`. `BoundEvidence::emit` obtains the bound from the exact referenced admission and records the physical/readback fields. The adapter joins emission vector indices by physical slot and borrows the complete admission/emission slices; it does not replace identities by canonical-bound equality. It also preserves unmatched emissions through the full borrowed vector. |
| Opposite ordering and alias transport | The actual consumer uses representative ownership, opposite polarity, direct entries before exact entries, and canonicalizes returned endpoints. The validator compares this API before and after a real merge. `merge_candidate_rows` copies both sides, retains `ParentCopy { parent_index }`, leaves source vectors intact, then updates the representative and provenance. The raw-row enumeration is therefore necessary and correct. |
| Structural ports | Actual `TermView` variants carry argument, argument effect, result effect and result separately. The worklist follows all four fields and preserves borrowed tuple/record/variant arrays, including field and alternative metadata. The fixture's distinct value-port and effect-port swaps are checked against native term readback. This is extraction, not a proof of semantic subtyping at the ports. |
| Retained replay and use evidence | Dependencies are copied without filtering; recipes, snapshots, transforms, origins, relations and bound fibers are borrowed. Every currently live replay/restoration map entry is retained with its ID and full record. All retained module/local/operator/member route slices remain borrowed, including their common maps and use identities. The note explicitly leaves any live partial continuation to its actual owner. |
| Parent/group/reuse identities | The parent slice retains its vector indices and complete original records. `observed_groups` and `observed_reuses` enumerate every respective record with its ID and fields, without qualification filtering. `recapture_candidate_extrusion` preserves original sources and adds later reuse occurrences before the guarded activation. The paper's uninterrupted/fixed-qualification premise is retained. |

The snapshot is not a complete native-machine serialization or an all-history
certificate, and the packet does not claim either. In particular completed
operation reclamation prevents recovery of all past operations from the final
snapshot. It does not preclude an erased mathematical event trace of a finite
actual execution. The proposed ghost trace is appropriately separated from
the unproved semantic history obligation and adds no runtime retention policy.

The saved-count/live-index shift is the already selected behavior. The packet
uses the existing all-local Value-block compensation result with its actual
premises; it does not treat that bounded result as shared-row, effect,
contextual, alias/merge or complete physical-incidence coverage. No duplicate
bug claim or restoration repair is proposed.

## 3. Falsifier quality and scope

The positive fixture first validates a nonempty native inventory, asserts all
eight lane kinds are present and a live replay record exists, then mutates the
extracted snapshot. Removing a slot fails cardinality; swapping the distinct
value ports and then the distinct effect ports fails native structural
readback; removing an actually found `Dependency::Replay` fails equality with
the retained native dependency vector. The assertions cannot pass through an
empty fixture or absent Replay edge. The original structural view is restored
before testing the dependency mutant, isolating that failure.

The post-extrusion/merge snapshot validates again and requires both a raw versus
canonical difference and real `ParentCopy` transport. Qualification comes from
an actual parsed/lowered self-reference event and the native seed owner, while
the typed bound inputs and processing cut are explicitly constructed by the
test. No `finish_candidate` call, native no-error source-acceptance theorem,
complete restoration execution, or coverage of every FreshUse family is
claimed. Zero reuses is reported honestly and is not used as all-history proof.

No Lean file or theorem is supplied. The finite enumeration proof is paper-only;
the packet's Lean declaration/axiom inventory is empty. The original semantic
row interpretation, saturated replay history, source/publication bridge and
full original Call witness remain separate open premises with named owners.

## 4. Frozen hashes, change boundary and recorded verification

All four assigned frozen hashes match the files reviewed:

| File | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_native_inventory_tests.rs` | `6b3670e5548ad0000c4717949476a3a3038b2e06490f7f58ed4c6a1ac522d638` |
| `crates/yu-solver/src/candidate_context.rs` | `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e` |
| `notes/theory/2026-10-26-native-bound-inventory-construction.md` | `a2abd394080be5f9de75ef6fed5771df950ea178a5e5cfb206d6484d765bffc4` |
| `tasks/agent-loop/inbox/20261026-inference-native-inventory.md` | `23a14b2c78c505035fe863e29876b47710d78541f1172694c5555ce47c876177` |

All 29 entries in `inference-native-inventory/final-hashes.json` were rehashed
successfully: 14 input entries, four outputs and 11 scratch evidence files.
The manifest itself hashes to
`f221930bbb9a8d0cf3116e836a03a9aea8196a6b6e1de4765496ba1aa8afeada`.
The saved pre-change context file exactly equals that path at the supplied
baseline. The current file is those bytes followed only by:

```rust

#[cfg(test)]
#[path = "candidate_native_inventory_tests.rs"]
mod native_inventory_tests;
```

Git reports four added lines: the blank line, `cfg(test)`, path attribute and
module declaration. The producer's "five-line" description is a minor metadata
counting imprecision, not an extra source change. This is the granted test-only
append; there is no production delta or widened accessor. The source files used
by the paper retain their input hashes.

The three complete logs, JSON run receipts and runner scripts were read. The
recorded command is the focused `yu-solver` library test filter with
`shadow-apply-candidate`, locked dependencies and one test thread. The runners
use the isolated target, offline dependencies, one build job, a 4 GiB
per-process address-space bound and process-group termination on timeout.

| Run | Receipt | Log conclusion |
| --- | --- | --- |
| 01 | Timeout, exit -9, 120.061273 s | Compilation only; no test execution or accepted result. |
| 02 | Timeout, exit -9, 120.017975 s | Compilation only; no test execution or accepted result. |
| 03 | Exit 0, 52.956683 s | One test passed, 815 filtered, test body 0.01 s. |

The 240-second revision and identical-source run are recorded in the progress
contract and producer handoff. Pre-freeze and final code hashes agree. The
passing log reports `18` slots, `18` emissions, `10` terms, `76` dependencies,
`6` parents, `1` group, `0` reuses and generation `6`. Its 19 yu-solver warnings
refer to existing locations, with none in the new module. Prior timeouts remain
preserved and are not converted into passes.

## 5. Cessation and next action

Only this review receipt was written. No descendants were launched; no Git
mutation, producer/source edit, shared status/import edit, Cargo run, Lean run,
semantic change or expectation change occurred. No reviewer process remains.
Writes stop after receipt readback. The primary owns adjudication and the
single paper-only repair/delta review, integration and publication. All
original inference parent gates remain OPEN.

## 6. Focused NI-1 delta review — ACCEPT

Date: 2026-10-26
Current packet verdict: **ACCEPT at the original bounded inventory scope.**
NI-1 is resolved. This disposition supersedes the initial repair-required
verdict above while preserving that review and its historical input hashes.

The revised paper limits expected `O(B+E+R)` work to physical-vector
enumeration and emission indexing, explicitly excluding representative
traversal. It separately accounts for repeated retained-relation roots,
reachable structural children, copied dependencies, retained identity
enumerations and qualification, live operation-map traversal/sorting, and
representative-forest traversal. Distinct terms are no longer used to bound
relation-root multiplicity. This is the requested narrow correction; it changes
neither the finite-address argument nor its native/source premises.

Repaired paper SHA-256:
`7d2635134a61b02a6669bf1465766dd79ba6fc8922a58772cd0373eea8e8c5ca`.
Replacing only the revised cost paragraph in memory with its reviewed original
reproduces the original paper hash
`a2abd394080be5f9de75ef6fed5771df950ea178a5e5cfb206d6484d765bffc4`;
there are no other paper changes. The nine native owner files in the original
manifest were rehashed unchanged, using the reviewed final hash for
`candidate_context.rs`. The new test module and producer receipt also retain
their original frozen hashes. The historical producer manifest/receipt remain
historical evidence rather than being silently rewritten.

The test-module append remains four added Git lines. The producer's five-line
wording remains the already noted minor metadata imprecision. No source,
fixture, test expectation, semantic authority or original parent gate changed.
The prior native verification applies without rerunning Cargo or Lean.

Only this disposition was appended during delta review. Read/hash operations
were the sole verification; no checker, test, Git mutation, descendant or
producer edit occurred. Final writes stopped after receipt readback. The
original inference soundness, source/publication, principality, termination
and production gates remain OPEN.
