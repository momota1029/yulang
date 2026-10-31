# R85 source handoff — retained Origin completion blocks checked roots

Assignment: `/root/r85_source`, revision 1. Outcome class: **source-native-evidence; conditional constructor invariant**, pending independent review. Author: this worker only; no descendants. Requested role: researcher, read-only Rust investigation; effective model/effort metadata: UNKNOWN. Parent and sole Git/state owner: `/root`.

**Result.** In the inspected, hash-pinned producer path, every Origin-attached source-drain receipt remains `completed = false`. Terminal completion appends a different, completed receipt to `source_drain_completions`. `checked_internal_use_root` requires the attached receipt itself to be completed, so this producer path cannot supply a successful checked Internal root. This is an earlier obstruction than the proposed successful-root/selector collision. It is not a source-qualified counterexample to original A/B, and no successful-root counterexample was found or fabricated.

## Objective, authority and dependencies

Determine whether actual native checked-root success establishes R84 `originCandidates = [origin]` and R57 relation-ID-only `originRead` uniqueness on the same retained records. Method: constructor/assignment inventory, receipt lifecycle tracing, and direct predicate comparison. No executable model was used as an oracle for Rust behavior.

Source baseline: `c4e594fc64d72dba30a73c64fcbf258eaebdfc32`, branch supplied by primary as `yulang3`. Original admission committed at `a70f26d85`; amended read admission committed/pushed at `56526f479`, and Amendment 02 at `1a32d22b4`, according to the primary. No Git command was run by this worker.

Governing sections: R85 contract “Original goal and fixed scope”, “Fixed outcome and success predicates”, “Baseline and pinned inputs”, source-lane lease and stop conditions; Amendment 01 receipt ownership; R84 `originCandidates`, `readRecords`, `Primitive`; R57 `relationRead`, `originRead`, `rootDrain`, `completed`. Parent scope remains the original source statement in `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §1, its missing original-scope premise in §§3, 5–7, and the accepted birth-level qualification in `notes/design/2026-10-24-birth-level-scc-intrusion.md` §§1–6. Neither qualification nor source meaning is changed here. Repository research, design-authority and Git-concurrency rules were read; the `yulang-proofs` source-bridge guidance was applied without delegation.

Frozen hashes observed:

| Dependency | SHA-256 |
| --- | --- |
| R85 contract | `d12c5cf57d89b043677cb43f4122898ab17f5cb843c9e9dd648d3731a4ab3420` (admission pin) |
| R85 input manifest, final Amendment 02 revision | `5d20fd16e3903a8ef1fb88cd941b3f8c301421f56dbc60e9341d9e96c8e3af4c` |
| R85 Amendment 01 | `8094b5ebb4555e3b0c2dff593035f3591ba8943ecc3845f6af55bd84ad8c11af` |
| R85 Amendment 02 | `4d17ce674a7245ecb504912792288e6f81680574f56d2744c43bc8a9239c7710` |
| `candidate_context.rs` | `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905` |
| `lib.rs` | `c43fcc4f39e4ba8bfea10aa39879c37973100d9f4b8bdef71fa5b3dc3fae01df` |
| `candidate_receiver.rs` | `6004fd4252d15d8c99ac0e9f97582347a0de94946f497c0e29520d872e77dae2` |
| `ProviderNativeContextR57.lean` | `804b3431c2e585370b8adc28f59b36c26a36e1524f42278a860823c9bd7eaa63` |
| `ConstructedPhysicalRootR84.lean` | `5d8ad6429906cdf971dbb9ee44841223c1fcc28e6591e1a75d1f453ea4eac13d` |
| Original source statement | `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` |
| Birth-level decision | `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae` |

Rust hashes match the initial and amended manifest pins; no Rust dependency changed. The manifest changed from initial `db94797269f3c50840a3d89235b75007452e02a9400442c67ac2fe755aadc549` through Amendment 01 `42b92c305e5408701db4d619d8e6f52dc1d7a031973cb6c57ba66b87e596b052` to the final value above. Amendment 02 also supplies the accepted R84 proof handoff/normalized-prefix pin `8241f3b7ab3a656c15d114a987159fd33c66f04ae48fc3d82dbda0e4972ed17b`; this source lane did not run that recipe. R65/R66 were read as manifest-pinned formal definitions; this lane did not independently hash every formal/transitive dependency.

## Producer → consumer field map

All Rust paths below are under `crates/yu-solver/src/`.

| Retained field / selector | Actual producer or read | Consumer consequence / gap |
| --- | --- | --- |
| `RelationId` and typed pair | `candidate_context.rs:3481–3513`: intern `RelationKey { pair, context, sources, scoped }`; existing key returns existing ID; new ID is vector length before append | Pair lookup is functional by vector index for retained, valid IDs. Interning does not make IDs unique per Origin or occurrence. |
| Origin relation, occurrence | `candidate_context.rs:3851–3857`: append `Origin { relation, occurrence: occurrence.clone(), inferred_entry, formal: None, source_drain_receipt: None }` | Origin append is separate from relation interning; it does not reject an already Origin-owned relation. |
| Formal evidence | `candidate_context.rs:3863–3875`: seed first; then mutate only the last Origin's `formal` | No completion bit or Origin relation is changed here. |
| Drain index, original task/cause | `lib.rs:14272–14320`: begin frame, save current Origin length, seed, select incoming relation or seed, enqueue, then attach receipt | Receipt publication follows successful enqueue. Receipt can describe a non-root incoming/replay path; later checked-root rejection distinguishes it. |
| `origin_index` | Same start path records Origin length immediately before seeding, then uses indexed Origin filtered by relation, occurrence and absent receipt | The attached receipt addresses the appended Origin, not an Origin selected by relation-ID search. |
| `created_seed`, `selected_relation` | Seed result and `item.relation.or(seed)` respectively | Checked root requires both to equal the selected Origin relation; an incoming relation can violate this. |
| `incoming_relation`, `replay_ack` | Copied from incoming work item | Checked root explicitly requires both absent. |
| `task`, `cause`, slot | Receipt retains task and full `CauseId`; `Origin` retains full `ConstraintOccurrenceId` | Checked root compares full use occurrence and task typed pair; cause occurrence must equal the same full occurrence. Receiver constructs the Internal query at local slot 0 (`candidate_receiver.rs:2672–2681`). R57 splits source occurrence and slot into separate fields. |
| Attached `completed` | `lib.rs:14304`: fresh receipt has `completed: false`; `14313` attaches it to Origin | This receipt is the one returned by `checked_internal_use_root`, not the separate terminal copy. |
| Terminal completion | `lib.rs:15025–15028` calls `record_source_drain_completion`; `candidate_context.rs:2284–2290` clones, flips clone to true, appends separate vector | Original attached receipt remains false. Allocation failure silently omits completion evidence and still cannot make attached receipt true. |
| Completion membership reader | `candidate_context.rs:2292–2335`: construct expected completed copy and find it separately; `3048–3095` additionally checks cut/index uniqueness and explicitly requires attached receipt false | Existing residual/publication readers use the two-record protocol. Their success does not imply checked Internal-root success. |
| Full retained inventories | `candidate_context.rs:2990–3004` enumerates relations and completions separately; receiver's retained projection enumerates Origins and borrows attached receipts separately | No completion-to-Origin update or completed-drain substitution occurs in these borrowed projections. |
| Checked Internal root | `candidate_context.rs:3183–3219`: enumerate every Origin matching full use occurrence and exact typed pair; reject second match before inspecting receipt; require attached receipt true and root fields consistent | Incomplete, incoming and replay competitors with the same occurrence/pair still count toward ambiguity. No global relation-ID uniqueness check is performed. |
| Checked emission | `candidate_context.rs:3141–3179`: indexed emission/admission, readback/current equality, effect lower lane/entry owner, unique physical slot, relation typed pair, checked root, ancestry | Receipt obstruction prevents successful checked emission once this path reaches root validation. Slot/admission/ancestry checks cannot repair it. |
| Consumed same-owner entry | `candidate_receiver.rs:1896–1938`: retrieve indexed Origin, require pointer equality with saved Origin/receipt, and require that receipt completed | A separately completed receipt cannot be substituted while retaining these pointer identities. `3987–4013` explicitly expects attached receipt false and terminal receipt true for residual calls. |
| R84 candidate selector | `ConstructedPhysicalRootR84.lean:51–58`: full Origin list filtered by state, source occurrence, slot 0 and relation endpoints matching selected route | With faithful complete extraction and endpoint alignment, this is the native occurrence/pair filter. Those extraction/alignment premises are additional bridge obligations. |
| R57 `originRead` | `ProviderNativeContextR57.lean:202–203`: unique by native state and relation ID only | Origins at other occurrences/slots remain competitors; native occurrence/pair uniqueness alone does not eliminate them. |

Supplementary constructor observations were obtained from the already inspected whole hash-pinned source owners before the parent's final “no new reads outside amended exact ranges” restriction: seed pair canonicalization, source-reference lookup and scoped-demand construction occur immediately before the Origin append; retained receiver inventory capture and borrowed inventory copying preserve all rows. These observations are not used to assert source reachability of a collision.

## Complete mutation inventory for the admitted owner path

The textual assignment/call search covered all three pinned Rust owners, including test-only matches, rather than just the initially listed navigation windows. Meaningful matches were:

1. Sole `Origin` record constructor: `candidate_context.rs:3851`, attached receipt `None`.
2. Sole assignment of a present Origin receipt: `lib.rs:14313`, assigning the fresh `completed: false` receipt. The frame receives a clone at `14306`.
3. Only mutable Origin access besides attachment: `candidate_context.rs:3870`, setting `.formal` only.
4. `record_source_drain_completion` sets `.completed = true` on a new local clone; `source_drain_completed`, `checked_source_drain` and `checked_source_drain_in_cuts` set it only on local expected copies for comparison.
5. Frame undo/replacement clones `frame.source_drain_receipt` (`candidate_context.rs:2427`); it does not mutate an Origin. Frame completion pops the frame after appending completion evidence.
6. Rollback truncates completion records (`2183`) and Origins (`2271`); truncation preserves the false-bit property of survivors.
7. Receiver projections borrow Origins/receipts or copy their references; receiver checks read completion fields. No setter occurs there. Test-local `completed` loop flags are unrelated variables.

No admitted mutator changes an attached receipt to true. This is a source inspection result for these owners, not a whole-crate visibility proof: the structs/fields are `pub(super)`, so absence of a sibling-module writer outside the admitted dependencies remains an explicit closure assumption. This worker did not broaden the source dependency set to search those modules.

## Derivation and smallest discriminating lifecycle

Hypotheses for the constructor invariant: start with no attached true receipt; perform only the inspected seed, attach, completion, frame-update, rollback and read/projection operations; preserve ordinary Rust ownership/clone semantics; no outside mutation of the public-to-parent fields.

Invariant `I`: for every retained Origin `o`, `o.source_drain_receipt = None` or its attached receipt has `completed = false`.

- Seed preserves `I` by adding `None`.
- Successful enqueue/attachment preserves `I` by adding a fresh false receipt.
- Terminal completion preserves `I`: it mutates a clone and a different vector only.
- Formal update, frame operations and read/projections preserve `I`; rollback retains a prefix.

For any query, the checked reader either finds no matching Origin (`MissingUseRoot`), at least two (`AmbiguousUseRoot`), or exactly one. In the last case `I` gives no receipt, or a false attached receipt, and the reader returns `MissingUseRoot`. Hence no success for this transition family. This is a conditional source-derived derivation, not a kernel-checked theorem from this lane.

The invocation chain inspected is receiver physical lower-slot read and slot-0 semantic use pair (`candidate_receiver.rs:2625–2682`) → `checked_emission_for_internal_use` (`candidate_context.rs:3141–3179`) → `checked_internal_use_root` (`3183–3219`) → only after root success, relation ancestry. Its `?` propagates the root error, so the receipt mismatch blocks creation of `CurrentInternalEmission` and its downstream saved `InventoryEntryRequest` root fields. This is a static call trace; this lane executed none of those functions.

For R84, direct encoding of `Origin.source_drain_receipt` as `Origin.drain` preserves false. R84 `Primitive` requires both `d.origin.drain = some d.drain` and `d.drain.completed = true`. Therefore a faithful direct encoding cannot supply that conjunction. Encoding the terminal true clone as the Origin's drain would require an explicit, authenticated join/projection theorem; it does not follow from the existing checked reader, which returns the attached receipt by reference. R57 `Native` has no separate completion-list field, so an extraction selecting the clone must state that choice and its full identity correspondence. This finding does not invalidate R84's theorem under its explicit `Primitive` premises; it identifies an unmet native producer premise.

The smallest useful lifecycle has **one** seed/Origin, one attached receipt `r₀` with false bit, and one normal terminal completion `r₁` equal in all receipt fields except its true bit. Keep both records. The ordinary completion reader can recognize `r₁`; checked Internal root still inspects `r₀` and rejects. If completion recording fails allocation, omit `r₁` and rejection remains. This trace follows actual constructor control flow conditional on an admitted task/enqueue/completion; it is not an executed source program, a malformed Native list, or a checked-success witness.

## What the two uniqueness premises still require

Ignoring the preceding impossibility only to compare selector strength, successful native root selection supplies exactly one Origin with the full queried occurrence and typed pair, counting all retained competitors. Under a faithful complete extraction with one state/indexed relation per native relation, faithful typed endpoints, Internal local slot 0, and route endpoints equal to that query pair, R84's `originCandidates = [origin]` follows by predicate equivalence. This is a **conditional correspondence**, not an established extraction theorem.

R57's state/relation-ID predicate is broader. A different occurrence or slot can own the same relation ID without entering the native same-occurrence filter. Relations are interned by pair/context/source-set/scoped-flow, while Origins are appended separately. The constructor does not itself enforce an inverse map from relation IDs to one Origin. A candidate collision needs two seed admissions with equal four-part relation keys and different occurrences; this is not yet a source-reachable witness. Source-reference sets and slot-0 scoped call demand may distinguish the keys. Proving that they always do requires the omitted constructors of `references.checking` and call/source inventories, or a narrower invariant for the selected Internal root. Repeating an arbitrary two-Origin Native list would leave that premise untouched and is not evidence.

Therefore this lane establishes neither a successful native inventory violating R57 uniqueness nor a nonvacuous implication supplying both R84 premises. The exact first producer/consumer mismatch is attached-false versus required-attached-true. The conditional second missing premise is exclusion of every other retained Origin sharing the root relation ID, regardless of occurrence, slot, receipt or completion. Neither is supplied by physical-slot uniqueness or ancestry.

## Commands, coverage, resources and exclusions

Commands used: read-only `pwd`, `rg --files`, targeted `rg -n`, `cat`, `sed -n`, and `sha256sum`; `apply_patch` wrote this exact leased note only. Representative mutation search:

```sh
rg -n 'completed\s*=|source_drain_receipt\s*=|origins\[|origins\.get_mut|origins\.iter_mut|origins\.last_mut|origins\s*=' crates/yu-solver/src/candidate_context.rs crates/yu-solver/src/lib.rs crates/yu-solver/src/candidate_receiver.rs
```

A read/hash helper attempt using `python` failed immediately with executable-not-found; it produced no artifact. SHA-256 checks then used `sha256sum`. No Rust compiler, Cargo, Lean, Lake, tests, formatter, model execution, caches, scratch paths, environment changes or Git operations ran. No seeds, enumeration range or mutation experiments apply; there is no independent executable oracle. Rust constructor source is the evidence, and the derivation explicitly shares its clone/field transition semantics. The proof lane was informed of the exact receipt mismatch; this author cannot independently review the resulting proof.

Resource grant: 1,000 seconds; exact elapsed wall time/peak RSS were not instrumented and remain UNKNOWN. Work used short single-process read/hash commands with no build; no additional CPU or memory allocation was requested. No exhaustive search or source-program execution was completed. Unverified scope: sibling-module mutators, full source admission/reachability, authenticated Rust-to-Native extraction, full ancestry, independent review, formal module acceptance, original A/B, whole-language and production.

**One recommended next action:** have the fresh reviewer validate the false-attached/true-terminal lifecycle and the proof lane's exact formalization before the primary chooses an explicitly authorized owner-local receipt bridge. Preserve the separate relation-ID uniqueness and complete-extraction obligations.

Worker state: **STOPPED; writes stopped after this revision; no descendants or unresolved descendant leases.** This artifact is frozen for review. Shared records and source repairs are left to the primary.

## Commit packet

- Exact leased/changed path: `tasks/agent-loop/inbox/effect-permission-native-root-premises-r85-source.md` only.
- Baseline: `c4e594fc64d72dba30a73c64fcbf258eaebdfc32`; original admission `a70f26d85`; Amendment 01 receipt supplied by primary at `56526f479`; Amendment 02 at `1a32d22b4`.
- Changed dependency hashes: primary-owned manifest changed from `db94797269f3c50840a3d89235b75007452e02a9400442c67ac2fe755aadc549`, through `42b92c305e5408701db4d619d8e6f52dc1d7a031973cb6c57ba66b87e596b052`, to `5d20fd16e3903a8ef1fb88cd941b3f8c301421f56dbc60e9341d9e96c8e3af4c`; Rust hashes unchanged as listed above. No dependency was changed by this worker.
- Review status: unreviewed source evidence and conditional derivation; no independent certification or parent closure.
- Checks already run: three Rust source hashes and listed direct source/formal hash comparisons; textual constructor/mutator/call-path inventory and R57/R84 predicate inspection. No builds/tests/formal execution.
- Proposed commit message: `research: trace R85 attached receipt completion obstruction`.
- Shared-record deltas intentionally left for primary/curator: record source lane frozen/STOPPED; receipt lifecycle blocker; successful-root reachability OPEN; R57 global Origin uniqueness and authenticated complete extraction OPEN; original A/B and production unchanged; independent review pending.
