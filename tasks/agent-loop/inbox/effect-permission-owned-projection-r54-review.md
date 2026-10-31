# R54 independent review

Assignment: EFFECT-PERMISSION-OWNED-PROJECTION/20261031-R54; reviewer /root/r37_inventory_review. Both authors were STOPPED before review. This was an independent static review only.

## Verdict

BOUNDED PASS for the borrowed native projection, finite owner mathematics, and conditional same-owner R53 application. NO SAFE CERTIFICATE for full Rust-to-R50/R51 semantic extraction. No BLOCKING, major, or minor correctness finding was established within the claimed bounded contribution. Full R54 extraction remains OPEN and is not gate closure.

## Frozen inputs independently hashed

- Contract: 480535acc8ef0a25c9aa4a9a96a567dd546cc7043dbf45324683733f8a49421f.
- Admission: 7826998d952795a7fddf01790cb3838a1e9a834e903dcb87aba86a0ceae289e3.
- candidate_receiver.rs: cd914826f79cec065af2dbba7bb79d0ddc7681080e12a0e974738186118e769f.
- candidate_context.rs: 8fa738f5050b642a9a52a55ffb2744cadeb95a0a0decefcc336663430deb4f89.
- Rust handoff: 6f11869c7c06b72b737e74d63d88e8fe7d47174c304e164b5c10c6e6a575f6fb.
- OwnedResidualProjectionR54.lean: cc5d0b01485560e5091ce454b066ca2fc41eb350eee24ae525133a13bed401c9.
- Proof handoff: 6fde724aafbaffd63dc957d7a0fdda375a84d964ee5004db1d64301a33e23677.
- R53 outcome/review: 711d0a6ee8f836c3483f67ca5515b1b30cea82994945021563a9b236ca8c7bc5 / cb24c5619cefc84434421773d38c7e5810219313e7e9f4613232447e960f92b1.

All match. Governing authority/source-map hashes in proof metadata also match. All nine actual Lean cone sources match final Audit5 hashes and occur exactly once, complete with only local YulangClosure import lines removed, in its archived stdin. No Git provenance was independently checked.

## Rust evidence and adversarial checks

candidate_receiver.rs:390-426 retains borrowed experiment/schema/batch/session/live-State/whole anchors and owner-indexed borrowed inventories. capture at 1637-1684 gets State through the exact owning session graph. It enumerates all current publication candidates (the owner's single Option), all calls/facts/effect rows, relations/origins/completions/admissions/emissions, and every origin-attached optional drain before filtering individual records. Context iterators at 2959-2980 enumerate complete backing collections without candidate filters.

verify_owner_round_trips at 1687-1753 compares owning pointers, both raw/canonical endpoint recomputations, singleton publication identity, every inventory index and pointer, and source-drain option shape. borrowed_inventory_matches at 2000-2012 rejects missing, extra, reordered or collapsed-index entries and requires source exhaustion. A foreign State sharing batch bytes and numeric ordinals cannot pass the exact live-State pointer comparison. Borrowing ties the accepted constructor result to that owning experiment; this is no theorem about allocator history or execution lifetimes beyond Rust's intended borrowing discipline.

verify_source_fact_owner at 1756-1786 uses the original relay/answer schedules, exact occurrence/slot51, complete fact equality, cause, catch and source owners, rejecting absent or multiply matched facts. verify_live_observation_owners at 1789-1841 checks the live result row against retained final vectors and initial prefixes, then traverses the full plan in order: Suppress consumes no call; each Forward consumes one exact original-index/publication/endpoint/upper/occurrence/cause call; trailing calls reject.

verify_call_records at 1844-1957 resolves original source-origin/drain/completion/relation indices within the captured windows. New evidence resolves admission/relation/emission owners, exact bound/readback/slot, own-window membership and uniqueness. AlreadyPresent checks current physical slot and exact prior matching emission count, allows zero prior emissions, and rejects an own-window emission of that slot. verify_emission_owner at 1961-1989 completes direct-index/pointer/admission/relation/readback joins.

raw_source_effect_endpoint at 1993-2011 retains Component's pre-representative ordinal and guarded LiveVariable ordinal; canonical_effect supplies the separately retained canonical coordinate. Existing lib.rs:11780,11851,13527 confirms that decomposition. Raw/canonical substitution is detected by recomputation against the original fact; canonical coordinates are not relabeled raw.

The constructor is an Option-returning observation query at 492-494. All added allocation failures return None. Its validation errors neither propagate solver Err nor enter Forward decisions. The borrowed Vecs contain references and indices, not copied native state snapshots. This static audit establishes constructor consistency, not Rust compilation, runtime acceptance or a tamper-proof public certificate.

## Lean statements and exact application boundary

Actual declarations and proof bodies were inspected in OwnedResidualProjectionR54.lean: Owner includes State separately from Batch; Handle includes owner/kind/ordinal; Table retains whole typed keys. locate lemmas prove list lookup and coverage; round trips, injectivity, coverage and lookup_commutes are about the provided owning list. available rejects missing required keys and duplicate keys. Foreign owner/kind checks precede lookup. Coordinates preserves raw and canonical identities separately.

interpretR53 at 274-288 reads values already typed as AuthenticatedResidualConsumerR49.Context and NativeResidualPublicationR51.Inputs. same_owner_r53_application at 293-317 uses those exact reads, checks identical owners and valid inventories, and applies R53 with the same context/base. Its full printed type retains acceptedPlan, assembly, complete keyed inventory, Installed/DrainSource/ModeSource/NativeSource for every call, same artifact, FactReads, OwnerReads and CutChain. No entire observation predicate or faithful-extraction equivalence is assumed as a replacement premise.

Concrete witnesses at 330-406 check equal batch/equal ordinal foreign states, missing and collapsed inventories, raw/canonical substitution, an actual same-owner R53 instance, missing fact and foreign-state transplantation even when the underlying R53 payload still accepts.

The first unavailable premise is a constructor mapping actual borrowed HIR/native values into the same complete R50 Context: source Catch/operation readers, R39/R45 internal incidence readers, R48 provider/view readers and complete R50 path/provider inventories. R51 base/call/slot/readback interpretations in one live State also remain to be constructed and related to actual Rust reads. Generic nativeRead is model-list lookup, not Rust extraction. Owner equality alone supplies none of these semantic fields. The named read_preserves_property theorem only transports a property already proved for the exact model value.

Thus the contribution addresses finite identity/lookup causes of owner aliasing, while leaving semantic extraction explicitly unproved. R53/R52 primitive premises, native execution, extraction completeness, all-source parent A/B, SourceProblem.InferenceSoundness, principality, termination, complete hygiene and production remain OPEN. R32-R34 callback-domain results were not imported or applied.

## Complete root and axiom census

All names below are prefixed YulangClosure.OwnedResidualProjectionR54. Audit5 prints full types and complete transitive axioms for every actual source root, in exact source order, 29/29. No omitted roots, warnings, sorryAx, project axiom, Classical.choice or native-evaluation dependency appears.

Exactly [propext] (13): locate_sound, locate_coverage, lookup_commutes, foreign_state_rejected, foreign_kind_rejected, same_owner_composition, join_rejects_foreign_state, read_preserves_property, collapsed_inventory_unavailable, concrete_finite_roundtrips, concrete_foreign_batch_and_kind_attacks, concrete_missing_and_collapsed_candidates, concrete_raw_canonical_substitution_rejected.

Exactly [propext, Quot.sound.{u}] (16): locate_complete_index, decode_encode, encode_decode, inventory_coverage, encoding_distinguishes, covers_complete, raw_canonical_distinctions, every_native_index_enumerated, locate_missing, missing_candidate_unavailable, same_owner_r53_application, foreign_context_state_unavailable, concrete_same_owner_r53, concrete_same_owner_missing_fact_rejected, concrete_collapsed_context_inventory_rejected, concrete_foreign_state_transplant_rejected.

## Archived receipt audit

Independently decoded all five archived inputs (zlib/base64) and stdout/stderr (base64): every byte count and SHA matched. Audit2/3 failures remain failures; Audit1/4 are intermediate; only Audit5 authenticates final 29-root bytes. Final input: 229672 bytes, SHA 5470bd512093f1fbd8e8373ea1f2d15c405e4ad280840edac9fd69c93a77a76e. Final stdout: 30881 bytes, SHA dc3097530951f2347889267ecb54c478303ffc57c2ecbddb69f80c8841da515e. Empty stderr SHA e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855. Archived Audit5 exit0, wall13.144911914998374s, maxRSS936276KiB; all-five wall60.82315405600821s, peak942444KiB. These are authenticated producer receipts, not an independently rerun checker. One review metadata script initially treated module names as filesystem paths and stopped; the corrected read-only script completed all nine source checks. No artifact was changed.

## STOP receipt

Read-only review complete. No writes, builds/tests/checker reruns, Cargo/Lake/formatter, Git, scratch/cache/target, new environment/worktree, subprocess descendants or quarantined-file access. Prior quarantine incidents remain separate history and supply no evidence here. Primary owns report placement and adjudication. STOPPED; WRITES STOPPED; no future work under this assignment.
