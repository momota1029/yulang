# Sprint EFFECT-PERMISSION-INVENTORY-REQUEST/20261031-R63 — construct the owner-derived request package

Status: ADMITTED_BOUNDED_RESEARCH. Primary: Luna (`/root`). Branch `yulang3`; baseline `b32651e265d0184c8bff92cfe5511a56eca591cb` (= `origin/yulang3`). Revision 1; primary approval is recorded in the R63 admission receipt.

Authority: the unchanged Yulang compiler/source semantics and standing `research/simple-sub-intrusion` goal. No source-domain narrowing, semantic change, parent-claim alteration, or production authority is granted. R62 is closed BOUNDED PASS for research only; its source-to-inventory/request and successful outer `Run` premises remain OPEN.

## Original outcome and success evidence

The original whole-language soundness, effect hygiene, principality, and termination claims retain their original quantifiers and remain OPEN. R62's finite policy construction still takes source records, `Native`, dependencies, and request coordinates as separate model inputs. This packet attempts the next source correspondence seam: construct those values from the existing Rust owner projection and relate the constructed Lean package to that same owner.

The implementation/proof outcome is a private, fallible, in-memory package extraction. It constructs the R55 source/Internal primitive records, R57 native records and ordered dependency projection, the Internal request, and Entry/Catch search requests from owning records and actual source-call coordinates. It must preserve raw and canonical source coordinates and keep semantic facts distinct from collected-fact identities. It may not accept a caller-supplied expected package or hide the gap behind another opaque borrowed wrapper.

Success evidence:

1. Rust reads only the complete existing owner inventories, uses checked owner-local indices retaining their native references, and constructs the package without pointer-to-integer casts, disk serialization, whole-state dumps, or effects on inference, forwarding, routing, or subtraction.
2. Lean constructs the package from typed native-record carriers and proves coverage, lookup, coordinate, and request equations sufficient to instantiate R62 with those exact constructed values. No wholesale faithfulness predicate is assumed.
3. Fresh independent review attacks foreign sessions sharing a batch, equal numeric indices in distinct namespaces, missing competitors, wrong request owner, and substitution of canonical coordinates for raw Entry coordinates; complete theorem types and transitive axiom reports are reconciled.

The falsifier is any trace where a foreign owner or incomplete inventory extracts successfully, or where a request's owner/call coordinate is not the one selected by the existing native path. Any such case blocks the affected correspondence claim.

## Governing source and frozen inputs

Primary owner path: `Experiment` projections in `crates/yu-solver/src/candidate_receiver.rs`, read-only support in `candidate_context.rs`, `candidate_effect.rs`, and `candidate_scheme.rs`. The new extractor is private and fallible. Do not edit the latter three files or source constructors; if a required source fact has no existing owner accessor, return that exact blocker to Luna.

Baseline and source pins:

- full baseline HEAD: `b32651e265d0184c8bff92cfe5511a56eca591cb`.
- `candidate_receiver.rs`: `3b60a58a1dba75b908607d91a76f49403314d3667a07987e29fc30fc4a7907e5` (write lease).
- `candidate_context.rs`: `962af7c44b2e57ba50b7738e82785bd68b517e881ba08ea41c544c9314d60021` (read only).
- `lib.rs`: `25498cc1be404b12d060cbd47f77e78c23ad27b2b99113e15823bc8b6fa92ca4`; `candidate_effect.rs`: `75267bd1a195121ca79addb62b2a446a4b1b26afcc11e8c70aa1fa732c9e2909`; `candidate_scheme.rs`: `bf8f5c80ce2761dc2a1235d2e02e348a91bc9e8965653db26b9abd4c8d6ca631` (all read only).
- R39 `ComputationPermissionEntryR39.lean`: `748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e`; R45 `InternalPermissionIncidenceR45.lean`: `9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f`; R47 `CurrentEmissionOwnershipR47.lean`: `d64c54f7c977e110305a76e6437fc87c8ff14201a4d69eb0bbcb5ee0e1cd8b9c`.
- R48 `ProviderEntryArrivalR48.lean`: `b85dfad5c0e80f7fbc2480e7f38421cc6c50107144d9abb160e688208b192575`; R49 `AuthenticatedResidualConsumerR49.lean`: `4fc4380f3ad1827ecf155f982e5186b32d6d66d91909039fb118063d8f1e2df2`.
- R62 `InternalRootPolicyR62.lean`: `e76e41a853673e75555cc5e603f1f84c456332794980613c554a2d69af8d976e`.
- R54 `OwnedResidualProjectionR54.lean`: `cc5d0b01485560e5091ce454b066ca2fc41eb350eee24ae525133a13bed401c9`.
- R55 `SourceInternalContextR55.lean`: `7aaecdd3d358d769123f00acb4b19b4d7d61ccfef98fee4eb53179da4a105123`.
- R57 `ProviderNativeContextR57.lean`: `804b3431c2e585370b8adc28f59b36c26a36e1524f42278a860823c9bd7eaa63`.
- R58 `ReachedSlotSearchR58.lean`: `431d3b4cb031fd86ad4a0537c1c8a42adecb8433f3ef775b3371eb37611b3079`.
- R59 `ReachedSlotCompletenessR59.lean`: `d0d1a33e416a13ed29e5ba018f5adf1e0a71b6b5886d2d04f74956522836bfab`.
- R60 `NativeLocalDecodeR60.lean`: `3eccc41902a8a8768a55cac020efd4936517da3feb2d91a7ec158994a133ca20`.
- R61 `BoundedAncestryR61.lean`: `9e1c783016bc14487dd0a4ebc2839dfab0dc3daf911ee88fa02f3624e2ad60a4`.
- R62 outcome: `f8195a9ac73ad6eeb14e4c7f21a454cd8536201d59c66a9a7a19865667298b47`; R62 review: `113041f925ee3e13824d4eb2ded34903c23fa1e6ac96dcb4867a5d3a379177e5`.

Before any write, each lane rehashes its direct dependencies and returns to Luna on drift. Do not alter imported Lean sources or read-only Rust owners.

## Two lanes, leases, and resources

**Rust implementation — `/root/r63_rust`, Luna/high, 1,800 seconds.** Write only `crates/yu-solver/src/candidate_receiver.rs` and `tasks/agent-loop/inbox/effect-permission-inventory-request-r63-rust.md`. Reuse existing owner projections to construct explicit primitive records and requests. Keep construction observation-only, in-memory, and fallible. No tests, builds, Cargo, formatter, or edits to other Rust files.

**Constructive proof — `/root/r63_proof`, `lean_prover` Sol/high, 1,800 seconds.** Write only `notes/theory/lean/YulangClosure/RustInventoryRequestR63.lean` and `tasks/agent-loop/inbox/effect-permission-inventory-request-r63-proof.md`. Reuse the accepted finite owner-table method, construct the R62 package, prove the needed coverage/reader/request equations, and apply them to the exact R62 consumer. Use pinned Lean 4.35.0 with stdin-only audit; no Lake project change, cache, scratch, target, or build directory.

**Fresh reviewer — `/root/r63_review`, compiler_referee Sol/low, 1,200 seconds.** Start only after both authors stop and their artifacts freeze. Read the pinned source/model and author artifacts; write only `tasks/agent-loop/inbox/effect-permission-inventory-request-r63-review.md`. No self-review, descendants, builds/tests, compiler/checker reruns, Git, scratch, cache, target, or environment.

**Primary Luna — 1,200 seconds including 500 closeout.** Owns contract/admission/current state, intake, review, adjudication, explicit-path staging, commit, and push. No Astra assignment or descendants. Aggregate sprint budget 6,000 seconds. Use the existing checkout only; create no worktree, environment, scratch, cache, target, or build directory. Keep UNKNOWN observations, pending count 32, and quarantined leases intact.

## Parent application, limits, and stop conditions

The proof applies the constructed package to R62 while preserving its source/request quantifiers and Entry/Catch separation. A coherent receipt must state which owner equations now let R62 consume actual records and identify the exact first remaining premise.

Still OPEN unless independently closed: actual native execution of the extraction, complete outer Rust-to-Run simulation, arbitrary allocator/resource/failure correspondence, original A/B, whole-program soundness/effects/principality/termination, full hygiene, and production. A finite model or successful package construction alone proves none of these.

Stop on an unrepresentable owner identity, incomplete inventory, required change to a read-only producer, dependency drift, any semantic/observable behavior change, reviewer scope expansion, or budget exhaustion. Do not cast addresses into model identities or replace raw coordinates with canonical coordinates. Authors freeze and STOP before review. Only Luna integrates a safe, coherent, reviewed checkpoint; unrelated dirty/quarantined paths remain unstaged.
