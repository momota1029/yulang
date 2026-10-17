# Handoff: NPAIR-SCOPED-COLLECTION-REPAIR-20261018 (rev 1)

Sprint `npair-fixed-c-source-selection-scoped-collection-20261018`, rev3 contract SHA-256 `6b3780d13b47ad5742b0cc375f803254d6d33a41c487543c88f3d625cc9d949f`; baseline `d9e6949a4cdc2d1899f55d5e7a75a014d4630606`. Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR` remains OPEN, closure 0.

Fresh exact-byte compiler review was CLEAN before the only command. Reviewed query/dependency pins: `candidate_source.rs` `09a29794eafd2c93aac69b3335120878308a6804ebd6e95c2272556b744e943b`; harness `research_source_registration.rs` `f5c61bd5a4515545fad49bfc24158ef235c6ac2ebc6f00e15daabade394e79ad`; unchanged `shadow_apply.rs` `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf`, `candidate_call.rs` `2bcbab3d27e259fc4b22824980bd625014d4a19f4fa257cd74c69683c1be0359`, `candidate_scheme.rs` `abe1eb6d6176c035d237c3f51f7ccfe99dea5224df20de285465c510c6c2a494`, `candidate_context.rs` `72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6`, `lib.rs` `2c1fff385e5270ef7b7eb5fc4d9ed5f6edb6a4c01886887b183401212c5f398f`, and `candidate_operation_source.rs` `ee95a08bcb7da80c17bdba60034377c4d230d3469f261838205cb8af3f39d8bc`.

Command 1 at 2026-10-17 21:05:00 UTC (elapsed 372s / 528s remaining):

```text
YU_SCOPED_COLLECTION_DIAGNOSTIC=1 timeout 120s cargo run --offline --manifest-path crates/yu-solver/Cargo.toml --example research_source_registration --features shadow-apply-candidate
```

Exit 2. Exact output:

```text
candidate_collection.unavailable branch=crates/yu-solver/src/candidate_source.rs:1098:171
STOPPED at candidate-solve: Collection(ComponentIdentityExhausted)
```

The exact branch in `emit_candidate_source` refuses `LocalSourceForm::Name` resolved as `Local(_)` or `CatchBinder(_)` while scanning an Apply callee spine. The original `receive` body includes `my g = f (); g ()`, so the local `g` callee reaches this source-provenance guard. This is not an allocation/limit failure, despite the existing generic error label. No candidate/source-call/scoped relation was returned.

An existing source route can be reconstructed: exact Apply `LocalSourceIndex` -> `Name(Local(HirLocalId))` -> same-owner `local_slots` entry -> `Action::Local { occurrence, slot }`; same slot -> `Action::Install { initializer endpoint, boundary }`; runtime local-use -> Capture plus `FreshUse` scope remaps. Missing: a single typed authenticated edge from `ApplySourceInput` callee to that local supplier/captured scheme. A Local-only relaxation requires adjudication that this reconstruction is sufficient; it would change the candidate admission rule. No code correction was made. CatchBinder remains unsupported.

The exact received Apply HIR owner/occurrence/callee/argument/source keys/scopes were validated before the candidate solve, but the failed solve produced no source_call or scoped relations. Received-call -> relation/scope and both ordered Replay BoundKeys are UNOBSERVED. No theorem, eta/T_rho/At, or production conclusion follows; parent closure remains 0.

Fixture is restored to SHA-256 `969e20e0f38a2c341a96ff4fe07028bf567ca134e0fb24602fadf6e4c723d9c0`. Primary stop decision: 2026-10-17 21:09:41 UTC at elapsed653s / remaining247s. Worker froze outputs and STOPPED 21:10:24 UTC at elapsed696s / remaining204s. No repair, commands2–3, retry, additional build/test, compiler API/semantic change, or Git operation. Environment-gated branch/occurrence diagnostics are provisional; falsifier is a future authorized run failing to report the same branch for the `g` local occurrence. Cleanup owner: Luna primary `/root` after evidence consumption, before promotion.

Next step for Luna: decide whether exact local source slot, Install/Capture/FreshUse correspondence supplies the missing typed callee identity; otherwise preserve the refusal and specify the missing owner rule for a future approved sprint. Requested Luna/high; observed UNKNOWN/UNKNOWN. Evidence note: `notes/progress/2026-10-18-npair-scoped-collection-repair.md`.
