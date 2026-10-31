# R80 Rust source/native join handoff

Sprint: `EFFECT-PERMISSION-SOURCE-INCIDENCE/20261031-R80`, contract revision 1  
Contract SHA-256: `1177aecc987930ddcd326968b973bc72c35fc645ca5efb6e24f075220c29b3f7`  
Assignment: R80-RUST, handoff revision 1  
Parent: construct the original R66 `Incidence` from aligned source choice and native permission evidence; bounded by the R80 contract  
Baseline: admission `2dc25d121866e62a6a3489ab921318696584df03`; receiver baseline SHA-256 `c570bc01cc7536a617ac3c65beab153dc71d7d0981dcfa8c01b77593385774f2`  
Dependencies: pinned R45 `9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f`; R55 `7aaecdd3d358d769123f00acb4b19b4d7d61ccfef98fee4eb53179da4a105123`; R65 `3253e00f9b523446363507ae39567bab0a4ca69a2fc84cc128f8952c43bb700b`; R66 `5db5ad3f3f5e5803e2bc564fc8922d5eb8a72182c7ba11de3904eebd7b5950e1`; R77 `0aa1185675cc92ac97a20f4163bd2b2486f34cfb5ca725a3fcb3c1861efdf682`; R79 `6dff2ab5f1a5f2403822c180c21074cc1a063ed84b697bd484017705d53222ac`; read-only `lib.rs` `c43fcc4f39e4ba8bfea10aa39879c37973100d9f4b8bdef71fa5b3dc3fae01df`.

Role: Luna/high implementation packet; worker `/root/r80_rust`; session/launch receipt unavailable in this worker context. Requested model/effort: Luna/high. Observed model/effort: UNKNOWN (no runtime metadata available).

## Outcome

`SourceInternalProjection::capture` now obtains both the existing native `InternalFormalPermissionIncidence` and R77's source-derived `internal_owner_choice`, then rejects unless they select the identical borrowed `DefinitionUse`, Apply call, origin, formal registration, Lambda recipe, and parameter recipe. The join preserves the Name/use and Apply/checking coordinates separately. It checks receiving/target owners, parameter-recipe index/value, original permission formal/parameter/owner/scope/occurrence/entry-effect coordinates, and the registered Lambda root against both native facts. Existing Function argument-effect checks remain attached to this exact origin and permission. The joined choice is retained and revalidated by the existing owner round-trip gate; it is consumed there, not exposed as an unused alternate constructor.

This fails closed for mismatched source/native selections, another registration sharing Function or row images, substituted permission records/coordinates, duplicate or wrong recipes, and parameter-native-root versus registered-Lambda-root confusion. The native incidence helper still supplies the unique slot-0/slot-2 fact lookup and unique routed-use/origin checks. No Simple-sub bypass, collection behavior, semantic rule, source domain, expected output, or diagnostic changed.

## Evidence and checks

- Changed artifact: `crates/yu-solver/src/candidate_receiver.rs`, SHA-256 `b1873abe5b88a3d6b750bf517d565b1ffcfc3a619f223243c19d00e9d15c0085`.
- `git diff --check -- crates/yu-solver/src/candidate_receiver.rs`: passed.
- No Rust compiler, Cargo, tests, build, formatter, Lake, cache, target, scratch, worktree, or nested CLI was run or created.
- The code path was inspected against pinned R45/R55/R65/R66/R77/R79 definitions and prior R77 Rust and R79 accepted outcome evidence. R77's same-use source choice and R79's typed HIR-to-collected-definition bridge were reused. R76's failed assumption equating Name and Apply occurrences remains rejected; the join keeps these coordinates distinct.
- Resource use stayed inside the assigned 1,000-second ceiling; exact active seconds are unavailable in this worker context.

## Remaining TODOs and boundaries

- `R80-RUST-JOIN-PROOF-1` (proof lane): derive the original R66 `sourceProbe`, R45 `OwnerReads`, `Identity`, and parameter-recipe field from these exact aligned records; distinguish the specified mismatch, duplicate-fact, foreign-registration, bad-recipe, permission-substitution, and root-confusion falsifiers. This Rust result does not prove that derivation.
- `R79-ORDERED-ROOTS-EXTRACTION-1` (source owner/Luna): provide authenticated Rust-to-Lean extraction of collected definitions and `OrderedRoots`; the accepted R79 bridge leaves this external correspondence open.
- R66 `Root`, physical root joins, original A/B, whole-language soundness/principality/termination, and production remain OPEN. No compiler/runtime behavior or independent review is claimed.

Next in-envelope step: after both author lanes freeze, independent review checks this fused path against the proof construction and the named falsifiers. Any missing owner record returns to Luna; this packet adds no fallback relation.

Lease: only this handoff and `crates/yu-solver/src/candidate_receiver.rs` were written. No scratch/generated outputs or descendants. Worker writes stop when this handoff is frozen. Outcome class: bounded implementation candidate; review pending, not independently certified.
