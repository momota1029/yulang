# R45 independent review — FAIL pending three compilation repairs

Reviewer: `/root/r37_inventory_review`. Contract SHA-256: `c866a7ecc4c80df8b1345a89e6733650ddb334f35b7d3a79f4e825e134d2847a`.

Both producers were confirmed STOPPED before review. This is a read-only source and retained-proof-receipt review; no checker, compiler, build, test, Git command, scratch, cache, target, worktree, or file write occurred.

**Three BLOCKING findings remain. No additional major or minor correctness finding was established.** The source chain appears constructible after these mechanical repairs; this is not evidence of an unavoidable `NO_SAFE_INTERNAL_CERTIFICATE` obstruction.

## Findings

### BLOCKING B1 — crate-root visibility refers to a nonexistent parent

Location: `crates/yu-solver/src/lib.rs:3371–3379`, `InternalFormalPermissionIncidence` and its eight fields.

The declaration and fields use `pub(super)` in the crate root. That scope has no parent module, so these visibility paths cannot resolve. The containing source is the crate root, not a nested module.

Violated requirement: R45’s implementation success predicate requires an actual private borrowed certificate implemented against the owning compiler records.

Minimum closure: use valid crate-root visibility, such as `pub(crate)` for the type and private fields where sufficient. Freeze the changed bytes and obtain focused independent delta review. No semantic change is needed.

### BLOCKING B2 — receiver identity comparison has incompatible operand types

Location: `crates/yu-solver/src/lib.rs:18287`.

```rust
receiving_owner.definition != use_record.parent.definition()?
```

`CollectedDefinition.definition` is a `DefinitionOrderId` (`lib.rs:538–540`). `SourceReceiver::definition` returns `Option<&DefinitionOrderId>` (`lib.rs:631–635`). The available equality implementation is `PartialEq<DefinitionOrderId> for DefinitionOrderId` (`lib.rs:516`), not comparison with `&DefinitionOrderId`.

The receiver identity guard therefore cannot type-check as written. This is static type evidence, not an observed compiler diagnostic.

Violated requirement: the exact source receiver/target join must be an implemented, type-correct guard.

Minimum closure: compare matching reference types, for example:

```rust
&receiving_owner.definition != use_record.parent.definition()?
```

Freeze and independently review that exact replacement.

### BLOCKING B3 — unconditional certificate references feature-gated modules

Location: `crates/yu-solver/src/lib.rs:3371`, especially fields at lines 3375–3376; governing module gates at `lib.rs:226–229`.

The new certificate is unconditional but names:

```rust
candidate_context::LambdaArgumentEffectOrigin
candidate_effect::InternalFormalEntryPermission
```

Both modules exist only with `shadow-apply-candidate`. The certificate’s query method is gated, but the certificate declaration itself is not. A configuration without that feature therefore contains unresolved module references even after B1 is repaired.

Violated requirement: R45 must remain a bounded private addition without breaking sibling compiler configurations.

Minimum closure: apply the matching feature gate to the certificate declaration, or otherwise ensure every referenced type exists in each supported configuration. Matching the query’s gate is the smallest repair.

These three findings explain the compilation defects identified in this review. Compilation remains unobserved; the review cannot claim they exhaust every possible compiler diagnostic.

## Source correspondence assessment

The change addresses the owning incidence construction rather than downstream suppression symptoms.

`lib.rs:18273–18308` resolves the complete `DefinitionUseId` through the batch’s artifact-checked lookup, checks cause and occurrence identity, resolves exact receiver/target records, selects a unique same-ID route, requires `Internal`, and verifies its admitted fact identity and original target/use endpoints. Definition-use equality includes both the collection allocation and HIR occurrence.

`lib.rs:18311–18359` selects computation registration/origin evidence using target owner and recipe root-component identity. It checks unique recipes, registered parameter-recipe identity, and the actual retained source Lambda/formal at the registration’s local-source index.

`lib.rs:18361–18389` requires a singleton constructor origin, its exact Lambda occurrence, an actual positive Function, and its actual negative live effect-variable argument child with the retained entry ordinal. The unique admitted Lambda slot-2 fact must connect that Function to the original target root.

`candidate_effect.rs:601–644` selects a singleton permission by registration before validating its formal, recipe position, owner, scope, occurrence and original entry. Its concrete slice is borrowed intact, preserving order and duplicates. Equal canonical rows, terms, or common provider roots cannot select the permission.

The receiving wrapper at `candidate_receiver.rs:34–46` additionally requires the experiment’s single complete use and exact relay/answer roots. It adds no consumer or second admission.

Missing, duplicate, non-Internal, foreign or mismatched selected evidence returns `None`. Existing immutable batch/component construction supplies valid component positions; the query does not introduce caller-controlled unchecked component indexing.

## Retention, rollback and dirty-input isolation

R45 adds borrowed views and read-only traversals, with no new persistent vector, allocation, solver mutation, or publication. The existing definition-use lookup increments its existing diagnostic probe counter; it does not change semantic state.

Existing constructor-origin retention remains under `candidate_context` reservation, checkpoint/truncation and accounting. Existing permission retention remains under `candidate_effect` reservation, byte accounting and rollback. R45 adds no new retention owner to those mechanisms.

I independently verified the five Rust blocks in the handoff against the actual final sources. Removing those exact additions, with their adjacent separator newlines, reconstructs all three admitted input hashes exactly:

- `candidate_receiver.rs` → `620b09011ec4dc4bfa71998e2b6fc1498b9299b3056662fdaa80b17376ba23c3`
- `candidate_effect.rs` → `73ad01324356672f1e45e56ea18d6f5bf0ded8628cce56e884960eb29bd5786d`
- `lib.rs` → `b1dac8bd244e282ff42a2d580e237393153f9b912c6ac0adf110367def5c79ce`

Thus the supplied additive R45 patch inventory is lossless relative to the pinned working inputs, including the dirty R43 effect snapshot. This does not authorize integrating the entire working-tree delta or establish committed-baseline cleanliness. No Git inspection was authorized or performed.

## Lean characterization and limits

All fifteen theorem statements and proof bodies were inspected. The model explicitly separates complete use identity, Internal kind, registration, source/target owners, component identity, admitted facts, Function child and singleton permission.

`accepted_iff` characterizes the actual model guard, including all `OwnerReads`, `Identity` checks and exact certificate output. `accepted_component_identity` preserves original component coordinates rather than substituting equal terms. Payload preservation retains the whole permission and every concrete-list index.

`retained_entry_to_internal` applies R39 preparation and publication to the **same** permission returned by extraction. Its source preparation, permission construction and acceptance premises remain explicit. The numeric witness establishes model inhabitance and duplicate preservation, not native reachability.

The `Inputs` observations remain abstract partial owner reads. The model does not implement the Rust search algorithm or prove completeness of native extraction. The reviewed source supplies concrete owners for those reads, subject to the compilation repairs above. No unproved generic Rust simulation is asserted.

This certificate supplies an alternative Internal incidence package. It does **not** establish R43’s FreshRoute binding, R44’s `SameUseFresh` or `nativeAvailable`, provider arrival, `arrivalAtEntry`, selected Catch, or residual subtraction.

## Retained checker evidence

No checker was rerun. The producer’s final invocation batches 2–5 contain all fifteen declarations, with complete ordered BEGIN/END markers, printed types and full axiom reports. All five preserved stdout blocks—including the failed first invocation—independently reproduce their recorded SHA-256 hashes. Final batches share source-base SHA-256:

`5c342027771deb0b2d56b6b05745136e1dd2fd8200f9a86b3d8b7e120d03c115`

The failed initial invocation’s `sorryAx` is preserved as failed history and is absent from the final audited declarations.

Complete final axiom census, namespace `YulangClosure.InternalPermissionIncidenceR45`:

| Theorems | Full transitive axiom set |
|---|---|
| `accepted_iff`, `accepted_identity`, `accepted_constructor_and_endpoints`, `accepted_component_identity`, `accepted_payload`, `unavailable_owner_rejected`, `identity_mismatch_rejected`, `foreign_registration_rejected`, `foreign_use_or_kind_rejected`, `component_identity_mismatch_rejected`, `missing_or_duplicate_permission_rejected`, `shared_images_do_not_authorize`, `concrete_foreign_and_incoming_rejected` | `propext` |
| `retained_entry_to_internal`, `concrete_internal_witness` | `propext`, `Quot.sound` |

No final project axiom, `Classical.choice`, `sorryAx` or native-evaluation assumption appears. Source scans of the actual R39/R45 checker cone found no proof hole or checker bypass. The pinned helper’s theorem-kind and transitive-axiom checks were inspected.

## Frozen hashes

| Artifact | SHA-256 |
|---|---|
| R45 contract | `c866a7ecc4c80df8b1345a89e6733650ddb334f35b7d3a79f4e825e134d2847a` |
| Rust handoff | `5ca8058e79015b4896260c19aa2b389449324e223c169419fd873177910c4341` |
| Proof handoff | `4b1f54f1c4fa915d694c1a15068f93333f25f12f9073fa461b975638db7cde27` |
| R45 Lean | `9ff4fd544375a3d4a46100647cba93ddde6f34bebd767ba402f3bd3d35a84b1f` |
| Final `candidate_receiver.rs` | `f5bff0d8aa7a20551fb2c5ad60b7b2b41907f471a55068a9ec1ae61ceba02911` |
| Final `candidate_effect.rs` | `2a86befde95581decef8fe01698961062bd22388cff2459e9611570a20b9fba3` |
| Final `lib.rs` | `7bff32f03def005688b37bcc4f81423f0a19cc2a2b8c0970f723a2973ac54499` |

All unchanged source, model, prior-review, design, toolchain, project configuration and helper pins listed in the proof handoff matched independently. Changed-source input pins were authenticated by the exact in-memory reconstruction above.

## STOP and remaining gates

Acceptance is blocked by B1–B3. Repair them in a separate primary delta, preserve this frozen finding history, then obtain focused independent re-review.

Provider arrival, exact-entry arrival meaning, selected Catch/residual correspondence, original hygiene/A/B claims, soundness, principality, termination and production promotion remain OPEN. No quarantined runtime path was opened or searched; no quarantine or unknown lease was released.

Reviewer **STOPPED**, read-only, with no writes, descendants, persistent verification processes, or pending child work.

## Focused repair review — PASS

Reviewer: `/root/r37_inventory_review`. The primary repaired B1–B3 in `lib.rs`; reviewed repaired file SHA-256:

`25498cc1be404b12d060cbd47f77e78c23ad27b2b99113e15823bc8b6fa92ca4`

- B1 closed: crate-root certificate is `pub(crate)` with private fields.
- B2 closed: receiver identity compares `&DefinitionOrderId` on both sides.
- B3 closed: the certificate declaration has the same `shadow-apply-candidate` gate as its query and referenced modules.

Independent reversal of only these three repairs reconstructs the previously reviewed source SHA-256 `7bff32f03def005688b37bcc4f81423f0a19cc2a2b8c0970f723a2973ac54499`. No other source byte changed in the repair. It changes visibility, feature availability and borrowing only; incidence selection, owner checks, endpoints, payload, routing and consumers are unchanged. All 15 theorem audits and frozen producer artifacts remain applicable.

**Final bounded verdict: PASS after B1–B3 repair. No remaining blocking, major or minor finding.** Rust compilation remains unobserved. Provider arrival, exact-entry arrival meaning, selected Catch/residual correspondence and parent/production closure remain OPEN.

Reviewer STOPPED read-only. No checker, compiler, build, test, Git, scratch, cache, target, worktree or environment was used.
