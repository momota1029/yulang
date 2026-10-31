# R80 independent closure review

Disposition: **BLOCKING for R80 theorem closure. Rust join passes this bounded static review; compilation/runtime remain unverified.** No new major or minor compiler-correctness findings.

Reviewed actual Rust and Lean artifacts and governing definitions before reading producer explanations. Applied `yulang-lean-proofs` for proof auditing. No descendants, author contact, Lean invocation, Rust compiler, Cargo, tests, builds, Lake, formatter, scratch/cache/target/environment/worktree creation, or Git mutations.

## BLOCKING — original Incidence construction has no accepted proof

Locations: `notes/theory/lean/YulangClosure/ConstructedSourceIncidenceR80.lean:112`, `:113`, `:143`, `:164`, `:255`, `:263`, `:276`, `:294`.

The final candidate still fails elaboration:

- Lines 112–113: the role and receipt-kind `simp` proofs make no progress.
- Line 143: rewriting the plan premise fails against the dependent `sourceProbe` expression, including its `Decidable` argument.
- Lines 255, 276 and 294: `decide` cannot reduce the construction.
- Line 263: the finite permission/root assertion lacks a synthesized `Decidable` instance.

Consequently, `assemble` at line 164 depends on rejected derivations. The required nonempty successful witness and adversarial rejection proofs are also unaccepted. This is an elaboration/proof failure, not evidence that the mathematical claim is false.

Both authorized exact stdin audits failed with exit 1, without timeout:

| Audit | Input SHA-256 | Elapsed |
|---|---|---:|
| 1 | `d67576cf54949582d25432adac6fc01df67c4455c931f79d4b925c1909b0ba2d` | 9.581s |
| 2 | `0801e2eb90f4fdc2f3328ef7a9ec6f2533d91eb147464ac474f01c09818ed8f2` | 9.933s |

No theorem is accepted from either failed run. Independent decoding and hashing confirmed both retained input/stdout/stderr receipts. Audit 2 reconstructs byte-for-byte from all 15 final source slices.

Violation: R80’s fixed outcome requires constructing the **existing R66 Incidence**, including its source-probe agreement, R45 owner/identity proofs, parameter recipe and successful witness. The repository proof-closure contract prohibits treating error-recovered declarations or conditional projections as parent closure.

Minimum closure evidence: repair the actual elaboration and finite computation failures without changing claims or inputs, then obtain a separately authorized successful exact-input audit with complete theorem types and acceptable transitive axiom reports. **No third audit is authorized in R80.** Close this sprint with the construction gate open.

## Complete available axiom census

Names are in `YulangClosure.ConstructedSourceIncidenceR80`. `P/Q` means `propext, Quot.sound`.

| Declaration | Audit 1 | Audit 2 |
|---|---|---|
| `primitive_records_derive_fields` | No axiom report | P/Q + `sorryAx` |
| `primitive_records_derive_source_probe` | P/Q + `sorryAx` | P/Q + `sorryAx` |
| `constructed_applies_r45` | P/Q + `sorryAx` + `Classical.choice` | P/Q |
| `bridged_target_in_collection` | P/Q | P/Q |
| `nonempty_successful_finite_witness` | P/Q + `sorryAx` | P/Q + `sorryAx` |
| `finite_permission_and_root_identity` | P/Q + `sorryAx` | P/Q + `sorryAx` |
| `local_global_and_shared_foreign_rejected` | P/Q + `sorryAx` | P/Q + `sorryAx` |
| `adversarial_inventories_rejected` | P/Q + `sorryAx` | P/Q + `sorryAx` |

The two clean audit-2 projections remain conditional: one takes an already inhabited `Constructed`; the other takes `BridgedConstructed` and R79 `OrderedRoots`. They supply neither construction success nor authenticated extraction.

## Construction and responsibility assessment

The candidate targets the cause: it joins independently computed source choice with native owner records. It does not introduce a replacement incidence relation.

At the statement level, the general derivations quantify arbitrary `S,T` with decidable equality and share one R77 choice, native records, source/fact inventories and original annotation/row coordinates. `construct` computes alignment and owner selection, reads records, and evaluates `PrimitiveRecords`; its caller supplies no `Incidence`, `Root`, successful `sourceProbe`, or global-selection success.

`PrimitiveRecords` retains the actual owner equations and identities rather than placing the desired Incidence conclusion in an assumption. This structure appears faithful to R45/R55/R65/R66, but the rejected proof terms do not establish it.

## Rust join assessment

Inspected `candidate_receiver.rs:4102–4585`, its choice constructor at `:2368–2600`, native incidence owner at `lib.rs:18320–18478`, and permission owner at `candidate_effect.rs:607–663`.

No new correctness defect found in the bounded join:

- Capture joins identical borrowed use, call, registration, origin, Lambda recipe and parameter recipe records.
- Name/use and Apply/checking coordinates remain separate.
- Owner/registration selection precedes Function or row-image comparisons; foreign registrations sharing those images cannot select the witness.
- Parameter-native-root observation remains separate from the registered Lambda root.
- Slot-0/slot-2 readers count all occurrence-key competitors before checking fact identity.
- Original permission annotation/row/concrete fields remain borrowed from the retained permission and are checked against scheduled and HIR annotation owners during round trips.
- Function argument-effect kind, polarity and original entry ordinal are checked.
- The choice is consumed in the existing capture and round-trip path.
- Failures return `None`/`false`; this path reads immutable owners and publishes no partially constructed projection.

Existing relevant tests were read, including suppression, foreign same-spelling operation, grouped scrutinee and unsupported-envelope controls. They were not run and do not certify the new join.

## Authentication and remaining gates

Matched nine unchanged baseline pins; the receiver matches the dispatched candidate hash. All 15 final source/slice hashes and the reconstructed audit-2 input match. The installed executable’s SHA matches both receipts.

Frozen artifacts:

- Receiver: `b1873abe5b88a3d6b750bf517d565b1ffcfc3a619f223243c19d00e9d15c0085`
- Lean module: `2d6f8c3a900ab2d37b86b415bbbcaef1bafa658f2092bf597691a2e6c1d933b4`
- Rust handoff: `b69e770e9f3885d5cb065d3d49fc5ae64e80ab936a71931faaf65da9222bf691`
- Proof handoff: `6e21ebb74356e37ff2dc092cac4b03de326c1b66338ede07f59308414ff9535a`
- Lean executable: `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`

**First blocker now:** accepted R80 Incidence construction and successful finite witness.

After that, R66 Root still requires `sameArtifact`, exact permission-entry/native-row agreement, and `BeforeAncestry` for actual physical/current-slot, admission, relation and source-root records. Authenticated Rust-to-Lean extraction, R79 `OrderedRoots`, physical/ancestry joins, Rust compilation/runtime, Lake import closure, original A/B, whole-language soundness/principality/termination and production remain open.

Reviewer stopped; review text frozen; no writes or further execution.
