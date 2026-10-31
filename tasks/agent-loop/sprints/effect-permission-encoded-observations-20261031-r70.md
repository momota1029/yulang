# R70 contract — encode the source-owned observation tables

Sprint `EFFECT-PERMISSION-ENCODED-OBSERVATIONS/20261031-R70`, revision 1. Status CANDIDATE until this contract and inputs are admitted by the primary. Baseline commit `6bbb11bc509a694a5ded1e0e49bcbd1305073c0e` on `origin/yulang3`.

## Original outcome and success evidence

Continue the unchanged research goal in `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1, 3, 5, with corrections in `notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6. Preserve the original supported source domain, all lawful finite Simple-sub histories, quantifiers, actual retained extrusion occurrences and polar pairs, and one shared description/evidence strategy. No semantic narrowing or production promotion.

R69 now constructs the R68 `Owner` from primitive mathematical observations, but its tables still begin with abstract `T` and `Component.identity : Nat`. R70 constructs an owner-scoped finite encoding from the corrected Rust `InventoryEndpointObservations`, then gives a Lean construction and lookup theorem for that exact finite representation.

**Rust fixed algorithm:** use the ordered R69 TermView rows as the Term identity table; they are already checked unique under full `Term` equality (brand plus index). A Term reference encodes to its table position, found through the exact equality-backed lookup. Build a separate ComponentId identity table in first-occurrence order from the owner component rows, using full `ComponentId` equality; repeated equal IDs reuse one token, unequal IDs never alias. Encode every TermView case, every nested child, component view, component row, and component-position association through those two tables. Preserve all list order and metadata, and keep Value/Effect representative vectors separate. Missing references or inconsistent repeated data fail as `BoundMismatch`; allocation failure remains `SearchLimit`. Do not use ordinal casts, hashes as identity, unchecked identity assumptions, or a supplied alternate table.

**Lean fixed algorithm:** define finite identity tables and an explicit first-occurrence encoding operation over equality-decided source identities. Construct encoded observations, children, component rows, positions, and representative vectors from those tables. Prove membership/lookup round trips, injectivity on distinct source identities, nested TermView payload/order preservation, exact encoded R69 validity, and decoding/qualified-read commutation. Compose with R69 construction, R68 endpoint decoding, R67 qualified lookup, and the same R66 slot-0/slot-2 selected reads. No independent interpreted inventory or blanket faithfulness law.

Success evidence: frozen source and Lean hashes; complete Lean theorem types and transitive axiom audit from the pinned Lean 4.35.0 stdin method; independent review of the actual identity algorithm, source field ownership, every nested TermView payload, namespace/order preservation, and the R69/R68/R67/R66 composition. This packet does not claim that Rust compiled or that the finite representation is serialized/authenticated by an actual native run.

## Accepted semantics and open gates

The correction from R69 source follow-up is part of this baseline: `InventoryPackage` reads its declared `value_row_representatives` and `effect_row_representatives` fields. Fresh R69 delta review passed this exact correction; Rust compilation remains unverified. R69's Lean proof remains conditional on its explicit successful construction/decode/read premises.

Actual native arena/store pointer identity, Rust-to-Lean execution correspondence, actual successful source-instance construction, original R66 `Root`, native failure/resource equivalence, original A/B, whole-language effect hygiene, soundness, principality, termination, and production remain OPEN. R70 changes no inference, routing, constraint generation, propagation, subtraction, permission consumption, or execution semantics.

Falsifiers: two Terms with equal arena-local indices but different brands must encode differently; the same full Term must reuse one token; two unequal ComponentIds must not alias; a missing nested Term or ComponentId must fail; variant/record/tuple/function payload order and metadata must survive; equal numeric Value/Effect ordinals remain in separate namespaces; reordered or stale source rows must reject; allocation failure must not become a semantic mismatch.

## Lanes and exact leases

- Rust author `/root/r70_rust`: `crates/yu-solver/src/candidate_receiver.rs`, `tasks/agent-loop/inbox/effect-permission-encoded-observations-r70-rust.md`. Implement only the private finite encoder and source checks. No compile/build/test/formatter.
- Constructive proof author `/root/r70_proof`: `notes/theory/lean/YulangClosure/EncodedOwnerObservationsR70.lean`, `tasks/agent-loop/inbox/effect-permission-encoded-observations-r70-proof.md`. Use pinned Lean 4.35.0 stdin `-j1 -M1024 --stdin`, retain complete types and transitive axiom audits.
- Read-only reviewer `/root/r70_review`: `tasks/agent-loop/inbox/effect-permission-encoded-observations-r70-review.md`. Start only after both authors STOPPED.

Only the primary edits central state, reviews/adjudicates, stages explicit files, commits and pushes. Workers cannot start subteams. No overlapping writers.

## Inputs, resources, and boundaries

Baseline and all direct dependency hashes are frozen in `effect-permission-encoded-observations-20261031-r70-inputs.json`; rehash before author edits. If any pin differs, stop before editing. Reuse the corrected R69 source, R69 Lean proof and source-fix review; R68/R67/R66/R65 are read-only dependencies.

Fresh bounded envelope: 6,000 seconds total: Rust 1,400; proof 2,200; review 1,200; primary 1,200 including 500 closeout. Astra 0. Same existing checkout only. No Cargo, Rust build, tests, formatter, Lake, cache, target, scratch, worktree, environment, dependency or configuration changes. No large captured output. Preserve 32 pending items and all UNKNOWN/quarantined rows/paths.

Stop at a missing equality owner, counterexample, material authority/dependency/lease boundary, exhausted budget, user STOP, or session end. Rust and proof may continue related in-scope steps within their exact files and fixed algorithm. Final review is independent; bounded PASS does not close the parent or production gates.
