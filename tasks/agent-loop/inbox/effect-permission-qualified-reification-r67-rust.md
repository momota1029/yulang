# R67 Rust handoff — borrowed qualified fact reification

Sprint `EFFECT-PERMISSION-QUALIFIED-REIFICATION/20261031-R67`, contract
revision 1, SHA-256
`bc04c56942bd1078c9415fdac5cf4c11001948255fcfd8f4473aa81f5098211f`.
Assignment `/root/r67_rust`, handoff revision 2. Prior frozen handoff revision 1
SHA-256: `4c52c08ac16047f82a31656491c1c8b5cf2b2b295bc06d7020cb5f906dfea327`.
Parent: unchanged
Simple-sub/effect-hygiene obligation and source domain; no claim or permission
semantics changed. Baseline HEAD named by the contract:
`5ca4363b55ae2637b6858406fd85cce96bca28cc`.

## Runtime, leases, and inputs

Role requested: implementer, `gpt-6-luna`/high. Effective model, effort,
session launch receipt, elapsed assignment time, and remaining assignment time
were not exposed in this child runtime and remain UNKNOWN. No descendants.
Exact write leases used: `crates/yu-solver/src/candidate_receiver.rs` and this
handoff only.

The contract and every listed direct dependency were rehashed before the source
edit and at freeze. All hashes matched the frozen contract:

- Contract: `bc04c56942bd1078c9415fdac5cf4c11001948255fcfd8f4473aa81f5098211f`.
- `candidate_receiver.rs` frozen baseline: `253c0e469b91a30580a65ec57569a20ed7ad53fd7d7e82c0dc7d2e71102fad1a`.
- `lib.rs`: `25498cc1be404b12d060cbd47f77e78c23ad27b2b99113e15823bc8b6fa92ca4`.
- `candidate_context.rs`: `962af7c44b2e57ba50b7738e82785bd68b517e881ba08ea41c544c9314d60021`.
- `yu-hir/src/module.rs`: `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646`.
- `term.rs`: `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1`.
- R65 `OccurrenceQualifiedFactReadersR65.lean`:
  `3253e00f9b523446363507ae39567bab0a4ca69a2fc84cc128f8952c43bb700b`.
- R66 `OccurrenceQualifiedConsumerR66.lean`:
  `5db5ad3f3f5e5803e2bc564fc8922d5eb8a72182c7ba11de3904eebd7b5950e1`.
- R66 Rust handoff: `540f0ed4d616824f53860aa5b460a26953c129f0d409324e14361c39af0db787`.
- R66 proof handoff: `2d8c38878553713b475e32c6846be8a1c05a6b63d3345db1a851eb6660112039`.
- R66 review: `ac56e01d6ec413a96d12fc0f3b4664f8a926d0c55196886dd884aa7569c4534b`.
- R66 outcome: `24e41d60e902cad84ff4c56fb1edeb34c6975199d910a8af1596efd72c7f8c5e`.
- Top-level inference principles, `notes/design/2026-10-11-yulang-inference-top-level-principles.md`:
  `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`.
- Effect-hygiene integration, `notes/design/2026-10-10-annotation-effect-hygiene-integration.md`:
  `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`.

## Outcome and exact source correspondence

Added a private finite `InventoryQualifiedReification` built from the actual
borrowed `InventoryPackage.semantic_facts` and `.provenance` rows. It retains
the complete fact and edge slices in their original order, and adds one
reified borrowed edge per provenance row. Each edge keeps its original edge
index, resolved fact index and `FactId`, exact occurrence coordinate, slot,
borrowed records, and the original lower/upper `Term` values. Repeated FactIds
on distinct edges remain distinct records.

Occurrence coordinates use first appearance in provenance order and exact
`HirOccurrenceId` equality. The source definition at `yu-hir/src/module.rs`
implements equality with both ordinal equality and `Arc::ptr_eq` on the
artifact token. Reification validates the occurrence with the package's own
`ConstraintStore::require_owned` before assigning or comparing a local
coordinate. It uses checked `u32`/`usize` conversions, reserves output vectors
before insertion, and rejects noncontiguous owner indices, fact-index/identity
mismatch, dangling edges, and duplicate exact `(occurrence, slot)` keys through
the existing private `CurrentEmissionGap` channel.

`InventoryInternalRootView` now obtains its slot-0 Internal and slot-2 Lambda
rows through this reifier. The selected rows are still cross-checked against
the existing borrowed `InventoryAdmittedFact` records and exact selected
`SemanticFact` pointers. This is an owner-local source/fact/provenance
contribution feeding the R66 read view. It does not enter ordinary inference,
permission consumption, routing, propagation, subtraction, or execution.

Revision 2 preserves reification failures through the capture boundary. The
exact path is `InventoryPackage::capture` → `package.internal_root_view()?` →
`internal_root_view` → `reify_qualified_facts()?`. Thus a `SearchLimit` caused
by allocation or checked index conversion remains `SearchLimit` to the caller.
The subsequent borrowed root-view structural checks still return `Option`; an
unavailable or inconsistent package/root is mapped to `BoundMismatch` by
`internal_root_view` only after reification succeeds. The earlier
`.ok()?`-to-`Option` erasure is removed.

**Exact unresolved owner conversion:** `lib.rs::SemanticFact` stores only
`FactId`, `lower: Term`, and `upper: Term` (around line 3348); its accessors
expose only those fields. `term.rs::Term` is opaque and `TermView` exposes term
shape and children, not the four R57/R65 `Endpoint` fields. No inspected
`SemanticFact`, `ProvenanceEdge`, or owner accessor supplies per-fact
`rawLower`, `rawUpper`, `canonicalLower`, and `canonicalUpper` coordinates.
Package-wide `raw_lower`/`canonical_lower` and `raw_upper`/`canonical_upper`
are not tied to each semantic fact and cannot justify those fields. Therefore
the Rust reifier retains the original Term endpoints but does not fabricate the
R65 endpoint projection. Rust-to-Lean `FactRow` correspondence and the full
R66 selected-row agreement remain OPEN at this exact source-owner premise.

## Diff, checks, and limits

- Modified: `crates/yu-solver/src/candidate_receiver.rs`.
- Added: this handoff.
- No other paths, scratch files, caches, build outputs, targets, worktrees,
  environment changes, or generated files were created.
- Manual inspection covered the reifier, its `InventoryInternalRootView`
  call sites, `SemanticFact`, `TermView`, and `HirOccurrenceId` equality.
- No Cargo/build/test/formatter, Git command, or generated-output command was
  run, as prohibited by this assignment. Compile behavior remains unchecked.
- Final source SHA-256 at handoff preparation:
  `f5e7a845cb650b309ff36face7ba44ab2b48e828db67221637c3015f9881658c`.
- Frozen handoff SHA-256 is reported with the STOPPED receipt; the handoff
  content does not embed its own digest.
- Budget spent/remaining: UNKNOWN; no assignment timer telemetry was available.

## Reused evidence, open premise, and next step

Reused R65's occurrence/slot reader and R66's owner-derived Internal/root
view, plus the actual source accessors and equality implementations listed
above. No Simple-sub shortcut was restored. The Lean lane was informed of the
first-appearance occurrence enumeration, complete fact/edge order, repeated
FactId behavior, and the endpoint mapping boundary.

Next related step within the sprint: Luna/source owner identifies whether an
existing authoritative owner can map each `SemanticFact` to its four raw and
canonical `Endpoint` coordinates while retaining term distinctions. If none
exists, keep endpoint agreement OPEN and send that exact owner TODO through
Luna's frozen cross-lane handoff. No production cutover follows from this
partial reifier.

Worker state: STOPPED; WRITES STOPPED. No descendants or scratch leases remain.
