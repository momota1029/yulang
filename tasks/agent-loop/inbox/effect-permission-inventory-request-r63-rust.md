# R63 Rust handoff — owner-derived source/native request package

Sprint: `EFFECT-PERMISSION-INVENTORY-REQUEST/20261031-R63`, revision 1.
Contract SHA-256: `5570818da03080050d0ac5b29474e84ae31084efd319555232e2250c6ac13a74`.
Admission SHA-256: `035bb7cd39c08468aae5c5f50dad402643145d69c56a9fa8e272da30030114be`.
Baseline supplied by Luna: `b32651e265d0184c8bff92cfe5511a56eca591cb`.
Assignment: `/root/r63_rust`; requested runtime `Luna/high`; observed model/effort: **UNKNOWN** (runtime metadata was unavailable to this worker). No descendants.

## Outcome

Added a private, fallible `InventoryPackage::capture` and its private owner query in `crates/yu-solver/src/candidate_receiver.rs`. It composes the existing R55 `SourceInternalProjection` and R57 `ProviderNativeContextProjection`, preserves owner-local indices alongside retained references, and materializes the complete projected source/native tables needed at this seam. It also constructs Internal, Entry, and Catch request records from the selected Internal use and provider certificate.

The source-call inventory is collected in its existing order. Each call record keeps its owner root, expression index, source occurrence, checking occurrence, and input reference. Extraction reads the owning local source at `(owner root, expression index)`, checks the source occurrence against the call's checking occurrence and HIR ownership, then uniquely joins the Internal use occurrence to that complete call table. The request keeps the selected definition-use index, caller/target roots, formal registration and lambda coordinates, source annotation and row keys, and raw entry effect.

The Entry request is tied to that same checked source call and retains the semantic Internal fact, raw entry row, `use_root` relation, and owner-local emission/admission indices. The Catch request keeps a separately indexed collected batch fact (local slot 51), catch and scrutinee occurrences, selected arm and provider-view indices, and separate raw/canonical input and output endpoints. The package's provider terminal is derived by the existing complete provider enumeration: `provider_entry_certificate` scans every view/member for the exact provider occurrence, declaration identity, and family; zero matches fail with `MissingProviderOrigin` and multiple matches fail with `AmbiguousProviderOrigin`. The package accepts no caller-supplied endpoint and snapshots both certified paths to that selected terminal while retaining the complete view table. Semantic-store facts and collected batch occurrences remain in separate package fields and index namespaces.

The package copies only indexed references and small scalar/endpoint records into fallibly reserved vectors. It does not cast pointers, serialize, dump solver state, or enter inference, forwarding, routing, subtraction, or execution. It has no call site in the inference path and establishes no cutover.

## Parent and source/native correspondence

The R62 path already selects the R55 Internal incidence before reading the physical Entry emission and then evaluates the existing ancestry path. This addition supplies the next source seam: the exact owning source-call coordinate and owner-derived R55/R57 inventory/request records that a Lean construction can relate to the same owner. It preserves raw entry/source coordinates independently from canonical native endpoints and keeps semantic and collected facts disjoint.

No Rust-to-Lean equality or parent theorem is claimed. The proof/source owner still needs to show that its typed primitive package is constructed from these same table entries and request coordinates, prove the exact reader/request equations used to instantiate R62, and identify the first remaining source/native premise. Successful outer `Run`, actual native execution of this package, arbitrary resource/failure correspondence, Simple-sub A/B, whole-program soundness/effects/principality/termination, full hygiene, and production remain OPEN.

## Prior evidence reused

- R62 closed as bounded research only. Its Rust change was confined to `candidate_context.rs`; R62 left `candidate_receiver.rs` unchanged. Its source-order handoff documents the existing physical emission/readback/admission checks, typed use-root/drain check, and unchanged ancestry order. R62 did not establish R55/R57 construction or Rust/Lean inventory equality.
- R62 Lean `InternalRootPolicyR62.lean` computes its Internal request from a supplied R55 `Source` and checks exact owner reads before its native Entry-root reader. R55/R57 define the primitive inventory and typed fact namespaces. These are the accepted finite consumers this package targets.
- The exact R62 Rust handoff hash `7cfa00da6b3aff81fdd06f17750017714d6681d1cc6bebf1a6e95185fdfca7c2`, R62 outcome hash `f8195a9ac73ad6eeb14e4c7f21a454cd8536201d59c66a9a7a19865667298b47`, and R62 review hash `113041f925ee3e13824d4eb2ded34903c23fa1e6ac96dcb4867a5d3a379177e5` were read. No Simple-sub bypass or withdrawn shortcut was used.

## Frozen inputs, diff, and checks

Before writing, all contract-named direct dependencies were rehashed. Contract and admission, all five Rust owner files, R39/R45/R47/R48/R49/R54/R55/R57/R58/R59/R60/R61/R62 Lean modules, and the R62 outcome/review matched their frozen pins. All read-only Rust/Lean/source-owner inputs were rehashed after implementation and still matched. The R62 Rust handoff also matched its recorded hash.

Exact leased changes:

- `crates/yu-solver/src/candidate_receiver.rs` — SHA-256 `3119ed33909f85ddbee5864b8f0e910ee65c69fdf3d056d600b95deab0cbf84a`.
- `tasks/agent-loop/inbox/effect-permission-inventory-request-r63-rust.md` — this handoff; its SHA-256 is recorded by Luna after freeze.

Inspection checks were limited to the frozen input hash audit, owner/projection/type reads, source-call and request join review, and final leased-file/hash review. No build, test, Cargo, formatter, Git operation, compiler/checker run, scratch, worktree, cache, target, environment, or generated output was created or run, as required by the packet. Compile and runtime behavior therefore remain unverified.

No other path was written. No disposable scratch path exists.

## Limits, falsifier, and next step

The extractor is private and reversible; the current inference path does not call it. A foreign owner, incomplete/duplicate inventory, mismatched source-call coordinate, wrong fact namespace, or request owner/call not selected by the existing native path must make extraction fail. The current construction reuses the pre-existing owner projection round-trip checks and adds the source-call and fact-index joins; its terminal comes from the complete provider enumeration, which rejects missing or competing provider members. A fresh reviewer should attack foreign sessions sharing a batch, equal indices in semantic/collected namespaces, missing competitors, multiple provider matches, wrong request owner, and raw/canonical Entry substitution.

Next in-envelope step: Luna and the proof owner should compare the frozen package fields and source-call/request equations against `RustInventoryRequestR63.lean`, then hand the frozen author artifacts to the separately leased fresh reviewer. This Rust worker's writes are stopped.

**Worker state: STOPPED — WRITES STOPPED.** No further edits are pending.
