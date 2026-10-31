# R68 contract — source-owned semantic fact endpoints

Sprint: `EFFECT-PERMISSION-ENDPOINT-INTERPRETATION/20261031-R68`, revision 1.
Baseline: pushed `9bac816c440ca0b64fdc99ae3bd52c99fbdcaa98` on `origin/yulang3`.

## Objective and fixed outcome

Continue the user's unchanged Rust/Lean effect-hygiene goal. Close R67's first
actual source gap: construct each occurrence-qualified R65 `FactRow` endpoint
from the `SemanticFact`'s borrowed Terms and the same owning `InferenceSession`.
Then connect that checked decoder to R67's complete ordered fact/provenance
tables and selected R66 slot-0 Internal / slot-2 Lambda reads.

The Rust decoder must interpret raw lower with positive polarity and raw upper
with negative polarity, and compute canonical endpoints from the current
owner state. Preserve Term arena identity, effect/value namespaces, every fact
and provenance row, table order, identity, occurrence, slot, and indices. Use
checked `TermView`, component-position, representative, and index reads. No
partial accessor may panic on an invalid or foreign record. Preserve allocation
and checked-conversion failures as `SearchLimit`; report unsupported/mismatched
source rows through the existing private gap channel. Never omit a row or turn
unavailability into an empty inventory.

The constructive Lean artifact must state the exact primitive owner data used
by the decoder, define the matching finite endpoint interpretation, prove its
branch/coordinate/canonicalization equations, and compose that result with R67
lookup commutation and the R66 slot-0/slot-2 witnesses. No supplied
`FaithfulExtraction`, universal endpoint axiom, or independently mirrored
inventory may stand in for the decoder. If a required owner coordinate or
polarity rule is absent, freeze at that exact premise and leave source
correspondence OPEN.

## Required adversarial cases

Review nontrivial canonical row representatives; equal value/effect ordinals
in distinct namespaces; wrong-polarity live variables; missing/out-of-range
component positions; foreign or unavailable Terms; all positive/negative
function, record, tuple and variant views; effect bottom/empty leaves; repeated
FactIds at distinct occurrences; duplicate same-key edges; missing competitors;
and preservation of `SearchLimit`. A Lambda Function fact must remain a value
endpoint. All previously supported source forms and the original A/B claims
remain unchanged.

## Exact leases

- Rust author `/root/r68_rust`: `crates/yu-solver/src/candidate_receiver.rs` and
  `tasks/agent-loop/inbox/effect-permission-endpoint-interpretation-r68-rust.md`.
- Constructive proof author `/root/r68_proof`:
  `notes/theory/lean/YulangClosure/SemanticFactEndpointInterpretationR68.lean`
  and `tasks/agent-loop/inbox/effect-permission-endpoint-interpretation-r68-proof.md`.
- Fresh read-only reviewer `/root/r68_review`:
  `tasks/agent-loop/inbox/effect-permission-endpoint-interpretation-r68-review.md`.

Only the primary changes `current.json`, sprint/admission/launch/outcome records,
and stages/commits/pushes explicit reviewed paths. Supporting files below are
read-only. No overlapping writers; no worker starts another team.

## Immutable inputs

- `crates/yu-solver/src/candidate_receiver.rs`:
  `f5e7a845cb650b309ff36face7ba44ab2b48e828db67221637c3015f9881658c`.
- `crates/yu-solver/src/lib.rs`:
  `25498cc1be404b12d060cbd47f77e78c23ad27b2b99113e15823bc8b6fa92ca4`.
- `crates/yu-solver/src/candidate_context.rs`:
  `962af7c44b2e57ba50b7738e82785bd68b517e881ba08ea41c544c9314d60021`.
- `crates/yu-hir/src/module.rs`:
  `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646`.
- `crates/yu-solver/src/term.rs`:
  `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1`.
- R65 `OccurrenceQualifiedFactReadersR65.lean`:
  `3253e00f9b523446363507ae39567bab0a4ca69a2fc84cc128f8952c43bb700b`.
- R66 `OccurrenceQualifiedConsumerR66.lean`:
  `5db5ad3f3f5e5803e2bc564fc8922d5eb8a72182c7ba11de3904eebd7b5950e1`.
- R67 `BorrowedQualifiedReadReificationR67.lean`:
  `4b40cc5f1e832eaac226235d7c9c8a974bd3c6b895fa2d9fab7051d3271ee4e1`.
- R67 proof handoff:
  `ee4bc812c85e76de7ee1aa673e89471e3c6eb5ce57d1787ca94e590059d4850f`.
- R67 revision-2 independent review:
  `9f2dfe25a1566d99fbcaf818588c89a95a5e8a931710cc2b1bce0628198d883b`.
- R67 outcome:
  `f49d599f73fc8dbe80a7de64a28f13eabfea57d65b7bf28c7dfbd51716df9903`.
- Top-level inference principles:
  `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`.
- Effect-hygiene integration:
  `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`.

Before editing, each author verifies their leased source and all direct inputs.
If any pin differs, stop before source work and report it.

## Verification, resource cap, and limits

Fresh total cap: **6,000 seconds** — Rust 1,400; proof 2,200; independent
review 1,200; primary 1,200 including 500 for closeout; Astra 0. Use the
existing checkout and pinned Lean 4.35.0 stdin audit (`-j1 -M1024 --stdin`),
retaining complete theorem types and per-root transitive axiom reports. Run
`git diff --check` on exact leased paths. No Rust build, Cargo, tests,
formatter, Lake, target, cache, scratch, new worktree, environment, dependency
or configuration change is authorized. The user did not request tests.

Fresh review must inspect source construction before accepting the Lean
composition and report exact remaining premises. A green proof, bounded PASS,
or owner-local reifier does not close the original A/B theorem, whole-language
effects, actual native Runs, full source/native correspondence, production, or
any termination/principality/soundness gate.
