# R278 — Backward public-entry guard analysis

Status: CANDIDATE until Luna's pin gate and explicit stage-1 GO.
Revision: 1
Original goal: inference/effects soundness → R70 → R71 canonical-fiber coverage.
Original parent, source domain, quantifiers, accepted semantics and A/B claims are unchanged. Parent/A/B remains 0→0; `Need_D`, R71 and full soundness remain OPEN. Implementation remains `NO_SAFE_CODE_SLICE`.

## Outcome and fixed evidence

Determine whether the existing authenticated public `assemble` entry admits the proposed carrier shape, by working backward from its guards. Treat the prior one-module-root/local-binding shape only as a hypothesis. Do not accept it from R271/R272 prose and do not claim that the fixed 87-byte source actually lowers to it unless production source equations establish that edge.

Stage 1, Sol/300 seconds: independently derive the necessary admission conditions from the authenticated R277-E001 payload, then prove or refute this conditional: **if production lowering returns one root Binding `outer` whose carrier contains the proposed nested local bindings, `assemble` cannot admit that pair.** Identify the exact first incompatible guard and value. Use only R277-E001 and directly pinned evidence already needed to state the conditional; do not reconstruct all fourteen slots, complete tokenization, a candidate prefix, or external callers.

Stage 2, Sol/600 seconds, requires a separate Luna GO: only after stage 1 identifies the exact structural fact sufficient for the incompatibility, Luna may prepare an exact indexed production-source view for the minimum owner set needed to justify or falsify the source-to-shape implication. Include the full production definition and directly required helpers for any admitted owner. `scan_trivia_part` at `crates/yu-syntax/src/lexical/lexer.rs` may be included only if stage 1 establishes it is needed; its inventory SHA-256 is `620f91d99cd4b0bd320315398466cbbec2ed625b8a8ebc6ba07f84d0c97524d1`. No broad lexer reads. If the source bridge cannot be justified within exact owner coverage, state the missing edge and stop without actual-witness rejection.

Possible conclusions:

1. `CONDITIONAL_GUARD_INCOMPATIBILITY`: the guard condition and incompatibility are independently derived, but source production of the hypothesized carrier is not established.
2. `SOURCE_QUALIFIED_GUARD_REJECTION`: only if the exact source-to-shape implication is independently justified from admitted production owners and the fixed witness reaches this API argument; name the first actual failed guard.
3. `UNRESOLVED`: exact owner or implication remains missing. Distinguish parse/lowering exit from `assemble` rejection.

Any rejection excludes only this fixed witness from this public experiment. It does not reject ordinary source, establish global unreachability, or refute soundness. No existing production caller is required.

## Immutable inputs

R277-r2 contract: `tasks/agent-loop/sprints/public-entry-admission-r277-r2.md`, SHA-256 `952973eb7a61e2b0e9866eb54382eceead68956c4eda97cbf723721f6f23fd33`.
R277-r2 STOP: `tasks/agent-loop/history/20261103-r277-r2-stop.md`, SHA-256 `cdf5921f2bd763728d01257a3d0b1ba93f8d5ef22625e5ca5c1e3b3c9685ee37`.
R277 source view: `tasks/agent-loop/sprints/public-entry-admission-r277-source-view.txt`, SHA-256 `ebeae02540be5811850017b6f8b7ff49783a95e17d2b05358a155bd47bb22b21`.
R277 byte index: `tasks/agent-loop/sprints/public-entry-admission-r277-view-index.json`, SHA-256 `8fb7a74c4953d0f78e04f321f437432bbdb9baae811027c555854ade06bfa0da`.
R277 range map: `tasks/agent-loop/sprints/public-entry-admission-r277-ranges.json`, SHA-256 `63f2ce9d1ffb2e14a497d89b928065edd955f3ecd2266b0eb51f670fabd4e855`.
R273 source inventory: `tasks/agent-loop/sprints/source-successful-consumer-r273-inputs.json`, SHA-256 `42040552635bb7c2652eb0bad68cb46295078d03ae70620b7edd555d3883fa5f` (229 entries). This is an authority for deriving exact in-inventory paths and hashes, not permission to open unselected bodies.

Stage-1 reading is limited to R277-E001, exactly `candidate_receiver.rs:2921–3179`, and necessary metadata/locators in the pinned index/range map. Do not open R271/R272 producer bodies as evidence. Do not read test bodies. Recheck all pins sequentially before displaying a technical payload. Stage-2 source view has no authority until a separate exact contract extension and GO.

## Method, lanes and exclusions

Proof lane: Sol `/root/sol_r274_source_acceptance`, requested `gpt-6-sol/high`; first derive guards by inversion, then identify the minimal source invariant needed to apply the conditional. Sol may continue the related stage-2 bridge only after a separate GO. Fresh reviewer must not be a coauthor.

Implementation lane: no approved code slice. No source edits or semantic changes. Keep `NO_SAFE_CODE_SLICE`.

No tests, builds, probes, Cargo, Lean, runtime execution, fixture substitution, private-constructor bypass, caller search, external paths, generated/scratch/cache outputs, descendants, or production promotion. Do not alter prior frozen artifacts or either R277 STOP record.

## Leases, resources and review

Stage-1 Sol outputs, leased only after GO:
- `notes/theory/2026-11-03-public-entry-guard-incompatibility-r278.md`
- `tasks/agent-loop/inbox/public-entry-guard-incompatibility-r278.md`

Luna owns this contract, exact source-view preparation if justified, `current.json`, GO/resume records, adjudication, review assignment and Git. Sol writes only the two output paths. Stage 2 is not authorized by stage-1 GO and receives no source-view lease until a separate exact extension is pinned and approved by Luna.

Envelope: 1,800 seconds total: Sol stage 1 300; Sol stage 2 at most 600 under separate GO; fresh independent review 600 after freeze; Luna preparation/adjudication 300. Charge full reservations when issued; no reset/refund. Sol has 11,100 seconds cumulative R277 charge; a full stage-1 grant raises it to 11,400. Reviewer identity is selected by Luna after freeze. Stop at an exact guard result, genuine owner obstruction, budget or user STOP. Consult the dispatcher after the reviewed guard/application result or a genuine source-owner obstruction.

Review must distinguish (a) independently checked guard conditions, (b) conditional carrier incompatibility, and (c) a justified source-to-shape application. It must inspect frozen outputs only after source-first reconstruction and stop if pins or owner boundaries fail.

## Parent application and remaining premises

This packet targets a public-entry feasibility question only. Even `SOURCE_QUALIFIED_GUARD_REJECTION` applies to this witness and route alone; it supplies no accepted-source counterexample and discharges none of Parent/A/B, `Need_D`, R70, R71, F1/FK1 or foreign-continuation obligations. No result is promoted to a theorem or production gate without the original parent application and its separate review.
