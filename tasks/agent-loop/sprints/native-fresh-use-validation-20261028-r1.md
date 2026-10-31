# Sprint NATIVE-FRESH-USE-VALIDATION/r1 — validate native FreshUse reconstruction

Status: CANDIDATE until live primary admission and exact leases in `current.json`.
Branch / baseline: `yulang3` / `1d59e3acc`.
Source baseline: isolated review-admitted candidate from `bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d`; exact dependency hashes below.
Authority: unchanged user goal for Yulang inference/executor soundness and effect hygiene; `rules/goal-driven-sprints.md` SHA `e57c5c23e1956e09ea0da130a137ac50ce723ce5f0a90323adb17da88dab68b7`; `notes/design/2026-10-16-goal-driven-sprints.md` SHA `2dfeb555c913d3142078de535ee4b7f68e9a27f2b91a5f0bb82d4d867db4fc4e`; `notes/design/2026-10-11-yulang-inference-top-level-principles.md` SHA `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`; original source/native and effect-hygiene obligations below.

## Original outcome and success evidence

Original parent: `SourceProblem.InferenceSoundness` in `notes/theory/lean/YulangClosure/Contracts.lean:128` (SHA `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`) and its source/native/effect-hygiene instance obligations; original effect-hygiene root is documented by `notes/theory/lean/YulangClosure/OriginalEffectHygiene.lean` (SHA `926613078f1f3f2e197bff29793b120128f18d3676657af25db72eca47f2c89f`) and `notes/progress/2026-10-26-whole-metatheory.md` (SHA `242015bcca9ca9bb5bff038f26755a13dcc6defb555505b40be4a6b854392d43a`). Preserve the whole supported source domain, original scopes, dependent fields, shared witnesses, method selection and effect hygiene. The original parent and effect-hygiene theorem remain OPEN.

Bounded decisive premise: for the actual captured native `Graph`, rows, interner and successful `RetainedFreshUseMaps`, independently interpreting every represented node/map and validating native interner readback must imply that the returned root term is the interpretation of `graph.root`. This work does not prove every successful freshening run passes validation, source-to-Graph allocation authenticity, original whole-branch allocation correspondence, `H_u`, or the whole-language parent.

Implementation goal: add one `cfg(test)` validator in the isolated copy of `candidate_scheme.rs`. Compare the immutable captured Graph and actual interner `TermView`/row readback against an independent reconstruction over all seven Graph `Node` forms: Leaf, EffectOperand, Row, Function, Tuple, Record, Variant. Account for polarity, child order/sharing, dependent fields, effect operands and all relevant FreshUse maps (scope, scoped relations/context/use, attachment bundles, evidence and obligation rows). No opaque-success fallback; state precisely any unsupported field/case. The validator must not define reconstruction by reading `terms[graph.root]` and comparing it to itself.

Proof goal: in `YulangClosure.NativeFreshUseValidation`, define the complete native observation/interpreter independently of the retained root result and prove validator soundness for every represented Node/Map form, then apply it to the returned-root equation. Reuse scope lemmas only under their printed hypotheses. No axioms, `sorry`, `admit`, or checker bypass.

Success evidence:
1. Source handoff identifies exact Rust owners, field-by-field validator and mapping from captured constructors/readback to Lean definitions; reviewer confirms there is no circular `terms[root]` premise and no omitted accepted Node/map case hidden as success.
2. Lean checker accepts named theorem roots; report complete theorem types and transitive axiom audits. Parent application identifies precisely what the theorem supplies and its remaining source-authentication premise.
3. Focused Rust verification runs the validator on the existing admitted native cases and exercises mutations that change children, row/polarity, effect operand, scope or evidence map; each applicable corruption is rejected against unchanged graph/interner evidence. Preserve all prior assertions and expected-output fixtures.
4. Fresh independent review accepts the frozen Rust/Lean outputs and exact dependency hashes. Only this validator gate may be recorded as closed; all original parent, A/B, effect-hygiene, source/native and production gates stay OPEN unless separately proved.

Known limits: the previous selected-module proof established only two scope lemmas and identified the missing complete Node/FreshUse interpretation. Existing `Shape` and live-capture modules omit cases and cannot discharge this gate. Existing effect-permission source-observation attempts still leave ordinary-source unequal row transport and full native extraction open. `H_u` is AUTHORITY_BLOCKED. Do not retry those failed tests/Lean invocations without a new exact target and preserve all failure artifacts.

## Two continuing lanes

Rust implementation owner: registered `implementer`, Luna/high. Write only the copied isolated `candidate_scheme.rs` and `tasks/agent-loop/inbox/native-fresh-use-validation-rust.md`. Do not touch the frozen reviewed source or shared root candidate files. Complete implementation and its handoff; primary alone owns builds/Cargo/Lean verification.

Proof owner: registered `lean_prover`, Sol/high. Write only `notes/theory/lean/YulangClosure/NativeFreshUseValidation.lean` and `tasks/agent-loop/inbox/native-fresh-use-validation-proof.md`. The proof lane may use multiple related stages within its envelope. No child dispatch.

Fresh independent reviewer: primary assigns after source/proof freeze; reviewer writes only `tasks/agent-loop/inbox/native-fresh-use-validation-review.md`, no tests/build/Cargo/Lean/Git.

No Astra assignment. Production code, semantic changes, expected-output edits, module Name semantics, F5/cutover, global scope changes, and any new source owner are outside this contract.

## Pinned inputs

The review-admitted source snapshot is under `isolated/selected-module-entry-freshening-repair-r1`, based on `bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d`. Luna creates a clean new isolated workspace from that base and overlays only these three pinned candidate files. The old worktree and its frozen review target remain immutable.

- `crates/yu-solver/src/candidate_scheme.rs`: `33235b840c42be38be1df634291e309c0d143fa62f412afa633768be9b40aa0e`
- `crates/yu-solver/src/candidate_effect.rs`: `8d80a98b4fe22bd91409b645dbac3d5bcd10eed4b45bbe6f5c17a773e65874f6`
- `crates/yu-solver/src/shadow_apply.rs`: `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`
- `crates/yu-solver/src/term.rs`: `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1`
- `crates/yu-solver/src/candidate_context.rs`: `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e`
- `crates/yu-solver/src/candidate_source.rs`: `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`
- `crates/yu-solver/src/lib.rs`: `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`
- workspace `Cargo.toml`: `a8852982d5a3ff4d159aa546767b217000d50c9ff8617ac139700885bf5b090a`
- workspace `Cargo.lock`: `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5`
- `crates/yu-solver/Cargo.toml`: `aaf341e14643b73668552a3bf499f6410bdd0e9ad6ebeea1a5d6ef454d9494ed`
- Lean `NativeFreshScopeTransport.lean`: `1827358830b331ea6c4eafccf83279a1294a3df5b889405cf27ee2f95ff49df5`
- Lean `NativeScopeTransformer.lean`: `68f37763bcaab831ec6248a28144e7b76ede42b7813681850f7c67b0d8df10f6`
- Lean `lean-toolchain`: `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` (Lean 4.35.0)
- Lean `lakefile.toml`: `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4`
- Lean `lake-manifest.json`: `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3`
- Lean `README.md`: `8d27e0b90fc04eb8a0a30606a857e564e5269e8e33e72fddbf1190cb6a7072e3`
- governed original Lean roots: `Contracts.lean` SHA `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`; `OriginalEffectHygiene.lean` SHA `926613078f1f3f2e197bff29793b120128f18d3676657af25db72eca47f2c89f`.

Any additional source/dependency or changed pin returns to Luna before use/write. Candidate sources and proof outputs are research-only; no promotion to production.

## Exact leases and resources

- Rust write: `isolated/native-fresh-use-validation-r1/crates/yu-solver/src/candidate_scheme.rs` only.
- Rust handoff write: `tasks/agent-loop/inbox/native-fresh-use-validation-rust.md` only.
- Lean write: `notes/theory/lean/YulangClosure/NativeFreshUseValidation.lean` only.
- Lean handoff write: `tasks/agent-loop/inbox/native-fresh-use-validation-proof.md` only.
- Review write (after frozen review assignment): `tasks/agent-loop/inbox/native-fresh-use-validation-review.md` only.
- Verification build/cache: primary only, `isolated/native-fresh-use-validation-r1/target` and `notes/theory/lean/.task-tmp-native-fresh-use-validation-r1`; preserve the existing frozen Rust and Lean build paths.
- Sprint contract/current state and final evidence: Luna only.

Envelope 2,600 seconds, charged in full on admission: Rust 500s; proof 1,000s; review 600s; primary verification/integration 300s; contingency 200s (not preauthorized for producers). Two producer assignments, zero Astra. One heavy Cargo process and one Lean process at a time; Cargo at most 2 invocations, aggregate 180s, one CPU and 2 GiB RSS cap; Lean at most 2 invocations, aggregate 240s, `-j1 -M1024`; stop before any cap. One assigned verification owner (primary), fresh independent review only after frozen outputs.

Stop when the validator/theorem outcome and review close; on an exact missing field/constructor, report it without inventing an interpretation. After two materially different proof methods fail at the same premise, change method/inputs/owner or stop with exact blocker. Keep original parent/effect hygiene OPEN. Unknown workers retain leases/resources; user STOP/session end requires real cancellation receipt.

## Frozen review and integration

Review complete source and proof deltas against the exact pinned snapshot, including all validator branches/mutations and Lean theorem hypotheses/types/axioms. Reviewer must be independent of both producers and inspect sources before handoff explanations. Luna adjudicates; no self-certification. Primary applies proven theorem to the original parent and records the exact remaining source/native construction/authenticity premise.

At successful review, run only the contract-authorized focused checks, preserve full argv, stdout/stderr, resource measurements and hashes in the leased verification outputs, update `current.json` and a unique outcome receipt, inspect every commit in the outbound range, then commit/push the coherent checkpoint by Luna. Do not stage unrelated source, Lean, task artifacts, target outputs, UNKNOWN paths or quarantined writer files.
