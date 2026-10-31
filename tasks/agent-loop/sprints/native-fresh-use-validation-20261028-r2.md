# Sprint NATIVE-FRESH-USE-VALIDATION/r2 — constructor-directed FreshUse validation

Status: CANDIDATE until Luna records live admission and exact leases in `tasks/agent-loop/current.json`.
Branch / current primary baseline: `yulang3` / `1d59e3acc`.
Research source baseline: `bc2a0836ec8fc9dee6a1094552a3dd34cfbcfd0d`, overlaid only with the three review-admitted candidate owners listed below. r1 outputs remain frozen partial evidence and are not copied into this candidate.
Authority: unchanged user goal for Yulang inference/executor soundness and effect hygiene. This sprint is limited to a research-only native validation gate; it grants no production change, source-semantic change, expected-output edit, H_u authority, or parent closure.

## Fixed outcome

Establish whether the admitted native construction/readback interfaces support an independent, complete FreshUse validation recipe. Inspect and model the real owners for fresh allocation, effect payload copying and context renaming. Implement the recipe and its Lean soundness argument only for fields that can be authenticated from the pinned interfaces. If a necessary field has no authentic observation, return the exact field/owner and `NO_SAFE_CODE_SLICE` for complete validation; preserve any structural partial checker only behind an explicitly partial result that cannot report success.

The decisive statement is conditional on the actual captured `Graph`, actual fresh allocation/remapping outputs, actual interner readback, and actual retained FreshUse maps. The validator must reject changed or missing map entries against unchanged construction/readback evidence. No self-consistent supplied snapshot, opaque-success branch, or equality premise that restates the desired root image may serve as authentication.

Cover all seven `Graph::Node` forms, 13 atoms, exact row/effect-operand key domains, child order/sharing, polarity, dependent record/variant fields, and all retained maps: scope regions/scopes/inputs, scoped relations/demands, context-use/context-remap, bundle-remap, evidence-remap, terms, effect operands, and source obligation row indices. In particular account for fresh `Contribution.instance`, copied `View.source_weight`/`closed_weight`/tail, and dependent `Context` weight remapping; explicitly reject if these cannot be related to authenticated native allocation/readback.

## r1 adjudication and inherited scope

r1 outcome `tasks/agent-loop/history/native-fresh-use-validation-20261028-r1-outcome.md` is CLOSED_INCOMPLETE. Its Rust success validator was independently rejected because unsupported scoped/context maps and weight fields can silently pass, map domains/fresh images are incomplete, provenance syntax is suspect, and required mutation falsifiers are absent. Its Lean source is unchecked partial research. Preserve those exact artifacts and hashes; do not treat r1's claims or code as accepted evidence. The original `SourceProblem.InferenceSoundness` quantifiers, source/native correspondence, shared witnesses and effect-hygiene theorem remain OPEN; `H_u` remains AUTHORITY_BLOCKED.

## Pinned source inputs

Use only these already authorized hashes from r1's authenticated source snapshot:

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
- governed parent `Contracts.lean`: `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`
- governed `OriginalEffectHygiene.lean`: `926613078f1f3f2e197bff29793b120128f18d3676657af25db72eca47f2c89f`

Any new dependency/owner or changed pin returns to Luna before use. Primary prepares a clean isolated r2 workspace from the pinned base and source overlays before producer work. Frozen r1 paths remain immutable.

## Exact outputs and leases

- Rust implementation, requested implementer Luna/high: `isolated/native-fresh-use-validation-r2/crates/yu-solver/src/candidate_scheme.rs` only.
- Rust handoff: `tasks/agent-loop/inbox/native-fresh-use-validation-r2-rust.md` only.
- Lean proof, requested lean_prover Sol/high: `notes/theory/lean/YulangClosure/NativeFreshUseValidationR2.lean` only.
- Lean handoff: `tasks/agent-loop/inbox/native-fresh-use-validation-r2-proof.md` only.
- Fresh review after frozen outputs: `tasks/agent-loop/inbox/native-fresh-use-validation-r2-review.md` only.
- Primary-only Rust verification cache: `isolated/native-fresh-use-validation-r2/target`.
- Primary-only Lean scratch/build cache: `notes/theory/lean/.task-tmp-native-fresh-use-validation-r2`.
- Luna owns contract/current/outcome and Git integration. No child dispatch.

Workers must ACK the contract hash, requested/observed model+effort, exact write lease, active status and estimated remaining time before source-body work. Observed metadata unavailable at runtime remains UNKNOWN. Freeze all authored bytes before assigning a fresh reviewer; reviewer reads source before handoffs and runs no executable checks.

## Required evidence and close conditions

1. Rust handoff maps every validator success path to the actual constructors/allocation and readback; unsupported fields cannot return success. Validate exact map key domains, fresh target identities, dependent payload transformations and shared witnesses.
2. Mutation falsifiers alter/delete each applicable child, row/polarity, effect operand, scope, relation/demand, context-use/remap, weight/payload, bundle, evidence and obligation-map entry while leaving captured construction/interner evidence unchanged; every applicable corruption rejects.
3. Lean states the complete authenticated recipe independently of returned `terms[root]`, proves its soundness under printed hypotheses, and applies it to the actual return site without assuming the desired root image. Primary reports full theorem types and transitive axiom audits only after pinned Lean 4.35.0 checking.
4. Fresh independent review accepts frozen source and proof deltas against exact dependency hashes and confirms unsupported cases fail closed. Only this bounded validator gate may close. Parent/source/native/effect-hygiene/production gates stay OPEN unless independently proved.
5. If the first missing native field/owner cannot be authenticated with the exact pinned interfaces, stop at that field and record `NO_SAFE_CODE_SLICE`; do not keep a nominal success validator or manufacture equalities.

## Resources

Envelope 2,600 seconds: Rust 500s; proof 1,000s; fresh reviewer 600s; primary verification/integration 300s; contingency 200s (not preauthorized for producers). Two producers, zero Astra. At most two Cargo attempts, aggregate 180s and 2 GiB RSS, one CPU; at most two Lean attempts, aggregate 240s with `-j1 -M1024`. One heavy check process at a time. Stop before any cap. No executable check until frozen review accepts the exact candidate; preserve full argv, stdout/stderr, runtime/RSS and hashes if checks become authorized.

At close, record actual worker receipts, exact remaining obligations, unique outcome hash and compact state. Never stage unrelated or quarantined paths. Commit/push only an explicitly reviewed coherent checkpoint by Luna after inspecting the entire outbound range. The whole inference/soundness goal remains active beyond this sprint.
