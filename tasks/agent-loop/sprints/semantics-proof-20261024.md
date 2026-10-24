# Yulang semantics and soundness reconstruction, 2026-10-24

Status: active research contract; no semantic adoption or parent closure.
Baseline: 424566114, isolated branch research/semantics-proof-20261024.
User scope: write the complete Yulang type-soundness and semantics account in docs/ and notes/theory/; exclude implementation; use only Astra for child assignments. This explicit scope overrides ordinary Luna/Sol routing and the implementation lane. Requested model identities are not observed execution metadata.

## Original objective and evidence

For every finite well-formed Yulang source derivation in the original approved source domain, construct its declarative operational meaning and prove value preservation/progress, effect inclusion at immediate/latent/reentry ports, receiver-relative protection, scoped release, and typed shallow resumption. Keep original Simple-sub A/B, principality and algorithm correctness obligations: a safe declarative candidate does not discharge them. Compiler changes, builds and runtime tests are excluded. Existing candidate policy and missing surface clauses are mathematical/semantic gaps, not implementation-only work.

The first outcome is an explicit corrected-machine abstraction/simulation argument, including hidden witnesses, current release state and repeated resumption, directly applied to the existing source theorem; independently audit coverage and any obstruction. No assumption of a ready-made sound abstraction is permitted. A genuine counterexample must be retained, never repaired by quietly restricting the source language.

## Isolation and ownership

Original checkout contains another session's current.json and R149 work. Its workers and three legacy reservations are UNKNOWN from this session; collaboration.list_agents exposes only this root, which does not prove cessation in other sessions. Do not edit, reclaim or merge into those paths. All new writes occur in this isolated worktree. Only this primary mutates this worktree's Git and scheduling files. No compiler/source/test/expectation changes.

Primary exact leases: this contract; tasks/agent-loop/current.json; tasks/agent-loop/sprints/semantics-proof-20261024-outcome.md; docs/yulang-semantics-and-soundness-ja.md; docs/yulang-proof-index-ja.md; notes/theory/2026-10-24-surface-elaboration-closure.md.
Producer exact lease: notes/theory/2026-10-24-corrected-machine-simulation.md. A final message supplies the single handoff (no additional file). Old manuscripts are frozen read inputs, not leased writes.

## Work and review

Astra dispatcher /root/astra_semantics_direction has returned read-only direction. Its packet budget was 120 seconds. The corrected-machine producer receives the remaining 180 seconds of this bounded sprint's 300-second Astra grant, at medium effort, up to three substantive stages. Primary constructs the integrated account and surface coverage proof while the producer works. No other simultaneous Astra child; no descendants. All returned effective model/effort values remain UNKNOWN unless runtime explicitly exposes them. At the material frozen-outcome/review boundary, establish the next bounded review allocation; do not count self-review as independent.

Freeze all output hashes and dependencies before fresh independent review. Review must falsify missing transitions, correlated witness loss, expiry resurrection, unjustified adoption and circular proof claims. A written candidate is not a promoted theorem. No tests are necessary for this prose-only task; run only focused link/inventory/whitespace checks. Preserve a coherent research checkpoint and inspect the entire intended outbound range before a non-forced push to the dedicated branch.

## Pinned direct inputs

- `docs/yulang-operational-type-safety-ja.tex`: `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`
- `docs/yulang-source-type-safety-ja.tex`: `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166`
- `docs/yulang-dot-selection-safety-ja.tex`: `47b7fcec1f501e7c326ab9859885e329aab2730066806ea79212e825ebb32b0b`
- `docs/yulang-whole-language-semantics-ja-expanded-20261023.tex`: `28dc9b7fcb818e99a9513054d5847274ccce0d816a8c4a9644b802f0aa3fbd65`
- `notes/design/2026-10-15-callback-identity-forwarding.md`: `c544ed3c7b83686a740aa43b1db92d901de31a3b197f81f90a4c9dbdae561134`
- `notes/design/2026-10-15-compose-scoped-effect-release.md`: `fd56f819f9b33adc5d75cbfdae378c90903e4aa3a266fc053c05dda315d40679`
- `notes/design/2026-10-11-yulang-inference-top-level-principles.md`: `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`
