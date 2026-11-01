# R204 — Admissibility of the canonical literal introduction in source rules

Status: ACTIVE under the user's standing Yulang inference goal; primary approval follows the reviewed next-action selection. Exact rule bytes remain candidate pending independent review.
Branch / baseline commit: `yulang3` / `8c4d62764d5411c112d7ee632005e04c05a5f841`.
Authority: user goal to prove Yulang inference; authoritative Simple-sub principles; selected Source-Generalize §§2–3 and L1/L2; no new semantics adopted by this contract.

## Original outcome and success evidence

Parent: `YulangClosure.SourceProblem.InferenceSoundness`, `Contracts.lean:128–130`, unchanged quantifiers and one `sameScoped` witness. This sprint addresses only its source literal induction edge. Soundness, principality, termination, and the other source constructors remain open.

Establish a source-rule admissibility derivation (or exact missing-law stop) connecting R203's all-payload static value/type introduction to the selected SG Literal rule. Preserve the actual literal declaration, full local typing relation, original Return/effect/world obligations, all permitted alternatives and guards, original occurrence, event, and shared scope. Local intrinsic purity must not erase contextual permission, inflow, residual effects, or Call obligations.

Required outcome: a frozen sequential revision of `notes/theory/2026-11-01-abstract-inference-model-r199.md` that states the sufficient SG rule, proves each premise from an already selected authority or names its exact unprovided L1/L2 law, and records whether a new semantic choice would change accepted typings, payload validity, effects, alternatives, or scope. No theorem is claimed from assumed `LiteralDeclaration` or `Ground`.

Parent metric: exact premise before/after and application site. Candidate rule construction alone counts as zero parent reduction; do not claim more than `0/4 roots; 0/5 packages` unless an independently reviewed derivation is actually consumed by the unchanged parent.

## Frozen inputs

- HEAD/origin baseline: `8c4d62764d5411c112d7ee632005e04c05a5f841`.
- User-approved inference principles: `notes/design/2026-10-11-yulang-inference-top-level-principles.md`, SHA-256 `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`.
- Selected source rule: `notes/design/2026-10-08-source-generalize-definition.md`, SHA-256 `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38`; construction `notes/theory/2026-10-08-source-generalize-definition-and-proof.md`, SHA-256 `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`.
- Current model candidate: `notes/theory/2026-11-01-abstract-inference-model-r199.md`, SHA-256 `f60b89d98ced17cabf860c6dd65aa3929796c85a407c8f82af25607adf0017cb`.
- R203 literal intro: `notes/theory/2026-11-02-static-literal-introduction-r203.md`, SHA-256 `99af6a50a9b1a049000a834bcb6066ea3eb9fd51a17b84f8331797ffb9bd358d`; R203 outcome `tasks/agent-loop/history/r203-outcome.md`, SHA-256 `d17f2c1f40e1e2d7c092add2a972ed5c84af50d58e33b81db685aac103fb4bb1`.
- Original SG L1/L2 interpretation: `notes/theory/lean/YulangClosure/OriginalSourceInterpretation.lean`, SHA-256 `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef`.
- Symbolic generation: `CanonicalInferenceModelR194.lean`, SHA-256 `c922c01283e89c4cb76ee509f9c8c4dc96bc30644568199546f7ccdf0fbb2550`; R196, `CanonicalSourceInferenceModelR196.lean`, SHA-256 `69d551760efc1b40f9235e749c4d2edde3e439b2cb91655495bf1c22d7d55c7c`.
- Original parent contract: `Contracts.lean`, SHA-256 `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`.

## Method and boundaries

Primary-only construction on the exact existing R199 model path; one fresh read-only `spec_auditor` reviews frozen bytes and the governing inputs. A definition proposal remains a proposal until review and, if it changes accepted source meaning, explicit user approval under `rules/design-authority.md`.

Do not repeat payload mapping, use Rust identifiers/receipts/owner traces, inspect the pending typed-Union question, create Lean modules, run Lean/Lake/build/tests, or create caches, scratch, targets, environments, or worktrees. Keep Call and contextual effects visible; no source restriction or effect erasure.

Falsifier: the claimed SG derivation omits an actual declaration, Return, effect/world law, permitted alternative, guard, occurrence, or shared scope field; or its rule broadens/narrows accepted source meanings without approval. Stop at the exact missing original law; do not replace it with a conditional theorem.

Budget: primary construction 600 seconds; one independent review up to 300 seconds. No Rust implementation lane is admitted because no reviewed abstract literal rule is available to drive one. After the rule is frozen, consult the dispatcher before the next material theorem packet.
