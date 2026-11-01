# R214 — construct the adopted L1 literal equation

Baseline: `yulang3` / `9bf70ea58`

Status: **STOPPED_INCOMPLETE_REVIEWED**. R213 is `STOPPED_INCOMPLETE_REVIEWED`; its original roots
remain **0/4 closed**, packages **0/5 closed**.

## Fixed parent and outcome

Keep the unchanged `Contracts.SourceProblem.InferenceSoundness` statement and
its arbitrary satisfying assignment. Construct the first source-to-independent-
constraint equation for the already adopted L1 literal rule. Decide, from the
existing algebra and authorities, whether an arbitrary satisfying assignment
supplies the L1 type/effect facts while the original syntax supplies the same
literal payload/value and the source rule retains the occurrence/root/event/
scope/shared witness. Do not require runtime literal values to be encoded as
type terms. Preserve annotated
synthesis versus `writtenTarget`, all checking alternatives and enclosing
effects. Do not require an endogenous solver run.

This packet does not reopen L1 or define new source semantics. It must not add a
source-domain restriction or smuggle source judgment/readout conclusions into
generation, satisfaction or `sameScoped`.

## Frozen inputs

- Original roots: `notes/theory/lean/YulangClosure/Contracts.lean:128–154`,
  SHA-256 `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`
- L1 adoption: `notes/design/2026-11-02-literal-l1-adoption.md`,
  SHA-256 `f69a11121b0bade01586293fbda5500c4264424c3ac568fd1336ebb1b2eec9b8`
- Original syntax: `OriginalSourceSyntax.lean`,
  SHA-256 `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`
- Source generator: `OriginalSourceGeneration.lean`,
  SHA-256 `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`
- Independent constraint syntax: `SimpleSubConstraintSyntax.lean`,
  SHA-256 `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6`
- Regular comparison semantics: `SimpleSubRegularSolutions.lean`,
  SHA-256 `755d267714bd23bcfc17ec37d43d258392567b7d1356afc4897f541ae9855b29`
- Lattice graph/store satisfaction: `SimpleSubLatticeInference.lean`,
  SHA-256 `c534c060dfde84f2817fbaa53222f430b59d9b6377cfacedabeca7b9b4b8ffa3`
- Lattice comparison rules: `SimpleSubLatticeCertificates.lean`,
  SHA-256 `55533eee35ed7058abd125ac0e01d8f29b8c0534800018d254c1bd9f9c0bb79b`
- Original source interpretation: `OriginalSourceInterpretation.lean`,
  SHA-256 `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef`
- Paper type/value syntax: `PaperExecutionSyntax.lean`,
  SHA-256 `d0dc9871c382ca945059167b8b9e05f8f672170208a994f081e29760a207b87d`
- R213 reviewed model:
  `notes/theory/2026-11-02-fixed-inference-model-r213.md`,
  SHA-256 `17319f77031c5f2135fb7ea14cffbea6d8e1b0b5466aa26d1b8bc5b14082223e`

Rehash before substantive use; stop on mismatch.

## Exact lease and method

Primary `/root` owns only:

- `tasks/agent-loop/sprints/literal-independent-equation-r214.md`
- `notes/theory/2026-11-02-literal-independent-equation-r214.md`
- `tasks/agent-loop/inbox/literal-independent-equation-r214.md`
- `tasks/agent-loop/current.json`

Construct all eight payload cases (unit, bool, int, floatBits, string, bytes,
path, character) using the unchanged raw payload. Test the strongest candidate
against actual `Term`, `Constraint`, `Store.Satisfied`, graph decoding, and
`RegularSub`. Any ground fragment must give an explicit embedding and decoding.
Distinguish subtype satisfaction from exact descriptor/readout and the value
fixed by original syntax. Preserve the same `(q,r,e₀,ξ,ω)` and keep value/effect,
permission/inflow/residual, and synthesis/target coordinates separate.

A candidate is acceptable only if generation is independent, arbitrary
satisfying assignments yield the adopted local facts, and no premise assumes
source judgment or readout. If the actual authorities cannot define that
implication, freeze the exact first missing equation and a concrete falsifier;
do not declare completion or invent a new semantic choice.

## Lanes, review and resources

- Mathematical model construction: primary, at most **1,800 seconds**.
- Implementation lane: **NO_SAFE_CODE_SLICE** until this equation supplies an
  authorized consumer change. No Rust source edits.
- Independent fresh read-only review: at most **600 seconds** after the model
  artifact is frozen; check each concrete equation against the falsifier below.
- Lean, Lake, builds, checkers, tests, Rust, Cargo, cache growth, scratch,
  worktree, and new environment: **zero**.

Falsifier: a satisfying assignment permits a descriptor or Return effect
that cannot instantiate the original literal rule (including any required
source subsumption), loses the original root/event/scope or synthesis endpoint,
or the model assumes the source conclusion. The source payload/value remains
fixed by the original literal syntax.

No theorem worker is authorized unless every premise for the proposed theorem
domain is fixed. R214 closes no root merely by producing an equation document.
Consult the dispatcher at a decisive counterexample, missing authority,
reviewed sprint end, or budget boundary.


## Frozen checkpoint and review status

The primary's candidate audit found a concrete countermodel to the weak
one-sided literal bound and localized the missing source-independent
Value/Effect constraint/readout equation. This does not refute stronger
bidirectional constraints or a source-subsumption construction; no full
equation is currently authorized by the pinned source/model interfaces. The
model remains `MODEL-INCOMPLETE`, with **0/4 roots; 0/5 packages** and no
theorem worker. The frozen model and handoff require fresh independent review
against the concrete falsifier before this sprint outcome is accepted. No Lean,
build, test, Rust, Cargo, cache, scratch or worktree activity occurred.


## Final review and disposition

A fresh independent read-only review passed the one-sided top-node countermodel
and found no blocking, major or minor findings. It confirmed all 11 evidence
pins and accepted preservation of the checkpoint as explicitly incomplete.
The model gate remains `MODEL-INCOMPLETE`; no full L1 equation was closed, no
theorem was admitted, and parent accounting remains **0/4 roots; 0/5 packages**.
See `tasks/agent-loop/history/20261102-literal-independent-equation-r214-review.md`
and `tasks/agent-loop/history/20261102-literal-independent-equation-r214-outcome.md`.
