# R220 outcome — checked structural literal fragment; original bridge open

Contract: `tasks/agent-loop/sprints/abstract-generator-denotation-r220.md`,
SHA-256 `42ca0a85107b13af019dd6049e5b92d8bc03dadf51317ada45036af9120db79b`.
Baseline: `6f3656d9ae0214721df9e160e7ae69ba29ee773f`.

## Parent result

The unchanged parent is `YulangClosure.SourceProblem.InferenceSoundness`
(`Contracts.lean:128–130`):

```lean
∀ s x d a, supported s → generates s x d → solves d a →
  ∃ e, sourceJudgment s x e ∧ sameScoped s x e a
```

R220 proves only structural readout from the same satisfying graph/reference
assignment. It does not establish that assignment's source descriptor, raw
value, root, event, scope, Return, or shared witness. Parent-premise delta **0**;
roots **0/4**; packages **0/5**; Effect-hygiene theorem delta **0**.

## Checked artifact

Module: `notes/theory/lean/YulangClosure/AbstractGeneratorDenotationR220.lean`,
SHA-256 `bbd73afe54030cf3e4378a379a58a6836da1b44c9fd227b0bb8b372329f8a254`.
Contract and all pinned Lean dependencies matched their admitted hashes.
Environment: project pin `leanprover/lean4:v4.35.0`; Lake 5.0.0-src;
Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
The sole build owner was the primary and the only cache path was the existing
`notes/theory/lean/.lake/build`.

Commands and exits:

- `lake build +YulangClosure.AbstractGeneratorDenotationR220` — exit 0,
  11 jobs.
- `.agents/skills/yulang-lean-proofs/scripts/check_lean.py` for the module and
  all six declarations with `--timeout 1800` — exit 0.
- `python3 tools/agent_sprint.py check` — PASS after compact-state repair.

The checker printed complete types for:
`node_atom_of_mutual_expansion`, `atom_rigidity`,
`effect_bottom_rigidity`, `clause_satisfied_decoded`, `decoded_var_index`, and
`literal_structural_readout`. Each complete axiom list is `[propext]`; no
`sorryAx`, project axiom, or other non-whitelisted axiom was reported.

## Source boundary and application

`literalCode` records only the constructor tag; the fragment does not decode
payloads into the adopted `PaperTypes.Value.literal` or `Value(τ(l))` descriptor.
`OriginalSourceGeneration.sourceRules` emits a literal-declaration atom.
`SourceAssignment.row` reads descriptor/value/root at `⟨site, finalRoot⟩` and
retains its event. The original syntax distinguishes synthesis, finalRoot and
writtenTarget, while the annotated source rule has its own synthesis-to-written
target boundary. No frozen definition supplies the equation mapping R220's
structural references to that original row, root, event, pure Return, scope or
shared witness. `LiteralAtom` consumes supplied declaration and ground-row
facts; it does not construct them from structural store satisfaction.

The proof handoff SHA-256 is
`e5201bd86bde686aed220c3fc0f91f58b83c2d7868400d752a3e4da8ececd930`; the
independent falsifier handoff SHA-256 is
`e237662bb869f982cdb069a08ffe97ee91e9940d9740b6532bfbcbf8fa2c0b35`. Both
confirm the structural result's limit. The falsifier found no source-qualified
counterexample. Its reference-index and contextual-effect witnesses reject
stronger shortcuts only; they do not refute L1 or soundness.

The parent application therefore remains open. Keep intrinsic empty Effect
separate from contextual permission, inflow, residual, Call and future effects.
R219's reviewed `NO_SAFE_CODE_SLICE` remains the implementation result; R220
made no Rust edit.

## Review and continuation

Fresh independent review by `/root/r220_structural_leaf_review`
(`compiler_referee`) returned **PASS; 0 blocking, 0 major, 0 minor**. The reviewer
independently inspected the frozen module and actual definitions, confirmed all
six local theorem proofs match their statements, and confirmed that duplicate
atom indices, arbitrary payloads, and unconstrained contextual effects remain
represented. The reviewer agreed that the source bridge is absent at
`OriginalSourceInterpretation.lean:837–850` and
`OriginalSourceGeneration.lean:34–43`. The reviewer did not rerun Lean; the
checker output and `[propext]` audits above are primary-supplied verification.
Review is limited to the structural leaf and its stated boundary. It does not
approve parent application, source/native correspondence, or production.

The reviewed result is a complete R220 stopping outcome at the exact original
interface obstruction. The next bounded step is to determine and construct the
endpoint/descriptor/value/root/event/Return equation at its existing
original-source model owner, then apply it to the unchanged literal induction
premise using the same assignment and witness. Do not count a definition alone
as removing that premise.

Lean worker `/root/abstract_generator_denotation_r220_lean` froze its sole
module and stopped writes before the primary build. Proof and falsifier authors
also froze their handoffs and stopped. No tests, Cargo, Rust commands,
additional worktree/project/cache, or production changes ran. All unrelated
dirty and quarantined paths remain untouched.
