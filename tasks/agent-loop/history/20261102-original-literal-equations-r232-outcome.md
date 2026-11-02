# R232 outcome — original literal generation/readout gate

Status: **REVIEWED MODEL-INCOMPLETE**. Parent is the unchanged
`YulangClosure.SourceProblem.InferenceSoundness` at
`notes/theory/lean/YulangClosure/Contracts.lean:128–130`.
Baseline: `05586b1473e3194b80fb5ce7b30c531875e27929`.
R232 contract: SHA-256
`3b7fb263381574d72ba4ea490840af09d73df6cd3c11ae8d1a35c87b182d83f9`.

## Outcome and parent application

The original L1 source rule remains fixed for all eight payload-preserving
forms and at the same `(q,r,e₀,ξ,ω)`: Unit, Bool, Int, Float, String, Bytes,
Path, Character. Its descriptor/value, pure Return and contextual-boundary
requirements do not define the Simple-sub generator or arbitrary-solution
readout.

The R232 reciprocal-bound equations were only a candidate. Independent review
found they are not derived from the actual selected generator, and their
structural `Sub` premises do not imply syntactic equality. Concretely, for
`B = atom b`, `ρ(value, α) = union B B` satisfies both `α ≤ B` and `B ≤ α`
using `unionElim`, `refl` and `unionLeft`, while the substituted term is not
syntactically `B`. This blocks direct identity readout; it does not refute a
future semantics that interprets equivalent terms identically.

Primary follow-up inspected the existing R336 K0 literal rule. It records
mutual value bounds and bottom/empty effect bounds in a declared four-form
submodel (Unit, Bool, Int, String), whose effect interpretation is finite
subsets. That candidate does not supply the unchanged full source parent, the
other four literal constructors, full contextual effect/Call obligations,
annotated-port mapping, or a same-witness arbitrary-solution interpretation.
It cannot be promoted to the full model or replace the missing equation.

The exact unresolved seam remains at the original abstract model owner:

1. `generate` must derive the source/scope/port-specific Simple-sub constraints
   and fresh typed coordinates for all original forms from the selected
   algorithm; and
2. `solve` must map every satisfying assignment of those constraints to the
   original descriptor/effect/value/root/event carriers and derive the
   original L1 premise and Return, retaining the same scope, shared witness,
   annotation boundary and enclosing obligations.

`OriginalSourceGeneration.sourceRules` currently emits a declaration atom,
not those independent constraints. `OriginalSourceInterpretation.SourceAssignment`
has endpoint-indexed fields but no graph/valuation interpretation;
`LiteralAtom` assumes declaration/groundness. R220 supplies neither equation.
No downstream premise was added to conceal this gap.

**Parent-premise delta: 0. Roots: 0/4. Packages: 0/5.** No theorem worker was
activated. No source form was excluded, no approved meaning changed and no
Rust behavior was promoted to mathematical authority.

## Independent review and authentication

Fresh nonauthor `/root/r232_literal_model_review` returned PASS for this exact
MODEL-INCOMPLETE disposition only. The complete review is at
`tasks/agent-loop/inbox/original-literal-equations-r232-review.md`, SHA-256
`af39b2953a09ff19212c41524298125ec101f9d5bd36bf5acbe28bdcde317e79`. The reviewer authenticated all eight R232 direct
dependency hashes against the contract. Its reference Simple-sub source is
pinned at commit `9bae772624c23b52a93c1b226157e16898b4d9db`; its byte hash was
not available, so none is claimed.

Material-boundary `next_action_selector` agrees: retain the parent and source
domain, freeze this candidate as incomplete, and use only authority-derived
equations for the next proof/model work. Its concrete countermodel and the
R336 K0 scope were inspected before this outcome. No new worker leases or
capacity changes were made.

## Checks, resources and Git

- `python3 tools/agent_sprint.py check`: PASS (static record consistency only).
- No Lean/Lake, Rust/Cargo, test, compiler build, cache generation, worktree,
  scratch, or Rust source edit was performed. User-authorized cache growth was
  not needed; existing cache stayed untouched.
- Reviewer stopped. Selector consultation returned; no descendants remain.
- R231 predecessor checkpoint `05586b1473e3194b80fb5ce7b30c531875e27929`
  was committed and pushed to `origin/yulang3`.
- This R232 record is a separate incomplete research checkpoint. Only its
  explicit reviewed/intended paths may be included in a later Git checkpoint;
  pending questions and unrelated dirty/quarantined files remain excluded.
