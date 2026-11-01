# R221 outcome — original literal readout

Status: **CLOSED_INCOMPLETE** after independent falsifier and fresh review. Parent-premise delta: **0**.

## Original obligation and fixed boundary

The target remains `YulangClosure.SourceProblem.InferenceSoundness` in
`notes/theory/lean/YulangClosure/Contracts.lean:128–130`:

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

R221 tested whether the reviewed R220 structural literal fragment could be read
as the original source literal judgment under the same satisfying assignment,
with Authoritative L1's payload, `(q,r,e₀,ξ,ω)`, pure Return, and enclosing
checking/effect obligations intact. L1 remains unchanged.

## Frozen result

The proof lane attempted both construction directions and found the same exact
missing equation: no admitted carrier/readout connects R220's graph references
to `OriginalSourceInterpretation.SourceAssignment.row`'s descriptor, value,
root, and event at `(site, finalRoot)` for the same assignment. The original
literal rule consumes a supplied declaration, ground descriptor form, and
ground row; `OriginalSourceGeneration.sourceRules` emits the declaration but
does not generate a structural variable/reference allocation. The existing
interpretation supplies arbitrary `Sorts` and `Inputs`; it does not define this
connection. R220's code atom and bottom at caller-chosen references do not
establish it.

This is missing construction evidence in the inspected model, not a
source-qualified counterexample, impossibility result, or claim of semantic
underdetermination. No carrier law was postulated and no source interpretation
was changed. Parent source judgment, `sameScoped`, and all four original roots
remain open. In particular, soundness, coverage, principality, and termination
remain distinct and open; R221 does not close any one of them.

## Evidence and review

- Contract: `tasks/agent-loop/sprints/original-literal-readout-r221.md`, SHA-256
  `bdaa51efd7aecb2a0e291e256cec4749fc0ad78ca0623e4b1cc7b08bf8a49876`.
- Proof artifact: `notes/theory/2026-11-02-original-literal-readout-r221.md`,
  SHA-256 `1d4f46b9e9d2375d31284957c4157906df9fd00477fc976d43204262dedcb805`.
- Frozen handoff: `tasks/agent-loop/inbox/original-literal-readout-r221-proof.md`,
  SHA-256 `3da0827d4c71ade065b33660ea3d8b2ba355374674b4bda537bcc02f10dcf25c`.
- Independent falsifier: `tasks/agent-loop/inbox/original-literal-readout-r221-falsifier.md`,
  SHA-256 `f06751e46d07cd50b43df3605c93d716d725f1483a233777f8099563d26ae444`.
- The falsifier found no admitted construction in the inspected sources linking
  the same graph/reference solution to `A.row q` at `finalRoot`, while retaining
  the original pure Return. It also found no source counterexample or semantic
  underdetermination. Its parent delta is zero.
- R220's checked artifact and `[propext]` axiom audit are inherited only; R221
  produced no theorem and ran no Lean checker or build.
- Fresh compiler-referee review: `tasks/agent-loop/inbox/original-literal-readout-r221-review.md`,
  SHA-256 `d71a02eda08ca289a2795c795acfa8cdcbce774d77c6e06d42e8f54850926aca`;
  **PASS**, 0 blocking, 0 major, 0 minor findings. It confirms both
  construction directions leave the admitted equation absent and retains the
  contract's obstruction classification. Reviewer and author writes stopped.
- No source module, Rust code, test, or cache was changed by R221.

## Next decision boundary

The next-action dispatcher recommends constructing the endogenous shared
regular-graph readout for the existing abstract Simple-sub bound state. This
advances the fixed abstract algorithm independently of R221's missing original
carrier interpretation. Preserve the R221 obstruction as a model-input
boundary; do not repeat local literal or source-owner searches without a
concrete carrier equation. No semantic choice is implied by this stopping
result.
