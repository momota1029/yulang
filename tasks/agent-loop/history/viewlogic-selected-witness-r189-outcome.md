# R189 outcome — selected ViewLogic witness stops at formation denotation

Status: **CLOSED_INCOMPLETE after independent review**. R189 accurately
establishes `BLOCKED_AT_EXACT_FORMATION_EQUATION`; it establishes no App
theorem. Original App sub-obligations discharged: **0**. Original parent
premises discharged or refuted: **0**. The unchanged
`YulangClosure.SourceProblem.InferenceSoundness`
(`Contracts.lean:128–130`) remains OPEN. Semantic under-specification,
impossibility and a source-qualified counterexample remain unestablished.

## Frozen artifacts and review

- Contract: `tasks/agent-loop/sprints/viewlogic-selected-witness-r189.md`,
  SHA-256 `2550c149c6f9798d53ee8fcf69764493eb0fada1781f220824638262429c7076`.
- Artifact: `notes/theory/2026-11-02-viewlogic-selected-witness-r189.md`,
  SHA-256 `fc29b3344cce5e82f58f1ca41a243fac67a60f6f356bb76e4bb0ec736d6daf48`.
- Handoff: `tasks/agent-loop/inbox/viewlogic-selected-witness-r189-proof.md`,
  SHA-256 `a956c5f0edbbaec0090ec67858747f5e133ddc45253e9e179c7df59f9ad8350c`.
- Fresh reviewer: `/root/r189_formation_review`, read-only. Accepted the
  blocked outcome with 0 blocking, 0 major and 0 minor findings. All three
  frozen target hashes and all 13 direct dependency hashes matched.

## Parent effect and exact equation

The original unannotated App source rule places
`atom .descriptorFormation q Γ [f.site,arg.site]` beneath
`b_q = ⟨q,.viewLogic,0⟩` (`OriginalSourceGeneration.lean:111–123`). The source
consumer `Judgment.existsE:751–754` requires one admitted `ScopedValue` under
the same environment extension. R189 used the weaker, correct target of the
single witness selected by the satisfying assignment; it did not require
admission for every possible raw domain element.

The first unresolved independent equation is the denotation of the actual
generated `descriptorFormation` occurrence under that assignment and
telescope:

```text
⟦DescriptorFormation(q,f,arg,v_q)⟧_(a[v_q↦z_a],Δ) = ? : Prop.
```

Its source-side target is
`k.atom (E.extend b_q v_a) (atom .descriptorFormation q Γ [f.site,arg.site])`.
The accepted representation prefix does not prove that Simple-sub actually
emits this atom as the corresponding independent constraint or that solving
it yields the source atom. In the existing heterogeneous adapter, selected
logical admission reduces, conditional on its decoded prefix, to
`LocalAdmissions.logical state b_q .viewLogic L_a`; that field remains an
independent input. The reduction is not generalized to every source kernel or
claimed as a completed selected-witness proof.

No admission law was assumed or inserted into generation. No different
witness, scope or telescope was substituted. No Lean theorem, checker/build/
test, source-native correspondence or production change was claimed. The
permitted result is an exact formalization boundary, not a semantic decision.

## Next dispatcher boundary

Any next step must target the independently declared meaning of the actual
`descriptorFormation` occurrence and its relationship to the selected
assignment witness. It must decide whether existing source authorities give
that definition or leave a precisely owned input open. Local adapter evidence,
source `Build` satisfaction, or a conditional `WellFormed → admitted` lemma
cannot be promoted to the original parent.
