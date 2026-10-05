# Integration receipt: nested-block-function-source-realization/q1

Question revision: `q1`
Approved answer: `nested-block-function-source-realization-answer/a1`
Branch: `research/simple-sub-intrusion`
Integration commit: `a6bdcf99fba35497cf1323c70101e34669a3ba71`
Outcome: accepted scoped source-semantics decision; implementation remains gated

## Validation

- The question, current answer draft and approved answer identify the same
  question and answer revisions. The complete embedded a1 draft in
  `approved-answer.md` is byte-for-byte equal to `answer-draft.md`
  (SHA-256 `a96d187d9e6991e4b3d974e2128ca6af830ba5a8004142351d8439976e08d1bb`).
- `approved-answer.md` records the user's original selection and explicit
  `> OK` approval of the full a1. Its interpretation of the selected scope is
  explicitly included in the approved text.
- The source baseline `757c90564789dd6dd3f9908fd4bb2b1400206962` is an ancestor
  of the integration commit. The named syntax, F5, call-view, HIR and solver
  sources are unchanged between that baseline and the integration commit.
- The current question, answer draft and approved answer match the versions
  committed together at `a6bdcf99fba35497cf1323c70101e34669a3ba71`.
- The predecessor `function-call-view-formation/q1` a2 bundle was integrated
  and consumed at `61a3651376166346a5baa03ec6679c310b0edbdb`; its receipt records
  matching committed question/draft/approved files and excludes the a1 archive.

## Integrated decision and affected scope

For the exact candidate
`my apply f = { my step x = f x; step }`, select sequential local binding,
final-expression result, lexical resolution of inner `f` to the outer formal
and `x` to the inner formal, and retention of the returned function's capture
of outer `f` across later calls. This permits a conditional source-to-core
derivation for that candidate, using the legacy Yulang2 material only as
compatibility evidence.

This decision does not establish current production acceptance or general
brace, recursive-local-group, effect-execution, closure-lifetime, or call-view
registration semantics. Before implementation, a narrow reviewed Authoritative
addendum must record this candidate's approved meaning. The proof gates remain:
raw-brace to core/call-view correspondence under the approved call-view rules,
capture and evidence transport, principality, production source acceptance,
and the overall inference-replacement obligations. No compiler implementation
authority follows from this receipt.
