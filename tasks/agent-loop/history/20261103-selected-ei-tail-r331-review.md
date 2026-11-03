# R331 — selected EI tail, independent review

Baseline `839f7e3aa`; frozen proof SHA-256
`2aec3d3381ce8e99925c164be2d14a1a0f12e9ac1f05dc34cacb3d49a9195a9d`.
The construction composes existing R310/R311 rules to derive the R311 tail
and selected callee phase from separate Return, Function checking, primitive
guard and whole-carrier assumptions. It retains the same returned value and
provider and universal receiver domains. It does not assume a finished EI
body or source child. This is a conditional intermediate result, principally
composition of existing helpers; it does not discharge an unchanged R159
parent edge.

Independent source review confirmed the authentication gap: `PrimitiveLeaf`
checks a signature but permits changing the source key and use while retaining
the same declaration. The checked retagging construction demonstrates this.
Independent selected-key/use resolution, typed request/response and whole-action
laws remain necessary. The selected theorem concludes only R311's incomplete
callee clause and a static scope equation; it does not construct the R306
registered source contribution, licensed Call child, complete response and
future linkage, or every independent Union arm. Original R159 admission,
formation, locals, checks and both child judgments remain open.

Fresh independent pinned Lean 4.35 checking rebuilt the entire 55-module
dependency cone from source with `-j1 -M2048`; all modules and all 11 authored
theorem type/axiom queries succeeded. The higher bound is required by the
unchanged R315 dependency under the standard 1 GiB limit. The reported axioms
are Lean's standard axioms; no `sorryAx` was reported. This review does not
claim completion of EI-All or source Union correspondence.

Independent type/axiom audit SHA-256:
`c6a5473711c2ed025e1defcf0bc02e4fb50a97ff5d20ea6c5af83c1fde9ca3e8`.
