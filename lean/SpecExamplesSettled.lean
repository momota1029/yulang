import Yulang.CommonRoleSettledExamples

/-!
# Additive specification-conformance status (2026-11-08)

This table supersedes the historical X6/X8–X12 rows in SpecExamples.lean.
That existing module is unchanged under the task's explicit hard edit rule.
All six additions run CommonRoleSettledResolver.classify, the single outer
entry with proved concrete FrontierExact and declaration-derived Acc.
They concern actual lowered declarations and settled role goals, not source
expression inference, file loading or Core.infer. Precise scope is in
CommonRoleSettledSyntax and notes/handoff/2026-11-08-astra-settled-frontier-results.md.

| ID | Status | Entry/evidence |
| --- | --- | --- |
| X1 | PROVED (existing) | SpecExamples.x1_declaration_accepted |
| X2 | PROVED (existing) | SpecExamples.x2_declaration_rejected |
| X3 | PROVED (existing) | SpecExamples.x3_shadow_rejected |
| X4 | NOT-EXPRESSIBLE-YET | Source record-tail scheduling remains open |
| X5 | PROVED (existing) | SpecExamples.x5_rejected |
| X6 | PROVED (settled fragment) | x6_single_selected, x6_ambiguous, x6_source_lowered |
| X7 | NOT-EXPRESSIBLE-YET | Associated declaration checking remains open |
| X8 | PROVED (settled fragment) | x8_len_selected |
| X9 | PROVED (settled fragment) | x9_where_tree, x9_show_rejected |
| X10 | PROVED (settled fragment) | x10_inspection_rejected |
| X11 | PROVED (settled fragment) | x11_rejection_before_ambiguity |
| X12 | PROVED (settled fragment) | x12_named_selected |
| X13 | NOT-EXPRESSIBLE-YET | Source bounds/co-occurrence bridge remains open |
| X14 | NOT-EXPRESSIBLE-YET | Non-singleton nested intervals excluded here |
| X15 | NOT-EXPRESSIBLE-YET | General interval simplifier excluded here |
| X16 | NOT-EXPRESSIBLE-YET | Different endpoint heads excluded here |
| X17 | NOT-EXPRESSIBLE-YET | Invariant function interval source bridge open |
| X18 | PROVED (existing) | Declaration-derived variance examples |
| X19 | PROVED (existing) | Declaration-derived variance examples |
| X20 | PROVED (existing) | Declaration-derived variance examples |
| X21 | NOT-EXPRESSIBLE-YET | Rank-2 source body bridge remains open |
| X22 | MISMATCH (existing) | Optional-field main generator remains unchanged |
| X23 | NOT-EXPRESSIBLE-YET | Source static effect generator remains open |
| X24 | NOT-EXPRESSIBLE-YET | Source pipe/catch bridge remains open |

The new theorem names in this table have prefix
Yulang.CommonRoleSettledExamples; all_six_independent derives all six
independent Classify judgments through the same unconditional exactness.
-/
