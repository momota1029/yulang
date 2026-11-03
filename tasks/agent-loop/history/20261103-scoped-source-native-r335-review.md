# R335 — scoped source lookup and native return evidence

Baseline `55b636b69`. The reviewed source resolver proof SHA-256 is
`219eecf85e03aae12b71b773497a9506f229832e7a7c7e8c5bf944a84063cc10`.
It reads source callee entries by their complete position, telescope, scope,
operand sort and slot, retaining inventory order and duplicates. It checks
successful-read provenance and the actual R315 tick declaration/use. Its
applications reduce the selected outer App and inner tick App judgments to
their original same-extension premises; original admission, locals/checks,
primitive atom and child judgments remain independent. It does not establish
an exhaustive source arm inventory, EI/Union semantics or a licensed child.

Independent source review found no counterexample to these bounded claims;
it does not establish global key uniqueness. Independent Lean 4.35 checking
authenticated 81 sources and relevant artifacts, compiled 28 modules and
audited all 91 originating constants including 46 theorem constants. Only
standard Lean axioms occurred. Complete audit SHA-256:
`6ed00e2f70ca2b8372d94e28e5e582388c59ea8778d1cae0219c378b1870be3e`.

The test-only native change in `machine.rs`, SHA-256
`3727e1f4f32b9bed251a30224bd63b87a575d9ef84b97564f95e5774800a11c5`,
repairs a reproduced observation-validation gap: a different valid view for
the same response value was accepted before the fix. The exporter now checks
the exact response tuple recorded at the actual continuation Hole and links
the selected source Call's receiver Return to the selected-definition result,
keeping their invocation owners distinct. Negative tests exercise alternate
views, missing records and incorrect activation. This is finite native evidence,
not a construction of the original semantic world, lawful whole actions,
universal response domains, EI or R159.

Independent review found an initial non-test compilation failure caused by
missing `cfg(test)` on field initializers; revision 2 repaired it. Review also
requested an independent selected-result tuple join, which revision 2 added at
the actual `complete_selected_definition` boundary. Subsequent source and
regression reviews found no blocking issue; coordinated mutation of both
private receipts remains outside the one-sided mutation checks. The non-test
offline Cargo library check and the focused test passed (one passed, 94 filtered).
The generated R335 witness was separately elaborated by pinned Lean 4.35 with
exit 0. `rustfmt --check` on the whole existing machine file reports widespread
format differences; no whole-file formatting was applied.
