# Operation signature rewrite-to-capture: independent review

`/root/retained_rewrite_join` added one test to the existing test-only module in
`crates/yu-solver/src/candidate_effect.rs`, frozen SHA-256
`ba9016eb41789f554df60c6b612573d4742d27ac2e05251f662ee95aee6eee3c`.
For a real nested-operation source, it runs the graph plan once, rejects
semantic diagnostics, identifies the actual source occurrence and slot-42
fact, follows that exact pair's retained extrusion rewrite, then matches the
complete positive captured BoundKey including receiving row and rewritten
Function. It follows captured Function children and each of two distinct
FreshUse term/row maps; captured and reconstructed Function paths and
polarities match the original constructor observation.

`/root/rewrite_join_review` independently reviewed and ran the final focused
fixture offline/locked in an isolated target: one test passed. The original
constructor/transactional sibling also passed independently. The producer's
final `operation_` suite passed 11 tests. `/root/rewrite_join_regression`
independently inspected the final change and confirmed it is one test addition;
production behavior and public APIs do not change. Both reviewers found no
blocking findings. The initial no-feature build failed and was rerun with the
required `shadow-apply-candidate` feature. All writes stopped.

Function comparisons use exact retained Terms; row checks establish canonical
incidence rather than raw allocation equality. This finite fixture does not
prove effect-support contents or symbolic-tail semantic equivalence after
extrusion, source/Lean general equivalence, EI/Union semantics, admission or
R159 closure. The pre-existing inline-extraction Cargo.lock change was excluded.
