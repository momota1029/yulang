# Source signature extracted R301: independent review

`/root/r301_extracted_lean_review` independently rebuilt the reviewed source
extractor offline, regenerated the Lean output byte-for-byte from the frozen
fixture and checked metadata against the original source. A fresh isolated Lean
4.35.0 build and all fourteen theorem type/axiom audits passed. Five use no
axioms, eight use `propext`, and `original_app_requires_computation_check` uses
`propext`, `Classical.choice`, `Quot.sound`. Full printed types and exact
commands are retained in `source-signature-extracted-r301.md`.

Frozen SHA-256: generated module
`f88acdeeca2d083c0408c488b05c8d0f8d91b8604f754a5b59cf067a30a9bad6`;
handwritten checks
`279e8771297dad208af6fce199f8163b8a0e0508b11a748a9c22b5a8c2aaddbe`;
fixture `65f88c17fbc256ea31f2fe4859308a479455f1d04ff771c5042b85faabc7b5fd`;
handoff `1aef1a4fcbd816aa13297ef3b4d0367c6f8d234ebc0f7adf60d523d489fa079d`.
The extraction tool and its independent source review are committed separately.

`/root/r301_extracted_parent` independently checked the source metadata and
application of R300 field/plan lemmas. The App theorem extracts the original
computation check from an assumed complete original App judgment at the same
candidate extension; it does not construct that judgment or discharge any
R159 premise. Numeric identity classes refer only to one extraction run; equal
output across runs establishes reproducibility, not native identity equality.

This finite source fixture is useful evidence, not a general HIR-to-Lean
correspondence, native execution theorem, EI/Union field construction or
semantic admission. IF, R159 and production remain open. Reviewers made no
repository/Git writes and all verification processes stopped.
