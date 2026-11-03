# Operation signature constructor trace: independent review

A test-only session-owned trace records actual operation declaration/occurrence,
Function source paths, returned Terms and four ports, polarity/variance, memoized
variables/effect rows and the family argument passed to effect construction.
Its storage and checkpoint truncation are compiled only for tests; the dormant
recorder does not collect. The focused constructor/rollback test includes a
committed prefix, a later aborted attempt, and retry. No capture/FreshUse
correspondence is asserted: the attempted captured-root join did not identify
the constructor Function terms and its incomplete instrumentation was removed.

`/root/operation_trace_review` independently inspected final
`crates/yu-solver/src/candidate_effect.rs`, SHA-256
`102dc5f8e5cb1d8f227f302ccc55a4daa84b9040e2196f12c286d6c7d1a06937`.
The initial review found that a path-derived Self marker did not authenticate
what the constructor passed. The producer changed it to record the actual
`family_argument`, explicitly without claiming the effect was emitted; a
later assertion-only delta checks actual Function polarities. The reviewer
accepted the final delta; the independent focused test was run on the prior
revision and the producer reran the final test successfully.

`/root/operation_trace_regression` independently confirmed cfg gating,
transaction rollback and committed-prefix/retry coverage and ran a non-test
`cargo check -p yu-solver --features shadow-apply-candidate --offline` on the
prior revision. The last delta added test assertions only. No production
behavior, diagnostics or public APIs were changed. The producer also ran the
final focused test and a non-test check. Existing compiler warnings are not
claimed fixed.

These are provisional constructor-input observations, not a native Term to
capture/FreshUse certificate, not source/native equivalence or EI/Union
semantics. Original admission and the R159 parent remain OPEN. Reviewers made
no repository or Git writes; all worker writes stopped.
