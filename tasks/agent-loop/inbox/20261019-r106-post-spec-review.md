# R106 post-output spec review

Reviewer: `/root/r106_post_spec`, fresh and independent, read-only.
Contract SHA-256: `edd6c951b46b3f1993c57b5f5cdec4928652cfb313120bd60d9e64c6ebc922bf`.
Result: **BLOCKING + MAJOR.** The authorized command must not run.

Verified the contract and all four frozen output hashes. The exact source is
148 bytes with SHA-256
`fb54857e70924c178842692d7cce1a9c35b7c2a55bceab78710889b913d7dfcb` and has
no final LF.

## BLOCKING: introduced existing-test compile error

Target: `crates/yu-hir/src/tests/shadow_method_role_source.rs:34–38`, output
owner `/root/r106_test_impl`.

The existing local declaration and its length assertion now use
`pending_declarations`, but the subsequent assertions still refer to
`declarations`, which is unbound. Restoring those two names in the original
file prefix and removing the appended test reproduces the pre-edit SHA
`6d5c3fec7b4ca0d4618f4ad378f0ad5e8e0689b4897d406ab90d175ba78e6135`; the
defect is introduced in this output. The whole `yu-hir --lib` test target
typechecks before test filtering, so `--exact` cannot bypass this failure.

Authority: R106 contract “Fixed finite outcome” (one appended test; preserve
existing assertions) and “Resources, reviews and stop conditions” (stop on
BLOCKING/major review). No test was run.

## MAJOR: ownership correspondence is incomplete

Target: same test file, member/root assertions and retained positions, output
owner `/root/r106_test_impl`.

The test checks the member as a child of some `Statement`, but does not connect
that statement and its ancestors to the associated `ImplDeclaration`. It also
checks retained syntax kind/range for each key but does not compare retained
parent/child relationships and order against the original syntax relationships.
Thus it does not establish the full ownership invariant promised by the
contract and proof note. The role/impl roots, exact source literal, occurrence
ranges, source-key ownership, and distinct formal/body occurrence checks
otherwise match the frozen source.

Authority: R106 contract exact-source outcome; proof note
`notes/theory/2026-10-19-r106-method-source-entry.md:54–60`; pinned
`shadow.rs:1198–1273`.

Closure: Luna adjudicates the stopped packet. A future authorized correction
must restore a compiling test and add the missing declaration-to-member and
retained-order/parent evidence, or explicitly narrow the accepted claim before
observation; fresh review is required. No repair, edit, test, build, Git or
runtime/CLI action occurred during review.

Receipt recorded by Luna from the reviewer's read-only message; reviewer wrote
no files.
