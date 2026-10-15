# Restore complete grouped application regression coverage

Date: 2026-10-15
Branch: `research/simple-sub-intrusion`
Status: complete; separate from ordinary carrier implementation

The ordinary-carrier package check exposed one pre-existing test failure:
`research_apply_lowering_preserves_mixed_unary_call_spines` expected fourteen
recovery-free sources while thirty were accepted. The same failure reproduces
on main before carrier integration. The generator contains no lambda syntax.

The causal authority is the
[October 5 parenthesized-ML addendum](../design/2026-10-05-parenthesized-ml-application-addendum.md).
Commit `745e3a4cc8502d5f9dc865cc3cdf55ea1ba35bc4` implemented ordinary ML inside
parentheses but retained this old subset assertion. The excluded masks contain
an ML stage before a later Call stage, such as `(f a)(b)`; the accepted grammar
requires their inner group to be a single valid application. All
`2 + 4 + 8 + 16 = 30` generated sources are therefore required to be valid.

The test now asserts validity for every source, removing its silent invalid
skip. It checks all thirty stage/mask pairs and retains its original name,
topology, atomic-argument, range, ordering and unique-occurrence assertions.
No parser production code or source contract changed. This is a stronger
coverage check under an existing approved specification, not an output update
to accommodate an unexplained result.

M1: read-only source/history exploration established the owner;
`ordinary_carrier_contract` supplied pre-write specification clearance and
post-write closure without findings. Primary verification:
`CARGO_BUILD_JOBS=2 timeout 300s cargo test -p yu-hir --lib research_apply_lowering_preserves_mixed_unary_call_spines -- --test-threads=2`
passes. No benchmark or timing samples; no broad repeat for this test-only
repair. The subsequent carrier phase owns its package/feature boundary checks.
