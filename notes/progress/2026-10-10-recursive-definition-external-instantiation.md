# Recursive-definition external instantiation regression (2026-10-10)

Branch: `research/simple-sub-intrusion`
Baseline: `bd999eee1`
Mode: M1 source regression
Authority: current Simple-sub inference objective and the selected parent-copy
SCC intrusion contract; no new semantic rule

## Result

`simple_sub_local_source_retirement.rs` now checks one self-recursive source
definition, `loop x = loop x`, with two external uses. The uses apply the
recursive definition to an integer and to an identity Function, and the
candidate reports no conflicts. The test obtains each use's actual
`CandidateGraphFreshUse`, requires both to contain generic source rows, and
checks that all rows in the two images are distinct by canonical solver
identity.

This supports the bounded claim that the two external occurrences receive
independent row images for this recursive fixture. It does not test the
internal recursive occurrence's monomorphic route, mutual recursion, returned
concrete result observations, recursive soundness/principality, public scheme
publication, or F5 replacement.

## Review and verification

An independent compiler-referee review inspected the exact test delta,
definition-use collection, active SCC routing and fresh-use API. Its initial
objection was that the test name claimed internal monomorphism without
observing it; the test name was narrowed to match the assertions. Final review
found no blocking, major, or open minor finding.

- `RUSTC_WRAPPER= timeout 120s cargo test -p yu-solver --features shadow-f5,shadow-apply-candidate --test simple_sub_local_source_retirement recursive_definition_is_fresh_at_external_uses -j 2 --offline -- --exact` — passed (1 test).
- `git diff --check -- crates/yu-solver/tests/simple_sub_local_source_retirement.rs` — passed.

No benchmark or timing sample ran. The contextual residual-owner decision and
concrete negative formal rows remain pending; authentic operation execution,
complete Call, public/default migration, soundness/principality and target F5
replacement remain open.
