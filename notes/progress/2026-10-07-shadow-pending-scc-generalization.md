# Shadow pending SCC generalization premise

Date: 2026-10-07
Baseline: `67d9e5279c499ff445acabf0b7262d1a7e8d1231`
Status: implemented default-off structural carrier; compiler-referee review passed
Claim class: exact current-component retention with an unresolved successor premise
Authority: user-authorized shadow identity/evidence plumbing only
Semantic and production inference authority: none

## Result

`SccComponentRef::pending_successor_generalization()` returns a borrowed
`PendingSccGeneralizationRef` retaining that exact current component and an
unconditional `SuccessorGeneralizationRuleUnresolved` premise. It does not
construct or equate a successor generalized component, assert eligibility,
merge member schemes or Q/R namespaces, assign `beta`/`Slots`, or freshen a
use. Empty incoming-use inventories and missing source-skeleton projections
leave the premise unresolved.

The carrier stores one existing artifact-branded component handle. It adds no
allocation, solver query, graph traversal, counter update or production route.
Existing member and use endpoint views preserve their collection identities.

## Review and verification

One independent compiler-referee M1 review passed with no findings. The review
covered exact component retention, collection branding, endpoint identity,
feature boundaries and the absence of semantic eligibility/generalization
claims.

Focused tests cover a singleton with no internal or incoming uses and a
mutual-recursive component with internal and incoming uses despite an absent
shadow skeleton. They check retained member/use/endpoint identities, foreign
collection rejection and unchanged observer counters.

Checks run:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-solver --features shadow-scc-observer shadow_scc_observer -- --test-threads=1
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo check -p yu-solver
rustfmt --check crates/yu-solver/src/shadow_scc.rs crates/yu-solver/src/tests/shadow_scc_observer.rs
git diff --check
```

The focused observer run passed 12 tests. Feature-off solver check and format/
whitespace checks passed. One Cargo process ran at a time, with at most two
build jobs and one test thread. No broad suite, benchmark, performance sample,
Q/R freshening, generalized-interface construction or production route was
exercised.
