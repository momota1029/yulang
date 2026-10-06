# Shadow SCC resolved-use definition endpoints

Date: 2026-10-07
Baseline: `283592aa9f83b480660067d1f4c51bd0690fb0c1`
Status: implemented default-off identity plumbing; compiler-referee review passed
Claim class: exact collection-owned SCC use endpoint exposure
Authority: user-authorized shadow structural/evidence plumbing only
Semantic and production inference authority: none

## Result

`SccTopology::use_definitions` resolves one exact retained `SccUseRef` to its
borrowed `(parent, target)` `SccDefinitionRef` handles. It checks the collection
brand, the retained use index, and both endpoints against the frozen SCC plan.
It allocates no identity, performs no solver query, and exposes only endpoint
ownership already stored by collection.

The focused regression checks both uses inside a mutual component and the
incoming use from another component. It verifies endpoint direction against
the retained records, component membership, cross-collection rejection even
for equal source HIR, and unchanged counters.

This is a structural join usable by future generalized-SCC source plumbing.
It does not construct a successor generalized interface, identify Q/R with
current scheme quantifiers, freshen a use, or infer source typing, eligibility,
role, `beta`/`Slots`, admission, or soundness. Missing endpoint identity stays
`MissingIdentity`; the opaque API does not permit a public missing-handle
fixture without private mutation.

## Review and verification

The compiler referee reviewed the API and tests at the stated baseline and
found no blocking, major, or minor findings. The review covered branded lookup,
plan membership, endpoint direction, component relations, counter preservation
and the nonsemantic boundary. Production inference beyond these direct
dependencies was not audited.

Checks run:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-solver --features shadow-scc-observer shadow_scc_observer -- --test-threads=1
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo check -p yu-core -p yu-solver
rustfmt --edition 2024 --check --config skip_children=true crates/yu-solver/src/shadow_scc.rs crates/yu-solver/src/tests/shadow_scc_observer.rs
git diff --check
```

The SCC observer run passed 10 tests. The feature-off check passed. One Cargo
process ran at a time, with at most two build jobs and one test thread. No broad
workspace suite, benchmark, performance sample, Oracle execution, Q/R
freshening, or production route was exercised.
