# Shadow SCC outgoing dependency occurrences

Date: 2026-10-07
Baseline: `6ae73005c`
Status: implemented default-off structural view; compiler-referee review passed
Claim class: exact outgoing occurrence selection over the retained current SCC inventory
Authority: user-authorized shadow identity/evidence plumbing only
Semantic and production inference authority: none

## Result

`SccTopology::outgoing_uses(component)` validates the component against the
receiving collection and validates every retained use endpoint before it
returns a borrowed iterator. The iterator yields each retained branded
`SccUseRef` whose parent belongs to the requested component and whose target
belongs to another component, in retained batch order. It preserves distinct
use identities even when records share parent and target endpoints; it
allocates no query inventory.

The view classifies topology only. It does not classify generalized imports,
fixed/local partitions, eligible binders, Q/R substitutions, typed paths,
owner/receiver relations, profiles or source licensing. Each component's
`SuccessorGeneralizationRuleUnresolved` premise remains unconditional,
including empty outgoing results and absent source skeletons. No production
SCC plan, inference path, counter, or generalization behavior changed.

## Review and verification

One independent compiler-referee M1 review passed. The initial minor test gap
was closed with an explicitly synthetic retained-inventory test: it changes
only a cloned use's parent endpoint so two distinct branded UseIds share one
`(parent,target)` pair. This isolates occurrence preservation because the
current source collector emits at most one `DefinitionUse` per parent. It does
not claim that source collection produces this shape.

Focused observer tests also cover reverse dependency order, mutual and
isolated components, foreign components, missing endpoints, absent shadow
skeletons, unchanged counters, and the retained unresolved premise.

Checks run:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-solver --features shadow-scc-observer shadow_scc_observer -- --test-threads=1
rustfmt --edition 2024 --check --config skip_children=true crates/yu-solver/src/shadow_scc.rs crates/yu-solver/src/tests/shadow_scc_observer.rs
git diff --check -- crates/yu-solver/src/shadow_scc.rs crates/yu-solver/src/tests/shadow_scc_observer.rs
```

The observer suite passed 16 tests. The Cargo command was the only build/test
process, with two build jobs and one test thread. No broad/default-feature
check, benchmark or performance sample was run. A query validates all `U`
retained uses, then its lazy iterator scans the `U` uses again; one query is
`O(U)` with constant auxiliary memory, while querying all `C` components is
`O(C·U)`. This remains an opt-in shadow inspection path.
