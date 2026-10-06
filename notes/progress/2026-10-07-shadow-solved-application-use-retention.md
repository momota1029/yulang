# Shadow: retain pending application source uses through solve

Date: 2026-10-07
Baseline: `ad47dc466e48119946ecfacc40fa7ba2423916c1`
Status: compiler-referee reviewed M1 structural shadow slice
Authority: user-authorized default-off experimental identity plumbing; no semantic or production authority

## Result

The `shadow-f5` collector already retained ordinary application rows, but
`InferenceSession::finish` dropped them when constructing `SolvedModule`. The
frozen change moves the existing row vector into the solved result and exposes
the same borrowed direct-Name/use iterator on both owners. It preserves row
allocation, ordering, HIR identity, operand positions and existing resolution
payloads across solve without cloning or rebuilding rows.

Every row remains
`ApplicationTypingRuleUnresolved`. This change creates no typing facts,
dependency edges, counters, callable roles, source slots, profiles, or SCC
behavior. It does not establish old-infer equivalence, application typing,
soundness, principality, or source adequacy.

## Verification and review

The implementer ran these checks sequentially, with two Cargo build jobs and
one test thread:

- `cargo test -p yu-solver --features shadow-f5 --test shadow_f5_differential -- --test-threads=1` — 4 passed.
- `cargo test -p yu-solver --features shadow-f5 --lib shadow_application_collection_remains_unsupported_without_facts -- --test-threads=1` — 1 passed, 449 filtered.
- `cargo check -p yu-solver` with `shadow-f5` disabled — passed.
- Targeted rustfmt check and `git diff --check` — passed.

The compiler-referee review passed with no correctness findings. It confirmed
the move preserves the collector-owned vector and that feature-off builds omit
the field, move and accessors. Review did not cover broad suites, combined
observer features, old-infer application equivalence or semantics.

Cost is the longer lifetime of the already allocated vector under the default-
off feature; borrowed iteration allocates no collection. No performance
samples were run.
