# Shadow: retain pending application source uses through solve

Date: 2026-10-07
Baseline: `ad47dc466e48119946ecfacc40fa7ba2423916c1`
Status: compiler-referee reviewed M1 structural shadow slice and follow-up operand-identity differential
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

A follow-up differential now joins both direct operands of `x(x)` after solve
through their exact HIR positions to distinct source `UseId`s, the shared
source `BinderId`, and the retained syntactic Lambda declaration. In this
supported positive fixture, missing skeleton, Apply, or declaration metadata
fails the test rather than silently skipping the join. Unresolved/grouped
operands remain outside this direct-Name join and gain no inferred identity.

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

The compiler referee later found the first test draft could skip its new
source joins when metadata was missing. The supported fixture was changed to
require that metadata; independent delta review passed. The focused differential
target again passed all 4 tests, with one Cargo process, two build jobs and one
test thread.

Cost is the longer lifetime of the already allocated vector under the default-
off feature; borrowed iteration allocates no collection. No performance
samples were run.
