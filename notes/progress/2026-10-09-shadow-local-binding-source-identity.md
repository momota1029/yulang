# Shadow local-binding source identity and pending Call

Date: 2026-10-07
Status: implemented; M2 compiler-referee and regression reviews passed
Authority: user's default-off shadow/experimental implementation authorization
Baseline: `ad514061de2792c374a4b5c224dff7f4772906e8`
Implementation: source identity/evidence plumbing only; no semantic or production inference authority

## Change

The opt-in HIR shadow sidecar now retains the exact approved sequential local
binding shape `my apply f = { my step x = f x; step }`. It keeps a distinct
`HirLocalId`, local parameter `x` and its lexical owner, the returned local
use, capture list, and occurrence identities for the local lambda and pending
inner application. Each added HIR occurrence is joined to a unique source
position. Ordinary HIR remains an Error body with its existing diagnostic;
ordinary `ResolvedExpr`, name-resolution variants and parameter ownership are
unchanged.

With solver feature `shadow-f5`, collection retains exactly the inner `f x`
row as `ApplicationTypingRuleUnresolved` and carries that row unchanged through
solve. The unchanged outer Error body continues ordinary outer-parameter
bookkeeping. The local initializer is not sent through semantic collection:
there are no local Lambda recipes, local `x` recipes, typed facts, definition,
SCC, owner/receiver, admission or generalization judgments. Foreign artifacts
and six adjacent source shapes reject.

## Frozen Oracle correspondence

The frozen Oracle's ordinary source route historically lowers application
operands, allocates the `ApplicationArgument` origin, submits a four-port
Function demand, retains `Expr::App`, and records optional application/callee/
argument spans. Lexical `RefId` resolution connects uses to definitions; a
separate local-call path aggregates selected call-upper endpoints under a
resolved local definition and frame/formal marker. These are historical
identity, demand and lifecycle mechanisms only. They do not produce the current
original `beta`/`Slots(beta)`, typed `p0`, complete receiver invocation
contribution, or shared original `xi`; no Oracle rule or result is authority.
The bounded historical traces and stop conditions remain in the linked entries
in `tasks/current.md`.

## Review and checks

- Compiler-referee review found and closed an occurrence-ID collision risk;
  regression review found and closed pending-row lifecycle assertion gaps.
- The delta removing a skipped outer-parameter recipe was independently
  re-reviewed by both reviewers; no findings. It preserves the baseline outer
  recipe while leaving local `x` semantic collection unresolved.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-solver --features shadow-f5 shadow_local_bind -- --test-threads=1` — 2 passed after the final code delta.
- `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo check -p yu-hir` and
  `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo check -p yu-solver` — passed with
  shadow disabled.
- Targeted rustfmt checks on HIR files and integration test passed. The
  solver file has pre-existing whole-file formatting drift; the changed hunk
  matches rustfmt output. `git diff --check` passed.
- No performance samples; additions are cold/opt-in and production type
  layouts remain unchanged. No workspace-wide suite was run.

## Remaining boundary

This closes one shadow source-identity and pending-evidence lifecycle slice.
It does not type the local binding or application, form a generalized SCC
interface, establish soundness, principality or source adequacy, or authorize
production cutover. `ORIGINAL_ASSOC` and all dependent theory gates remain
open. Oracle history contributes no semantic premise.
