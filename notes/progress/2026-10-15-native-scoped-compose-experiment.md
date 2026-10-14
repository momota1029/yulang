# Native scoped compose experiment

Date: 2026-10-15
Status: compiled and independently reviewed reversible native experiment; three finite source discriminators pass; full source theorem OPEN
Baseline: `3b95010a520157ab2b7dc902b44f9030c8d8b644`
Authority: [selected compose scope release](../design/2026-10-15-compose-scoped-effect-release.md), inference top-level principles and the native inference playground authorization

## Implemented responsibility

The opt-in `--scoped-experiment` route attaches the already reviewed scoped
transformer kernel to the actual native candidate relations. The ordinary
playground route leaves this experiment disabled. Source-owned region,
computation-scope and input-route identities are retained through capture and
FreshUse using shared injective maps. The original omitted-formal Function
demand qualifies its actual ArgumentEffect and ResultEffect dispatch:
`StampInput(u)` and `ProtectBody(F,u)`, respectively. The receiving Apply's
invocation-to-application effect edge releases its argument computation's
scope. Ordinary Value constraints retain the identity scoped transformer;
their existing context operations remain separate.

This is a provisional native representation. Catch still forwards the
scrutinee effect; handler subtraction, negative concrete callback permission,
principal scheme rendering and production cutover are not implemented here.
Unsupported callee provenance and recursive ownership are experimental
unavailability, not a restriction of the original source theorem.

## Proof applied to the identity case

The [ownership/capture derivation](../theory/2026-10-15-effect-scope-ownership-capture.md)
establishes ancestry and identity preservation under its explicit inventory
and frontier premises. Its native constructor induction separates Effect
transformers from Value contexts and establishes ordered replay composition.

A bounded constructive application to `compose id g` identifies this route
for a genuine contribution from `g`'s body:

```text
g ResultEffect      ProtectBody(E, u_g)
g Apply result      Release(X)
f ArgumentEffect    StampInput(u_f)
id entry -> return  identity
f ResultEffect      ProtectBody(F, u_f)
f Apply result      Release(E)
```

Here `E`, `F`, `X` and both input tags denote actual same-use copied
identities, with `E != X` and `u_g` absent on the genuine body route. The
resulting protection set is `(U union {E}) minus {X,E} = U minus {X,E}`.
The stamped `u_f` suppresses only newly introduced `F`; an inherited `F`
survives. Every independent protection outside `{X,E}` survives. This applies
the release to the path through the actual result of `f`, not merely a
separate output summand.

This calculation is conditional on the authenticated native chain and its
complete activation. A single released observed route is insufficient:
all completed fibers for the same outgoing contribution must be checked for
a remaining actual `E`. Shared original-source provenance does not establish
equality between distinct FreshUse instances.

## Review repair and resource boundary

M2 uses the same two independent reviewers for semantic and resource risks.
The first semantic review found a callee-guard bypass through a block-local
alias or conditional; the repair follows block final expressions and defers
unsupported callee joins and forwarding. The resource review found repeated
whole-state accounting scans, eager unbounded Support-member observations,
and copying of historical owned forests. The repair uses cached totals,
compact capped executed-relation evidence with bounded lazy rendering, and
explicit experimental inventory/work limits. Compact interned flow IDs
replace the large embedded per-relation flow record. This still has ordinary
per-key representation cost; disabled mode is not claimed cost-neutral.

No shared-inventory redesign or all-source complexity theorem is adopted.
The historical-forest concern is bounded for the experiment and remains an
architecture issue for a general implementation.

## Verification and remaining gate

The initial native prototype and its observer repair compiled. Eight direct
CLI executions covered compose identity, two uses, omitted callback and
direct argument. The first four lacked Support observations; the second four
showed live transformed records but lacked final source/use correlation.
They do not establish the selected complete compose result.

The first bounded repair compiled without warnings. Sixteen direct executions
covered five effect sources, four callee-provenance shapes and forest depths
0--6. Five effect sources and the direct callee solved; block-alias,
conditional and identity-forwarded callees deferred only in scoped mode.
Three detailed executions retained the actual dependency/origin records;
four ordinary-mode controls solved. Two additional count-only executions
covered forest depths 8 and 9, locating a successful bounded inventory and
the explicit availability limit, respectively. These are source executions,
not tests or a proof of the returned behavior.

The same semantic reviewer closed the callee finding, then identified a
nonidentity scoped self-edge shortcut before bound replay. The accepted
experimental repair rejects such a canonical relation before admission and
execution, including before endpoint memoization. No admitted-source witness
for this separate self-edge seam was claimed. The resource reviewer closed
the original three major findings for the capped experiment; source guard
work is now charged into the shared counter, and scratch reporting is
qualified as a maximum recorded owner envelope rather than a complete peak.

### Actual compose obstruction and owning repair

The detailed `compose-id` execution supplied actual same-use demands:
`g` parent 182 has `E28/u6`, and `f` parent 125 has `F25/u7`, both in use 1.
The good route `200 -> 215 -> 232 -> 258 -> 285 -> 321 -> 386` stamps the
input, forwards through copied id edge 111, withholds new F25 and releases
E28 through relation 91. Its descendant 689 reaches the final answer effect
row 15 with no protection.

However, all 48 recorded fibers at that same final destination included:

| Protection set | Fibers |
| --- | ---: |
| empty | 24 |
| F25 | 12 |
| E28 | 8 |
| F25 and E28 | 4 |

This is an actual finite failure of the prototype's all-fiber release
invariant. Two uses retained distinct identities but repeated the failure.
The independent-scope source preserved T53 on its good route, while another
route retained E40 alongside T53. The kernel calculation was not refuted.

Both the constructive proof worker and a separate architect traced the owner:
`begin_candidate_fresh_bound` attached mapped release relation 91, but
`candidate_bound_origin_with_evidence` then ignored its operational ownership
and called the idle `candidate_context_bound` fallback, creating identity
relation 92 for the same bound. The same fallback created an unqualified
Value demand beside the qualified demand, losing its input stamp. Diagnostic
origin copying and extrusion bootstrap have the same responsibility boundary.

The cause repair retains the exact transported relation for scoped FreshUse
and separates metadata-only origin/physical-copy records from executable
fiber admission. It must preserve authentic original identity fibers,
ordinary accumulated bounds, future replay, journals and the disabled route.
The new native observation is not accepted until the original three sources
are rerun and all final fibers inspected.

That repair is now integrated in the experiment. A subsequent semantic delta
found the same bootstrap responsibility in `merge_candidate_rows`; all three
physical-copy sites now share one metadata-only insertion helper, preserving
their original capture flag and exact subsequent fiber transfer. FreshUse
validates its mapped relation using the original snapshot, source bound,
use identity and the existing Transport HashSet. Diagnostic metadata retains
its explicit association gap with `Option<RelationId>`; it does not select or
create an executable relation. The disabled route retains its prior behavior.

### Final observed source result

All recorded completed final contribution observations now have the expected
protection state:

| Source | Actual release / receiver scopes | Final observations | Retained protections |
| --- | --- | ---: | --- |
| `compose id g` | E28 / F25, use 1 | 1 | empty |
| first of two uses | E35 / F32, use 1 | 1 | empty |
| second of two uses | E50 / F47, use 4 | 1 | empty |
| independent scope | E40 / F37, use 2 | 1 | T53 |

For the identity source, the actual chain is
`166 -> 170 -> 174 -> 178 -> 182 -> 185 -> 188 -> 191 -> 217 -> 232`.
It stamps u7 at 178, forwards through copied id edge 107, withholds new F25
through ResultEffect edge 123, and releases E28 through edge 89. Source
occurrence 25 slot 2 identifies the final application edge 226 and destination
15. The two-use final destinations are 15 and 22; the independent-scope final
destination is 22, identified by occurrence 35 slot 2, edge 317.

The proof worker inspected every recorded contribution at these final
destinations. There is no remaining fabricated default-flow bypass in these
logs. These counts are relation/operand observations, not an enumeration of
all semantic derivations. The kernel theorem and constructor-relative
calculation apply to these authenticated routes; global source completeness
and principality are not inferred from the finite observations.

The final sibling repair was rebuilt and the same three detailed executions
were byte-identical to the inspected logs. SHA-256:

```text
d70923500ba112f63bcc4f751034dd21083bf59ef1d41c8dfebc72d3703d4d78 compose-id
d32ba0f4e3f28bf79ba5c65a43ff6830a53ca1f9504b184696c25ef614b792ed two-uses
5ad7ad77e6f75c6c4e10e8294308f3a0dcabcdec3e1efc1bc5c91260ae2d1b40 independent-scope
```

Runnable sources are retained in
`tools/inference-playground/examples/compose-scoped-{identity,two-uses,independent}.yu`.
For example:

```sh
cargo run -q -p yu-playground -- --scoped-experiment tools/inference-playground/examples/compose-scoped-identity.yu
```

Add `--intrusion` for the bounded dependency/origin observations. The CLI
does not execute the VM or render the selected principal type scheme.

### Count-only inventory evidence

The family is `my a0 x = x`, followed by
`my aN = { my unused = aPrevious; aPrevious }`. At depth 6, 198 source bytes
produced 494 regions and 614 scopes. Each of the final two copies contained
126 regions and 157 scopes, although each captured type graph still had
10 nodes and 3 bounds. Thus historical nominal inventory growth is real and
independent of type graph size. Depth 8 completed at 2026 regions and 2528
scopes; depth 9 deferred without publishing output at the inventory limit.
There were nine count-only family-discriminator child processes and one
final cap recheck, no timing samples and no benchmarks. No tests were added
or run.

## Final integration checks

The same M2 `compiler_referee` closed the callee, self-edge, FreshUse and
physical-copy findings after their respective narrow deltas; no finding
remained. The `performance_auditor` closed the accounting/observation findings
for the capped experiment, retaining the explicit forest-growth and ordinary
layout-cost limitations. The primary's log checks do not replace those
independent reviews. The proof worker used requested Sol/high; runtime model
metadata was unavailable.

`CARGO_BUILD_JOBS=2 timeout 300s cargo build -q -p yu-playground` passed on
the final code without warnings. Three final detailed source reruns and all
three retained runnable examples succeeded. The corrected callback and direct
argument sources also solved; Catch still forwards everything, so these are
not subtraction or return-1 observations. The private alias guards and
inventory limit still deferred without partial output.
`CARGO_BUILD_JOBS=2 timeout 300s cargo check -q --workspace` also passed
without warnings. Cargo commands were serialized with two build jobs; no
test target or benchmark was run. Final `git diff --check`, local document
links and code-fence checks passed. Task, laboratory and design-status records
were synchronized in the same checkpoint; no required record was deferred.

The source compose theorem, complete alias/returned-function/recursive
coverage, handler eligibility/subtraction, soundness and principality remain
OPEN. The separate annotation-remainder question affects a handler with
both signal and write arms; it does not block this scoped compose experiment.
