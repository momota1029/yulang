# Successor source levels and live local schemes

Date: 2026-10-10
Baseline: `269f10a27`
Scope: private candidate solver; not ordinary source acceptance or F5 cutover
Authority: current inference objective, Simple-sub reassessment and user correction
Mode: M2; independent compiler-referee and performance-auditor

## Source and live scheme path

`CandidateInference` now consumes an actual HIR `LocalSource` where present.
The source planner retains flat actions, actual component/parameter levels,
local identities and every ModuleDef dependency. Roots without a carrier retain
their previous collector, with compatible schedules when the module uses the
new source route. Default and legacy non-graph collection stay on their routes.

Top initializer coordinates are level one with boundary zero. Local initializer
coordinates use the checked child level of the enclosing computation; Lambda
parameters inherit that actual level. Formal references alias their actual
parameter row. Local uses resolve the original local identity, not spelling.

A local installation retains its actual live value root and enclosing boundary.
It does not freeze a graph or certify saturation. Each use captures the current
eligible graph as temporary freshening input and reconstructs it with one
kind-qualified map. Older/non-generic rows retain their live identity and bounds.
Directional owner-side bound restoration and all four Function ports survive
the shared module/local freshening kernel. A timed graph and row map are retained
for private observation of that use, not as the binding's semantic authority.

Source-directed execution uses existing immediate constraints. Intrinsic RHS
relations are installed before copying them; this implementation does not claim
that completed solving must precede continuation constraints. Later constraints
through shared older extrusion coordinates remain valid. Initializer evaluation
effects enter block evaluation once; local Name fetching does not rerun them.
Lambda construction remains pure with body effects retained in its Function.

Dependency-first top components execute source actions; module Name uses route
when their action executes. Every member graph is staged before component
publication. Existing internal-SCC rejection remains. Local routing reuses the
route transaction, including fresh rows/terms/bounds/pairs/diagnostics, observer
truncation and resource totals on failure.

## Independent review

The frozen semantic review found no blocking, major or minor correctness issue.
It checked actual levels and formal aliases, source identity/scoping, independent
use maps, four-port incidence, later captured-anchor refinement, mixed carrier
module routing, one-shot initializer effects, rollback and default dispatch.
A symbolic captured-function trace confirmed later constraints through the outer
formal reach fresh local uses. This is static evidence, not executed coverage.

The resource review found no blocking/major issue. One minor observer-cost
finding is accepted and documented: `fresh_use` scans local then module routes.
One lookup is O(U), and looking up every use individually is O(U²). No occurrence
cache is introduced without a demonstrated bulk-observation requirement.

## Costs and limits

Source planning is expected O(N+B+F) plus identity hashing/cloning, with flat
work/action storage. Per-use capture/reconstruction visits its reachable graph;
aggregate retained use graphs and maps cost the sum of their sizes. Propagation,
extrusion, diagnostic/journal work is additional. Repeated large locals and
graphs containing prior instantiations can multiply work; no overall linearity
claim is made. Rollback rescans surviving graph/route totals on the failure path.

Samples use logical capacities, excluding allocator overhead, some identity
payloads and failed partial-capture peaks. Width/graph size are not bounded by
the existing source depth 128. No RSS, complete exhaustion recovery or numerical
practical resource certificate is asserted.

## Checks

Primary checks passed without warnings on the frozen artifact:

- `RUSTC_WRAPPER= cargo check -p yu-solver --features shadow-apply-candidate -j 2 --offline`
- `RUSTC_WRAPPER= cargo check -p yu-solver -j 2 --offline`
- `git diff --check`

No tests, execution probes or measurements ran. Budget consumed: zero samples
and zero measurement processes. Existing inspected tests do not execute this
generic local-source consumer. No workspace-wide build/suite was repeated.

Frozen SHA-256:

- candidate_source.rs: `102751d8eb2425c74d8cb094d1cc2bdd2796dcd5b1eb099c3a506c6ffe7a242f`
- lib.rs: `03801bed84e3dc371ff448800ad4410f376995b6d87ce808fff1fab893994db1`
- candidate_scheme.rs: `ae1c8555f600dc0bc5c1468ae7271c8770d6727c94c997a7305c393e7e8bf243`
- shadow_apply.rs: `2de1407cd31229e278ea40caf75cd49bf99c0635944a0f3d369ba4c3d4819748`

## Remaining objective

Retain actual complete Call source-spine inputs at these owning source events,
using the existing LocalSource plain-header admission provenance. No new
annotation-absence boolean is required. Specific complete consumer obligations
must not be replaced by scalar success or fabricated certificates. Complete
Call, structured effects, general source/public scheme correspondence,
principality and replacement on `yulang3` remain open. The full goal stays active.
