# Current SCC copy, closure, and update correspondence

Date: 2026-10-06
Status: reviewed bounded production correspondence; no successor-gate closure
Baseline: `5f5362993e7540ec9be171617396bdee9991c042`
Scope: map the three abstract obligations in the [premise-separation checkpoint](2026-10-05-source-scc-copy-closure-falsification.md) to current finalized-scheme instantiation and binary row-constraint propagation
Implementation authority: none

## Result

The current implementation has concrete owners that exclude the checkpoint's
three exact failure patterns within the inspected pure closed-scheme and
binary row-replay routes. This narrows the gap from abstract possibility to a
successor correspondence obligation. It does not establish the successor's
general source/context closure premises, source-admission completeness,
soundness, principality, or practical resource bounds.

## 1. Closed-scheme traversal

`InferenceSession::closed_parts` (`crates/yu-solver/src/lib.rs:14199`)
performs iterative postorder materialization. It places a completion marker
before child work and inserts positive/negative memo entries only on completion
(`lib.rs:14340,14481`). Quantified and Recursive values resolve to rows in the
substitution and do not traverse recursive bounds (`lib.rs:14252,14262,14396,14406`).
Thus the copier itself is not a general memo-before-recursion graph copier;
its termination relies on the finalized constructor relation.

`ClosedTypeFinalizer` constructors validate that children already exist before
appending Function, Union, or Intersection parents
(`crates/yu-types/src/lib.rs:1822,1840,1881,1899,2041,2048`). Indexed input
validation separately uses visiting/completed colors and rejects a constructor
node reached while visiting (`yu-types/src/lib.rs:405,527`); Recursive and
Quantified nodes are leaves of this constructor relation (`:540,:559`). This
proves acyclicity of finalized constructor edges, not of recursive-binder
semantics.

`instantiate_and_route_closed_inner` allocates quantified substitution rows,
then recursive binder rows, before restoring bounds or traversing the
predicate (`yu-solver/src/lib.rs:14527,14536,14563,14592,14627`). This is the
current pure scheme route, not arbitrary future scheme/freshening semantics.
Function reconstruction enumerates finite child products; traversal
termination does not imply one output node per source node, a small expansion
bound, or a practical resource bound. `ClosedValueScheme::clone` copies its
descriptor; freshening is the later substitution and traversal operation.

## 2. Canonical comparison carrier

Current canonical value and typed pair keys have fixed binary arity
(`crates/yu-solver/src/lib.rs:717,731`), as do `LiveConstraintTask` variants
(`:3722`). Function decomposition emits four typed child comparisons (`:11164`).
Variable-length diagnostic children are adjacency lists attached to a pair
(`:3741,3747`); the list is not part of comparison-key identity. Immutable
interned Function terms validate their existing polarized children before
construction (`crates/yu-solver/src/term.rs:1122`).

Consequently, the arbitrary-length parent tuple in the checkpoint is not a
current typed-pair key. With a supplied finite endpoint inventory, this
specific binary comparison carrier is finite. The inspected implementation
does not provide a successor source/context judgment whose complete rule,
evidence, and canonicalization carrier could be bounded by this observation.
Nor does it bound intermediate summaries or instantiated products by source
size.

## 3. Retained-bound update replay

For current value bounds, inserting a row edge retains both directions and
replays previously present endpoint memberships; inserting a membership
checks existing opposite memberships and direct edges
(`crates/yu-solver/src/lib.rs:12118-12164,12196,12211,12252,12268`). Effect
bounds have analogous symmetric replay (`:10901,10919,10967,11020`). Mutation
and scheduling occur synchronously, and the driver drains its queue before
successful return (`:11072,11219`). Pair memoization skips already admitted
comparisons (`:11084,11093`). This supports arrival-order coverage for these
retained bounds/edges and rules out the checkpoint's lost-subscription trace
for this mechanism.

It does not establish arbitrary versioned dependency rechecking or invalidate
all cached judgments under every later update. New definition-dependency arcs
have a separate owner and lifecycle: the Authoritative F0-F2 foundation
excludes solve-discovered dependencies, requires an approved incremental or
readiness owner (or recollected sealed plan), and does not permit published
components to reopen (`notes/design/2026-09-20-constraint-collection-scc-foundation-draft.md`,
“Lightweight-port boundary”). Finite value changes on existing rows do not
authorize new SCC arcs.

## Review and limits

Independent `compiler_referee` review found no blocking or major issue in this
bounded correspondence. The reviewer required retaining the distinctions
above: constructor acyclicity is not recursive-binder acyclicity; postorder
memoization is not arbitrary cyclic copying; fixed binary pair keys do not
establish a successor context carrier; symmetric row replay is not a general
versioned invalidation protocol. The review also confirmed that indexed
validation and row insertion-order tests exist, but this note relies on source
inspection and did not run them.

Inspected: focused sections of `yu-solver/src/lib.rs`,
`yu-solver/src/term.rs`, `yu-types/src/lib.rs`, `yu-solver/src/scc.rs`,
`yu-solver/src/f5c_generalization.rs`, the cited F0-F2 authority, and the
abstract checkpoint. This is a bounded production correspondence, not a
repository-wide absence claim.

Actions: read-only source inspection and independent review; zero tests,
builds, probes, code edits, or production inference changes. No implementation
or semantic-policy authorization follows.
