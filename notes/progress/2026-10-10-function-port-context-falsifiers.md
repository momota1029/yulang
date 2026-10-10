# Function-port contexts: bounded falsification result

Status: frozen, unreviewed research-only source characterization and conditional
derivation; no theorem closure or production authorization.
Baseline: `3efa7a86c233ea0cbad5d034f8023c4ce731f69a`.
Authority: `notes/design/2026-10-10-contextual-attachment-admission-design.md`
§§3–6, particularly §4 Function ports and negative-wrapper discharge.
Method: trace existing source constructors, four-port decomposition, context
seeding and closed-filter execution; distinguish abstract weights from live
source reachability. No Cargo or executable model was run.

## Result and exact premise

FunctionField provenance can be added without changing current child-local
context reconstruction, conditionally on retaining the same typed endpoints,
relation/context handles, child admission, filter execution, bound registration,
replay order and rollback behavior. Metadata alone neither supplies nor
authorizes Swap/Both execution. This is a proposed implementation boundary,
not a verified patch or whole-compiler preservation theorem.

No supported current Function Value comparison with an inherited closed-filter
context was found. The actual argument-port closed-filter example below exists,
but its direct Function child has identity context. Its Allowance descendant
has a child-local filter and already requires the existing consumer. Thus it
does not falsify the narrower premise that provenance-only enrichment can
preserve current execution.

## Smallest inspected actual shape

An existing fixture supplies one written Function with a concrete argument
effect row at positive composed variance:

```yulang
act io
my bridge (consume:([io] int) -> ()) = consume
```

This is the arrow-depth-one argument-effect case in
`crates/yu-solver/tests/candidate_formal_effect_polarity.rs:59`
(`positive_argument_effect_port_admits_a_concrete_row`). The enclosing formal
starts negative; its argument reverses variance to positive. The fixture's
assertion establishes the intended existing test contract, not a test result
from this assignment. No global source minimization search was performed.

Let v be the closed io view; q+ and q− are the paired argument-effect rows.
The source-owned construction is:

1. `candidate_formal_pair`, `candidate_effect.rs:898`, reverses the argument
   variance and builds positive/negative Functions with all four ports.
2. `candidate_formal_effect_port`, `:918`, delegates the positive written row
   to `candidate_signature_effect`, `:1303`, on both polarities.
3. That constructor inserts `Support(v) <= q+` and `q− <= Allowance(v)` and
   returns ordinary row terms. The Function's argument Effect port is a row,
   not a ContextExpr or direct Allowance term (`:1418`).
4. At a comparison F+ <= F−, `lib.rs:11977` emits argument Effect
   `argE(F−) <= argE(F+)`, reversing endpoints. Its context is reconstructed
   by `candidate_context_admit`, `candidate_context.rs:1339`, from this
   child pair. For row-to-row endpoints this yields identity.
5. Ordinary bound/operand propagation subsequently reaches an Effect pair
   with upper `Allowance(v)`. `candidate_closed_allowance`, `:1292`, and
   `candidate_context_source`, `:1297`, reconstruct
   `PrefixLeft(weight(v), Identity)` at that pair. The filter can also be
   processed during signature-bound construction before a Function comparison;
   it is not first created by the Function port operation.
6. `candidate_context_execute`, `:1365`, checks/registers the true receiving
   Allowance before memo handling. `post_check_context`, `:1246`, consumes the
   closed prefix for the stored bound while retaining its obligation and
   derivation. Future lowers retain the Allowance owner.

A result-port witness uses the existing simpler whole annotation
`act E; my id x: int -> [E] int = x` in
`candidate_effect_annotation.rs:39`. Its direct result Effect comparison is
also between row ports. Later Allowance tasks reconstruct their own filter.
The outside E-versus-F boundary fixture at `:178` records why that obligation
must remain live; this assignment did not execute it.

## Abstract context table and composition order

Write I for `(left=empty, filter=All, right=empty)` and C_A for the closed
zero-word prefix `(empty, A, empty)`. A may be empty or contain one family.
The existing detached evaluator at `candidate_context.rs:699–738` gives:

| Parent context | Argument inherited meaning | Result inherited meaning | Current live Function-parent reachability |
| --- | --- | --- | --- |
| I | swap(I) = I | I | ordinary source comparisons |
| C_A | swap(C_A) = I | C_A | no source-owned filtered Value parent found |
| Replay(C_A, I) or Replay(I, C_A) | I | C_A | abstract only; consumed closed-filter bounds store I |
| context with nonzero left POP/right POP | potentially nonidentity | unchanged | detached only in this baseline |

Swap uses right POPs as left POPs, uses left POPs as right POPs, and removes
left PUSHes and filters. It is not an involution in general. Consequently a
closed-filter-only parent is not the expected nonidentity argument falsifier.
For a child-local filter, wrapper order matters:

```text
PrefixLeft(C_A, Swap(I)) evaluates to C_A
Swap(PrefixLeft(C_A, I)) evaluates to I
```

The first means the child introduces its own wrapper after inherited argument
transformation. The second swaps an already present parent wrapper. Applying
Swap to a child's reconstructed local filter would change which operation
owns it; FunctionField provenance must not conflate these two constructions.
For results, inherited context is preserved and local wrapper admission still
belongs to its source constructor. Ordered Replay keeps lower then upper;
the zero-word example's coincident values do not justify commuting Replay in
the general algebra.

Structural and executable identities are distinct. A literal `Swap { input:
IDENTITY }` node evaluates to I in the detached evaluator but is a nonidentity
ContextId. The live executor accepts only identity or a closed PrefixLeft;
it returns `exhausted()` for Swap. Adding executable Swap(I) tasks therefore
needs a separate consumer/admission change even on current ordinary sources.
The table does not authorize canonicalizing arbitrary contexts or dropping
source certificates.

## Why the expected live parent witness is absent in the inspected paths

`candidate_context_source` introduces a prefix only for an Effect pair whose
upper endpoint is an Allowance with `closed_weight`. `LocalWeight` has zero
left/right words (`candidate_context.rs:17–24`). Function decomposition is
dispatched on Value pairs (`lib.rs:11833,11977`). Signature constructors return
EffectRow ports after installing Support/Allowance bounds. Closed prefixes
are consumed before bound replay; identity/identity replay stores identity
(`candidate_context.rs:1505`). Context transport retains component kind.
These inspected owning paths provide no route that turns an executable closed
Effect filter into a Function Value parent context. Test-only insertion of an
arbitrary ContextExpr is not such a source route.

This is bounded source characterization: no exhaustive graph induction over
all extrusion, freshening, intrusion and restore branches was undertaken.
Nonempty source operations, contextual Function execution, inferred-entry Both
authorization and circuit admission remain open and cannot use this result
as closure evidence.

## Mutation boundaries, oracle and verification

The attacked shortcuts were: treating a child-local filter as inherited parent
context; assuming Swap(closed-filter) is nonidentity; and treating semantic I
as permission to enqueue a structural Swap(I). Source inspection discriminates
all three. No mutation was applied and no observable compiler mismatch is
claimed. In particular replacing a filtered relation with identity alone may
still leave an ordinary Allowance endpoint check in `candidate_check_effect_operand`
(`candidate_effect.rs:749–813`); lost observable checking needs separate
memo/discharge/lifecycle evidence. Deleting the endpoint/bound obligation is a
stronger mutation than adding FunctionField metadata.

The abstract algebra derives from the baseline detached evaluator and the
approved Function rule; it is not an independent oracle and does not prove
source generation. The source bridge uses actual constructors and retained
tests as separate evidence. No seed/range enumeration or new tests ran. Exact
checks: targeted `rg`/`sed` reads; `git rev-parse HEAD`; dependency SHA-256
comparison against baseline; leased-note whitespace check. No Cargo, builds,
formatters, Git mutations or child delegation. Independent lightweight reads
were batched, with at most four concurrent shell read commands; the final
dependency/whitespace check used one Python process. CPU/RAM and exact wall time were not
metered; no heavyweight compute or persistent process was started. One broad
task-record read was output-truncated and is not claimed fully inspected.

Recommended next action: add operation-incidence/FunctionField provenance
while preserving existing child-local reconstruction, then require a separate
live-context consumer gate before enqueuing Swap/Both operation nodes.

## Commit packet

- Exact leased/changed path:
  `notes/progress/2026-10-10-function-port-context-falsifiers.md`.
- Baseline: `3efa7a86c233ea0cbad5d034f8023c4ce731f69a`.
- Dependency changes: none at freeze. Authority SHA-256:
  `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc`.
  Direct context source SHA-256:
  `4bca8eb673c578b4db52c4ca05cd1604a7560f0a949e17e132b6e9f514621b0a`.
- Review: unreviewed research-only; author is not an independent reviewer.
- Checks: source trace and baseline/dependency checks; note whitespace check;
  no executable/compiler verification.
- Proposed commit message: `research: characterize current Function-port closed-filter contexts`.
- Shared-record deltas left for primary/curator: retain child-local filter
  construction as an explicit premise of the next provenance slice; record
  structural Swap(I) consumer as a separate gate; do not mark contextual
  Function execution or general admission complete.
