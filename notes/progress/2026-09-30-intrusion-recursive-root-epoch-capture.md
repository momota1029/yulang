# Recursive selector fixture: root epochs and use identity maps

Date: 2026-09-30
Branch: `research/simple-sub-intrusion`
Reference: frozen Yulang2 Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Classification: instrumented source-path observation; no root simulation theorem

## Captured root preparation

In the existing detached Rust probe worktree, temporary diagnostic-only output
was added around the production `generalize_root_with_prepasses_and_metrics`
path. A focused run of

```text
YULANG_INTRUSION_ROOT_TRACE=1 YULANG_INTRUSION_INSTANCE_TRACE=1 YULANG_TRACE_SCHEME_DEFS=5,6 CARGO_TARGET_DIR=/tmp/yulang-intrusion-oracle-target cargo test -p infer --lib source_recursive_nominal_field_projection_probe -- --nocapture
```

passed. The test's source-name lookup maps `ints` to `DefId(5)` and `mixed` to
`DefId(6)`. In this run, `ints` used root `TypeVar(20)`: root preparation
began at `ConstraintEpoch(569)`, selected compact views at epochs 569, 570,
573, 574, and 574, and saved the generalized compact root at epoch 574.
`mixed` used root `TypeVar(54)`: preparation began at epoch 823, selected
views at 823, 824, 827, 828, and 828, and saved at epoch 828. These numeric
epochs are run-local diagnostic identities, not semantic names or a claim that
other builds must use the same numbers.

The final selected compact view for `ints` contains the nested nominal `step`
interval with lower `CompactType` containing `TypeVar(138)`, secondary
`TypeVar(35)`, and `Int`, and upper `TypeVar(138)`. The corresponding `mixed`
view contains `TypeVar(142)`, secondary `TypeVar(69)`, and `Bool` below, and
`TypeVar(142)` above. The outer productive recursive
variables are separate: `TypeVar(137)` for `ints` and `TypeVar(141)` for
`mixed`; each recursive interval's lower side points back to itself and to a
guarded `step`, with upper `Top`. The exact finalized raw scheme nodes and
their relationship to this compact view are in
`2026-09-30-intrusion-recursive-selector-adequacy.md`.

This supplies a concrete source-root view at each member's actual preparation
epoch for two separately self-recursive definitions; they are not one mutual
SCC. It does not prove projection congruence for arbitrary roots, nor that all
intermediate epochs are related to an intrusion state. The final compact
interval evidence also does not by itself define a denotational satisfaction
relation.

## Per-use freshening observation

The same trace observed the two external source uses. `ints` was instantiated
for parent `DefId(8)` at `TypeVar(113)`; its source binders
`TypeVar(137/138/139)` mapped in one invocation to
`TypeVar(144/145/146)`. `mixed` was instantiated for parent `DefId(9)` at
`TypeVar(126)`; its source binders `TypeVar(141/142/143)` mapped to
`TypeVar(147/148/149)`. The two per-use ranges are disjoint, and each mapping
preserves the inner payload and recursive-root identities as distinct binders
within that use. This is a direct observation of the existing instantiator on
these calls; it is not a general proof of use independence or outer-anchor
preservation.

Together with the asserted public inferred results (`int` and `bool`), the
probe now connects the actual prepared views to fresh use maps and public
observations for this fixture. The same run also reports two OCast classifications,
zero source-boundary-eligible events, and two incomplete events with
`UnknownOrigin(OriginId(1))`. Each producer's `why_constraint` explanation is
complete, has five source leaves, and contains two unknown-origin
variable-to-variable root edges. No diagnostics are emitted. Those edges have
the shape produced by `AnalysisSession::constrain_open_use`, but this trace does
not yet identify each edge with a particular recursive call occurrence.

The two incomplete OCast producers themselves are both nominal head checks of
`Pos::Con(step, ...) <: Neg::Con(int, [])`. Thus the classifier sees an actual
`step`-to-`int` mismatch on each selector call, but emits no diagnostic. The
full explanation also reaches unknown-origin variable links.

A second Rust-only trace of structural parents identifies the local route. For
the `ints` use, record 610 is a same-head outer `step <: step` comparison.
Its second argument produces record 616 (`Union <: int`) through
`ConstructorArgument { index: 1, direction: LowerToUpper }`; record 625 is
branch 1 of that union and is the `step <: int` producer. The `mixed` use has
the parallel chain 612 → 620 → 629. These record and type-arena IDs are
run-local observations. This establishes that the nominal events arise along
the recursive second-argument path of the selector comparison. It does not
establish what created the parent `step <: step` comparisons.

The full `why_constraint` probe initially left a provenance gap because OCast
classification uses `why_constraint_without_scheme_instantiation`. A follow-up
Rust probe captured that exact classifier query. For `ints`, the path is:

```text
producer 625
  <- UnionBranch 616
  <- ConstructorArgument(index=1, LowerToUpper) 610
  <- BinaryReplay(pivot=TypeVar(144), lower=bound 828, upper=bound 932)
  <- lower bound 828 <- constraint 514 <- UnionBranch constraint 513
  <- RootOrigin UnknownInternal(OriginId(1))
```

The source map identifies `TypeVar(144)` as this use's fresh instance of
recursive binder `TypeVar(137)`. Constraint 513 has shape
`Union(Var(TypeVar(144)), Pos::Con(step, ...)) <: Var(TypeVar(144))` in this
run. The classifier's own explanation therefore contains the unknown origin
on the ancestry of the nominal event; the earlier edge-count mismatch is
resolved for this producer. The mixed branch has the parallel chain 629 → 620
→ 612 → BinaryReplay at `TypeVar(147)` (lower bound 835, upper bound 940) →
lower-bound ancestry 835 → 520 → 519 → `UnknownInternal(OriginId(1))`.

These paths establish a reachable unknown-origin explanation for each
classifier result. They do not show where the `UnknownInternal` origin was
created, that it is the only possible cause, or that the subtype constraint is
accepted. IDs are run-local.

The final constraint bounds for the selector-result path also expose a smaller
endpoint graph. For `ints`, let `p=TypeVar(145)` be the fresh inner payload
from `ints`, `a=TypeVar(154)` be the getter result binder, `u=TypeVar(120)` be
the call-result intermediate, and `r=TypeVar(110)` be the exported result
root. The captured lower/upper endpoints are:

```text
Int ≤ p, a, u, r
a ≤ p ≤ a
p, a ≤ u ≤ r
```

More explicitly, both `p` and `a` have `Int` and the other variable as lower
endpoints, and each has the other variable plus `u` and `r` as upper
endpoints. `u` has lower endpoints `p`, `a`, and `Int`, and upper endpoint
`r`; `r` has lower endpoints `u`, `p`, `a`, and `Int`. For `mixed`, the
same endpoint shape holds with `p=TypeVar(148)`, `a=TypeVar(155)`,
`u=TypeVar(133)`, `r=TypeVar(123)`, and `Bool` replacing `Int`.

Conditionally interpret each captured lower/upper endpoint as an ordinary
inequality in a preorder. For this endpoint subgraph alone, assigning every
vertex `Int` (respectively `Bool`) satisfies the inequalities, and every
satisfying assignment places that constant below `r`. Thus the constant is the
least root value for this subgraph, up to preorder equivalence. This gives a
local calculation for the public endpoint result, but does not select the
replacement carrier or prove that the Oracle uses this subgraph as its complete
principal-solution relation. It also does **not** show that the complete
recursive-use graph is satisfiable in the same carrier: the separate
`step <: int` OCast events are ineligible for source diagnostics due unknown
origins, and their semantics must remain a separate outcome in the machine
relation.

This separates two simultaneous Oracle observations: the selector result is
inferred as `int` / `bool`, while the nominal event classifier cannot establish
source-boundary eligibility because recursive unknown-origin edges remain in
the explanation. The latter is not evidence that all subtype constraints
succeeded. The remaining local proof step is to trace which instantiated
constraints produce the endpoint result, then relate that path and the exact
incomplete classifier route to candidate inference and diagnostics. The
broader Gate C carrier, root-step simulation, and principality obligations
remain open.

No compiler source or test in the redesign worktree changed. All temporary
instrumentation was confined to the Oracle probe worktree; it emitted
diagnostic output and made the classifier explanation method visible to the
test module. The focused Rust test passed; no Python model or performance
measurement was used.

## Review

A compiler-referee delta review found the structural chain above supported by
the trace and identified the mismatch between full and classifier-specific
explanations. A follow-up review of the classifier-specific trace confirms the
UnknownInternal ancestry for both producers. The source of that origin and the
upstream creation of records 610/612 remain uninspected; this is not an
acceptance or soundness result. Reviewers made no edits or ran tests.
