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
observations for this fixture. The remaining local proof step is to derive the
selector's subtype/projection obligations from those instantiated views and
show that they expose the least endpoint payload. The broader Gate C carrier,
root-step simulation, and principality obligations remain open.

No compiler source or test in the redesign worktree changed. All instrumentation
was confined to the temporary Oracle probe worktree; it only emitted diagnostic
output. The focused Rust test passed; no Python model or performance measurement
was used.
