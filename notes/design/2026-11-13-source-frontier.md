# Source frontier and termination for point identity leaves

Date: 2026-11-13. Base: `2ea63eb6c98c6ed4a16ecefea5c06bb63f529852`,
branch `astra/source-frontier`.
Status: **Restricted end-to-end accessibility proved; general B4(1) remains open.**

This continues the five obligations in §6 of
[Hole elimination, observations, and interval facets](2026-11-13-hole-elimination.md).
Authority remains spec/06-roles.md §6, the approved B4 draft including addendum 7,
and the current task. No Step or guard is changed and no language decision is added.

## 1. General finite direct-path frontier

For a fixed source snapshot with n slots, label every structural child edge by
its shape and position, and every point nominal argument edge by its nominal
name and position. A walk records the slots it expands and its final opaque
slot. Every expanded slot must satisfy `¬ CycleK2.RecursAt`. The final slot need
not satisfy this condition: capturing a recursive value without inspecting it
is permitted.

If any slot repeats, take its first occurrence and the edge leaving that
occurrence. The remaining walk reaches it again. This is a `DirectCycle` at an
expanded slot and contradicts its K2 certificate. Hence the expanded slots
followed by the terminal slot are distinct. They belong to `List.finRange n`,
so the number of projections is strictly less than n. A finite traversal of all
labeled edges to fuel n, starting at each source slot, therefore contains every
such origin. Add the initial listed source IDs to include non-slot reservations.
These claims are `walk_distinct`, `walk_length`, `frontier_covers`, `cycle_stops`
and `initial_inputs` in `GeneralNominalSourceFrontier`.

This is a theorem about labeled direct walks. It does **not** extract a walk
from every actual recursive-inspection report, prove the observational readback
of each label, or cover strict nominal interval captures. For a strict argument,
the actual projection cannot simply be replaced by either endpoint; identical
strict endpoint pairs alone cannot identify two different argument occurrences. The general
frontier producer remains open at precisely these bridges. No infinite safe-walk
counterexample or infinite shared-Step execution was established.

## 2. Precisely restricted source class

To obtain a complete source-to-Acc result without assuming those bridges, use:

- Every declaration has head `[var 0]`, no where clauses, and every associated
  RHS is `var 0` (`IdentityLeaf.RegistryShape`). The registry may be nonempty
  and may contain several declarations and roles. Checked leaf declarations
  already have no output-only binders, by their production condition.
- The root is unary and its argument is the single interval `(i,i)`, expressed
  exactly by `List.ofFn root.demand.arguments = [(i,i)]` (`IdentityLeaf.Point`).
- The registry is checked and the initial data satisfy the existing
  `InitialSource`. No restriction is imposed on unrelated source slots,
  source constructors, ordinary constraints, or unrelated strict intervals.

This is not a theorem for arbitrary point-only programs: it also restricts
all implementation heads and their associated equations. It still permits a
real installation that identifies a distinct, previously unknown output with
the input. The final theorem is about the **existing** `SharedSteps.Step`, with
all its current matching, K2, settled-provenance and consistency conditions.
It has no SourceBudget, cover, rank, semantic-readback, or future-reachability
premise.

## 3. Initial H and the producer invariant

Let

```
H = [0, ..., initial.seed] filtered by membership in initial.sources.
```

`InitialSource.below_seed` proves that H is exactly the initial listed IDs.
It is duplicate-free because it is a filtered range. `initial_frontier` proves
that the input i and every root output target belong to H. The origin basis is
`H.map Origin.source`. The input remains a symbolic leaf; any recursive
structure inside its value stays opaque to variable-head inspection. Root K2
still applies through the existing installation conditions.

There are no relevant projection paths in this class. Source-slot lookup and
injectivity give the same singleton bounds `(s,s)` for every enabled packet,
with `source s = i`. Actual producer calculations establish:

1. The ordinary report has one capture `(0,(s,s),none)` and two reflexive interval
   checks. Its constructor tests and inspected positions are empty
   (`report_exact`).
2. The inherited report retains `some (source i)` in that same capture
   (`inherited_capture`). It does not choose an interval interior.
3. The allocator reuses `(i,i)`; its input facets are each `leaf i`
   (`capture_exact`, `capture_facets`). No join, meet, or fresh endpoint is used
   by the capture. The complete semantic `Inputs` condition is true for every
   assignment (`inputs_valid`).
4. There are no child emissions or input-materialization requests
   (`children_empty`, the existing `leaf_input_schema`). The named schema is
   exactly the list of actual-variable uses at the targets returned by the real
   associated-equation lookup (`named_schema`).
5. Every such target is an original requested output (`target_requested`).
   Each output use has a one-leaf readback `leaf (source i)`
   (`output_readback`, and `installed_readback` over H).

Administrative operations preserve the root site; enqueue is impossible for
an already generated, registered root. A leaf installation adds no sites.
Therefore every reachable site is the original point site and every generated
occurrence is the root (`formed_sites`, `generated_root`). All visible
candidate declarations have empty query reads, not just the selected packet.
The exact root/read positions in the decision guard can consequently name only
i (`decision_use_exact`). A different reserved or newly allocated ID cannot be
one of those positions (`new_id_not_decision`). This last result concerns direct
consumer positions, not arbitrary syntactic mentions inside support proofs.

No complete general mixed constructor/facet representation is being claimed.
For this class the producer calculation exhausts both kinds of term: one actual
leaf and two endpoint leaves. Output-only leaves and compound materialized
roots do not arise. Unused allocation reservations carry no semantic delta:
`Inputs` is valid under every assignment and the exact output delta below uses
only original source IDs.

## 4. Genuine refinement versus observation progress

Define the fixed source condition

```
D(m) = for every root output o, Equivalent (m o.target).type (m i).type.
```

It is important to obtain completeness of associated requests from the enabled
packet's `Prepared.RequestReady.RootDefined`, rather than from Checked alone:
role defaults can make a checked declaration omit an explicit equation. The
actual installer defers such a missing requested equation. With RootDefined,
`delta_exact` proves, for every assignment m,

```
Inputs(packet,m) ∧ Outputs(packet,m)  ↔  D(m).
```

This formula contains neither the packet's changing cached context nor fresh
allocated IDs. Sharing constraints among multiple named uses follow by
transitivity through the one captured point input.

`administrative_alias` proves that normalization/refresh, entailed equality
feedback and reobservation preserve which aliases are entailed. A novel demand
merge is impossible with the singleton site. `step_semantics` proves that every
actual shared Step either preserves all models or adds exactly D. Induction
(`source_refinement`) gives just two possible model classes: the initial models,
or the initial models satisfying D. It is an exact characterization, not an
assumption about how a future executor will behave.

Every novel installation has a requested target t with `t ≠ i` whose alias to i
was not previously entailed and is entailed afterward (`genuine_alias`). Both
IDs belong to H. Replacing t by `leaf i` is closed over `H.erase t`
(`elimination_closed`); duplicate-freedom proves t is absent there
(`eliminated_absent`). These are local replacement certificates, not a newly
constructed general `HoleElimination.Trace`. Several output aliases may be
installed together. Counting them one by one is unnecessary here because one
installation adds the whole D. `no_second_installation` proves that every
subsequent installable packet is already committed, after any finite sequence
of actual shared Steps.

## 5. From source bounds to the singleton cover

The five-obligation chain for the restricted class has the following concrete
bounds and standalone producers:

| Obligation | Bound/result | Formal evidence |
| --- | --- | --- |
| Initial frontier | duplicate-free H; zero relevant projections | `initial_frontier`, `report_exact`, `reads_empty` |
| Actual origins and facets | input `leaf i`; both facets `leaf i`; output `leaf i` | `inherited_capture`, `capture_facets`, `installed_readback` |
| New relevant IDs | all decision reads are i; output targets already in H | `decision_use_exact`, `target_requested`, `elimination_source` |
| Genuine refinement | exactly initial models or initial models ∩ D; at most one novel installation | `source_refinement`, `genuine_alias`, `no_second_installation` |
| Invocation/report budget | one occurrence, no child edges, one semantic delta | `generated_root`, `children_empty`, `delta_exact`, `represents` |

Paterson branch depth is zero because the actual emission is empty. Every
eligible symbolic input and settled output has one leaf, so constructor depth
is zero and output size is one. There is no substitution growth to iterate.
Allocation keys come from the finite registry at the one invocation; their
numeric identity and support-list syntax do not enter the signature. The proof
does not enumerate raw slot numbers, arbitrary repeated support lists or stored
snapshots: it proves their irrelevance to this complete semantic delta. This is
exactly the quotient permitted by the existing SignatureCover interface.

Take the basis consisting of the single signature

```
(parent = root, children = [], delta = D).
```

`represents` proves it represents every future enabled packet;
`cover` constructs the existing `SharedBudget.SignatureCover` from the source,
point restriction and registry shape. The primary measure is the number of
missing signatures, either 1 or 0. Novel installation makes it strictly smaller;
all Steps preserve held signatures. When it does not decrease, the already
proved administrative accessibility supplies the secondary descent.
`checked_initial_accessible` applies the existing finite-signature theorem to
obtain Acc. `source_budget` is explicitly a **restricted** budget theorem and
does not prove the globally quantified `SharedBudget.SourceBudget roles`.

`GeneralNominalIdentityExample` has a checked singleton registry, source input
0 constrained to int, and distinct requested output 1 initially unconstrained.
The int-output model proves consistency; the str-output model proves novelty.
`actual_step` proves an actual guarded installation, `installed_alias` proves
its new equation, and `accessible` proves termination from this InitialSource.

## 6. What remains for general B4(1)

The general direct-walk theorem still needs semantic label readback and capture
extraction, including strict interval projections. Then a global mixed
origin/facet producer invariant must handle non-leaf where clauses, compound
materialization, output-only binders, aliases, and all administrative exposures.
The extraction of an actual elimination history, instantiated Paterson descent,
settled-tree growth and a finite bound on exact future invocation identities
remain unproved. Those bounds must eventually produce a general semantic report
cover. Neither a general SourceBudget nor unconditional Acc for arbitrary
checked registries follows from this change.

These are remaining proof obligations, not a newly established semantic or
implementation counterexample. No new guard was added and no owner question is
needed.

## 7. Validation

The `yulang-proofs` workflow was used. The configured prover role and its launch
configuration were unavailable; no prover agent ran. The primary constructed
the proofs, with a separate read-only reviewer checking scope and producer
ownership. Final review found no blocking issue. It prompted the all-visible
head-use theorem, the duplicate-free H certificate, and two scope-wording fixes.

Final commands from `lean/`, each with exit code **0**:

```sh
lake build Yulang.GeneralNominalSourceFrontier Yulang.GeneralNominalIdentityLeaf Yulang.GeneralNominalIdentityProvenance Yulang.GeneralNominalIdentityBudget Yulang.GeneralNominalIdentityExample
lake build Yulang
lake env lean Audit/GeneralNominalSourceFrontier.lean > /tmp/yulang-source-frontier-audit.log
```

The audit covers all 80 new public theorems. A parsed allowlist check returned
exit code **0**; its dependency union is exactly `propext`, `Classical.choice`,
and `Quot.sound`. The five modules have appended imports in `Yulang.lean`.
A byte-prefix and tracked-path check returned exit code **0**, confirming that
existing Lean content and frozen paths were preserved and that branch and HEAD
were unchanged. `git diff --check` returned exit code **0**. No commit was made.
Development builds had elaboration failures before correction; the commands
above are the final successful validation, not a claim that every attempt passed.
