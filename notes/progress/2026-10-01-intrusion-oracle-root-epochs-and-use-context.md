# Oracle root epochs and use-context characterization

Date: 2026-10-01
Branch: `research/simple-sub-intrusion`
Reference: frozen Yulang2 Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Status: source characterization; not successor semantics or an adequacy proof

This audit continues the comparison between Oracle root views/use constraints
and the conditional batch-transport criterion in
`2026-10-01-intrusion-coarse-effect-abstraction-candidate.md`. It records
which source relations are visible in the frozen event pipeline. It does not
derive the successor's source elaboration or prove that its complete relation
is principal.

## Root epochs are intervals, not frozen snapshots

`AnalysisSession::quantify_component` in
`crates/infer/src/analysis/session/instantiate.rs:14-39` processes roots in
component order. For each root it calls
`generalize_root_with_prepasses_and_metrics`, then collects role-implementation
member prerequisites before moving to the next root. All resulting schemes
are inserted only after this first loop (`:51-53`) and finalized in a second
loop (`:55-83`).

Each root generalization records a constraint epoch at entry and at return
(`crates/infer/src/analysis/session/generalize.rs:30`, `:563`). The root
prepasses can add merge, subtype, cast, role, and dominance consequences,
route SCC events, and restart their local loop before returning. Its compact
view is fetched by `(root, current constraint epoch)` through
`compact_root_for_generalize` (`:578-603`); it can therefore be recomputed
after mutations made during that root's own prepasses. The epoch pair
characterizes the interval of mutation, not the exact compact view chosen at
each iteration or a permanent boundary snapshot.

Since roots are processed sequentially, a later root starts after earlier
root prepasses and prerequisite collection. This is consistent with an
ordered root/epoch characterization; it is not evidence that all members see
one immutable SCC constraint graph. The exposed epoch start/end values alone
do not reconstruct the full sequence of intermediate root views. A complete
successor comparison still needs a source-defined group relation and a proof
that its projections preserve all consequences of this ordered processing.

## Use and open-use constraints visible in the event stream

`route_scc_events` in
`crates/infer/src/analysis/session/selection.rs:1035-1126` handles two distinct
use events:

- `InstantiateUse { parent, target, use_value }` clones `target`'s published
  scheme for that use and connects the instantiated predicate to `use_value`.
  Eligible shapes insert a direct lower predicate; other shapes insert a
  subtype relation. Role predicates are inserted under `parent`, and cloning
  recursive bounds inserts their bound constraints. Contiguous instantiate
  events are collected as a batch, cloned in event order, and their type
  constraints are inserted after the cloning pass
  (`analysis/session/instantiate.rs:311-341`). Each use invokes its own
  scheme-instantiation operation and local variable map. The `parent` field
  also identifies provenance and role ownership; it is not by itself a type
  equality to `use_value`.
- `OpenUse { target, target_root, use_value }` adds the unweighted subtype
  constraint `target_root <: use_value`
  (`analysis/session/instantiate.rs:4-12`), then retains the event for the
  subsequent SCC pass. It does not instantiate a closed scheme.

The corresponding event payload is declared as `SccInstantiateUse` in
`crates/infer/src/analysis/mod.rs:424-429`. In the conditional joint criterion,
the external use predicates and these caller-root constraints belong to the
receiver/continuation relation `K_ctx`; open-use edges belong to the internal
live-root graph of their owning SCC copy. The distinction follows event kind,
not raw identity equality. `QuantifyComponent { component, roots }` invokes the
ordered root pass; the event itself is not a constraint edge.

This characterization still does not enumerate every event-to-constraint
cause or reconstruct the full public root observation. In particular, it
does not establish that every scheme use is represented by a type constraint
alone: role predicates, recursive-bound evidence, diagnostics, provenance,
and later specialization must be accounted for by their own relations.

## Consequence for the candidate criterion

The refined candidate criterion now has two necessary inputs that must be
extracted from a source semantics rather than inferred from IDs:

1. a complete, per-copy base/member view for each root/generalization event,
   including any mutation that occurs while that root settles; and
2. a complete `K_ctx` containing caller-use links, open-use edges where
   applicable, and cross-use constraints required by the language.

The Oracle event and epoch evidence gives a concrete comparison checklist for
those inputs. It does not prove the candidate's ownership partition, the
semantic necessity of Oracle's order, a weighted/effect transport theorem, or
final well-typed acceptance equivalence. There is still no concrete fixture
for a source ID freshened by one member scheme and preserved by another.
