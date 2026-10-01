# Oracle root/use ownership characterization

Date: 2026-10-01
Branch: `research/simple-sub-intrusion`
Reference: frozen Yulang2 Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Status: source characterization; not successor semantics or an adequacy proof

## Per-root generalization boundary

`AnalysisSession::quantify_component` in
`crates/infer/src/analysis/session/instantiate.rs:14` processes the SCC's
`(DefId, root)` pairs in order. For each member it calls
`generalize_root_with_prepasses_and_metrics`, retains the resulting generalized
root, and only after all roots have been processed inserts/finalizes the
schemes. The prepasses can mutate the shared constraint machine, so a later
member view is not necessarily a read of the exact graph epoch used by an
earlier member. This agrees with the existing ordered-root/epoch ledger; it
does not make the views one immutable shared snapshot.

The boundary comes from `AnalysisSession::generalize_boundary` in
`crates/infer/src/analysis/session/generalize.rs:767-774`, which calls
`binding_fetch(def).generalize_boundary(TypeLevel::root())`. In
`crates/infer/src/typing.rs:79-104`, `FetchValue` keeps the supplied boundary
and `FetchComputation` moves it to its child. This is frozen-Oracle behavior
for choosing the scheme quantification boundary, not a rule selected for the
successor.

At `crates/infer/src/generalize/mod.rs:900-914`,
`quantified_vars_in_root_and_roles` collects free variables from that member's
`CompactRoot` and role predicates, then keeps only variables whose level is
strictly above the chosen boundary and which are not in `non_generic`. The
current generalization path supplies an empty `non_generic` set. Thus, for an
already prepared compact root view `H_d`, the initial generalized-root
quantifier set is characterized by

```text
Q_d^root = { v ∈ FreeVars(H_d, roles_d) | level(v) > boundary_d }
```

This formula is about the compact prepared view and its epoch. It is not
necessarily the final scheme quantifier set: finalization applies ancestor
simplifications, dead-quantifier pruning, and stack cleanup before publishing
the scheme (`finalize_generalized_compact_root_with_ancestors` in
`crates/infer/src/generalize/mod.rs:837-853`). Let `Q_d^final` denote the
published scheme's actual `quantifiers`. Neither set classifies every ID in a
successor's retained full constraint graph, and neither authorizes dropping
source constraints. The exact source-to-successor ownership partition still
needs its own declarative binder rule.

## Per-use identity map and inserted constraints

`SchemeInstantiator::instantiate_scheme_parts` in
`crates/infer/src/instantiate.rs:620-650` allocates fresh variables for the
scheme quantifiers and every recursive-bound variable, plus fresh stack IDs
for listed stack quantifiers. Its `fresh_var` map in `:720-750` is shared by
positive, negative, neutral, role, and Function-effect occurrences during one
clone. Repeated occurrences of one mapped source variable therefore share one
fresh ID within that instantiation; a later use creates a new instantiator and
new local identities. A source variable not in the quantifiers or recursive-
bound variable set is preserved by the ordinary `clone_var` path.
Imported-boundary and freshen-all callers have separate policies.

`prepare_instantiated_use` in
`crates/infer/src/analysis/session/instantiate.rs:342-535` then inserts the
instantiated predicate at the use site. An eligible direct-lower shape is
added as a lower predicate; other shapes are related to the use variable by a
subtype constraint. Role predicates take a separate insertion path. These
caller/use constraints are part of the joint receiver context when comparing
multiple uses. A quantified source ID does not create an equality between
independent instantiations; a preserved free ID intentionally remains shared.

Define `RVar_d^final = { b.var | b ∈ recursive_bounds_d^final }`. For a
published Oracle scheme, the set that the ordinary instantiator maps to fresh
type IDs is `F_d = Q_d^final ∪ RVar_d^final`; a recursive-bound variable
already in `Q_d^final` still receives just one image because `fresh_var`
memoizes by source ID. The ordinary use map has the shape

```text
rho_(d,u)(v) = fresh_(d,u)(v)   if v ∈ F_d
             = v                if v is unquantified/free
```

with other boundary maps applied by the imported-scheme path. A common map
within one use and fresh local ranges between uses are source facts about the
clone operation. They are useful constraints on an Oracle comparison proof;
they are not the successor's chosen source semantics.

## Consequence for the conditional joint-transport criterion

Conditioned on a source ID belonging to `F_d` for one finalized member scheme
and to neither `Q_e^final` nor `RVar_e^final` for another, a use of the first
member freshens it while a use of the second preserves it. Root reachability,
boundary selection, finalization, and recursive-bound ownership can all affect
these sets. Independent uses share only identities the latter scheme leaves
free, plus caller identities explicitly connected by their use constraints. A
cross-use relation must come from those caller constraints or from the
successor's declarative source rule; it must not be inferred solely from the
raw numeric ID.

During a primary reread of the clone path, the fresh type map was narrowed
from “quantifiers” to `Q_d^final ∪ RVar_d^final`: recursive-bound variables are
explicitly freshened even if not listed in `scheme.quantifiers`. The shared
memoized `fresh_var` map preserves one image when a variable occurs in both
sets. This distinction is required for the per-use map characterization
above.

This establishes the shape of the Oracle map for a prepared compact scheme,
not the mixed-ownership condition for the successor's full graph. It also does
not reconstruct the complete public root observation: ordered root epochs,
constraint/proof provenance, stack cleanup, role resolution, failure outcomes,
and final specialization remain separate obligations. No Oracle builds,
probes, tests, or weight transformations were run for this source audit.
