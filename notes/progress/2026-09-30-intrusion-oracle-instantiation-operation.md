# Oracle use-instantiation operation characterization

Date: 2026-09-30
Branch: `research/simple-sub-intrusion`
Reference: frozen Yulang2 Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Classification: read-only source characterization; not a denotational proof

## Ordinary scheme clone

In `crates/infer/src/instantiate.rs`, `SchemeInstantiator::instantiate_scheme_parts`
allocates fresh variables for `scheme.quantifiers` and each
`scheme.recursive_bounds[*].var` before cloning recursive bounds and the
positive predicate. It also allocates fresh IDs for listed stack quantifiers.
`fresh_var` memoizes one source-to-target `TypeVar` map; the positive,
negative, and neutral graph cloners each memoize source nodes.
Repeated variable and graph-node occurrences therefore share their clone
within this invocation. A later invocation constructs a new instantiator and
fresh map. `clone_var` preserves an otherwise-unmapped free variable in this
ordinary path; likewise an unlisted subtract ID is preserved. Imported-boundary
variables can be preloaded, while the freshen-all adapter has a different
policy. Role predicates and function effect positions use the same mapping
when cloned. Stack quantifiers additionally wrap the cloned positive predicate
with stack pops; stack-weight contents are cloned through their own ID map.
The source establishes these cloning operations, not that the transport
preserves any proposed denotation.

Recursive neutral bounds are cloned, projected to positive/negative bounds,
and restored as `lower ≤ fresh-var` and `fresh-var ≤ upper` constraints.
`AnalysisSession::prepare_instantiated_use` invokes this clone at the secondary
level for ordinary non-imported, non-finalized schemes. It then relates the positive predicate
to the target `use_value`: eligible direct-lower predicates are inserted as a
lower bound; other shapes are related to `Neg::Var(use_value)` by subtyping.
Role predicates are inserted on their separate path. Relevant frozen source
locators:

- `crates/infer/src/instantiate.rs`: `instantiate_scheme_parts` around
  lines 620–650; `fresh_var`/`clone_var` around 720–750;
  `clone_recursive_bounds` around 1002–1028; positive/negative/neutral graph
  cloning around 788–955.
- `crates/infer/src/analysis/session/instantiate.rs`:
  `prepare_instantiated_use` around lines 344–535.

The focused Rust characterization already recorded in
`2026-09-30-intrusion-bounded-negative-counterexample.md` exercises a
multi-member component through three source uses. That test checks event
identity and disjoint raw TypeVar sets in immediate lower predicates; it does
not establish transitive graph isolation or key every production map entry to
its use.

## Limits

This source reading specifies an operational use path, not a mathematical
scheme denotation or subtype relation. It does not define the carrier, prove
principal scheme projection, prove that intrusion preserves the entire set of
instances, or settle recursive subtype comparison. Stack/effect weights,
role predicates, imported boundaries, and freshen-all clients need separate
denotational transport proofs. No compiler code, tests, or Oracle files were
changed, and no tests or measurements were run for this record-only slice.

Gate C remains open. The next proof task is to define an observable relation
for an instantiated predicate graph in the replacement candidate, then show
that root projection and each Oracle use-site constraint path preserve it for
the declared envelope. The reviewed carrier option remains unselected.
