# Cycle247: ordered query transport, design before implementation

A source field can contain a private aggregate address (cycle240 promotes an
aggregate into base.source). It cannot simply be dropped from the public view.
For the new ordered finite substitution, transport an explicitly supplied
CompTerm query with the same mapping as atom consumers. Exact evaluation of
that query in the rewritten assignment equals evaluation through solve(old).
On an old model, solve(old) is pointwise type-equivalent, with exact rows.
Consequently any predicate stable under mutual subtyping and row equality is
preserved. A finite tagged bundle preserves tags and length; existential public
models with that observation bundle should be equivalent across ordered rebase.

Quantifiers: arbitrary names, model with245.Laws, old/fresh finite blocks,
SafeOrder old/fresh, fresh target subset of old, arbitrary atom consumers,
explicit tagged queries and a stable predicate on their component values.
Public free variables must be outside old targets. Queries may read those
private targets. This covers only queries actually supplied and transported.
It does not enumerate actual descriptors, cache keys, historical origins, live
packet children or inspector control fields, and it is not operational Evidence.
Concrete Common probe invariance can use producerEq_iff_probe at every finite
depth and negative rank. Literal Common type syntax equality is not claimed.
