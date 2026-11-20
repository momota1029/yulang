# Cycle 290: finite metadata evidence for the actual pattern translation

Cycle 289 bound a receipt to current raw descriptor constructor keys and an
exact generated occurrence from a historical producer. That read set is
not the read set of `GeneralNominalInspection.translate`: a normalized
candidate can contain a constructor that occurs in no recorded descriptor.
Translation also consults primitive classification and invariant-nominal
classification. Conversely full `Candidates.Metadata` contains function
equality and primitive compatibility even at keys not read by this phase.

First define a syntactic upper bound of constructor key reads on an arbitrary
finite **normalized head** (at the call boundary, not source syntax before
normalization). Each application contributes its key and recursively all
argument keys; variant payload, record payload/tail, and conservative join
branches contribute their keys. Record labels, variant tags, and binder names
are not constructor keys. Pair and nominal descent are both covered by the
same list. The upper bound may include a deferred branch never read; it is
sufficient, not minimal.

Independent judgments: `LocalEqual keys c₁ i₁ c₂ i₂` compares constructor
layout/name, primitive case with scalar payload, and invariant flag at each
key. `LocalPrimitiveOK keys c i` requires the layout prescribed by any
primitive at each key, independent of pairwise equality. Make two executable
finite checks and prove iff without assuming arbitrary function equality.
Target theorem: for every pattern and pair of tables/interpretations, local
equality on the key list implies identical old translation; for every
declaration and unchanged observation state, the corresponding normalized
head check implies equal old query lists and recursive reports. Then combine
the normalized head keys of current candidates with the original recorded
descriptor keys. Keep historical producer evidence, current state, and
supplied comparator separate; never infer a full Frame from a finite proof.

Tests: (a) gain of a key in a declaration not present in raw descriptors; a
key mutation can pass the old footprint yet change a query, (b) key outside
both sets, invisible to local translation but violating full Metadata;
primitive changes and invariant-flag changes are separate controls.
If an old frozen inspector cannot structurally descend into rows, record it
as unchanged, not repaired by this finite certificate. No new raw Step,
general authorization, Yulang2 execution claim, or termination claim.

## The second real translation site: materialized requests

`GeneralNominalRecursiveCandidates.generated` also calls the same
translator, but on each normalized pattern in the concrete request list
computed by `GeneralNominalMaterialization.requests` (associated rhs,
generated where inputs/outputs). A head-only certificate has no authority
over this site. Keep the reference observation state and declaration
registry/allocation fixed. Given that state, declaration and bounds,
compute the reference report and bindings, then the actual request list.
Extend the footprint with the normalized patterns of **that** list.
Prove: any locally agreeing proposed constructor/interpretation tables
produce the same old report, the same derived list, and the same
materialization schema; no assumption of arbitrary function equality.
Schema equality means identical variable uses, typed tests, and defer flag;
it is not a proof of allocation or full Frame for another registry.
Try a constructor key present only in an associated rhs as the independent
closed control, and verify the real source parent read separately.

The historical recursive `generated` phase above is not the current
MixedKernel class-effects implementation. The latter uses
`CenteredHeadMatEffects.compileBody` and a different output-expression
translator that preserves joins and arbitrary record tails. Treat it
separately. Collect raw expression-pattern keys for explicit bodies and
raw Roles.Term keys for positional defaults. Pointwise table agreement
should preserve that compiler's Option expression, schema and equations,
with plan, request class and body provenance unchanged.

## Persisting the finite proof inputs, then rechecking them

The report comparison and the historical body comparison are separate:
each admissible historical effect independently matches the exact
current parent/child, offers the target, and certifies the scopes of
its **current** class requests under its packet's historical tables.
Do not join an anchor from one effect with acceptable output metadata
from another.

A small data capsule may record the prior typed receipt stamp and two
ordered `(key, Entry)` tables: current normalized-head/descriptor reads,
and current live-body reads of one qualifying historic producer. A
capsule is not authority to publish by itself. Recompute the current
ready gate plus the list of allowed capsules from the actual effects;
compile a mark only if the saved capsule is still in that list. Equality
rechecks observed data; two observationally equal live effects need not
be uniquely distinguished. Off-scope differences can remain invisible,
and no full Metadata/Frame follows. Test a stale entry with the same
old typed stamp, and use the two original raw branches to bound what
this mechanism really releases.
