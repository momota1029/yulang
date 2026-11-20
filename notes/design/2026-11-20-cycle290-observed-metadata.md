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
