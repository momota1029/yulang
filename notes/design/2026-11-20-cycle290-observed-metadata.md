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

A constructor-key list is not a complete description of current class
requests: a new target could use a constructor-free body. Add the ordered
request/lookup list `(name,target,Option Body)` as a separate stamp field.
It records missing lookups too (it does not assert all are compilable).
A previously verified alias regression gains a target through a real
MixedKernel merge, though the supplied premerge journal was not shown
reachable from these sources. Use that exact distinction to test field
sensitivity, independently of which metadata keys its bodies use.

## Separate table agreement from live compilation totality

A present body may compile to `none` under both identical tables. Then its
schema has no equations and may satisfy `ClassEffects` vacuously; table
agreement faithfully preserves that behavior, not successful evaluation.
Use an additional executable totality test over the request book: each
requested name must have a body and its compiler must return an expression.
Under the finite local agreement hypothesis, test success is equivalent to
the original `Ready` predicate on the unchanged plan/state. The actual
preinstall Ready transports to the installed parent because its class
reqs are unchanged. Prove an independent closed checked declaration with
unsupported associated rhs still separates `ClassEffects` from `Ready`.

## End-to-end noninterference on a fixed raw state

Keep the registry, raw state, occurrences and Offer fixed. Require equal
proposed interpretation entries on the current filtered-candidate list
with descriptors, and the live-body key list of every recorded effect.
The two preflights, every candidate qualification, the exact ordered
permitted seals and the final auxiliary publish result should then be
equal. This is stronger than equality of a single report, but does not
allow changing roles, references, current requests, or the old raw Step.
Requiring all historical effects is sufficient rather than minimal.

For the executable strict check one can additionally vary the supplied
registry constructor table while keeping the declaration list fixed and
requiring the same finite entry hypothesis. Prove the previous exact
anchor checker only consults source descriptor constructor keys and the
same declared world. Compose that lemma with the newer current and
historical read checks; no global old Frame follows. An omitted catalogue
entry at an unused key is then a deliberate closed noninterference test.

## A finite-complete exception requires separately witnessed representation

The preceding noninterference cannot justify replacing full Metadata.
There is an independently checkable special case: both constructor
functions are represented as finite overlays of the **same** default
function, and the primitive table has a finite overlay with default none.
Add both override-domain lists and all primitive override keys to the
observed list. Outside that larger scope the separate residual equalities
are witnessed by the representation. The old Metadata predicate is then
equivalent to the enlarged executable check, not by inspecting arbitrary
functions. On this fixture, the default is the existing example catalogue;
key 6 is an override. Include a removed key-8 override and a key-8
primitive override, which the enlarged check must now catch. The
representation evidence is a named hypothesis unless independently
provided by the source/exporter construction.

## Reader map and next hard boundary

| Question | Verified Lean entry |
|---|---|
| Which table entries matter to the actual normalized-head translator? | `GeneralObservedMetadataTranslation290.translate_eq`, `GeneralObservedMetadataGate290.verified_report` |
| What about emitted source requests and associated/default code? | `GeneralObservedMetadataBranch290.accepted_branch` (legacy recursive schema), `GeneralObservedMetadataBodies290.bodySchema_eq` (centered expression compiler) |
| Is the saved object only repeatable, or is the current supporting producer legitimate and total? | `GeneralObservedMetadataSeal290.kept_has_reference_books`, `GeneralObservedMetadataStrict290.actual_owner_total`, `GeneralObservedMetadataPublic290.strict_live_sound` |
| Does this store a raw fact or solve the existing pending row branch? | No; `GeneralObservedMetadataStrictActual290.strict_release_exact` and `GeneralObservedMetadataPublic290.strict_fixture_mark_sound` make the two cases explicit. |
| When can a finite witness entail old full Metadata? | `GeneralObservedMetadataClosure290.metadata_iff`, `GeneralObservedMetadataOverlay290.closed_world_iff`; independent representation witnesses must cover off-scope reads. |

A natural small follow-up is a source-backed exporter for the overlay
hypotheses. It needs independent completeness of the constructor and
primitive override lists, then a witness that their role classification
agrees with actual extraction. Do not introduce that completeness as a
silent precondition of the receipt. Separately, no amount of metadata
agreement here changes the frozen row inspector: defending one real
positive ordinary-row observation through a different supported route
requires its own source/example and reading proof. Neither follows from
the new metadata seal or from the closed old alias regression.
