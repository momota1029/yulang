# Contravariant concrete annotations: conditional hygiene derivation

Date: 2026-10-10
Status: reviewed conditional derivation; research-only; source attachment construction open
Review: compiler-referee PASS, 2026-10-10; primary clarified receiver scope
Baseline: `32c65f07671b9de7b05ece3044a714c4d8d0e61b`
Method: instantiate existing typed transport/owner preservation, then prove exact-contribution filtering and support projection algebra
Lease: this new note only; no production, test, shared-record or semantic authority

## 1. Objective and governing premises

The objective is hygiene of a source-owned contravariant concrete annotation,
including nested Function positions. This note proves a conditional preservation
statement for supplied attachments. It does not prove that source lowering
constructs them or that annotation permission alone consumes a runtime request.

The governing policy is [annotation integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–5: a contravariant `[E]` permits subtraction of concrete E in that function
at that exact position; a covariant `[E]` permits concrete E there. Variables
are ignored only when collecting concrete annotation atoms. Their flow and
current/future concrete checks remain. Polarity composes and identity is
resolved. Section 6's callback result is retracted and supplies no oracle.

The [implementation gate](../design/2026-10-10-concrete-effect-annotation-implementation.md),
opening scope and “Annotation checking and publication owner”, distinguishes
immutable annotation support from actual contributions. It explicitly leaves
source subtraction open. Its paired checking/exposed endpoints do not determine
source variance by their endpoint sign.

Reused results are [typed boundary transport](../design/2026-10-02-typed-boundary-realization-draft.md)
§6, particularly “One relational transport operation”, “Receiving ownership and
observation”, and “Transport and lifetime theorem package”; and [typed source
owner realization](../design/2026-10-02-typed-source-owner-realization.md) §§1–4.
These results have supplied finite monomorphic decorated descriptors, typed
correspondences and source profiles as premises. Their reviewed conditional
subresults remain reusable despite the enclosing Draft status.

The [concrete profile corollary](2026-10-05-concrete-capture-profile-derivation.md),
“Conditional concrete-item corollary” and “Separate subtraction obligation”,
already separates eligibility from selection and complete support removal.
The [attachment probe](2026-10-05-effect-attachment-subtraction-playground.md),
“Finite model” and “Limits and next gate”, supplies historical bounded
characterization with assumed attachment/consumption/output flags. Those flags
are not a source-construction theorem.

Rules applied: `design-authority.md` (“Authority order”, “Natural compiler
behavior and proof-obligation economy”); `compiler-engineering.md` (“Natural
compiler behavior and proof-obligation economy”); `research-lab.md` (“One
semantic baseline”, “Evidence quality”); `git-concurrency.md` (“Disjoint-file
mode”, “Research-only checkpoint fast path”). No language meaning is reopened.

## 2. Quantifiers and explicitly supplied hypotheses

Fix any finite decorated monomorphic descriptor graph Ω, any shared assignment
ν and any finite execution prefix t in the existing owner/view realization.
Infinite executions are covered only by their finite prefixes. Fix any source
annotation occurrence a, its owner descriptor f, its exact signature path p,
and its dynamic boundary instance b when actually introduced. Separate ordinary
invocations that execute this boundary-entry operation allocate fresh receiver
identities. Resuming a saved owner span does not replay the boundary entry or
rebind its original receiver.

Let C_a be the resolved concrete atom set of a under ν, and T_a its retained
symbolic coordinates. For `[E]`, C_a = {E}; E means resolved family plus its
concrete operands, not a spelling. Parameterized operand comparison is supplied
by an already justified concrete compatibility instance; no general variance
for effect arguments is selected here. The executable slice currently supplies
nullary nominal identities. A variable occurrence contributes to T_a, not C_a.

Use c for an exact source contribution with retained event/path lineage, and
πν(c) for its family/type support point. If one event has different contribution
routes, their exact lineage witnesses remain distinct. No row multiplicity is
asserted: support is the set of their projected points. These are mathematical
names for supplied evidence, not a proposed new compiler carrier.

The hypotheses are:

1. **Source formation supplied.** a is attached to its actual source owner and
   path with composed variance σ(a,p). For σ = −, its concrete clause licenses
   a local subtraction view at that position. Its source profile and any
   Handler-role concrete clause are supplied valid derivations, not inferred
   from row support. A subtraction clause is not automatically a Handler role.
2. **Exact attachment supplied.** A_a(c) is an existing source-derived attachment
   judgment at this local view. It retains a, b where applicable, original
   owner/path, concrete compatibility and the contribution's event/path lineage.
   Equal family points or equal canonical row IDs alone do not derive A_a.
   Attachment need not equate producer origin with annotation origin: a request
   exposed by Force may have another origin and still have a valid typed route.
3. **Typed transport and owners supplied.** Every used M_i is a valid declared
   typed correspondence. Packets have the indexed image of their actual inputs,
   preserving χ, predicate identities K, dependency incidences D and lineage L
   under the same ν. Executing/saved owners, views and fresh identities satisfy
   owner realization §§2–4, including its executing-view projection premise.
4. **Executable local check supplied.** The consumer uses the original annotation
   and exact attachment for each concrete lower, including later lowers. It
   preserves symbolic connections and checks residual concrete contributions
   against the original correlated target constraints. Annotation support is
   not an emitted contribution or an attachment witness. This hypothesis is
   not established for source contravariant subtraction in the current solver.

These premises are jointly scoped: fixing a common ν does not independently
solve each packet's predicates. They do not include arbitrary-source typing,
principal inference, Call registry adequacy or a solver implementation theorem.

## 3. Nested Function polarity derivation

At a Function node with source variance s, the argument Value and argument
Effect children have −s; result Value and result Effect children have s.
Thus for any finite path p with n reversing descents:

```text
σ(root,p) = σ(root) · (−1)^n.
```

Proof is induction on p. The empty path has the root sign. A result descent
adds no reversing edge and preserves the induction equation; an argument
descent adds one and multiplies both sides by −1. Repeating these cases covers
arbitrarily nested finite Function paths. Unfolding a recursive descriptor uses
the supplied occurrence path; a shared undecorated node does not merge source
annotation occurrences.

The actual root conventions are recorded by the existing [formal integration](2026-10-10-selected-formal-contextual-integration.md)
§2: a whole-binding annotation starts at +; a formal annotation starts at −.
This read supplies concrete examples of the selected composition rule:

| Annotation occurrence | Composed sign | Consequence |
| --- | --- | --- |
| formal `cb: int -> [E] ()` | −, result preserves | local subtraction premise needed |
| formal `consume: (int -> [E] ()) -> ()` | −, argument flips, inner result preserves | covariant allowance |
| formal `cb: ((int -> [E] ()) -> ()) -> ()` | −, two argument flips | local subtraction premise needed |
| whole binding result `int -> (int -> [E] ())` | +, result descents preserve | covariant allowance |

These are position examples, not executed source fixtures or inferred schemes.
The consumer must select the clause using σ(a,p), even when checking uses a
negative endpoint of a covariant annotation's paired interface. Neither the
nearest textual arrow nor endpoint polarity is a substitute for this sign.

## 4. Conditional preservation and local subtraction result

For every choice satisfying §2 and σ(a,p) = −, the following holds at every
finite prefix and along any finite chain of the supplied typed correspondences.

**Transport hygiene.** Every transported local attachment/profile has an original
source witness at a corresponding path, with the same annotation, original
receiver, predicates and lineage. It supplies no contract at an unrelated port
or to another owner merely because a row, pointer or family is equal. Under the
same composite correspondence, receipt, event observation and current candidate
configuration, argument/environment/store/result routes yield the same candidate
incidence. Receiver/handler expiry removes candidate grants, without deleting
latent effects, symbolic dependencies or raw attachment/profile evidence.

**Exact local filtering.** Let O be any finite set of contribution witnesses in
the local view and R any selected subset satisfying

```text
R ⊆ {c ∈ O | A_a(c) ∧ πν(c) is admitted by C_a}.
Residual_a(O,R) = O \ R.
```

Then every c in O with no selected exact attachment remains in the residual;
another c′ with πν(c′) = πν(c) remains whenever c′ ∉ R. In particular:

```text
Supportν(Residual_a(O,R)) = {πν(c) | c ∈ O and c ∉ R};
E ∉ Supportν(Residual_a(O,R))
  iff no c ∈ O \ R has πν(c) = E.
```

This is soundness of the *specified contribution-local subtraction operation*
under supplied licenses. It is not a claim that O is an actual source output
image or that the current compiler implements this operation. Selecting a
subset expresses permission; it does not assert mandatory cancellation.

**Derivation.** Expand `(M_*χ)(p′,b)` as an existential original path witness.
Composition supplies the intermediate matching paths, and source-union
distribution preserves the input tags. The same proof applies to D; K and L
retain their original identities. No step introduces a boundary or changes a
source sign. Apply owner preservation to each source step: a saved owner can
resolve to a fresh executing occurrence, but that resolution does not rename
b.receiver or inherited evidence. At the same query configuration, the live
filter commutes with transport because the exact handler, owner and original
receiver references are identical. These are direct instances of the existing
reviewed theorem package, conditional on its hypotheses.

For subtraction, membership in O \ R is equivalent to membership in O and
nonmembership in R. Therefore c′ survives independently of c's projection.
Expanding set-image membership proves both displayed support equations. For
O = ⋃ᵢ Oᵢ with tagged input contributions:

```text
(⋃ᵢ Oᵢ) \ R = ⋃ᵢ (Oᵢ \ R).
```

Thus a targeted subtraction cannot delete another input's independent lineage.
This uses exact R, not a filter on πν(c) alone. It asserts no commutation of
arbitrary set difference with a possibly identifying row/path quotient; that
stronger law would require preservation of the full removal predicate.

## 5. Handler eligibility and runtime elimination are additional premises

When the supplied source profile also has the appropriate explicit Handler
contract, fix candidate h in its actual search configuration C and event q.
The existing §6 definitions give:

```text
Path(q,owner(h),b,p) and Active(h,C) and Active(owner(h),C)
and Active(b.receiver,C) and owner(h) = b.receiver
and Γ_b explicitly admits q.operation at p under ν
    imply Grant(q,h,C).
```

With Covers(h,q.operation), Grant implies Visible. A source-derived observation
of that exact q at the matching executing view and a receipt of that same view
must supply Path. Another q of the same family supplies none of those witnesses.
Origin equality is not required. Mere annotation/support membership supplies
neither Path nor an actual handler choice.

Ordered search must reach h and select a suitable arm; OpCompat remains its
separate selected-arm typing check. Handler arms, guards, forwarding and raw
resumptions may produce further contributions. A valid local grant consequently
does not prove absence of E in the function's complete output.

A runtime projection corollary needs a **separate discharge/complete-image
premise**: for the specified trace, its actual complete output witnesses are
exactly `(O \ R) ∪ N`, where each removal in R has a valid source discharge
derivation and N contains every new surviving contribution from the surrounding
computation. Only then is actual output support

```text
{πν(c) | c ∈ (O \ R) ∪ N}.
```

E disappears only if neither O \ R nor N contains an E witness. This premise
must follow from the source computation, not be supplied by assuming a consumed
flag in a checker. The present result does not discharge it. Expired candidate
grants cannot be replayed by raw continuation reachability; a fresh handler
needs its own current incidence and local contract.

## 6. Current/future lowers and symbolic tails

For every concrete lower c reaching the annotated port now or after a symbolic
refinement, the local consumer must retain a check against the original
annotation view. At a negative position the cases are:

1. Compatible concrete point and a genuine attachment at the licensed local
   position: the selected contribution may enter R.
2. Same concrete point without that attachment: it remains in the residual.
3. Different/incompatible point: it remains in the residual and encounters
   the ordinary downstream concrete check.

At a positive position the concrete clause is an allowance, not R formation.
For a closed pure `[E]`, a concrete lower must satisfy its supplied concrete
comparison; an incompatible F fails. With a symbolic tail, the full correlated
row constraint determines compatibility; this note does not force membership
in C_a alone or assume the tail admits everything.

Formally, if K contains the original predicate k_a and D links it to a symbolic
coordinate x in T_a, typed transport preserves k_a and its matching D incidence.
A later lower `c -> x` must use the same check after the correlated substitution.
Ignoring x when forming C_a is not `x = Empty` and is not deletion of k_a.
Owner/handler expiry changes candidate incidence, not this typing obligation.
For example, C_a = {E} and a retained symbolic x can later receive F: any
applicable rejection, flow or local attachment decision must still execute
against the original view; F is never silently erased by the earlier E clause.
This is a conditional obligation on the supplied consumer, not a verified
current negative implementation behavior.

## 7. Smallest witness and failed proof route

The claim “subtracting attached E implies E is absent from complete support”
has the following minimal fixed-image witness:

```text
O = {c0,c1};  πν(c0) = πν(c1) = E;
A_a(c0) true; A_a(c1) false; R = {c0}.
O \ R = {c1}; Supportν(O \ R) = {E}.
```

c0 and c1 have different contribution lineage; c1 is an independently attached
sibling, possibly belonging to another boundary. Two contributions are minimal
when N is empty and the removed contribution is itself E: with only c0 its
removal leaves no E witness. This countermodel falsifies the support-wide
shortcut, not the selected permission for exact local subtraction. It is an
algebraic witness, not an executed Yulang counterexample.

A failed route is to project first, obtaining `{E}`, then compute `{E} \ {E}`.
The projection forgets which contribution supplied the point. It consequently
cannot reconstruct A_a or distinguish c1 from c0. Another failed route is to
reuse transport preservation as annotation construction: Id_*χ = χ says nothing
about whether raw syntax produced a valid χ or A_a in the first place. No larger
toy enumeration using assumed attachments can repair either missing premise.

## 8. Minimal source bridge and recommended next action

The missing construction lemma is local:

> At the actual resolved annotation formation for owner f and path p, establish
> its composed sign and concrete/symbolic operands; for a negative occurrence
> construct its source-owned executable attachment/subtraction view. Derive
> exact attachment judgments from the genuine contribution and typed boundary
> construction at that position, preserving source identity and lineage through
> the paired checking/publication flow. Connect the original predicates and
> symbolic coordinates to the consumer for current and future concrete lowers.
> Separate annotation support members never count as emitted contributions.

For runtime Handler eligibility, the construction must additionally derive the
actual profile, receipt and event-observation route in the applicable role.
That is not obtainable from Call metadata or an effect-support point. For a
runtime elimination theorem, source discharge and complete output accounting
remain separate, as in §5.

This bridge is required safety/correctness (A in compiler-engineering), with a
reconstruction-debt risk (D) if formation discards known occurrence/owner data.
It is not a new arbitrary-view completeness prerequisite. Recommended next
action: inspect and specify the actual negative annotation formation/consumer
seam so it emits canonical source attachment evidence and the retained lower
check by construction; return that concrete lemma to the primary for assignment.
Do not add another support-only proof or a prerequisite Call registry.

## 9. Checks, independence, and frozen dependency packet

There is no executable checker or model run in this assignment. The derivation
uses the existing conditional theorem statements and elementary set membership;
it shares their source-profile, typed-correspondence and owner premises. The
two-contribution witness needs only the stated set/attachment facts. No Oracle
execution or independent review of this note is claimed. Historical Oracle
source evidence in integration §2 is inherited context, not freshly validated.

Coverage: all finite Function paths by induction; all finite supplied transport
chains/execution prefixes via the existing preservation theorem; exact finite
contribution sets by elementary projection. No seeds, bounded search ranges,
mutation runner or numerical sweep. Named falsified shortcuts are projecting
before subtraction and assuming profile existence from identity transport.

Failure conditions include unsupported or unproved concrete compatibility,
missing source profiles/attachments, a wrong root sign, mismatched typed ports,
discarded lineage under equality, a consumer that skips future lowers, rebinding
expired receivers, or incomplete output/new-contribution accounting. Unknown
shapes, parameterized effect inference, arbitrary raw-source safety, principal
schemes, recursive contextual solving and production lifecycle are unverified.

Resources: only lightweight read/document/check commands; independent initial
reads were batched. One-CPU allowance; no CPU-intensive or long-lived process,
builds, tests, benchmarks, delegation or Git mutation. Actual CPU/RAM and total
wall time were not instrumented. Frozen whitespace check:
`git diff --check -- notes/progress/2026-10-10-contravariant-effect-conditional-proof.md`
returned exit 0. Since the new artifact is untracked, that command checks no
untracked patch contents; a separate read-only scan of this exact file found
no trailing whitespace or whitespace-only lines. No stronger verification is
inferred from Git's exit status.

Direct dependency SHA-256 values at the pinned baseline:

| Path | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `3f70daf755fd6af59959fa48a35aa2d5153639621cc18edc58934246f2aabb69` |
| `rules/design-authority.md` | `4477be1344edb73e2873f94233d760c9a600bee6adbaaff3ec812a49c5219e7b` |
| `rules/git-concurrency.md` | `2561a7168ba8b2d655cc928c8adac565755ec7e3b6b4175e8ac87be4bcdaa5e6` |
| `rules/compiler-engineering.md` | `1ff144d376052d2e01d2e97ba3290e6942f126765067fbf11dfeffc06f89b442` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| `notes/design/2026-10-10-concrete-effect-annotation-implementation.md` | `3a3186723cd93edd2f767a7e4a481cb6dbed701fc749502e640071f65a4d89ae` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| `notes/design/2026-10-02-typed-source-owner-realization.md` | `5cbd8110736ee4d43e0c65460fa9ecf700228bfdbe9fbaa7642ea0302d86f1aa` |
| `notes/progress/2026-10-05-effect-attachment-subtraction-playground.md` | `7a831a5068d1fcc61a5ed350acce7b32822757c99e1ae778775ef80f0c52e0b6` |
| `notes/progress/2026-10-05-concrete-capture-profile-derivation.md` | `a7ef12555b688e0e7f22c1c9d8936ab952282da08896f49646cfe78c0afbfc79` |
| `notes/progress/2026-10-10-selected-formal-contextual-integration.md` | `0a07713df99571d19705333e73c195c3ad29b6165af92cb6821c02cd407da507` |

Dependency comparison against the baseline found no changes in the governing
paths; the final comparison also covers that additional root-sign locator.
Concurrent solver/test edits and pending questions are outside this lease.

Commit packet: exact lease is this note; baseline
`32c65f07671b9de7b05ece3044a714c4d8d0e61b`; dependency changes none;
review status compiler-referee PASS with primary clarification; research
conditional derivation only, no theorem promotion. Proposed message:
`research: derive conditional contravariant effect hygiene`.
Shared-record deltas intentionally left for the primary/curator: record the
conditional result and missing source attachment lemma, retain subtraction as
open, and do not promote hygiene/soundness/principality or production gates.
