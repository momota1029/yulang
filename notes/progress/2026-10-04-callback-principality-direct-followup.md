# Direct follow-up: callback bridge and principal common allowance

Date: 2026-10-04
Branch: research/simple-sub-intrusion
Initial base: eaad8358
Integrated concurrent research: through 07b0089f
Scope: proof/design only; no compiler implementation

## Request and result classification

After the reviewed pure structural FMP theorem, the user explicitly requested
direct attacks on both the Callback production bridge and Principality /
common allowance. This reopens those proof attacks despite the earlier
navigation wording that callback proof search had stopped at production
design. The source contracts and implementation gate are unchanged.

The result is **partial proof and sharper localization**, not closure of both
unrestricted gates. The completed pure structural FMP result remains
classification A. Neither a full production callback theorem nor a full
principal/common-allowance theorem is claimed here, and no counterexample to
the intended source schemes was established.

Two detailed proof records contain the complete arguments:

- [Source-indexed callback endpoint realization](../design/2026-10-04-source-indexed-callback-realization.md).
- [Common allowance and safe context preimages](../design/2026-10-04-common-allowance-context-preimage.md).

## Callback: what was actually proved

The approved typed observation projection can be applied once to a complete
joined generated observation. Theorem C's old-witness-copying lift then
preserves the projection for **all finite higher-order future-use and
resumption histories**, without a higher-order saturation or a local
projection/sequence commutation assumption. This result is about the
generated complete bounds, not merely exact source execution coverage.

The new reference interpretation gives finite membership and admission
constructors for a source-associated Function endpoint. They retain the
ordinary descriptor together with its existing source derivation, operands,
scopes, residual, latent labels and typed occurrence/path evidence. The rules
use actual entry, whole-argument reification, receipt, bind/rebind, body and
designated result consumption. Root membership has a finite constructor
witness; admission is a punctured source certificate independent of the
pending query.

Constructor-by-constructor translation proves, at the same `xi=(nu,K,D)`,

```text
D_C^ref = D_GC subset D_GA = D_A^ref
P_A^ref(h) = Pi[P_GA(h)]
P_C^ref(h) = Pi[P_GC(h)]       for every h in D_C^ref.
```

Theorem C then gives `P_A^ref(h) subset P_C^ref(h)`. Thus the reference
construction discharges its entire full-bound crosswalk. It is a concrete
candidate interpretation with an inversion proof, not a proof that a
different production interpretation admits no extra observations.

This distinction is substantive. The existing sources support a same-fiber
`Rel_C` projection as a candidate but do not define today's production
complete endpoint bounds. Merely assigning the name `P_prod` to the new
reference bound would conceal that missing conformance theorem. Current
source/endpoint owners also do not provide application and decorated
invocation derivations for the requested full examples. No missing carrier
or need for an alternative type system follows from those facts.

Role-first B remains independent: the expected boundary selects Handler
before independent parameter/body/result synthesis; supplied source evidence
selects `d-`, `d+`, `b+` and witnessed attachments; then one completed
`F_lit <: F_cb` is emitted. The finite reference construction is total when
those finite valid decorations are supplied. It proves neither success of
every B query nor source generation of those decorations for every raw
program. Theorem C's linked Pure-value success is not applied to arbitrary
inline literals or unrelated annotations.

## Common allowance: the new exact semantic boundary

For every original solution `s`, its finite complete source relation and
existing invocation projections define a derived joint view `A_s`. Keeping
the original residual makes the forgetful image of `{(s,A_s)}` exactly the
original solution set. Repeated calls and higher-order stages retain their
source occurrence, intermediate descriptor and continuation dependencies.
This proves finite intensional *forward* presentation, without equating
original endpoint variables or replacing sequencing by a row union.

Public validity goes in the opposite direction. If a source context is the
complete relation `T(i,h,o)` and `Adm_T(i,h)` is independently generated
admission, then the exact safe context preimage of public view `V` is

```text
U_T^safe(V) = {
  i |
  forall h in D_V. Adm_T(i,h)
  and
  forall h in D_V. forall o.
    T(i,h,o) implies o in P_V(h)
}.
```

For a complete input relation `R`, `R subset U_T^safe(V)` is equivalent to
admitting every checked challenge for every `i in R` and bounding every
complete source observation at those challenges. The proof preserves the
whole assignment and all finite histories. It is an exact semantic
equivalence for the existing domain-containment comparison route.

A finite positive source graph does not automatically represent this
universal condition in the inference language. The finite witness

```text
T0 = {(i,good)}
T1 = {(i,good),(i,bad)}
V = {good}
```

has `U_T0(V)={i}` and `U_T1(V)=empty`. Positive relational formulas are
monotone in a variable `T`, while universal preimage is antitone. This rules
out a uniform positive-only construction, even though each forward relation
is finite. It does not refute Yulang principality; an existing complete
Function comparison atom could encapsulate the condition if its exact
source interpretation and completeness were proved.

The note also proves the complete-contract join on a common challenge
universe: intersect domains and union complete observation bounds. Such a
join retains the required original challenges exactly when those challenges
belong to every original domain. Different source stages require the
existing typed pullbacks to a common *source tuple*, not identification of
their raw local carrier coordinates.

## What remains unproved, without changing the quantifiers

The common-allowance target is still

```text
forall s in S_xi. exists a. Q_xi(s,a)
forall valid public V. exists admissible m_V.
```

The derived semantic `A_s` is not yet a legal descriptor-valued `a` with all
required completed direct Function comparisons. Proving that step requires
the original source-owned abstract-component/port interpretation, including
domain preservation and one target descriptor with its legitimate occurrence
maps. An effect variable cannot simply be assigned an arbitrary tuple of
stage relations and endowed with a new selector at each occurrence.

Likewise, safe-preimage membership does not automatically supply an
admissible instantiation map for a whole public presentation. The completed
comparison relation must represent the required validity condition, and the
allowed maps must commute with the source occurrence views and preserve the
whole old residual. Generalization/renaming transports such a map once
constructed; it does not construct every `m_V`.

No scalar Read/Write counterexample is claimed: failure of literal shared-row
substitution does not rule out a direct higher-order subsumption witness or
an already admitted contextual view. The exact map class cannot be weakened
to manufacture a negative result.

## Review and verification

Three read-only producer lanes examined callback construction, principal
allowance and source authority. Only the primary edited the records. Two
independent read-only reviewers then inspected both complete arguments and
their direct governing sources without receiving producer reports:

- `review_callback_allowance_math`, compiler-referee: no blocking or major
  mathematical defect. One minor owner locator named a nonexistent
  `TermView::Function`; the primary corrected it to the actual
  `PositiveFunction` / `NegativeFunction` variants and checked the source.
- `review_callback_allowance_spec`, specification-auditor: no blocking,
  major or minor conformance defect; relative links in both drafts resolved.

Both reviewers explicitly found that these limited results do not close
either requested main gate. The proof notes are marked Reviewed within
those declared limits. No new semantic selection is marked Authoritative.
The later navigation/review-record edits only report these findings and were
checked by the primary; no additional mathematical claim was added after
review.

No compiler, type carrier, descriptor rule, source acceptance/rejection,
existential inference feature or test expectation was changed. Verification
is proof review plus document/link and diff integrity; no claim is made that
runtime compiler tests establish these semantic theorems.

The branch advanced concurrently through `3465e326` with callback lift/bind,
Value-entry/resumption and principal-support research probes. Those changes
were fast-forwarded and preserved before navigation integration. A later
concurrent point-row fresh-use probe, `07b0089f`, was merged without conflict
and its source-scope limitations inspected; it changes no premise of the
reviewed proofs. Their
[playground record](2026-10-04-callback-principal-playgrounds.md) explicitly
limits them to bounded characterization; they are not premises of the new
proofs and were not rerun as a claimed theorem test in this follow-up.
