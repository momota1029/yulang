# A directional fragment does not require completion of the entire profile

Date: 2026-10-06
Semantic/source baseline: `e12738d4f1452d87883516dfa5b709a4a5c38230`
Preceding research: `71f0cd46d1a8a60b3a15255e3bf3c6f283e58373`
Status: independently compiler-referee-reviewed conditional research; no findings
Claim class: completion-parametric conditional fragment realization/transport;
             reduced source-identity obligation, not source adequacy
Semantic/implementation authority: none

## 1. The specific remaining question

The [typed contribution bridge](2026-10-06-directional-typed-contribution-bridge.md)
derives a static upper profile fragment and locates its dynamic realization
and typed capture association. This follow-up asks whether the missing
**complete** profile is itself necessary for realizing this one fragment.
The answer is no: one can make the transport theorem uniform over every
independently compatible completion. The source-to-view association still
has to be generated; profile completion cannot substitute for it.

The current [directional user decision](../design/2026-10-06-directional-inferred-effect-protection-addendum.md)
licenses

```text
delta = Gamma_dir(k,beta,u) = { original upper p0 |-> Protected }.
```

It licenses no new grant. Independently inherited provider/result evidence
and independently source-licensed contract information remain separate.
[Inferred call views](../design/2026-10-05-inferred-function-call-views.md)
§§1.1–5 fixes source identity, original shared `xi=(nu,K,D)` and the scope
of this requirement. The construction below uses the reviewed conditional
[typed-boundary machinery](../design/2026-10-02-typed-boundary-realization-draft.md)
§6, without promoting that package to a complete Yulang source judgment.

## 2. Completion is a parameter, not a selected witness

At a fixed original scoped row `xi,w`, let `Completions(delta;xi,w)` be the
family of independently source-compatible original profiles which contain
this exact tagged fragment and retain all original constraints/evidence.
This is a parameter family, not a newly selected membership rule. In
particular, compatibility and any grants come from the original independent
source interpretation, never `Q`, endpoint equality or the theorem being
proved. The family may be empty; no existence result is asserted.

For each `Gamma` in that family, use the **same** original component row
and source-origin correspondence. One completion, together with its own
original witnesses, serves all uses of the shared contract in that row.
The theorem does not choose a different completion per port, event, or
challenge. Dynamic invocations can instantiate different boundary identities;
they still instantiate the same original static provenance as required by
their jointly typed source interface.

The exact correspondence needed for this fragment is provisionally named

```text
SourceViewInst(r_A,d_f,e_f; k,beta,u,p0,sigma).
```

It relates the original formal receipt and its activation `r_A`, the
received/rebound formal view's evidence root `e_f`, and the dynamic instance
of the original upper-use position `p0`. It is a required source judgment,
not an introduced Boolean flag or new compiler field. One may explain its
source-origin part as

```text
sourceOrigin(e_f, inst(p0)) = (k,beta,u,sigma,p0),
```

where this is equality of the original provenance correspondence, **not**
of value pointers, endpoint denotations or printed types. The judgment must
also supply the matching typed position and original formal-receipt identity.
The displayed equation alone, stripped of that typed/scoped evidence, is
insufficient.

## 3. DFRAG: completion-parametric fragment theorem

Assume that correspondence, the independently typed original receipt/view,
and its source-certified callback-boundary introduction. For every
`Gamma in Completions(delta;xi,w)`, the existing boundary constructor gives
the corresponding boundary instance

```text
b_Gamma = (receiver r_A, slot d_f, profile Gamma, original endpoints).
```

Its received/rebound profile contains the source-tagged fragment at
`inst(p0)`, with boundary reference `b_Gamma`. The result is uniform in
`Gamma`: completing other positions does not change this fragment's protected
mark or create a grant **from this fragment**. This is a family of
realizations indexed by `Gamma`. It is not an equality of full boundary
objects with different profiles, and does not assert equal final handler
visibility across arbitrary completions with other independent evidence.

Now assume the typed capture/read correspondence for the selected closure,
with maps `M_cap` and `M_read` on its source-tagged paths. Keep provider
evidence as a separately indexed input. Let `Select_delta` retain only
incidences carrying this original fragment's provenance. For each compatible
completion, the common typed image satisfies

```text
Select_delta(M_* chi^Gamma) = M_*(Select_delta(chi^Gamma)),

Select_delta(chi_read^Gamma)
  = (M_read o M_cap)_*(Select_delta(chi_f^Gamma)).
```

**Proof.** A transported incidence belongs to the left-hand side of the
first equality exactly when it has a source-path witness, an `M` edge and
the retained `delta` provenance tag. The common indexed image preserves
that tag rather than merging sources by target value. Move the tag test to
the source witness; this is exactly membership on the right-hand side.
Conversely, every such source witness and edge produces the corresponding
tagged output incidence. The composition equality follows by retaining the
same intermediate path witness for capture and read. It holds even if the
maps are partial: an incidence outside a map's domain contributes on neither
side. No missing path is asserted to exist.

The boundary constructor uses `Gamma`'s mark at the stipulated source
position, which extends `delta` by the parameter hypothesis. Everything
else in the proof depends on the typed correspondence and retained
provenance, not on completion of unrelated positions. Rebind is included by
the same composition for the provider-source input at its matching result
paths; the upper fragment begins at its own realized formal position.
`K` remains the original shared predicate ledger, `D` uses its corresponding
path images, and inherited lineage `L` remains attached. Independent
provider/result sources are retained in the full packet, although omitted
from `Select_delta` solely to state this fragment theorem. QED.

This proof concerns profile incidence and typed transport. Event observation,
same-view receipt, exact owner/handler/receiver activity and any concrete
grant are still the separate premises of `Path`, `Inc_C` and `Visible`.
There is no monotonicity or equality claim for complete handler behavior
when unrelated completion data change. In the selected nested source,
`r_A` is the receiver only **if** the correspondence realizes the original
formal boundary there; it is not inferred from the static `beta` alone.

## 4. The source cut after factoring out completion

The remaining first source obligation is now one fragment's
`SourceViewInst`, not construction of every member of `Slots(beta)`.
The immediately following capture obligation is the analogous association
with the closure's retained environment view and later read. There are
concrete reasons that the existing syntax/entry facts do not prove them:

1. Typed-boundary §6 defines a view by `(value, signature position, evidence
   root)`. Two aliases of the same value can have different boundary views.
   Lexical capture therefore identifies the value without necessarily
   identifying its evidence root or original upper position.
2. Its boundary introduction starts from a source-certified callback boundary
   and profile. Constructing a tuple named `(r_A,d_f,Gamma,...)` is not a
   derivation of that source input.
3. [Typed-core](../design/2026-10-02-typed-computation-core-elaboration.md)
   §6 retains admitted annotation/typed-flow premises in receipt path
   references. Value entry fixes force/rebind order and preserves its actual
   provider view; it does not generate the missing source-origin association.
4. Typed-core §7's representation-preserving `VIncl` checking is not a
   boundary introduction or additional receipt. Typed-boundary §6's
   `Receive` records ownership of an existing typed view and creates no
   boundary or concrete contract. Neither successful checking nor possession
   of the receiver activation supplies `SourceViewInst`.

These are a bounded rule-inventory cut and a reduced proof interface, not
an impossibility theorem for every future source formulation. They do not
prove that a new user semantic decision is required. A source rule derived
from the existing selected semantics may still supply this correspondence.
It must retain upper/lower provenance, original scope and the same joint
row instead of assigning the upper fragment to every alias or private
provider binding. A known external Name gets no new seed from this theorem.

## 5. Consequence for the main gate

The dynamic proof can proceed one directional fragment at a time **while
retaining all fragments in the same original joint relation**. “One fragment
at a time” describes a lemma's quantified projection, not independent
existential choices or permission to discard the rest of the profile.

Completeness of the full original profile and source solution relation still
has its own coverage obligation. DFRAG removes that completion as a required
input to the *form of this fragment's transport proof*; it does not prove
source-view instantiation, existence of a compatible completion, typed
capture attachment, independent all-world admission, unrestricted
principality or either production inclusion. Callback B, Option A/2 and
actual callable role/entry remain unchanged.

## 6. Verification boundary

This result uses the source/correspondence producer's additional two narrow
pinned-source reads and the primary's displayed tagged-image proof. An
independent compiler referee reviewed the frozen note, its typed-bridge
dependency and typed-boundary §6, with no blocking, major or minor findings.
The review checked compatible-completion quantifiers, the shared original
row, preservation of tags, distinct full boundary objects, partial-map domains,
and the absence of an all-completion handler-visibility claim. It kept
source-view/capture association, completion existence and full-profile
coverage open. See the [review record](2026-10-06-directional-whole-source-review.md)
for the frozen hash and exact scope.

No checker, build, source execution or Oracle run is involved. Local-reference
and whitespace checks accompany integration; they do not prove source adequacy.
