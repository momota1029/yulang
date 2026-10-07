# Original Call formation: adopted constructor definitions

Date: 2026-10-07
Status: Authoritative
Scope: the signature-demand and source Call-effect formation cases for actual emitted Gen-Call-0 records
Approved-by: user, directly in the working conversation
Approved-at: 2026-10-07T22:09:13+09:00
Approval baseline: `d3def26c1079566bc4bd7660e2a21ddcfe960530`
Reviewed definition: [Call-construction proof §10](../theory/2026-10-07-call-occurrence-construction-proof.md#10-proposed-completion-clauses-and-adoption-boundary), including §10.1
Reviewed-by: independent spec-auditor for exact approval/definition conformance; independent compiler-referee for adopted O0 and consumer use
Supersedes: the unadopted status and independent-original-definition choice for these two exact formation cases only
Production implementation / cutover authority: none

## 1. Direct approval and exact scope

After the complete construction, semantic root interpretation and preservation
proofs were reviewed and published, the working primary asked whether the two
formation cases should become the governing missing original formation
definitions. The user answered:

> 承認するよー．定義にしちゃっていい

This is a current explicit decision under `rules/design-authority.md`'s first
authority level. The approved object is §10 of the linked proof at the pinned
commit, whose file SHA-256 is
`fbfbe797cb4843ab9d76c9e0b2191872935079f82c427147219416bdebf766b0`.
The immediately preceding scoped question stated both definitions, their
full-invocation interpretation and the absence of automatic downstream closure.
No addressable conversation URL is available; the quote, timestamp, published
revision and declared scope provide the actual approval provenance.

The decision is uniform on already emitted Gen-Call-0 records. The approved
source `my apply f = { my step x = f x; step }` is an established generator
instance, not a special-case branch in these definitions. The decision does
not assert that every ordinary source Call has such a record. A Call without
one retains its old derivation and child evidence without an annotation or
new acceptance restriction.

The approval was given directly to the working primary. It is not an imported
question-board handoff: no separate answering conversation's draft or approved
answer is fabricated or consumed. The local question's disposition records
this direct decision; its unintegrated files remain outside ordinary commits.
No further approval of this already selected scope is required.

## 2. Governing inputs and dependent indices

Keep the existing source-generation theory, source records, scopes and
complete invocation semantics. The
[Gen-Call-0 construction](../progress/2026-10-06-source-call-generation-construction.md)
§§4.2–4.4 supplies the actual emitted record. The
[Function-view Authority](2026-10-05-inferred-function-call-views.md) §§2,5.1
requires shared source contracts, typed paths, comparison-independent
formation and the original joint tuple. This document fills only the selected
missing formation cases.

For each actual record retain

```text
Idx(e) = (B,X,xi,Delta_e;
          d_f,A_f,R_f,u_f,u_x,c,u,U_e,beta,p0,p_out(c),ElimOrigin)
xi = (nu,K,D)
U_e = F_c
beta = (d_f,R_f)
rho_e = demand(e)
```

`rho_e` projects the scoped complete Function demand and its original
root/provider/scope/dependency indices. It contains no desired `p0`
correspondence or original occurrence witness. `d_f,A_f,R_f` retain their
original outer declaration/capture provenance; locally dependent `U_e` remains
in its actual `Delta_e` at the inner Call. Declared Function sort is not
semantic descriptor membership, successful comparison, provider admission or
inhabited solution space.

## 3. Adopted signature-demand formation

Use the finite scoped signature frames, finite registered walks, distinct
`Inv`/`Run` constructors and exact root projection of construction §§4,10.
For the scoped complete Function demand at the retained dependent fiber:

```text
rho : scoped complete Function demand with original indices
U := descriptor(rho)
------------------------------------------------------- OSig-Demand
inv_eff_orig(rho) := Inv(Id(U),U)
                    : EffPosition_sig,orig(U;B,X,xi,Delta)
H_eff(rho) := its independent frame, position family and derivation
outEff_orig(U) := inv_eff_orig(rho)  [at this same dependent fiber]
```

`OSig-Demand` is the adopted name for the `Sig-CallEff` case in construction
§10. The definition reads the scoped demand and its retained indices, not the
source/signature correspondence it will later support. The immediate root
is distinct from body, native return and every result-latent path, even when
some erased type/effect endpoints coincide.

### Root interpretation

Adopt construction §10.1's interpretation of this exact root. For any legal
old sorted assignment `theta`, let `d=interpret_old(theta,U)` be the already
interpreted complete Function description at those same joint indices.
Its semantic root carries exactly the existing full parameterized
`J_call(d;xi)` / `ExecuteCallable` interface, including actual entry, body,
designated consumers and native-return delimiters with unchanged dependencies.

```text
RootEff_orig(d) = { Inv_sem(Id_sem(d),d) }  [this distinguished root fiber]
interface(Inv_sem(Id_sem(d),d)) := J_call(d;xi)
interpret_orig(theta,Inv(Id(U),U)) := Inv_sem(Id_sem(d),d)
```

The singleton describes the distinguished root case only. It is not an
exhaustive definition of every original signature position, path, view,
profile, contribution or licensed witness. No original domain is restricted
to this constructor's image. Other independently specified cases remain
outside this completion and retain their own rules.

Consequently this selected original interpretation satisfies

```text
interpret_orig(theta,inv_eff_orig(rho))
  = completeInvocationEffectPosition_orig(interpret_old(theta,U)).
```

The equation is the reviewed root-evaluation calculation in §10.1, now at the
user-selected original definition. It is not inferred from Q success, source
execution or endpoint equality. It selects no new invocation denotation and
proves no assignment, admitted description or execution exists.

## 4. Adopted source Call-effect formation

For an actual emitted record, use exactly its demand and that demand's root:

```text
e : emitted Gen-Call-0 record at its original dependent indices
rho_e = demand(e)
q_e = inv_eff_orig(rho_e) = outEff_orig(U_e)
------------------------------------------------------- OC-CallEff
CallEff_orig(e) : original typed Call-effect occurrence
                 at (U_e,q_e; beta,u,p0,c;Delta_e)
```

The eight eliminators are precisely construction §5.1's equations:

```text
signature position = q_e
source position    = e.p0
upper occurrence   = e.u
Call               = e.c
static root        = e.beta with its retained declaration provenance
source scope       = e.Delta_e
source origin      = e's complete original dependent record
invocation leg     = e.ElimOrigin, retaining e.p_out(c)
```

The dependent constructor supplies its typed incidence certificate; the
untyped pair of endpoints does not supply its typing. An arbitrary effect
position for the same Function cannot replace `q_e`, and returning the closure
inertly does not create an additional Call occurrence.

Every legal substitution acts once on the entire original tuple and these
dependent constructors. Captured imports are fixed where required; local
dependencies, upper origin, shared `xi` and the separate elimination leg are
retained. The reviewed constructor and finite-derivation proof gives the
coherence equations. No per-port choice, hoisting or fresh provider is added.

## 5. Exact replacement of the previous proof target

The [minimal-clause record](../progress/2026-10-07-original-call-output-minimal-clause.md)
§7 previously left both formation heads unadopted and required proving them
in an independently fixed original interpretation. For these selected cases,
the user has chosen the explicit missing original definition. That local
definition-selection requirement is resolved by this document; the reviewed
constructor proof is now available under the selected definition.

This does not prove the old proposed family embeds into every independently
fixed original interpretation, nor claim the historically unchanged undefined
judgment was derivable. Construction §9 remains the correct compatibility test
when relating a separately fixed interpretation outside this selected scope.
It is not a new premise for using the original constructors just defined here.

The independently reviewed [O0-selected theorem](../theory/2026-10-07-adopted-call-formation-o0.md)
specializes the construction and supplies its exact consumer account. Its
closed scope is local static formation and typed incidence on actual emitted
records, including source-root provenance, exact root realization and
whole-index coherence. This conclusion uses the proof and its independent
review, rather than approval alone. The aggregate ORIGINAL_ASSOC node and all
production dependencies remain unchanged.

## 6. Retained contracts and obligations

The [source-introduction contract](2026-10-07-original-call-source-introduction-contract.md)
§§3–6 retains every other original domain and judgment. These two constructors
produce no original slot/owner membership, complete carrier typing,
contribution preimage, joint `I_orig(X)` witness, coverage, attachment,
license, profile, row or admission result. Original consumers still require
their exact independent premises. A supplied static occurrence never serves
as an execution receipt or a semantic grant.

The already reviewed conservation proof applies to the old symbolic and
executable reduct. It does not establish preservation of every old consumer
formula after a hypothetical identification with a separately fixed original
family. All-source generation, solver preservation/reflection, generalization,
hygiene, recursive/method/effect extensions, lifecycle, required principality,
independent open-world admission and Option 2 extras retain their existing
obligations. No approved source form, annotation rule, inference behavior,
world domain or production meaning is changed by an implementation here.

The original directional protection rule remains in force. Preserve the
original upper demand and independently justified seed; do not back-protect
an existing lower/provider occurrence or remove provider-owned protection.

## 7. Review and use boundary

The selected definitions and their mathematical construction were independently
reviewed at the pinned baseline. The adoption received independent
spec-auditor review with no blocking/major finding; its minor local-disposition
record mismatch was closed by the primary-owned direct-approval receipt.
An independent compiler-referee passed the exact O0 specialization and
consumer substitution with no findings. The primary accepted both reports;
no mathematical or definition repair was required. See the
[integration record](../progress/2026-10-07-call-construction-proof-review.md#7-approved-definition-and-local-o0-integration)
for frozen hashes and exact scopes. No production code, test expectation or
compiler routing change is included. A later attempt to reinterpret other original domains,
discard independently licensed alternatives or change observable behavior
would exceed this approval and cannot be inferred from it.
