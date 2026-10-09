# Original registry constructor: concrete adoption proposal

Date: 2026-10-10
Status: Reviewed; non-authoritative
Scope: proposed source-owned pre-Call registry representation and constructor API
Baseline: `070281ce0`
Drafted-by: primary, from bounded architect assessment
Reviewed-by: compiler_referee, spec_auditor; no findings in stated delta scope
Supersedes: none
Implementation / default acceptance / F5 authority: none

## 1. Exact proposed decision

The [approved q3 gate](2026-10-10-source-owned-registry-design-gate.md)
already authorizes constructor design and independent review. This proposal
selects the concrete definitions to be reviewed for subsequent adoption. It
does not ask to open that gate again.

The definition source is the independently reviewed
[source-owned registry candidate](../theory/2026-10-10-source-owned-original-registry-construction.md),
integrated at `fdda52fd8`, SHA-256
`9bc209159fee600ed7bc3e389ceef54aeaaa72c7e9f67235e4fc9e2a5c26cfbb`.
The exact scoped clauses below refer to that frozen version; references are
part of the decision object. Its repaired construction proofs retain their
existing conditional scope.

Propose adopting the following six connected representation/API choices for
the resolved nonrecursive formal/Name/Int pre-Call fragment:

1. **Nominal source keys and complete recipes** (§§3.1–3.2): keys are
   `(source version, actual owner occurrence, role)`, with complete ordered
   schemas and a computed finite declaration-token closure. Endpoint equality
   never merges keys, owners or proof choices.
2. **Raw immutable registry before typed decoding** (§3.3):
   `P_old^src = Seal(I_syn, Keys, R)` stores source/context/recipe syntax and
   complete declaration tokens. It stores no runtime valuation, completed Code
   or recursively embedded WellFormed proof. Lookup selects the exact recipe
   or returns the exact external-query absence branch. WellFormed and the typed
   decoder are derived at this same P afterwards.
3. **Source owner and registration constructors** (§§4.1–4.2):
   Header → owned port declarations/licenses → complete Value Entry →
   `Reg_src` → shared invocation anchor. Result registration likewise forms its
   header/port before registration and Code-Result. Adopt the displayed raw-P
   argument presentations and `OwnerPortLicense_src` introduction/eliminator.
   This permission returns its exact owner, port, whole declaration and scope
   map; it supplies no original contribution license, C0 or live authority.
4. **Shared ordered decoding and generated source images** (§§4.2, 5.1):
   decode the same Formal key with its same source registration/proof-choice
   family across Name uses and aliases. Form `J_a/J_f` by the displayed whole
   original Data/Return/Prefix constructor-image clauses and complete local
   catalogues. These are source-generated roots in this proposed interpretation;
   they are distinct from the q2 `J_lit` and any separately fixed old image.
5. **Complete post-decoding consumer API** (§§6–7): retain original dependent
   arguments and the entire same P for SourceRef, original applications and
   full-registry observers. Preserve original local guards, domains, evidence,
   alternatives and future fields. Registry availability does not assert their
   admission, guard truth or witness inhabitance.
6. **Whole actions and domain boundaries** (§8): transport source/recipe/schema
   fields, shared choices and lawful actions as defined there; reflect external
   absence under bijective nominal renaming and only transported-image absence
   under injective embeddings. Noninjective endpoint substitution cannot merge
   source keys.

The candidate's seven source rows and Law/Formal/Data/Result/Image ranks
describe this theorem fragment. They are not a seven-row whole-program limit,
a language rejection rule or a replacement for later Call/recursive owners.
Allocator layout, traversal containers and internal implementation names can
be chosen later within these equations.

If approved, these definitions would be the selected source-owned old component
for this fragment, before q2's separate Arg/Lit extension. This selects an
interpretation; it does not identify it with a separately fixed original
registry or certify an unprovided original consumer map.

## 2. Source meaning and remaining actual correspondence

The raw-P operand signatures, owner permission, registration constructors and
generated image presentation are durable choices. Existing general direction,
successful lookup proofs or metadata cannot adopt them. No independently fixed
original declaration is cast into their types by this proposal.

The chosen production local declarations must provide the complete applications
required by these APIs at their actual binders. The correspondence ledger must
name Parameter/entry/Force/rebind, Int, Return/Prefix and scope/reference/world
declarations; every complete field-type argument, preceding constructor and
required local law; and each unresolved mismatch. Source row formation cannot
use an unavailable later/self typed decoder argument. A bare declaration token
does not supply its complete application.

The original static origin/registration/license consumers need their actual
typed maps. The source-owner permission supplies only its stated declaration
permission. Selected ReturnImage consumers need exact root/domain/incidence
and whole-field maps; `Comp` endpoints do not identify images. Post-decoding
observers retain the same full P, including domain/absence/lookup observations.
No universal equivalence with every foreign registry model is added.

The bounded [actual-kernel conformance attempt](../theory/2026-10-10-original-registry-kernel-conformance-attempt.md)
reaches the first formal. The original displayed Entry-Value rule consumes
ParameterOrigin and carrier/receipt/Force/rebind ports. Selected Generalize
fixes the formal's Value role and Desc scope, but the inspected source cone
does not elaborate their full original introduction signature against raw P.
The precise remaining input is an ordered substitution
`Gamma_form^src(P) |- mu : Delta_in^orig`, then authentic `intro_orig[mu]`.
`Delta_in^orig` names the required complete declaration, not a supplied
signature. No concrete mu, actual late-decoder incompatibility or downstream
Name/Int/Return map has been established. This adoption proposal supplies the
new candidate owner API; it does not claim that the unprovided independently
fixed original introduction has already been realized.

## 3. Production gate and failure boundary

Adoption of this representation alone would permit subsequent design and
correspondence work under its exact definitions. It would not authorize
compiler implementation or default source acceptance. A usable production gate
also needs the actual complete Call formation, O0/O1, independent C0/admission,
effective correlated solving, completed-source Generalize, transformed ordinary
public extraction/fresh checking and atomic publication.

The [ordinary-value/formal refinement question](../../questions/2026-10-10-call-formal-ordinary-value-refinement/q1/question.md)
remains separate; neither literal-only nor uniform scope is selected here.
The full Call contract and all four q2 choices remain fixed. No RuleCall_L
equations, effect/protection removal or new printed invoke scheme are adopted.

If a selected declaration needs an unavailable typed argument, stronger license
or different image domain, stop only that hookup and report the exact mismatch.
Keep its whole signature and alternatives. Do not publish a partial package,
weaken the contract or convert this supplier gap into a source type error.

## 4. Review and decision boundary

M3 proposal/conformance review, with two independent roles: compiler-referee for
typed construction and semantic boundaries, spec-auditor for exact q3/q2 and
Function-view scope. Review only the adoption delta and its direct dependency
cone; the repaired candidate's unchanged construction proofs are carried
forward. No tests, builds or measurements are needed for this document.

After review, present the frozen exact six-choice proposal for explicit user
approval through the question board. Neither q3's design permission nor a
positive review supplies that later approval.
