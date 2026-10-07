# Original ordinary Call: candidate source-introduction contract

Status: Reviewed
Scope: Typed source-generation evidence for the ordinary Call in
       `my apply f = { my step x = f x; step }`
Approved-by: none
Reviewed-by: `compiler_referee` and `spec_auditor` (O1 §3.1 candidate; upper-occurrence/J0 composition delta review)
Supersedes: none
Semantic and implementation authority: none

**Narrow adopted successor.** The O0 formation cases are now governed by the
[original Call formation definition](2026-10-07-original-call-formation-definition.md).
The reviewed [O0-selected theorem](../theory/2026-10-07-adopted-call-formation-o0.md)
supplies the table's local typed output/source-root incidence for actual
emitted Gen-Call-0 records. This document's other proposed introductions,
original domains and residual consumer premises remain unchanged. Its
pre-adoption interface/status text is historical where it asks for that
selected local formation again; no owner/slot/contribution/profile result
follows from the adoption.

## 1. Purpose and authority boundary

This proposal specifies interfaces for missing original source introductions.
Section 3.1 proposes a new static-only original slot/owner arm for the selected
emitted Call. It does not define the rest of `I_orig(X)`, contributions,
admission, licensing or the complete challenge family.

Governing sources:

- Inferred Function call views §§2,5: Authoritative shared source formation,
  typed paths, stable ownership, one original `xi` and comparison independence;
  constructing judgments remain open.
- Nested-block source addendum §§1–3: Authoritative sequential local binding,
  inert return of `step`, capture of outer `f` and local binding of `x`.
- Directional protection addendum §§1–4: current user decision protects an
  original upper output at a justified protected-variable exposure without
  back-protecting an existing lower/provider occurrence.
- Source-contracts §§2.1–3.5,10: conditional kernel, local typing, emission,
  independent admission and transport requirements.
- Round-4 constructor reduction: O0/O1/C0/C1/J0 producer obligations.
- Both round-5 artifacts: C-realization retains its owner/view input; static
  metadata does not certify ordered contribution interpretation.
- Compiler-engineering and design-authority proof-obligation-economy sections:
  preserve approved behavior and existing gate status.

No source restriction, annotation requirement, generic Value-entry-implies-Pure
rule, Oracle semantics or solver algorithm is proposed.

## 2. Owning responsibility and current invariant

Typed source constraint generation owns introduction of the original shared
contract, typed exposure, static ownership and source-to-contribution incidence.
Resolution supplies lexical facts; independent primitive/Call laws justify
semantic typing. Generalization and instantiation transport established facts.

The current shadow route retains source, binder, capture and Apply identities.
Its pending-application scan does not submit the local initializer to semantic
collection. Its conditional evidence adapters consume assumptions.

Consequently no inspected current phase constructs the complete required
O0/O1/C0/C1/J0 facts and then discards them. Their absence is not established
reconstruction debt.

## 3. Smallest candidate interface

Fix the original `X`, binder tree, providers, scopes and
`xi=(nu,K,D)`. Retain the approved nested source and original upper exposure.

The following are proposed interface requirements, not adopted inference
rules:

| Port | Required original evidence | Independent justification still required |
| --- | --- | --- |
| O0 | For an actual emitted Gen-Call-0 record, adopted `kappa_e` gives the typed correspondence from `U_e,outEff(U_e)` to original `p0` at its recorded root/scope. | All-source record generation remains open; O0 does not supply O1, semantic provider admission or contribution facts. |
| O1 | Proposed §3.1 static-only constructor supplies `s_e in Slots_orig(beta)` and `Own_orig(beta,s_e,u,p0,o_e;X)` for the selected source. | The new original arm is unadopted. Compatibility with a separately fixed historical owner interpretation remains unproved. |
| C0 | Independent complete typing of `R_U_all`, retaining every compatible filling and extension dependency. | Actual primitive, lookup/Return, Call, entry, Bind, receipt, response, resumption and future-provider laws with their joint inputs. |
| C1 | `Contrib_orig(c,rho_U;X)` and certified `Emb_orig` for the complete typed invocation image. | Original contribution-domain closure/preimage rule, including required independently licensed alternatives. |
| J0 | `a in I_orig(X)`, `Inc_orig(a,beta,s,p0,u,c;X)` and complete-family coverage by that same `a`, where `u` is the generated upper checking occurrence. The lexical callee use `u_f` remains evidence in `o_e` and is not substituted for `u`. | Original joint owned-image introduction and coverage elimination at the unchanged coordinates. |

For a successful original introduction, the required conclusion remains:

```text
exists a in I_orig(X).
  original owner/slot/path/contribution incidence at beta,p0 and
  forall z in F_C(X;xi). Cover_orig(a,z;X)
```

The witness precedes observation choice. Matching coordinates do not prove
incidence. Owner inhabitance and contribution representability separately do
not establish their joint original fiber.

O0/O1 and C0/C1 are separate dependency branches. This proposal selects no
global ordering between them. Static owner formation does not require dynamic
receiver activation: the returned closure can remain uninvoked.

### 3.1 Candidate O1 static slot and upper-owner formation

The adopted O0 definition now supplies `e`, its registered root, and the exact
typed Call-output incidence `kappa_e` for an actual emitted Gen-Call-0 record.
For the approved nested source, retain the following inputs at their original
indices:

```text
Idx(e) = (B,X,xi,Delta_step;
          d_f,A_f,R_f,u_f,u_x,c,u,U_e,beta,p0,p_out(c),ElimOrigin)
beta = (d_f,R_f)
p0 = (beta,call.effect)
q_e = outEff_orig(U_e)
kappa_e : TypedOutputCorrespondence_orig(
  U_e,q_e,p0;B,X,xi,Delta_step;beta,u,c)

h_res : Resolve(u_f,d_f)
h_cap : Capture(step,d_f,R_f), including its original import map
h_reg : registered root (d_f,A_f,R_f) at sigma_apply
h_ann : d_f is unannotated
h_seed : SeedOrigin(k,d_f,A_f,R_f,sigma_apply)
h_exp : ProtectedVarAt(k,A_f,sigma_step,u)
h_up : SourceUpperUse(u,A_f,U_e,sigma_step)
```

`u_f` is the lexical callee occurrence; `u` is the distinct generated upper
checking occurrence. The capture/root/provider remain at `sigma_apply`; the
Call demand, exposure, output correspondence and local dependencies remain at
`sigma_step`. S1 supplies `h_seed`, `h_exp` and `h_up` for this selected
unannotated-formal exposure. O0 supplies `kappa_e`. Neither successful `Q`
nor endpoint or identifier equality is an input.

The proposed static slot is a canonical constructor keyed only by the original
registered root and source output position. It is a distinct original term
from `p0`; registration and annotation derivations are evidence for its
introduction, not part of its identity:

```text
s_e := CallSlot_orig(beta,p0)
  : StaticSlot_orig(beta;B,X,xi,sigma_apply)

Slot-Key-Equality:
  CallSlot_orig(beta1,p01) = CallSlot_orig(beta2,p02)
    iff beta1 = beta2 and p01 = p02
  under the same legal original identity action

e : actual emitted Gen-Call-0 at the indices above
h_reg : registered root (d_f,A_f,R_f) at sigma_apply
h_ann : d_f is unannotated
---------------------------------------------------------------- O1-Slot-Call
s_e in Slots_orig(beta)
```

The proposed original `Slots_orig` introduction and corresponding owner
introduction are:

```text
o_e := CallUpperOwner_orig(
  e,kappa_e,h_res,h_cap,h_reg,h_ann,h_seed,h_exp,h_up)
  : OwnerEvidence_orig(beta,s_e,u,p0;
      lexicalUse=u_f,seed=k,capture=h_cap,
      B,X,xi,sigma_apply,sigma_step,ElimOrigin)

e : actual emitted Gen-Call-0 at the indices above
kappa_e : O0 typed output correspondence for this same e
h_res   h_cap   h_reg   h_ann   h_seed   h_exp   h_up
s_e in Slots_orig(beta)
----------------------------------------------- O1-Own-Call
Own_orig(beta,s_e,u,p0,o_e;X)
```

These are **proposed new original formation cases**, not consequences of O0
or S1 under a separately fixed historical owner interpretation. In the
selected static-only source-owned arm, `O1-Slot-Call` and `O1-Own-Call` define
the meanings of these constructors. They do not change other original
constructors or erase their evidence. No complete `SharedContract` or
provider-admission judgment is inferred from registration; this arm is
deliberately scoped to static ownership of this typed source output.

The key `(beta,p0)` is not the equation `s_e=p0`. The `Own_orig` incidence is
indexed by upper checking occurrence `u`, as required by K-Incidence; its
evidence retains lexical callee use `u_f`. The two occurrences are never
identified. Multiple exposure derivations at that same static source
position share `s_e`; each owner evidence term retains its own upper
occurrence, seed and capture provenance. No singleton or exhaustive
inventory claim follows. Other original slots, owners, providers and licensed
witnesses remain present and unchanged.

The proposed interpretation of `o_e` is static ownership of the protected
upper output at this source Call. Its defining elimination returns the exact
retained O0 output incidence and the S1 protection fact
`NewProtection(k,u,q_e)` at that same output. This new arm does not claim to
embed into every independently fixed historical owner interpretation; such a
compatibility theorem is still required for any cross-model use. It does not
mark an event, execute the returned closure, create a receiver or receipt,
rewrite the actual provider role, back-protect a lower/provider occurrence,
or introduce a contribution, license or complete-family witness. An inert
return of `step` transports the static derivation without activating `f x`.

For every legal whole-tuple substitution `theta`, the constructors must obey:

```text
theta(s_e) = CallSlot_orig(theta(beta),theta(p0))
theta(o_e) = CallUpperOwner_orig(
  theta(e),theta(kappa_e),theta(h_res),theta(h_cap),theta(h_reg),
  theta(h_ann),theta(h_seed),theta(h_exp),theta(h_up))
```

The same action transports `B`, `X`, `xi`, both scopes, the local demand,
capture/import map, seed and all incident evidence. Captured provider identity
is retained; no per-port freshening is allowed. Whole-tuple coherence is an
unconditional requirement for the proposed arm. Compatibility with an
independently fixed historical owner/view interpretation is required only if
this arm is used together with that interpretation; that embedding remains
unproved. A tagged carrier alone does not prove either obligation.

The static-only arm deliberately does not need complete `SharedContract`
validity. This is a new definition boundary, not a proof that the old K-Owner
rule's stronger premise was redundant. If the selected production contract
instead keeps a separately fixed complete owner/view interpretation, this
arm requires a typed embedding into that interpretation, with every existing
owner witness preserved. Root registration is never a substitute for
provider admission.

This case supplies only O1 for the selected emitted record. It does not close
ORIGINAL_ASSOC or supply C0/C1/J0, whole-family coverage, attachment,
licensing, PROFILE, independent admission or cutover.

## 4. Independent semantic inputs

A producer must not obtain its inputs from the desired association, successful
`Q`, admitted-row existence or an assumed profile carrying the conclusion.

C0 must instantiate the independent local laws retained by conditional
CALL_TYPE. The callee, inert whole argument, actual receiver, receipt, actual
entry, typed rebind, body, designated consumer, native return and invocation
return retain their original incidences.

Bind preserves the ordered pending suffix, original raw resumption and current
resumed state without replaying receipt. Future uses of returned providers
retain their independently justified contracts.

`R_U_all` ranges over the unchanged independently admitted whole-carrier
interface. The selected source diagonal `Delay(Name_x)` does not define this
domain. Actual provider role/entry remains distinct from the provisional
inferred Handler view.

C1/J0 cannot be inferred from these laws alone. Their original introduction
and coverage clauses remain unresolved semantic inputs. C-realization
transports supplied local witnesses; it does not generate them from raw syntax.

## 5. Canonical retained evidence candidate

Unverified proposal: when an independently justified original introduction
constructs these facts, retain its derivation and certified maps as the
canonical phase output.

Retain source origin, typed output correspondence, seed-at-exposure evidence,
static owner/slot, original scope and joint `xi`, contribution embedding,
joint incidence, complete coverage evidence and ordered continuation
interpretation. Consumers may inspect this existing derivation rather than
reconstructing it from IDs, shapes or successful queries.

This is a logical evidence requirement, not a selected Rust type, runtime
record, solver carrier or storage policy.

Generalization/use transport follows source-contracts §3.4: scopes, roots,
dependencies and all incident evidence move together. No per-segment hiding
or independently freshened joint witnesses is permitted.

The proposed arm adds a constructor case without restricting `I_orig(X)` to
its image, canonicalizing distinct licensed witnesses or removing
alternatives from other constructors. Compatibility with a separately fixed
historical relation remains a distinct obligation.

## 6. Obligation classes and retained gates

O0/O1 and C0 are A/B: semantic correctness and natural inference.
C1/J0 combine A/B with C strength from complete-domain and uniform-coverage
requirements expressly retained by the governing contract.

D applies only to a later recovery obligation when an owning phase actually
constructed and discarded the relevant fact. No such semantic loss is
established for the current exact-source route. Lexical identities already
retained by that route do not discharge semantic introductions.

Universal/exhaustive obligations remain open: complete original coverage,
all relevant original witnesses, exhaustive licensing introduction/inversion,
independent admission, Option 2 production extras, complete source adequacy,
production conformance, principality and soundness. Option 2 observations need
not have individual source-execution witnesses.

No gate is weakened, retired or closed. Production implementation and cutover
remain unauthorized.

## 7. Failure, rollback and verification boundary

Reject the candidate if it:

- assumes an original owner/contribution preimage from a typed relation;
- substitutes `s=p0`, `c=j_call` or a per-use slot count;
- uses `Q` to form ownership, paths, receipts or admission;
- conflates static ownership with receiver activation or provisional and
  actual callable roles;
- joins incompatible evidence arms or replaces uniform coverage by pointwise
  or finite-family witnesses;
- drops ordered suffix, resumption, provider, scope or licensed-extra evidence;
- restricts original witnesses to the certificate image;
- requires artificial annotations or source restrictions for proof convenience.

Rollback means abandoning this candidate representation and retaining the
existing unresolved gate and implementation state. This Reviewed proposal
authorizes no production mutation.

Future focused checks should discriminate each failure above, including
transport across generalization/use. They require independently justified
semantic inputs; a checker assuming those inputs cannot prove their source
introduction. Storage and transport cost remains unmeasured.

## 8. Remaining decisions and next review

No pair of complete Authority-consistent semantics with different approved
observable or principal outcomes has been constructed. The reviewed §3.1
candidate specifies one proposed O1 static-only case, but it remains
unadopted; treating it as the governing original definition still requires
explicit user approval. Until then, the canonical O1 gate remains open.

Unresolved: proof of §3.1 compatibility with any separately fixed original
owner/view interpretation; C0, C1 and J0 introduction/coverage; exhaustive
licensing and conservative-extra interpretation; eventual certificate
representation.

Any new semantic or architecture decision requires independent review and
recorded user approval before implementation. This document remains
non-authoritative and authorizes no implementation.
