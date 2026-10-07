# Original static Call ownership: shared-slot constructor and proof

Date: 2026-10-07
Original proof baseline: `370bb4634d0b5eb413c01bb984b995f74a743f59`, supplied by primary
Repair input baseline: `465c2af15dfb8ae5f603fea4dc4533e99f9b0c5a`, supplied by primary
Branch: `research/simple-sub-intrusion`, supplied by primary
Status: independently reviewed paired O1-static constructor theorem under the selected definition
Claim class: complete proposed original static O1 constructor case and its proofs;
  separately conditional old-family comparison and semantic consumer composition
Scope: actual emitted Gen-Call-0 records with original registration/capture,
  independently justified seed-at-exposure and adopted O0
Authority boundary: adopted O0 is an input, not reopened; this draft selects no
  production implementation, observable behavior, or canonical gate status
Exclusive write lease: this file only

**Integrated result.** The [governing static constructor definition](../design/2026-10-07-original-call-owner-definition.md)
selects the displayed missing original case under the existing source Authority
and the user's current construction authorization. Independent compiler-referee
and spec-auditor reviews both passed without findings; see the
[review record](../progress/2026-10-07-source-constructor-completion-review.md).
The reviewed lexical O1-static result remains sound on the stated actual
emitted, independently seeded envelope, including the approved nested source.
The incoming source-introduction contract now asks for checking-indexed
ownership at `u`, while the earlier proof introduced ownership at `u_f`.
This repair explicitly forms both original static facets from the same retained
certificate. A fresh independent compiler-referee passed the matching proof
and definition at proof SHA-256
`185ae5c590da45e9ed45d1e81368e0fdf513f4750c2f44cce53cbf4c1faadf34`
and definition SHA-256
`70673c298276360a539a01e39f2feddc5142d411b863bcb820c85f97776d3b8d`.
The primary accepted that delta; one minor review-provenance wording issue
was corrected in the definition. The frozen repair's mathematical body below
is unchanged and its review-pending wording is historical. Neither an
aggregate DAG node nor a semantic
owner/member, complete slot inventory or joint original-family theorem is
closed here.

## 1. Result and interpretation boundary

This note supplies a concrete original **static** slot/owner case. Its slot is
the shared complete-invocation position of the registered source contract, and
its canonical owner evidence is a typed attachment of an actual seeded upper
exposure to that position. Two explicit ownership introductions expose that
same evidence at the lexical and checking coordinates, respectively. The slot is formed at the original declaration/root; the local
Function demand remains in the exposure's dependent scope. Distinct lexical
callee `u_f` and generated checking occurrence `u` remain separate. Multiple
certified captures and upper exposures of the same registered root share the
slot and retain different owner derivations.

The construction reads actual source formation, seed and O0 certificates. It
does not assume `Slots`, `Own`, complete Function membership, a solution,
execution, a live receiver, or a permission. All independently valid other
original slot/owner cases are retained. This is one constructor case, not an
exhaustive slot inventory, and does not restrict the unchanged original
contribution/witness/admission domains.

The governing [Function-view Authority](../design/2026-10-05-inferred-function-call-views.md)
§2 calls the identity and inventory **static**, gives source resolution and
typed elaboration responsibility for ownership, and prohibits Q from creating
them. Its §5.1 leaves their precise construction judgments open. The
[source-introduction contract](../design/2026-10-07-original-call-source-introduction-contract.md)
§§2–4 distinguishes static O1 from independent semantic Call typing and original
contribution/coverage. No inspected clause defines `Own` as descriptor/member
validity. Accordingly the completed case interprets `Own` as static typed
source provenance. It must not be substituted for a stronger semantic owner
judgment without its separate realization law.

There are three claims with different proof obligations:

| Situation | Exact result |
| --- | --- |
| Missing original static constructor case is defined by §§3–4 | O1 introduction, exact eliminators, source safety and whole-index coherence follow by the proofs below. |
| A separately fixed old slot/owner interpretation exists | The comparison obligations in §8 must hold; this note does not identify it by endpoint equality or by the phrase “static owner.” |
| A consumer needs semantic shared-contract/member validity or complete original coverage | Its independent premises remain; static registration does not produce them. |

The user's permission to continue legitimate definitions authorizes this
construction work under the existing static source-formation direction.
The primary owns recording its exact reviewed scope. The paired theorem below is
complete under its displayed formation definitions. The lexical result retains
its previous review; fresh review and definition integration of the checking
facet remain pending. No closure of aggregate ORIGINAL_ASSOC follows.

## 2. Actual inputs and the precise S1 envelope

Fix a finite well-scoped source derivation `D` with its existing emitted
inventory `E_D`. For `e in E_D` retain the entire adopted O0 index:

```text
Idx(e) = (B,X,xi,Delta_e;
          d_f,A_f,R_f,u_f,u_x,c,u,U_e,beta,p0,p_out(c),ElimOrigin)
xi = (nu,K,D)                    beta = (d_f,R_f)
U_e = F_c                       rho_e = demand(e)
```

Here the `D` in `xi` is the existing dependency coordinate; the source
derivation's name does not introduce another such coordinate. The source
tree, providers, dependencies and scope correspondences are those of the
actual derivation. `u_f` resolves to `d_f`; `u` is its emitted upper demand,
not the lexical Name occurrence. O0 already supplies:

```text
q_e = outEff_orig(U_e) = inv_eff_orig(rho_e)
ce_e = CallEff_orig(e)
kappa_e : TypedOutputCorrespondence_orig(
             U_e,q_e,e.p0; B,X,xi,Delta_e; beta,u,c)
```

Its static root, origin and separate invocation leg are retained. O0's full
invocation root interpretation is taken as established, without repeating
its proof or treating it as a satisfying descriptor.

Define `Reg(beta)` to be the **actual** first source registration derivation
of `d_f,A_f,R_f` in its original declaration scope `sigma_0`. It is not the
pair of labels `(d_f,R_f)`. Define `Route(e)` to be the actual resolved
Name/capture correspondence from this registration to `Delta_e`. It includes
the same imported `A_f,R_f`, `Resolve(e.u_f,d_f)`, and the original scope map;
a direct use has the identity route. Inverting actual Gen-Call-0 and its
source context supplies these static inputs in the stated envelope. No
arbitrary syntax-shaped tuple can discharge them.

Define `SeedExposure(k,e)` to be the retained S1 derivation with all of:

```text
UnannotatedFormal(d_f) at its original binder
SeedOrigin(k,d_f,A_f,R_f,sigma_0)
ProtectedVarAt(k,A_f,scope(e),e.u)
SourceUpperUse(e.u,A_f,U_e,scope(e))
the same registration and Route(e), with e.u_f resolving to d_f
```

The use of `e.u` in the exposure predicates makes the older K-Owner display's
use of `u_f` there explicit as shorthand for its associated upper exposure.
This is a source-stage association from `e`, not an equality `u_f=u`.

For exactly `my apply f = { my step x = f x; step }`, reviewed
[S1](../progress/2026-10-06-directional-joint-source-judgment.md) §3 derives
these seed/exposure inputs: the outer formal is registered before body
generation, actual annotation absence supplies the selected seed, and the
inner Name/capture reuses that formal's still-inferred endpoint. This does
not require solving the generated predicates. S1 §4.2 gives conditional
multi-use composition when each source route/exposure is already certified;
§6 gives whole-origin transport when its generalized-use certificate exists.
This note does not create that missing general supplier, mixed-use role
eligibility, recursive seed, or late-seed replay policy.

Thus the O1 theorem is total on the **certified seeded subinventory**

```text
E_seed = { e in E_D | Reg(e.beta), Route(e), SeedExposure(k,e) supplied
                         for an original k }.
```

Every actual emitted record has adopted O0. Not every such record is asserted
to have a formal seed. A known external Name acquires none merely by lookup.

## 3. Complete slot case at the original source owner

At source registration retain the shared source contract-position carrier:

```text
reg : Reg(beta), originally at sigma_0
-------------------------------------------------- OShared-Register
H_beta := SharedPositions(reg)
```

`SharedPositions` is a static schema carrier over this registered source
contract. Its fields are the original declaration, shared endpoint/root,
annotation occurrence or its actual absence, original declaration scope and
source-origin derivation. Its complete-invocation field is the constructor

```text
s_beta := SharedInvoke(beta) : SharedPositionSchema(H_beta)
```

`SharedInvoke` designates the immediate **complete invocation** position of
this source contract. Its meaning is an address schema: an actual original
Function exposure of this root can supply a typed attachment to its own
complete-invocation output. It contains no local `U_e`, argument endpoint,
solved descriptor, profile row, or universally asserted semantic attachment.
The constructor does not declare that the entire endpoint `A_f` has a
Function solution or even that an unused formal has a typed Function effect
position. It is a source-owned symbolic anchor available when first
registering the source owner. Its slot membership is introduced only when
an actual typed Function exposure supplies the O0 realization below.

The proposed original slot case is:

```text
reg : Reg(beta)                    e : actual Gen-Call-0 at Idx(e)
route : Route(e)                   ce_e,kappa_e : adopted O0 at Idx(e)
------------------------------------------------ OSlot-SharedInvoke
slot_(beta,e) : s_beta in Slots_orig^+(beta)
```

Its formation requires the registered carrier and actual typed exposure,
not the printed spelling of
`f`, `call.effect`, or a numeric allocation. A rename that preserves resolution
preserves this carrier by typed transport. `s_beta` is not `p0`: the latter
is an exposure's source-effect position with its O0 typing and local demand
fiber. A slot and an effect occurrence can share an address projection without
being the same sorted object.

### Retention of every other original case

The superscript `+` names this displayed completion and makes the comparison
boundary visible. Given any independently specified existing slot domain
`S_old(beta)` and its membership/evidence, complete the domain as the tagged
sum

```text
SlotSchema_orig^+(beta) = RetainedSlot(S_old(beta)) + SharedInvoke(beta).
```

The sum is a schema/address universe, not a declaration that every address
has typed membership. `SharedInvoke(beta)` belongs to `Slots_orig^+(beta)`
exactly when OSlot-SharedInvoke has a certified exposure; an unused or
noncallable formal does not obtain that membership from registration alone.
The typed member domain consists of retained members and members introduced
by the displayed slot rule. Thus no eager Function assumption is made.

`RetainedSlot` is an injective inclusion retaining each old slot, membership
derivation, dependencies and all its owner evidence. The new case has exactly
the source formation above. Any other independently defined original cases
remain in the retained summand; they are not reconstructed, normalized,
rejected, or limited to this image. If those cases are recursive inductive
clauses, retain the clauses and their existing interpretations, rather than
replace their premise domain by just this constructor. This sum specifies a
possible completion, not an assertion that a separately fixed original
universe is already a sum or has an additional inhabitant.

Consequently no theorem `Slots_orig(beta)={s_beta}` follows. A non-singleton
old domain stays non-singleton by injectivity. Domains with independently
valid annotation, provider, latent or other source slots retain them. The
singleton emitted Call inventory for the selected source is not the complete
slot domain. Adding this constructor gives no contribution, licensed witness
or admission-domain restriction.

The choice to share this **one constructor case** across demands at the same
root is explicit. It is a natural stable contract-position definition, not
a cardinality law inferred from the number of uses. Whether it agrees with a
separately fixed old slot identity is the comparison question in §8.

## 4. Complete Own-Upper constructor and eliminators

For `e in E_seed`, form the typed attachment

```text
attach_e := UpperInvokeAttachment(
               reg,Route(e),e,ce_e,kappa_e,SeedExposure(k,e))
```

An attachment is the displayed **dependent record** of those already derived
inputs, with the equalities that each field has the indices projected from
the same `e`. It reads no original `Own`, slot membership, complete contribution
or coverage judgment. There is no existential provider or port to select.

The new original owner case is defined completely by

```text
reg : Reg(beta)                    route : Route(e)
seed : SeedExposure(k,e)           e : actual Gen-Call-0 at Idx(e)
ce_e,kappa_e : adopted O0 at precisely Idx(e)
--------------------------------------------------------------- OOwn-Upper
o_e := OwnUpper(attach_e)
Own_orig^+(beta,s_beta,e.u_f,e.p0,o_e;X).
```

The rule concludes **static typed source ownership**. It says this rooted
formal's seeded source upper exposure is attached to its shared invocation
position by the existing typed incidence. It asserts neither that a concrete
event belongs to an effect row nor that a provider, Function, source solution
or full profile is admitted. This interpretation is the original static case
being proposed; those semantic assertions cannot be obtained by eliminating
it. No semantic `SharedContract` predicate appears above this rule.

The dependent owner family also retains every old case by an injective
`RetainedOwner` at its retained slot and old indices. No old witness is
identified with a new proof term merely because endpoints or observations
coincide. No consumer of the retained branch is forced to use Own-Upper.

The constructor's eliminators are exactly:

| Eliminator | Value on `o_e` |
| --- | --- |
| `slot` | `s_beta`, with `slot_(beta,e)` from OSlot-SharedInvoke |
| `declaration`, `sharedRoot`, `sharedEndpoint` | `e.d_f`, `e.R_f`, `e.A_f` from the actual registration |
| `sourceOwnerScope` | `sigma_0`, retaining the registration origin |
| `lexicalUse`, `resolve`, `captureRoute` | `e.u_f`, its actual resolution and `Route(e)` |
| `upper`, `upperDemand`, `exposureScope` | `e.u`, `e.U_e`, `e.Delta_e` |
| `seedOrigin`, `protectedAt` | the original `k`/binder seed and the actual `e.u` exposure derivation |
| `signaturePosition` | O0's `q_e=outEff_orig(U_e)` in the exact demand fiber |
| `sourcePosition`, `typedAttachment` | `e.p0` and exactly `kappa_e` |
| `sourceCall`, `sourceOrigin` | `e.c` and the entire original dependent record |
| `invocationLeg` | `e.ElimOrigin`, including `e.p_out(c)` |
| `jointIndex` | the same original `B,X,xi` and binder tree |

These equations are constructor projections. They do not cast `kappa_e`
itself to a slot or turn an endpoint pair into membership. The introductions
occur in §§3–4 and the projections follow from the dependent record.

**Elimination/inversion law.** If an ownership derivation was introduced by
Own-Upper, inversion returns exactly the inputs above with their original
indices. Conversely any such input record yields the displayed owner.
The retained branch instead inverts to its retained old derivation. This
law is exhaustive for the new case only; it does not say that every valid
original owner arose from a formal seed or an emitted record.

### 4.1 Checking facet of the same original source certificate

Retain `attach_e` and `o_e = OwnUpper(attach_e)` exactly as above. The record
already contains the actual resolved lexical occurrence and the independently
justified checking exposure with its original O0 incidence. Define a second
original static introduction at the same dependent tuple:

```text
reg : Reg(beta)                    route : Route(e)
seed : SeedExposure(k,e)           e : actual Gen-Call-0 at Idx(e)
ce_e,kappa_e : adopted O0 at precisely Idx(e)
------------------------------------------------------ OOwn-Upper-Checking
attach_e := UpperInvokeAttachment(reg,route,e,ce_e,kappa_e,seed)
o_e := OwnUpper(attach_e)
chk_e : Own_orig^+(beta,s_beta,e.u,e.p0,o_e;X).
```

The original OOwn-Upper introduction is retained as
`lex_e : Own_orig^+(beta,s_beta,e.u_f,e.p0,o_e;X)`. Its premises and meaning
are unchanged. Both rules directly consume the same source certificate;
neither consumes an `Own` premise. The evidence term `o_e` is the same in
both judgments, while `lex_e` and `chk_e` are distinct ownership derivations.
The checking introduction is a completed original formation case, not an
eliminator that converts the lexical judgment, a downstream transport, or an
equality cast. Merely projecting `upper(o_e)=e.u` from lexical evidence never
established `Own` at `e.u` under the earlier definition.

For either new facet, the §4 eliminators still return exactly the retained
source inputs. The additional indexed elimination equations are:

```text
indexedOccurrence(lex_e) = e.u_f
indexedOccurrence(chk_e) = e.u
ownerEvidence(lex_e) = ownerEvidence(chk_e) = o_e
slot(lex_e) = slot(chk_e) = s_beta
sourcePosition(lex_e) = sourcePosition(chk_e) = e.p0
jointIndex(lex_e) = jointIndex(chk_e) = (B,X,xi).
```

Lexical inversion retains the actual `Resolve(e.u_f,d_f)` and original
capture route as its indexed source incidence. Checking inversion retains
`ProtectedVarAt(k,A_f,scope(e),e.u)`,
`SourceUpperUse(e.u,A_f,U_e,scope(e))` and `kappa_e` at `beta,e.u,e.c` as
its indexed upper-output incidence; the lexical resolution stays in its
payload. The `indexedOccurrence` operation acts on the ownership derivation,
not just `o_e`, since the same evidence has both facets. Neither rule claims
that these incidences are a complete `TypedOriginalSourceImage` or J0.

**Facet inversion.** A derivation introduced by either displayed rule inverts
to the same complete dependent input record and its chosen occurrence.
Conversely that input record forms both derivations. Proof: case analysis on
OOwn-Upper and OOwn-Upper-Checking, then reduction of their record projections.
For `RetainedOwner`, use the retained old inversion at its unchanged index;
no old case is required to have a paired facet. All original alternatives
and multiple independently justified source records remain distinct. QED.

## 5. O1 theorem, source safety and the exact nested instance

**Theorem O1-static, paired facets.** Under the definitions in §§3–4.1, for every
`e in E_seed` construct

```text
s_beta in Slots_orig^+(beta)
lex_e : Own_orig^+(beta,s_beta,e.u_f,e.p0,o_e;X)
chk_e : Own_orig^+(beta,s_beta,e.u,e.p0,o_e;X),
```

with all eliminators in §§4–4.1, independently of a solution, actual execution,
semantic shared-contract membership, or dynamic receiver activation.

**Proof.** Invert the actual source record to recover its registration and
same-root route. Apply OShared-Register at that original
registration, initially forming only the source-port anchor schema. Use
adopted O0 to obtain `ce_e,kappa_e`; apply OSlot-SharedInvoke with those
typed exposure inputs to introduce its slot membership. Use the independent S1
certificate at the associated checking occurrence `e.u`. Assemble the
dependent attachment, whose equalities use `e`'s actual fields once. Apply
OOwn-Upper and OOwn-Upper-Checking independently to that same attachment.
Their conclusions give both indexed totalities with the same `s_beta,o_e`;
projecting the evidence and derivations gives exactly §§4–4.1. There is no desired
`Own` or `Slots` input, no inference from comparison success, and no new
semantic typing judgment. QED.

**Static owner safety.** The output has one registered source root and one
joint index because those fields occur once in the dependent attachment.
Its lexical use is an actual resolved route to that root, its output path is
typed by O0 at the actual upper demand, and its protection source is the
actual seed-at-exposure. These are checkable eliminations of source proof
terms, not facts reconstructed from identifiers. A mismatched root, swapped
`u_f/u`, arbitrary effect position, invented capture or late seed fails the
dependent input typing. A provider lower `L <: A_f` cannot substitute for
the `A_f <: U_e` source demand. These inputs may coexist even when their
interpreted endpoint values coincide; their tagged source origins differ.

No field targets a provider's existing lower effect. Retained provider
protection is left in its original branch; Own-Upper neither propagates
the formal seed backward nor deletes independent provider evidence.
The internal Handler seed and any later NonHandlerFormal evidence remain
distinct from an actual supplied callable's role/entry. A constructor field
containing a seed is not a concrete handler-removal grant.

For the exact nested source, `reg` is at `sigma_apply`; `Route(e_c)` is the
resolved import of the same outer `f` into `sigma_step`. Form `s_beta` at
the outer registration as a source-port schema. Adopted O0 introduces its
slot membership using the inner exposure. S1 and O0 produce the attachment at the
inner `Delta_c`, with local `A_x,U_c` still there. No local demand variable
is placed in the outer slot. The enclosing Bind and final returned `step`
retain this static body certificate and do not execute `f x` or generate
another owner. The closure may remain forever uninvoked. The established
singleton emitted inventory supplies one canonical attachment/evidence record
and its two static facet derivations for this case, without asserting a singleton original slot
inventory. The checking facet is at the inner `e_c.u`; the lexical facet
is at the inner Name `e_c.u_f`. Neither executes the returned closure.

## 6. Several captures and exposures; no lost evidence

Suppose finitely many independently certified original exposures `e_i`
refer through actual direct/capture routes to the same registered `beta`.
Each retains its own local `Delta_i,U_i,u_i,u_fi,c_i`, seed-at-exposure and
O0 correspondence. Form the carrier once at `reg`, hence the same term
`s_beta=SharedInvoke(beta)` is used in every Own-Upper instance. Both facet
derivations of each `e_i` use that same term and its same `o_i`;
different demands need not be type equal or simultaneously satisfiable.

**Sharing lemma.** Every instance's `slot(o_i)` is `s_beta`, while its
`upper`, `lexicalUse`, `typedAttachment`, seed and local scope are exactly
those of `e_i`. Proof: reduce the slot projection, which reads `beta` only;
reduce the other projections, which read the full attachment. The slot
membership proofs retain their respective exposure realizations; shared
slot identity does not equate `q_i,q_j` or `U_i,U_j`. No field
chooses a second root or per-port `xi`. QED.

The slot identity expresses one shared static contract position. All demands
still constrain that contract through the old conjunction. This construction
does not turn incompatible demands into compatible ones. It does not choose
a Function witness independently for each exposure or prove the role
aggregation/solution-coverage theorem.

The dependent ownership family retains proof alternatives: different original
seed witnesses, capture routes or independently valid old owners stay
different derivations. Reusing exactly the same derivation twice need not
create a new slot or semantic witness. No equality of endpoints, erased
rows or observation projection merges distinct evidence. A joint incidence
consumer must select compatible whole evidence; sharing `s_beta` alone
establishes no compatibility between two contributions or coverage witnesses.

Distinct registered roots have distinct constructor parameters, even when a
solved endpoint substitution equates their denotations. The sharing law is
about source roots and their legal correspondences, not value equality.
Additional old slots at either root remain available; this is not uniqueness
of the completed contract, profile or original ownership relation.

## 7. Whole-index coherence and conservative old reduct

Let `theta` be one legal whole-source map of the adopted O0 scope. It acts
on the entire binder graph, `B,X,xi`, declarations, endpoints, source tags,
registration, capture routes, source demands, seeds and incident evidence,
fixing the imports required by that map. The map must already be certified
for all original premises; the constructor does not authorize a new graft,
hiding step or generalization.

Define its action structurally on the new constructors:

```text
theta(SharedPositions(reg)) = SharedPositions(theta(reg))
theta(SharedInvoke(beta)) = SharedInvoke(theta(beta))
theta(slot_(beta,e)) = slot_(theta(beta),theta(e))
theta(UpperInvokeAttachment(reg,route,e,ce,kappa,seed))
  = UpperInvokeAttachment(theta(reg),theta(route),theta(e),
                          theta(ce),theta(kappa),theta(seed))
theta(OwnUpper(attach_e)) = OwnUpper(theta(attach_e))
theta(lex_e) = OOwn-Upper(theta(attach_e)) = lex_(theta(e),theta(seed))
theta(chk_e) = OOwn-Upper-Checking(theta(attach_e))
             = chk_(theta(e),theta(seed)).
```

**Coherence theorem.** These actions preserve all constructor typings and
commute with every eliminator; in particular

```text
theta(o_e) = o_(theta(e),theta(seed))
theta(slot(o_e)) = slot(theta(o_e))
theta(typedAttachment(o_e)) = kappa_(theta(e))
theta(invocationLeg(o_e)) retains theta(p_out(c)).
```

**Proof.** Legal transport maps `Reg`, `Route` and seed/exposure together.
Adopted O0 gives `theta(ce_e)=ce_(theta(e))` and the same equation for
`kappa`. Thus the structural attachment has exactly the transported whole
index. For the lexical constructor case apply OOwn-Upper at the mapped tuple;
its coordinate is `theta(e.u_f)`. For the checking constructor case apply
OOwn-Upper-Checking at the same mapped tuple; its coordinate is `theta(e.u)`.
Both retain `theta(o_e)`, the same `theta(s_beta)`, root, `p0`, `B,X,xi` and
all scopes. This proves each facet formation, rather than changing an index
on a previously formed judgment. Applying OwnUpper to the mapped attachment
gives the first evidence equation. Each
projection then selects the corresponding transported input, giving every
other equation. Identity and composition follow structurally, and reflection
holds for legal injective renamings on their image. Noninjective substitutions
of endpoint values do not quotient source constructor tags or proof origins.
For retained cases use their existing legal transport, not either new rule.
These are the exhaustive constructor cases of the completion. The facet
equations also commute with `indexedOccurrence` and `ownerEvidence`; source
resolution and seed/O0 incidence map with their own original occurrences.
QED.

At inner generalization of `step`, captured `d_f,A_f,R_f` stay imports. Its
local demand and exposure witnesses remain under their original dependent
binders or move by the one independently justified whole-origin certificate.
The outer slot has no free `U_c,A_x` requiring hoisting. Hiding is not a
per-attachment existential choice, and this theorem supplies no generalized
use certificate when source formation has not constructed it.

**Old reduct.** Keep every old source predicate, strategy, binder and
executable operand unchanged; the new static evidence is a phase-side
derivation. For every supplied old source derivation, construct the carrier
at each relevant registration and the owner records at certified exposures.
Erasure returns exactly that old derivation. This deterministic extension
does not test its satisfiability, so inconsistent generated constraints also
receive the records. Conversely erasing a normalized decorated derivation
returns its old derivation. Old solution and execution claims formulated in
the unchanged old language therefore have the same reduct.

This is not preservation of every formula quantified over the completed
`Slots`/`Own` domains. An old universal consumer may require a new case, and
an old negative assertion may cease to hold after adding a missing case.
Such consumers require actual compatibility/semantic laws, not just erasure.
No solution preservation is claimed for any future profile, permission or
admission rule that uses ownership to add semantic constraints.

## 8. Separately fixed original-family comparison and semantic boundary

For a separately fixed kernel `K_old`, a genuine identification needs typed
maps at the same original fibers, not an assertion that this syntax is old:

```text
j_slot : typed Slot_orig^+(beta) -> typed Slot_old(beta)
j_own  : Own_orig^+(beta,s,v,p0,o;X)
           -> Own_old(beta,j_slot(s),v,p0,j_evidence(o);X)
           for each claimed fiber v, including e.u_f and e.u separately.
```

On the retained branch they must retain each existing old slot/owner and
its exact evidence. On SharedInvoke and each of
OOwn-Upper/OOwn-Upper-Checking they must independently prove
original membership and ownership with the full eliminators, typed
attachments, seed origins and scope/dependency indices preserved. They must
commute with legal whole maps and all original attachment consumers. If
old evidence has several legitimate alternatives, retain them as an
evidence relation; choosing one alternative cannot establish exhaustiveness.
If a quotient identifies the new slot with an old position, prove that its
consumer interpretation preserves every original arm rather than silently
equating the two sorts or merging owner witnesses.

When claiming agreement of complete slot/owner inventories, a converse
representation must additionally cover every old inhabitant and retain its
independent evidence. This draft proves none of those maps for an unknown
independently fixed kernel. The sum construction shows how to retain cases
in a missing-definition completion; it does not supply semantic inclusion
into an already fixed world. In particular the incoming candidate
`CallSlot_orig(beta,p0)` and `CallUpperOwner_orig(...)` remain separate terms.
Matching their root/position labels with `SharedInvoke(beta)` and `o_e` proves
no term equation, kernel identification or checking-fiber embedding. The
comparison obligations apply to either facet at its actual coordinate.

The `SharedContract(d_f,R_f,sigma_apply)` premise in round-2 K-Owner deserves
separate treatment. If it abbreviates **static shared registration**, the
carrier and origin projections give precisely that formation fact. If it
means an independently interpreted whole semantic contract, source
registration, S1 and adopted O0 do not prove its validity. Keep that fact as
an independent guard `h_sc` in that legacy specialization. An empty solution
set does not invalidate static registration, but cannot supply a satisfying
descriptor/member witness. The new rule must not redefine `h_sc` as a
registration tag to claim its elimination.

Likewise the dynamic execution `Owner(i,u,K)` of
[typed source owner realization](../design/2026-10-02-typed-source-owner-realization.md)
§§2–4 is a different sorted object. Its `u` is a dynamic execution occurrence;
the present `e.u` is an upper-checking occurrence. That theorem assumes
decorated profiles/maps, actual entry, receipts and live configurations.
Own-Upper allocates no active owner, rewrites no original receipt, creates
no boundary, and licenses no handler removal or raw-resumption re-entry.
It only supplies one static source provenance input where the theorem
already expects precisely that input. Its live-incidence theorem remains.

Option 2 and independent open-world admission retain their domains and all
independently licensed witnesses, including unreached contexts and production
extras without individual source-execution witnesses. No slot/owner clause
here constrains them. A safety or completeness theorem that quantifies over
their actual semantics still needs C0/C1/J0, attachment, licensing and
complete coverage laws. Static ownership does not make a relation an
original contribution and does not put a witness into `I_orig(X)`.

## 9. Exact existing consumer substitutions

Suppose a consumer proof has an O1 parameter at **these same dependent
indices**. Choose its actual coordinate `v`: use `lex_e` when `v=e.u_f` or `chk_e`
when `v=e.u`, together with `slot_(beta,e)` and the same `o_e`.
Its other original inputs retain their own meanings and scope. Substitution
is ordinary dependent proof application under the displayed definition;
identification with a separately fixed kernel instead needs §8 first.

| Consumer / exact locator | Supplied by this case | Exact residual |
| --- | --- | --- |
| [Round-2](../progress/2026-10-07-successor-original-kernel-construction-round2.md) §3.2 K-Owner | Actual `s,o`, typed `p0` attachment, lexical resolution/capture, upper occurrence and seed, at `beta` | For its guarded legacy use retain independently semantic SharedContract if that is its intended reading; other original cases and any stronger semantic owner realization remain. |
| Round-2 §3.2 K-Incidence | Its coordinate-parametric `Own_orig(beta,s,v,p0,o;X)` input, using the lexical or checking introduction at that same `v` | Independently supplied `TypedOriginalSourceImage(E,v,rho_U;X)`, original Contrib/Emb, source-stage/view map, joint incidence and coverage law at that exact `v`; the generic sequent does not force checking `u`. |
| Round-2 Own-Call-Lift display near §5 | The lexical `lex_e` branch at its explicit `u_f`, including its slot introduction | K-Leaf/K-Image for the actual original Name/argument/provider and full invocation; K-Incidence with whole-family coverage; licensing. |
| [Round-4](../progress/2026-10-09-original-call-fiber-construction-round4.md) O1 row and conditional completion | Its exact lexical `Own(...,e.u_f,...)` via `lex_e` at an actual emitted seeded exposure, using established O0 | C0 independently admitted full-inlet typing, C1 original preimage/Emb, J0 compatible whole incidence, one original witness before arbitrary observation choice. |
| [Source-introduction contract](../design/2026-10-07-original-call-source-introduction-contract.md) §§3–6 | Its existential checking O1 port `exists s,o. s in Slots_orig(beta) and Own_orig(beta,s,e.u,p0,o;X)` via `chk_e`, under this selected completed static definition | No identification with its unadopted §3.1 CallSlot/CallUpperOwner kernel. Other source generation, C0/C1/J0 at checking `e.u`, complete original witness retention, semantic SharedContract, profiles, attachment, licensing, admission and production conformance remain. |
| Typed source owner realization §§2–4 | Static provenance only where an existing decoration has that exact port | Executed receipt/boundary entry, live dynamic owner/receiver, typed transport and operational realization; no `Owner(i,u,K)` is inferred. |

In the guarded K-Owner specialization, supplying independent `h_sc` and its
remaining original hypotheses gives the old displayed sequent by O1-static.
The proof does not use `h_sc` to build the static record; it retains it for
the guarded original consumer. This is a completed constructor proof plus
an exact legacy specialization, not a proof of semantic shared-contract
validity from source labels.

For K-Incidence, keep `Own`, `TypedOriginalSourceImage` and `Inc` at one
coordinate throughout. Supplying the lexical facet and an image at `e.u`
is ill-typed, even though `o_e` retains that upper occurrence. Conversely
checking ownership supplies no image, contribution or joint witness by itself.
The incoming statement that checking `u` is required by generic K-Incidence
is read only as its own selected port; the generic sequent requires sameness
of coordinates, not that particular choice. Its §3.1 canonical constructor
remains unadopted and is not silently replaced by a term equality.

Combining the lexical facet with compatible C1 and J0 can then yield round-4's existing
uniform-witness conclusion. The present output alone does not establish
`exists a in I_orig(X)` or `forall z in F_C(X;xi). Cover_orig(a,z;X)`.
Nor does it prove complete-contract principality, source adequacy or
production cutover. No canonical DAG promotion is made here.

## 10. Actual alternatives and review questions

The inspected original static interpretation is missing a precise definition;
its required direction is specified. The construction completes that static
case with a stable shared contract-position carrier and source-derived
attachments. Semantic membership is a different genuine obligation, retained
in §8 rather than encoded in the slot tag.

Two actual semantic alternatives are still outside this proof. A separately
fixed original slot family may identify the shared invocation position with
an existing slot, requiring the typed comparison/quotient law in §8. A
stronger original owner interpretation may include semantic shared-contract
validity, requiring its independent guard/realization. Neither possibility
is an established second Authority-consistent semantics or a countermodel.
They are precise compatibility questions. No arbitrary per-use slot count,
dynamic-only owner or provider back-protection is an admissible shortcut.

Fresh delta review should check the checking formation, paired elimination,
whole-map constructor cases and corrected consumer alignment. The clean
lexical constructor proof remains unchanged in meaning. Review should check
that the paired completion retains every old case and alternative, and verify that no consumer is credited with semantic membership
or full joint coverage. If a governing original judgment explicitly makes
Own itself semantic validity, the static conclusion must remain a retained
provenance certificate until that judgment's independent realization law is
proved; the constructor and coherence proofs remain available in that scope.

## 11. Verification and frozen dependencies

Method: documentary source inversion, dependent constructor formation,
elimination, finite source composition and legal-map induction. Budget:
one bounded prose proof, no executable model, Oracle, build, test, children
or Git mutation. No semantic counterexample needs a scratch calculation.
Verification: focused source/consumer reads; final exact dependency hashes,
relative-link existence and note-local whitespace check. These checks verify
the artifact's inputs and scope, not independent mathematical correctness.

The following table is the historical original-proof freeze at `370bb463`.
It is not asserted to equal the incoming repair baseline. The worker does not
certify Git object equality; the primary rechecks that at integration.
Historical SHA-256 hashes are:

```text
ab9a26a0d1115a18e563b0119b919632b385407bea5107d1cecefaed9b07e46e AGENTS.md
925f1c5cd4ca6ce7306b1375eb9c1a699a83d3491efba21b50271e176eee5ba5 rules/design-authority.md
1ff144d376052d2e01d2e97ba3290e6942f126765067fbf11dfeffc06f89b442 rules/compiler-engineering.md
5788a2ef1c2181b43a9f82116fe6c4cfd32419dc7098fb84fa7c0d46a0a88ca6 rules/research-lab.md
e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e rules/git-concurrency.md
db2eb807a87720e83ad7aa7d5c6c018a024a6d9eb908cad3caf0e386d5ec6117 tasks/current.md
4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1 notes/design/2026-10-05-inferred-function-call-views.md
6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7 notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md
5cbd8110736ee4d43e0c65460fa9ecf700228bfdbe9fbaa7642ea0302d86f1aa notes/design/2026-10-02-typed-source-owner-realization.md
4940e031b83d3d0315f17beb51ba2e952ec64ae7d57d9ae0d086024c7305ca9f notes/design/2026-10-07-original-call-formation-definition.md
71202a2ffeb5a4dcf62bbd7731fb20d923ea5626b67647fb1815302b6659e3d8 notes/theory/2026-10-07-adopted-call-formation-o0.md
daa802bcf61695845718f669c1d35bfd101d2b61d49607ea8c8de82dee662910 notes/progress/2026-10-07-successor-original-kernel-construction-round2.md
2d55271aaaaa5d4af7b912116fa3299431bc10cc16926118767182695b2c4977 notes/progress/2026-10-09-original-call-fiber-construction-round4.md
4856d0848d50cb07f2d10ef048970d2450a1328805a2d51b57da3b9ca7e1b6c8 notes/progress/2026-10-09-original-kowner-underdetermination-round1.md
b35a0d51f23d73c8c2fe84b616dfb839d173e7f0d5823246507194efd800d186 notes/design/2026-10-07-original-call-source-introduction-contract.md
6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073 notes/progress/2026-10-06-source-call-generation-construction.md
fc459dfac03693f426dea575585a0d20d7a075f8c7ac27be9fd2e67a150466c1 notes/progress/2026-10-06-directional-joint-source-judgment.md
```

### Incoming repair dependency delta

The original independently reviewed proof freeze was
`c51ad734e6f90b4553495eec7beb6787e71482a4451cfb9cae6ea9fceac49ed0`.
The incoming `465c2af` baseline changes the source-introduction contract
semantically relative to the historical table: its O1/J0 ports use checking
`u`, it presents the unadopted `CallSlot_orig(beta,p0)` / CallUpperOwner
formation, and it says that checking coordinate is required by K-Incidence.
The accepted repair recognizes that generic K-Incidence instead requires
same-coordinate `Own`/source image/`Inc`. The historical lexical theorem
remains sound; its former source-contract substitution row needed this
explicit checking introduction. This is not a cosmetic dependency change.

Focused recheck against the historical table found these changed hashes:

```text
1d41f8f5c6626dfb247dfb79ad149ab775d09f9d86305f747b3114406c910aea tasks/current.md
434440c9e776853a9344f88f796a38e599010af58771cf6e6acf207bc8705271 notes/design/2026-10-07-original-call-source-introduction-contract.md
```

`tasks/current.md` is primary-owned coordination, not a new mathematical
premise. Every other historical dependency hash in the table above was
unchanged at this repair recheck. The primary-owned static owner definition,
added after the original proof baseline and read as the stable lexical
constructor source, had this repair-input hash:

```text
b2265b29a56ee584b40b3c921c4c8aaeb7815d70afc830184dfd1998d4529cc1 notes/design/2026-10-07-original-call-owner-definition.md
```

Its subsequent matching checking-facet integration is a required definition
sync, not an input silently assumed to exist already. The paired theorem is
proved here under §§3–4.1; the primary must freeze the matching definition
and consumer interpretation with it for fresh delta review. This producer
writes no dependency file, performs no Git operation and reads no active C1
lane. No complete all-source seed eligibility, source-image supplier, semantic
Call law, original contribution introduction, joint coverage, licensing or
admission theorem is added.

## 12. Commit packet

- Leased changed path: `notes/theory/2026-10-07-call-owner-construction-proof.md` only.
- Original proof baseline: `370bb4634d0b5eb413c01bb984b995f74a743f59`; repair input baseline: `465c2af15dfb8ae5f603fea4dc4533e99f9b0c5a`.
- Claim/review state: reviewed lexical constructor proof retained; complete checking-facet formation/elimination/coherence and paired consumer repair frozen for fresh independent review and primary-owned definition sync. No new Authority status, old/candidate-kernel comparison, semantic coverage, production conformance or DAG closure claimed.
- Dependency changes: none written by worker. The incoming source-contract semantic delta changes its O1/J0 coordinate and adds an unadopted candidate kernel; §11 records it explicitly. Frozen artifact hash is reported separately to avoid a self-referential digest.
- Verification: the focused documentary and mechanical checks in §11; zero executable probes, builds and tests.
- Proposed commit message: `research: form paired original Call owner facets from one certificate`.
- Deferred primary-owned deltas: review/adoption disposition and exact Authority scope; current-task and theory/navigation integration; any proof-status promotion only after its original scope is adjudicated. No production or question-board mutation proposed.

Producer writes stop after the final freeze report.
