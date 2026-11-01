# R227: candidate original Function and callback-profile equations

Date: 2026-11-02
Status: Candidate source-definition construction; not adopted semantics, a Lean theorem, or original-parent closure
Baseline: `eeb5cca724cbc4a9ebfb6d987a3da8fc1928cc89`
Scope: the declared ordinary Value-formal `f:int -> int` in R226's worked App; symbolic extensions retain their exact residual obligations
Production/API authority: none

## 1. Correct source inputs

The construction below outputs concrete syntax-directed coordinates, a
role/entry-indexed intensional Function contract, a candidate original root
Call profile, and one source-use substitution. The proposed annotation/root
Call introduction law is explicit in §5. Its adequacy as an original source
constructor remains unproved. This is more than an inventory, but it does not
establish E1/E4 or remove an original App premise.

Use the original source component, not annotation syntax alone:

```yu
my apply (f:int -> int) = f 1
my answer = apply (\x -> x)
```

The actual retained source input is the declaration/formal/annotation tree,
its lexical scope and shared formal root, together with the original source
use `f 1`. These are the same source shapes analyzed in the reviewed profile
construction and R226. No execution or present acceptance is asserted here.

This distinction is required by the explicitly pinned older results.
`2026-10-15-function-callback-profile-construction.md` §§1/5 and
`2026-10-15-callback-profile-applicability.md` §§2–3 already withdrew
annotation-only complete-profile construction. The selected directional rule
needs original upper-use/protected-variable evidence, and B requires delivery
before the **receiving literal's** body, not before inspecting the callee's
own source component. Those corrections remain binding. Missing a derivation
does not establish two permitted semantics or require another semantic vote.

The fixed meanings reused here are callback delivery B §§2–3/§2.1, joint
Function compatibility boundary §8, typed core §§6/9's source roles and
complete invocation, annotation integration §§1–1.2's concrete polarity policy,
the receiver-relative default, and directional protection §§2–6. Draft
packages are used only for those selected meanings and their reviewed
conditional results; their full unresolved calculus is not adopted.

## 2. Source coordinates and recursive value fields

Let `d,f,a,S,R_f` be the original declaration, formal, annotation occurrence,
annotation binding scope, and source shared formal root. They come from the
actual source registration. Let `pi` be a structural path in that retained
annotation. Define source coordinate keys, before solving:

```text
named(S,z)                     one original named annotation binder
hole(S,sourcePosition)         one original inference hole
omit(d,f,a,pi,AE)              original omitted argument-effect coordinate
omit(d,f,a,pi,RE)              original omitted result-effect coordinate
```

These are coordinate names, not dynamic boundary IDs. Two occurrences of
`named(S,z)` name one variable. Different omitted ports name different initial
coordinates; later ordinary constraints may identify their images. Native
constructor allocation and source-coordinate identity are separate claims.

**C1 — recursive value construction.** The primitive cases preserve the
declared primitive; a named variable/hole retains the keys above. Product and
other already supported explicit structural nodes retain their original
ordered child references. At a Function node, construct its argument/result
value fields recursively with signs `-s` and `s` respectively. At root formal
position `s=-`, the two effect-coordinate occurrences have signs

```text
AE(pi): +        RE(pi): -.
```

Function input reverses the offered/supplied side; complete invocation/result
preserves it. This comes from the primitive interaction directions in typed
core §9 and composed annotation polarity. It is not an independent port
subtyping algorithm. Reuse the reviewed finite coordinate construction: every
explicit Function node contributes AE/RE records with original row operands,
paths, scoped symbolic references and omitted-coordinate keys. Stop traversal
at symbolic value leaves. A later Function assignment does not fabricate an
original annotation path or protect every descendant.

**C2 — row-coordinate construction.** For each actual argument/result row:

```text
Row(None, key)          = OpenCoordinate(key)
Row(Some(C; z1,...,zn)) = WrittenRow(originalRowPosition,
                                    resolved C, named(S,z1),...,named(S,zn))
```

Keep these as source row descriptors and their joint constraints. `C` retains
resolved operation families and type arguments, including scoped rigid and
dependent binders. No descriptor is replaced by its set of currently observed
effects. A negative concrete descriptor contributes local subtraction
permission; a positive one contributes allowance. Neither contributes actual
inflow by declaration. Symbolic connections remain, and omitted rows are
open, not empty. Mixed rows retain the approved polarity-sensitive joint
meaning; this notation does not silently define them as independent unions.

For the anchor `f:int -> int`, C1/C2 produce exactly

```text
A_arg = Int, A_ret = Int,
e_A = omit(d,f,a,root,AE), e_R = omit(d,f,a,root,RE),
row_A = OpenCoordinate(e_A), row_R = OpenCoordinate(e_R).
```

There is no written concrete allowance or permission in this annotation.
There are still two original effect coordinates. In particular,
`Result(Value(Int)) = Comp(empty,Int)` for a synthesized pure body does not
replace a declared Function annotation's omitted row with `empty`.

## 3. Entry, role and the full intensional contract

**C3 — parameter interfaces.** At the outer formal `f`, the annotation's
outer computation row is absent, so its entry is `Value(F_f)`. For a Function
annotation's own argument `A`, use the original source parameter rule:

```text
no explicit outer computation annotation on A : Entry(A) = Value(A_value)
explicit outer computation annotation [E] A   : Entry(A) = Computation(E,A_value)
```

For the anchor, the declared callback's parameter entry is `Value(Int)`.
Its AE coordinate still describes the whole incoming computation carrier;
Value entry does not make that carrier pure or terminating. B's actual literal
parameter `x` independently gets Value entry from its own syntax.

**C4 — receiver view role.** The known Function-valued ordinary callback
formal supplies the Handler-capable expected boundary for a literal checked
there, by selected B. Write `RequestedRole(F_f)=Handler(beta)` for that
expected view. This is not an assertion that every actual provider already
has Handler introduction. Existing Pure values retain their own actual role
and entry and need the separate concrete comparison. Nor does `apply` become
a Handler merely because its formal has a callback view.

**C5 — source invocation skeleton.** Introduce a distinct source complete-call
position `p_call=(originalFunctionOccurrence,CompleteCall)`. It is not the AE
or RE source coordinate. At Value entry, the source execution equation is

```text
Invoke(U,D,C) =
  establish the same actual receiver and typed receipt in C;
  Force(D) >>= (v,C1 => typedRebind(v,C1);
                         execute the same U body and designated result consumer)
```

At Computation entry bind the same carrier and use the body's actual consumers
instead. For requests during Force, bind retains the same request/response,
current resumed state and pending rebind/body/result suffix. Do not replace
this by a union of argument and body support. A pure divergent carrier is
admitted whenever the independent argument contract admits it; it can prevent
the body from being reached despite empty request support.

The source upper use `f 1` constructs a complete symbolic Function demand
on `R_f`, before success of that demand is known. Its whole argument is the
inert source code for the literal `1`; its output value/effect coordinates
and its executing complete-call position `p_u` are from that original App.
The static signature slot `p_call` and executing position `p_u` remain
different identities. C9 proposes their original typed projection; their
equal type or family does not identify them. This supplies a concrete source
complete-call exposure for the declared root. No `OmittedFormal` seed is
manufactured for the explicitly annotated `f`.

**C6 — proposed Function formation equation.** Form the descriptor expression

```text
F_f = FunContract(
        original=(d,f,a,S,R_f), requestedRole=Handler(beta),
        entry=Value(Int), argumentValue=Int, resultValue=Int,
        wholeArgumentRow=row_A, completeCallRow=row_R,
        callPosition=p_call, profile=Gamma_beta,
        jointSourceConstraints=K, dependentIncidences=D).
```

`FunContract` is mathematical notation for the following intensional contract,
not a new runtime object, compiler API or assumed admission certificate.
Evaluate every field under one `xi=(nu,K,D)` and the original source event.
Its checked challenges are those of the independently typed compatible
punctured source context, with the actual registered callable/whole-carrier
holes, same incidences and independently formed carrier contract. Challenge
formation does not assume that an actual provider accepts the challenge or
that its result is safe.

Its observation clause is about the entire C5 invocation: every complete or
pending observation and admitted continuation/future development must satisfy
the declared Int result contract when a result is returned, the original
complete-call row/view constraints at their typed observation positions, and
the joint hard envelope. It retains request payload/response dependencies,
raw suffixes, current state and result consumers; it is not a predicate on
printed support alone. This describes only the invocation component of
membership. C6 preserves the unchanged original value membership: its
operator is `OriginalSourceInterpretation.PhiV` at the original family/fixed
point, with the original `FunctionAt` function branch. It does not replace
membership by an invocation-only universal implication. The pinned definitions
are (`OriginalSourceInterpretation.lean:420–438`):

```lean
def FunctionAt (inputs : Inputs s) (Z : Family s) (row : ValueRow s) : Prop :=
  (∃ provider, inputs.actual row.value row.root provider) ∧
  ∀ provider, inputs.actual row.value row.root provider →
    (inputs.functionGuards row provider).Valid ∧
    (inputs.capturedFields row provider).Holds Z ∧
    ∀ d : Challenge row, CheckedDomain inputs d →
      ActualAdm inputs provider d ∧
        ∀ observation, inputs.execute provider d.input observation →
          ObservationMem inputs Z d observation

def PhiV (inputs : Inputs s) (Z : Family s) (row : ValueRow s) : Prop :=
  (match inputs.valueForm row.descriptor with
    | .ground => inputs.ground row
    | .fixedExternal => inputs.fixedExternal row
    | .structural => inputs.structuralGuard row ∧ (inputs.structuralFields row).Holds Z
    | .function => FunctionAt inputs Z row) ∧
  ∀ later, inputs.compatible row.event later → Z (.value (row.atEvent later))
```

Thus the original Function formation classification must select the function
branch, actual-provider evidence must exist, and **every** actual provider must
satisfy the immediate FunctionGuards and captured-field membership as well as
the whole invocation clause. PhiV additionally retains value membership at
every independently compatible later event with that event's live state.
None is assumed merely to restrict the candidate's domain. In particular,
absence of an actual provider cannot make C6 membership true vacuously.

These equations reuse the selected contextual membership meaning. They do not
provide a constructor for the original independent context-domain, carrier
admission or observation relations. Those original relations remain fixed;
the equations do not define source typing to mean safety or make Q success
an admission premise. Thus C6 is an actual candidate descriptor/denotation
expression, not an established concrete original instance.

The present Lean boundary is concrete: `OriginalSourceInterpretation.Sorts`
leaves Descriptor/Interface as abstract types; `FunctionGuards.profile` is a
proposition field; the original generator's `Kernel.atom` interprets formation
atoms. No constructor in those declarations turns C1–C9 into an element of a
fixed original Descriptor with a proved formation clause. The candidate
equations specify what that source interpretation must construct, rather than
assuming those proposition fields or changing their meaning in place.

The candidate `completeCallRow=row_R` reading must preserve C5's *complete*
image. It cannot read RE as only the closure body's immediate effect or equate
it to AE. Source-rule adequacy of this reading is part of E1/E4; native four
children do not prove it. This is the explicit field law for review, not an
unmentioned assumed `LocalLaw`.

## 4. Original static template and the single substitution

**C7 — original template identity.** Use the already existing logical index

```text
beta = (original formal f, original shared contract root R_f)
```

with `d,a,S` retained as its source-owner/occurrence qualifiers. This is the
index in the selected directional source treatment. It names the original
callback slot, not an actual receiving activation `b`. Different uses retain
this original template with their distinct use identity and substitution.

**C8 — one source-use map.** Let `Q` be exactly the coordinates quantified by
the original generalization rule; let `NG` retain outer/non-generic coordinates,
rigid binders and all required shared dependencies. Do not decide `Q` from
annotation spelling. For source use `u`, define one capture-avoiding map

```text
rho_u(z) = fresh_u(z)   if z is an original quantified coordinate in Q
rho_u(z) = z           otherwise, in particular for non-generic/outer coordinates.
```

Apply this one map uniformly to value/effect fields, written row arguments,
K/D references, profile endpoint/dependency references and original source
constraint/exposure families. Original declaration/profile path labels remain
labels; rigid/existential binders are renamed only within their original
scopes. A dependency incidence still points to its same predicate under that
one substitution. This is one joint graph, not a product of marginal choices.

For an anchor extension `f:'a -> 'a` with another formal `x:'a`, the three
occurrences of `named(S,'a)` all map to one `alpha_u`. If `'a` is non-generic,
that image is the original outer coordinate; a use does not freshen it. AE/RE
omission coordinates use their original generalization decisions individually.
Another use can have another generic image while retaining the same outer
coordinate. No final solver answer is consulted; ordinary constraints later
relate these unknowns. The concrete `Int` anchor needs no named value-variable
image, but its omitted effect coordinates remain symbolic.

E3 must prove this abstract use map agrees with original generalization and
early checking; its later correspondence to the existing single FreshUse
row/term/scope/context maps is separate. The completed native route is never
an input to initial checking. Re-elaborating the annotation with a second
fresh map would violate C8.

## 5. Candidate profile equations and their source justification

The profile must have source producers. It is not obtained by calling C6's
native representation a profile. For the displayed first-order anchor, propose
the following **C9 — Ann-Call introduction rule**:

```text
original ordinary Value formal (d,f,a,S,R_f)
original annotation at a has root Function(Int,Int)
original source f 1 exposes R_f at its complete Call position p_u
---------------------------------------------------------------- Ann-Call
beta=(f,R_f)
Slots(beta) = {p_call}
ProtectSchema(beta,p_call)
PermitSchema(beta,p_call) = empty concrete permission
original typed callee-use projection: p_call -> p_u
```

These premises are actual declaration and original source-construction data,
not a supplied `Applicable`, profile, solved effect shape or successful Q.
The two omitted row coordinates remain attached to the contract separately.
The static slot is the signature's original complete-call position; multiple
actual source/execution uses can witness that same slot. Inherited provider
profiles remain separate source-tagged packets and are not erased by this
new template's local slot inventory.

The justification has three concrete parts. The explicit Function constructor
offers a callable with a complete J_call interaction (typed core §9); the
actual `f 1` source App supplies its direct whole-carrier/complete-call
exposure. Receiving the callback's associated effects has the selected
receiver-relative protection default; the absent concrete annotation supplies
no local capture grant. Both argument/result value leaves are Int, so this
signature contains no latent returned/argument Function or computation-data
position. AE is still a carrier coordinate, and events from its designated
force are seen through their genuine complete-call Observe paths; AE is not
silently identified with the new slot.

**Exact proof boundary:** these facts motivate C9, but the original source
formal-to-complete-call profile introduction/observation equation has not been
proved in the existing formalization. In particular, "all associated effects"
must be connected by the original typed receipt/Observe correspondence; the
phrase cannot manufacture such a path. C9 is the candidate original source
equation for that gap. It is not asserted as an independently established
complete-profile theorem, even for the anchor. A proof must show that the
rule gives precisely the original root interface and applicable position,
rather than treating source App or the negative type's existence as that proof.

For a root result row containing explicit concrete families `C`, the candidate
specialization keeps protection at this same original slot and sets its local
permission to the exact negative-position concrete contract `C` under nu,
including family-argument compatibility. This does not cap inflow at `C`, seed
`C` into inflow, handle anything by itself, or permit a handler at another
receiver. Its concrete policy is already selected; profile applicability and
actual receipt remain the same explicit construction obligation.

Higher-order/symbolic cases do not extend C9 by painting eventual type shapes.
Reuse the actual source-directed equations:

```text
ProtectedVarAt(k,v,S,u) and original SourceUpperUse(u,v,U,S)
  => NewProtection(k,beta,u,S,outEff(U)).

ProfileAtOriginalTypedPath(p,beta) and actual typed correspondence M(p,p')
  => the same profile/dependency packet at p', preserving source tags and K,D.
```

The first is the already selected and locally derived Dir-Protect rule;
it has one output-effect conclusion and no reverse rule for provider lowers.
The second is the existing typed-flow transport, which preserves profiles
rather than inventing them. Symbolic leaves stop C1's syntax traversal. Any
later exposure must have its own source-derived directional premise, genuine
typed profile transport, or justified non-applicability of that introduction,
while preserving inherited evidence. General classification/completeness is
still open. A whole-binder explicit annotation is not an OmittedFormal seed.

## 6. Delivery to the R226 App and remaining equations

For `s = apply (\x -> x)`, the callee Name identifies the exact `apply`
declaration/use and first formal `f`. C1–C9 generate the candidate original
formal contract, original root template/profile and their coherent use image.
E3 must establish the same source-use substitution before checking `s`'s
argument. E5 must implement the following selected order as a source-preserving
operation:

```text
obtain candidate (rho_u F_f, beta, rho_u Gamma_beta) from the original source
deliver that expected boundary to the literal
select Handler receiver role from that boundary
select x's own Value entry from its syntax
generate x/body/result constraints and the independent F_lit
check the one completed-interface inequality F_lit <: rho_u F_f
```

No expected endpoint is assigned to `x` or to the literal result. Unknown
callees and annotation/callback overlap stay open without adding a rejection
or mandatory annotation rule. The proposal is a bounded construction case,
not a replacement for any whole-language parent quantifier.

The callback formal is not the entire App descriptor. Preserve all original
App consumers under its same viewLogic witness and source assignment:

| Original premise | Contribution and exact remaining obligation |
|---|---|
| `descriptorFormation` | E6 must form the complete original App Function demand and join its formal to this exact acquired declaration/use; C6/C9 alone do not form that whole descriptor. |
| `wholeArgumentCompatibility` | E7 must derive complete inert-carrier formation/admission; the literal's final interface inequality contributes its returned-value boundary only. |
| `completeCallCertificate` | E8 must establish the same actual provider's complete call and receipt/world, with Force/rebind/body/result suffix intact. |
| `sourceCallIncidence` | E6 must join the original `(s,context,callee.site,argument.site)` owner to this same declared formal/use; source IDs alone do not prove a receipt. |
| `callableImage` | E8 must establish all complete/pending observations of that actual invocation, keeping force and body contributions and current-state continuations. |
| `callee.returnedValue -> s.descriptor` | E9 must prove the full original callee-to-descriptor value check, connecting B's final query within that same derivation. |
| `s.callableImage -> s.synthesis` | E9 must establish the original computation/effect/readout result check. |

E2 remains native representation/capture/use correspondence. The reviewed
same-source forward zip already provides its bounded structural ingredient;
do not require a new persisted per-coordinate map merely because a temporary
table is dropped. It does not supply C9's semantic profile law or E5 delivery.
No native graph is a premise of C1–C9's abstract source equations.

All rows share nu,K,D and the original scope, source witness, provider,
carrier, receipt/world and incidence. Computation entry remains distinct.
No independent port inequalities, composed concrete successes, row-wide grant
or unconditional argument/body effect union is introduced.

## 7. Observable-rule and approval boundary

C9 and C6's complete-call row interpretation are the concrete candidate rules
returned for review. They are not silently adopted. Their intended observable
requirements are fixed: associated callback effects remain protected inside
the receiving boundary unless the exact original concrete annotation permits
local handling; annotation permission adds no inflow; complete invocation
includes designated argument force and body/result consumers; forwarding
outside the receiver leaves the effect and independent protections intact.

The affected accepted judgments include the selected annotated relay
`cb:() -> [signal]int` handling signal while retaining additional write,
the unannotated relay forwarding signal, and ordinary B introduction of an
unannotated literal in a known callback slot. A source rule that applies
permission globally, caps input support, protects an existing provider lower
backwards, or drops Force(D) observations would change those requirements and
needs rejection, not local adoption.

No two complete authority-conforming alternatives have been established here.
The missing adequacy proof is therefore not a claim of semantic
underdetermination. No new approval is needed to reuse the already selected
default, polarity, complete Call and B order. Before C9 or C6 is installed as
a new governing source definition, the primary must adjudicate whether its
exact applicability/observation projection is derived from those original
contracts. If a genuinely new observable projection is required, present that
exact rule and affected judgments for user approval through the existing
authority process. This lane grants neither adoption nor implementation.

The mathematical result here is a **candidate equation set with a local
source justification and explicit adequacy boundary**. No theorem or parent
premise was proved. InferenceSoundness, SourceScopedCoverage, PrincipalCoverage
and InferenceTermination remain open; parent delta **0**, roots **0/4**,
packages **0/5**. The next useful proof/design target is C9's original
formal-to-complete-call introduction/Observe equation on this source component,
not another assumed-profile transport or native reconstruction exercise.
