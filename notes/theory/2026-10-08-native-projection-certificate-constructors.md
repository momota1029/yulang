# Native witness constructors and exact projection certificate expansion

Date: 2026-10-08
Status: independently reviewed native witness-semantics completion and algebraic proof
Scope: immutable projection entry/rebind/read/pure-return/invocation certificates
Baseline: `4b5215320587e94acf286ff49267a00515e8812e`
Reviewed phase dependency: `af8b6ed` / `30842d31f1b40e39b8a5b9fb271adcf99934a048`
Branch: `research/simple-sub-intrusion`
Exclusive write lease: this file only; frozen on submission
Foreign witness normalization, production routing and public-export closure: none
Review: independent mathematical and specification reviews passed without a
blocking, major or minor finding; [integration record](../progress/2026-10-08-projection-public-export-review.md).

## 1. Result and precise correction

A Name/rebind/Return proof selected by a producer is not equal to every legal
source proof. For example, source checking certificates `Identity(A)` and
`Compose(Identity(A),Identity(A))` can prove the same decorated-value inclusion
while a client distinguishes their tags. This note never identifies those
certificates or replaces one by the other.

The missing native witness semantics is completed instead **at source owning
rules before Build or Generalize**. Ordinary local certificate constructors
are independently typed relations on V/W/T/Car evidence, registered slots,
actual current events and original IF actions. They have no source definition,
Build, Generalize or whole-source predicate in their interpretation. The native
source rules select these same constructors and preserve every original
ViewLogic/EventProof/checking witness at its original scope.

The resulting source clauses for `id` expand into a finite ordinary certificate
interface. Only forced **runtime value/provider aliases** are substituted.
Every world, certificate, local checking derivation, intermediate evidence,
choice and auxiliary proof witness is retained. **Theorem CE** proves equality
of the expanded clauses and that ordinary interface on the same full retained
tuple; its F/G maps are identity on all proof fields and client W. When hidden
runtime aliases are removed, their inverse is their displayed total assignment,
not an evidence normalization map.

This is a new native definition and its algebraic consequence. It is not
equivalence with an unknown previously fixed witness grammar. Existing semantic
membership, raw source operations and local checking laws remain the governing
inputs; the new definition supplies their missing witness constructors only.

## 2. Authority and independent objects

Reused sources:

- [Contextual Function membership](../design/2026-10-08-contextual-function-membership-definition.md)
  §§2–3 and [input realization](2026-10-08-call-semantic-input-realization.md)
  §§2–4: original V/W/T/Car evidence, independent compatible histories,
  same-provider realization, immutable binding projection and hereditary
  restriction, pure Return and all prefixes.
- [Complete closure definition](../design/2026-10-08-captured-closure-constructor-definition.md)
  §§2–3: actual Strict receipt/Force/rebind/Bind/return and current-world
  invocation occurrence actions.
- [Source Generalize proof](2026-10-08-source-generalize-definition-and-proof.md)
  §§3.1–3.4,4–5 and selected [definition](../design/2026-10-08-source-generalize-definition.md):
  independent source constructor/checking rules, retained original proof
  choices, typed provenance, Shared/ViewLogic/EventField/EventProof scopes,
  constructor-directed Build and whole-frame allocation.
- [Source result synthesis](../design/2026-10-02-source-result-synthesis-choice.md)
  §§2,4: Value entry for unannotated x, same binding and pure value-result
  introduction without recursively forcing latent descendants.
- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §§2–3.7: typed whole-tuple images, original scopes, current-world Bind and
  independently licensed Option 2 alternatives.
- The reviewed [phase construction](2026-10-08-id-public-phase-constructor.md)
  §§2–5: concrete ordinary phase cases and independent production clauses.

The current task explicitly permits needed legitimate native definitions.
No unfinished export draft or uniform-inlet draft is a premise. Any repaired
whole-inlet observation-image certificate can be supplied as the independent
input described below; no equation about its contents is assumed.

### 2.1 Evidence is retained data, not just a proposition

Write `VCert(A,v,p,e)` and `WCert(C,e)` for the original independently typed
value and immutable-world evidence objects. `TCert(R,o,e)` and
`CarCert(I,t,p,e)` have their original complete/pending/hereditary meanings.
Multiple evidence objects at the same semantic tuple remain distinct.
Original independent primitive/ground/descriptor witnesses remain their own
typed parameters. No arbitrary evidence gets typed by a matching tag.

An immutable world evidence record includes its joint registry/scope/authority
guards and dependent binding environment. For each registered installed slot
b it carries the **one retained binding projection**

```text
(raw value/carrier, actual provider, declared contract,
 original incidence/root, hereditary certificate at its event).
```

Aliases/captures reference that same projection; they do not select independent
raw values or independent installed certificates. World and hereditary evidence
also retain all their original additional witness fields. The projection of
this required record is a typed operation; it does not imply that every
derivation witnessing this projection has one canonical proof term.

All carrier input fields remain in the full proof tuple: inert formation and
complete Car witness, full original J/I contract, result checking derivations,
static guards, original residuals and a **whole observation-image proof** for
any Delta restrictions on all J alternatives. The latter is an independently
typed finite local checking derivation at its original telescope, not merely
a predicate that happens to hold on the initial tuple. This note projects its
already justified complete image and never recreates it from actual execution
or scalar payload inclusion. Its entire proof is retained by CE.

## 3. Independent typed local proof registry

Let L be the global independently typed local proof registry. Its entries
carry their full dependent input/output telescopes, original scopes and genuine
local semantic laws. It is fixed before source witness formation. Its local
constructors use only semantic value/world/observation/carrier interfaces and
actual slot/event/IF operations; no entry may assert `OriginalNameClause`,
`Build(S)`, legal whole-source truth, Generalize adequacy, successful Q or the
desired final certificate equality.

The following existing local checking derivations are retained as proof data:

| Constructor | Typed interpretation; witness fields kept |
| --- | --- |
| Identity(A) | Same decorated tuple at A; input/output evidence equality required by this rule only; Identity tag retained. |
| Compose(d1,d2) | d1/d2 at their original intermediate interface; intermediate value/world evidence retained and both local laws checked. It is not simplified to Identity. |
| Record width/depth | Original selected raw fields/providers; each child proof, sharing/incidence witness and output certificate retained. |
| Union injection/case | Original branch tag and child/case proofs; same raw value/provider; all original branch proof fields retained. |
| Intersection introduction/elimination | Same raw decorated value and joint world; both/selected child certificates and their proof terms retained. |
| Top/Any | Original membership witness with its independent law, raw value/provider and required guards; never a replacement of a full Function/carrier guard. |
| Same-value/computation checking | Finite original local derivation with its same decorated operand, full observation/provider fields and original source consumer; no Value/Computation exchange from shape. |
| Complete Function checking | Original finite domain and whole-observation proof trees, narrower-domain witnesses, all original binders and provider identity; the actual complete inclusion is derived by those laws, not a leaf oracle. |
| Registered equation/congruence/guarantee rules | Original full parameter and witness interfaces, all branches and equation references, actual guards; scalar inclusion does not decide unrelated whole production semantics. |
| Registered method/adapter/annotation choice | Its actual original local proof or conversion law, choice identity and dependent fields. Executed conversion/runtime fields are not erased as proof choices. |
| Additional authentic local primitive | Its supplied declaration/typed local law and complete operands/witness; no whole-source or final-equivalence primitive. |

Finite terms of this registry can use registered recursive equation references.
Actual histories still have their original finite-development interpretation.
An open authentic local catalogue remains an independently typed catalogue
parameter. This gives a finite symbolic registry interface without claiming
all true extensional inclusions have finite proofs.

For a local semantic action f, a proof-program witness d has a typed local
relation

```text
Apply_L(d; input raw tuple, input evidence; output evidence, auxiliaries).
```

Its interpretation is induction on the registry term above (or the actual
independent primitive's supplied local law). Auxiliary/intermediate evidence
and alternative tags are explicit fields, not existentially erased. The
native elementary actions in §4 provide the projection/restriction/install/
Return/frame-image leaves. Compose can surround them with independently
allowed proof-only checks at the original source checking occurrence. Every
new intermediate witness remains at that rule's original telescope. This
notation denotes that finite typed term interpretation, not a new unspecified
truth predicate.

## 4. Native source-free local certificate constructors

### 4.1 Entry rebind and immutable world extension

The independent IF/slot operation `Install(C,b,(v,p))` replaces/installs only
the authentic formal binding at the original receipt/rebind port, after a
completed entry Return. Its joint path/profile/scope/receipt/world guards and
current occurrence action are the selected Strict operations. It performs no
latent Force and does not claim arbitrary State compatibility.

Define the elementary certificate constructor by dependent record fields:

```text
BindIntro(b,return-port;
          completed entry (v,p,C0,e), theta_v:VCert(A,v,p,e), omega0:WCert(C0,e),
          original IF rebind/path/scope/current guards,
          omega1:WCert(C1,e1), beta1:BindingCert(b,A,v,p,e1))
```

The fields satisfy `C1=Install(C0,b,(v,p))`. beta1 retains the same actual
returned value/provider and original input hereditary certificate restricted
along the supplied independently compatible event action. Every old installed
binding is the restriction of its same original projection; aliases/captures
agree. omega1's required environment is that extended dependent record, with
its same joint registry/scope/authority fields. Extra original world/evidence
witnesses are carried as explicit fields. This is exactly the immutable W
record introduction, whose semantic soundness follows by projecting those
old/new hereditary certificates at each later independent compatible event.

The complete native `BindCert` is the tagged finite local derivation with this
elementary record and all allowed original proof-only checking programs at
the rebind's actual proof scope. Their input, output and intermediate
certificates remain explicit; runtime `(v,p)` and C1 are not changed. The
signature admits no hidden executed conversion. A conversion, if originally
selected by the source, is its own retained executed constructor instead.

### 4.2 Binding/world projection and restriction

`ProjectIntro(b;omega,beta)` has omega:WCert(C,e), the registered b incidence,
and beta equal to **omega's retained environment field at b**. Its raw
projection is `Lookup(C,b)=(v,p)`. This is a record eliminator, independently
of any source Name occurrence. Additional certificate derivations at this
projection point are finite L terms with that same raw projection and their
original proof choices; they do not install a different binding.

`RestrictIntro(beta,e,e';chi,theta')` has the same actual binding/root/provider,
an independently supplied compatible history/context action chi with its
live authority/scope/lifetime fields, and theta' the hereditary projection
of beta at e'. The elementary hereditary action is part of beta's selected
certificate. A chosen local restriction/checking derivation can retain its
own L term, input/output theta and auxiliary evidence. No restriction derives
compatibility or an active grant from immutable identity or historical origin.

Define `ReadCert` as the dependent record of ProjectCert followed by
RestrictCert at the original read event. It stores the original slot/reference
map, world/binding evidence, selected projection/restriction programs, their
intermediates and final V evidence. Its raw result is the same retained
`(v,p)`; different legal proof programs/terms remain different records.

### 4.3 Pure Return and prefixes

`ReturnIntro(A,result-port;v,p,C,e,theta_v,omega,guards)` has theta_v:VCert(A,v,p,e),
omega:WCert(C,e) and the original result/provider/root incidence guards. Its
outcome is the raw `Return(v,p,C)` at that result port, and its T certificate
contains these exact input evidence fields. No request, activation, receipt,
store change or latent execution is introduced.

`ReturnPrefixIntro` carries the same world/current event and result-port
incidences with no asserted result before completion. Its zero-step case is
included. The original prefix position/world/evidence fields and chosen
finite local prefix/checking derivations are retained; later result fields
cannot be fabricated from the result endpoint type.

The complete native `PureReturnCert` permits those elementary records and
every original finite L checking derivation at that result/checking scope,
retaining its input/output T/V evidence and all auxiliary witnesses. It does
not identify a wrapped Return proof with its elementary ReturnIntro witness.

### 4.4 Actual invocation-frame image

Let `ExitOwn_IF(C,r,e)` be the selected lawful removal of this invocation's
*current own occurrence*. It has its original receipt/occurrence/order/scope
guards. Borrow-or-fresh resumption uses the current state's registered
occurrence, not a saved activation. Exit preserves the live store and returned
decorated value; it removes no unrelated frame or active handler.

`InvocationReturnIntro(IF,r;v,p,C,e,theta_body,omega;
                        C_out,e_out,theta_out,omega_out,guards)` requires that
same body's completed PureReturn certificate, the actual current occurrence
guards and `C_out=ExitOwn_IF(C,r,e)`. theta_out retains the same raw returned
`(v,p)` at the original outward/future port; omega_out is the projected valid
world and theta_out's V fields are the hereditary/world/incidence restrictions
of the actual returned certificate at that event. The soundness proof is
world projection plus those restrictions. It adds no future execution.

The complete `InvocationReturnCert` keeps any original finite L image/checking
derivation, its proof tags, intermediate/output certificates and auxiliary
fields. A different permitted proof term need not equal the elementary term.

### 4.5 Explicit local grammar and completeness scope

In proof-term notation, the four families use the finite schema

```text
Cert_f ::= Elementary_f(complete record)
         | Check_f(Cert_f, d_L, all intermediate/output proof fields)
         | Local_f(registry entry, full argument telescope, independent witness)
         | Ref_f(registered proof equation, original scoped arguments).
```

Here f is Bind, Project/Restrict, PureReturn/prefix or InvocationReturn.
Check_f requires its actual L law at the same raw tuple and original checking
scope; Local_f requires an authentic independently typed local action law
of that same signature. A registered equation can only refer to its declared
finite proof grammar. Composition and structural cases retain the L terms
specified in §3. This is a finite tagged grammar with explicit local records,
not a permission to introduce an opaque whole-source f predicate.

The four elementary constructor families and finite L derivations are the
**exhaustive newly defined native witness grammar** for these local actions.
Every clause is a same-tuple dependent record, typed image or finite registered
proof constructor. Every original free/shared/event/checking field is present
in the record telescope. Imported/opaque certificates remain their authentic
independent inputs; they are not claimed to have a canonical native term.

This completes the previously unspecified local witness grammar; it does not
prove that arbitrary foreign evidence is generated by it. Its membership
soundness follows from the actual immutable/Return/frame record operations and
induction on L. No witness-normalization or proof-irrelevance law is added.

## 5. Native owning source rules before Build

Define the following witness-level source rules at their authentic resolved
registration, using the independent constructors of §4:

| Source owning rule | Native full witness record |
| --- | --- |
| Completed Value-entry Parameter/rebind | Actual Force Return and its complete carrier/input-check certificate; original formal/receipt maps; BindCert at the actual return event. |
| Immutable Name/projection | Resolved registered reference b; ReadCert at its actual current event. It returns that projection's same raw value/provider. |
| Pure source Result | The Name/data witness and PureReturnCert at the independently formed body-result port. All separately allowed source checking/annotation derivations are retained adjacent to this rule. |
| Complete invocation return | Completed body PureReturn witness and InvocationReturnCert through original IF. |
| Pending/zero-step cases | Original phase/receipt/Force/prefix/current-world fields and their typed prefix/continuation certificates; no future completed fields. |

An allowed source Check at any of these original occurrences records its full
L derivation and every intermediate/output witness. Its constructor is not
absorbed into an automatic canonical Name or Return proof. Source ViewLogic,
Shared, EventField and EventProof classes are exactly their original owning
records; the new witness fields use the scope already specified by that owning
source rule. No field is hoisted into a template because it happens to be proof
data, and no new source instantiation is created at a Name.

Only **after** those rules are defined does Build emit their dependent-record
clauses. Thus the source meaning is not defined by Build success or export
decoding. The ordinary constructors and the native source rules use the same
local meanings because this definition explicitly selects them, rather than
because a producer assumes extensional equality with an unknown source clause.
The existing SRC construction/inversion can apply to this new local law as an
L2 case once independently reviewed; this note does not certify that adoption.

## 6. Expanded `id` clause and finite ordinary interface

Fix one original scope tree, one complete joint strategy, actual source-created
U and its authentic receiver/formal/result/return registrations. Fix the
prechosen inlet I and description A at their original type scope. Let X be the
full retained tuple of:

- intrinsic/shared/template/instance fields and all original nu,K,D residuals;
- actual challenge/carrier/receiver/receipt/current-world/history fields;
- the whole carrier/checked-input/observation-image proof and original choices;
- every Bind/Read/Return/Invocation certificate and its intermediate, auxiliary,
  ViewLogic/EventProof/checking witness, at its original dependent scope;
- body/outward/future ports and all independently typed continuation/future data;
- the client W and every original operand it reads.

World variables and all their evidence remain in X. No world certificate is
replaced by a producer's preferred construction. The finite interface has a
tagged clause at each reviewed VP phase; the completed branch expands as
follows. z contains only redundant *raw* value/provider aliases:

Here p denotes actual raw provider identity, not a descriptor endpoint or a
registered formal/body/outward result-port identifier. Those distinct ports,
roots, view decorations and their complete incidence maps remain separate
fields of X. CE never identifies them merely because the runtime value/provider
is preserved across the projection.

```text
force return:    (a,p,C_force); complete I result evidence theta_a, omega_force
formal alias:   (v_bind,p_bind)
read alias:     (v_read,p_read)
body alias:     (v_body,p_body)
outward alias:  (v_out,p_out)
```

The new native source rules give the explicit completed clause

```text
Input_I(X) and OriginalJointGuards(X)
and (v_bind,p_bind)=(a,p)
and BindCert(b;(a,p),C_force,C_bind; FULL Bind proof fields in X)
and (v_read,p_read)=Lookup(C_bind,b)
and ReadCert(b;(v_read,p_read),C_bind; FULL Read proof fields in X)
and (v_body,p_body)=(v_read,p_read)
and PureReturnCert(A;(v_body,p_body),C_bind; FULL Return proof fields in X)
and (v_out,p_out)=(v_body,p_body)
and InvocationReturnCert(IF,r;(v_out,p_out),C_bind,C_out;
                         FULL invocation proof fields in X)
and AllOriginalLocalCheckClauses(X) and W(X,z).
```

Here `Input_I` is the independently supplied complete typed input record and
whole observation-image checking proof, interpreted by its actual finite local
clauses. `OriginalJointGuards` is the explicit conjunction of the original
registry/scope/authority/incidence/residual fields already in X. Neither is
an opaque source relation. `AllOriginalLocalCheckClauses` is the finite L
term interpretation of each retained source checking node at its exact
original telescope; it is not a source-validity Boolean. Their actual fields
and interpretations are unchanged between the two presentations.

BindCert's independent record law gives

```text
C_bind=Install(C_force,b,(a,p))
Lookup(C_bind,b)=(a,p).
```

These are runtime slot equations, not statements about equality of V/W proof
objects. Substitute them and the displayed raw aliases **only in raw
value/provider argument positions**. Retain the alias graph when W or another
designated field exposes those aliases. The resulting ordinary clause is

```text
Input_I(X) and OriginalJointGuards(X)
and AliasGraph(z;(a,p))
and BindCert(b;(a,p),C_force,C_bind; SAME FULL Bind proof fields)
and ReadCert(b;(a,p),C_bind; SAME FULL Read proof fields)
and PureReturnCert(A;(a,p),C_bind; SAME FULL Return proof fields)
and InvocationReturnCert(IF,r;(a,p),C_bind,C_out;
                         SAME FULL invocation proof fields)
and SAME AllOriginalLocalCheckClauses(X) and W(X,z).
```

This is a finite ordinary **Echo certificate interface**, using global local
certificate constructors and original typed slots. It contains no source
Lambda/Name/body definition, Build node, source-root pointer or complete
source relation. The four global constructors and raw alias graph replace the
projection body skeleton. Arbitrary proof terms remain symbolic certificate
fields, not copied source syntax. Other original check alternatives remain
their own finite registered proof data.

At Start/Received/Forcing the appropriate clause contains only that phase's
original input/world/receipt/prefix/continuation fields; no completed a or
later certificate is introduced. At EntryValue, retain BindCert after the
actual typed I Return. At Body prefixes, retain the appropriate Read/pure
prefix proof fields without asserting a result. At BodyValue omit the not-yet
executed invocation image. Each branch substitutes only the aliases actually
present there. At Future the outer provider is the actual returned `(a,p)`;
nested future returns and operation responses keep their own raw values and
their full independent certificates, with no new Echo equation. Response/raw
Resume binders retain the original receipt and unfinished suffix and apply the
same clause at the live event. These are a finite branch inventory, with
positive finite-history developments at their original event scopes.

### Theorem CE: exact full-tuple certificate expansion

For the newly defined native source witness grammar,

```text
ExpandedSource_id(X,z) iff OrdinaryEchoCertificate(X,z).
```

**Proof.** Expand each source owning rule by §5, yielding exactly its §4
local dependent-record clause and all original checking nodes. On the completed
branch, substitute the value/provider alias equalities and the registered
Install/Lookup equation above. Equality substitution preserves every local
predicate with those same raw arguments; it changes no proof field. The two
displayed conjunctions are therefore logically equivalent. In the reverse
direction, the retained AliasGraph gives every original raw alias, and the
same generic certificate record satisfies the owning source rule. At each
partial phase there are fewer aliases; perform the identical local substitution
only on those present fields. Future/nested result operands are untouched.
Finite history/registered proof development induction applies this equality
at each original event binder with its original shared fields. QED.

On the full tuple with AliasGraph retained, define F(X,z)=(X,z) and G(X,z)=(X,z).
They preserve every proof term/intermediate/auxiliary field and W literally.
If private raw aliases z are instead eliminated, F forgets just z; G reinstalls
z by its displayed total graph on `(a,p)`. Any W referencing z is retained
with that same graph or rewritten by that exact total substitution. Public
observations of such aliases use that graph, so both maps preserve their
original values. No existential proof witness or original binder is hidden.

The original strategy is extended/restricted only at those forced raw aliases.
All ViewLogic/EventProof/checking choices remain at their existing positions
and are the same strategy functions. A proof term can depend on a permitted
preceding challenge/event; CE never chooses a new one to fit a different
frame or port. Shared witnesses are not copied. Consequently the equality
survives arbitrary well-scoped client W, including W distinguishing Identity
from Compose or correlating proof terms between source frames.

## 7. Limits and constructive conservation

CE is an exact equality for **newly completed native local source witness
rules** and their ordinary finite certificate interface. It is not a theorem
that every pre-existing unspecified Name/Return witness equals the new
constructors, or that a separately fixed foreign kernel has this witness
grammar. A foreign witness-level local relation needs its actual independent
typed bridge, with all original choices preserved. Such a bridge is not supplied
by membership soundness or endpoint equality.

The new rules preserve the selected raw immutable operations and semantic
membership obligations: rebind installs the actual returned value; Name reads
its original binding; pure Return retains it/current world; invocation return
removes its own current occurrence; pending prefixes/futures remain complete.
The registry retains all independently permitted checking/structural/conversion
choices and original scopes. No original arbitrary proof term is silently
declared canonical. Its primitive or checking law must genuinely exist; a
source-specific normalization promise is not a registry entry.

CE compares **source proof clauses**, not all VP production observations with
source executions. Independent VP/other licensed Option 2 observations retain
their own complete laws and evidence; an unanchored production alternative
receives no manufactured source proof. The whole input-check/image certificate
is retained and must account for all its own production alternatives. Its
complete semantics is not inferred from t's actual trace or actual acceptance.

For this new native projection scope, source synthesis can select the ordinary
VP plus finite Echo/Fixed residual, independently of its source-introduction
witness grammar. P is still the reviewed exhaustive ordinary phase/production
law; it is never defined by the certificate expansion in §6. For example, a
specific carrier t may actually return true while its independent complete
JBool contract licenses a pure false Return. That licensed false entry is
retained by the whole input image, VP can take it, and Echo returns that same
false. There is no source `id(t)` execution witness for this abstract branch.
It remains a valid production observation without obtaining a source Bind/
Name/Return introduction witness. Exact CE concerns the independent source
introduction/checking proof coordinates; it does not source-tighten P.

For the full public export, the primary still has to attach this finite
ordinary certificate interface to the actual root, integrate the generic
uniform inlet and original Generalize scope allocation, retain all other
non-definitional source/check choices, and supply actual ordinary query rules.
This note's contribution is the missing exact local witness semantics and
its concrete algebraic elimination; it does not assume the final export
equality as a local lemma.

## 8. Claim, checks and frozen packet

Claim class: reviewed native local certificate definitions, their membership
soundness by record operations/typed registry induction, explicit source owning
rules before Build, and exact CE alias-substitution proof on the full retained
proof tuple. No producer self-certification, foreign witness equivalence,
public solver/Direct completeness, principality or production adoption.

Method: documentary typed-constructor construction and elementary equality
substitution. Independent primitive/world/carrier/history/local checking laws
remain authentic inputs. The result contains no assumed canonicality law,
opaque OriginalName clause, opaque whole-source relation or arbitrary final
export-equivalence predicate. No executable semantic probe, build/test,
enumeration, Git mutation or child was used. Only this leased file was written;
both previously frozen notes and shared records remain untouched.

Both independent reviews passed at frozen SHA-256
`d9c14da0fe504c78f6d33154cab2122e580a175a70ac185f108cdad39163ce56`.
Only status metadata changed after review. The following packet records the
producer's original pre-review submission.

Historical producer commit packet:

- Exact path: `notes/theory/2026-10-08-native-projection-certificate-constructors.md`.
- Baseline: `4b5215320587e94acf286ff49267a00515e8812e`; phase input af8b6ed.
- Status: new research-only native witness constructor and algebraic proof,
  awaiting independent mathematical/specification review.
- Suggested checkpoint message: `research: define native projection certificate witnesses without normalization`.
- Deferred primary deltas: adjudicate exact native source witness selection;
  use CE only on that selected grammar; preserve every non-definitional local
  source choice and separately validate foreign/public/query seams.
- Final dependency-byte/digest and Markdown integrity checks are reported at
  submission. Peak RSS/research wall time were not instrumented.
- Writing stops at submission; renewed edits require a renewed lease.

### Frozen dependency check

Seven baseline semantic inputs equal their pinned bytes, and the reviewed phase
note equals af8b6ed. New uniform-inlet/repaired export files are not dependencies.
Markdown newline, whitespace, fence and local-link checks passed; these are
integrity checks, not independent mathematical certification.

```text
0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0  notes/design/2026-10-08-contextual-function-membership-definition.md
fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a  notes/theory/2026-10-08-call-semantic-input-realization.md
6292b778e804988b32d48df663061d01e1593340ccb584fb6a8c0565bd817cfd  notes/design/2026-10-08-captured-closure-constructor-definition.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240  notes/theory/2026-10-08-source-generalize-definition-and-proof.md
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38  notes/design/2026-10-08-source-generalize-definition.md
71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992  notes/design/2026-10-02-source-result-synthesis-choice.md
1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186  notes/design/2026-10-05-source-contracts-and-common-allowance.md
140c9c907f3ae27120acd84d96c75b2d9a64b437e3e0e71c540c0030864ebb6b  notes/theory/2026-10-08-id-public-phase-constructor.md [af8b6ed]
```
