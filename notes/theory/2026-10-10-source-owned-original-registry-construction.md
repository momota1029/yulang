# Source-owned original registry: staged construction of the invoke pre-Call spine

Date: 2026-10-10
Status: research-only candidate construction; independent mathematical and specification delta reviews PASS; exact new definitions UNADOPTED
Baseline: `d0f62c3bd97b11bc9eb6b46390a2cf1d9702a861`
Exclusive write lease: this file only; frozen on submission
Claim class: constructive candidate definition, finite-source formation/lookup/decoder theorems, exact staged/direct reflection and conditional semantic preservation
Adoption: none; this candidate does not answer or preempt registry q3
Implementation / solver / source acceptance / C0 / F5 authority: none
Independent review: [frozen rounds, accepted repairs and integration scope](../progress/2026-10-10-original-registry-construction-review.md)

## 1. Result and exact scope

This note actually constructs a registry from the resolved source occurrences
of `my invoke f = f 1`. It does not take `P_old`, a completed `Reg_f`, a
representation certificate, lookup correspondence, exhaustive entry manifest,
or successful old-consumer applicability as an input. It constructs the formal
registration, its key/payload/lookup/decoder square, the actual callee Name and
its normalized Result code, and the actual literal Data/Result child. The
registry contains complete declaration schemas and their original dependent
fields, rather than a table of endpoints or enumerated event/proof witnesses.

The registry representation is an explicitly **new candidate owner**. The
[previous construction attempt](2026-10-10-selected-source-p-old-construction-attempt.md)
§§3–5 correctly did not derive a representation from the selected existing
interfaces. Here that missing definition is supplied and its consequences are
proved. No equality with a separately fixed, supplied registry is asserted.
The name `P_old^src` below means the source-owned old component *within this
candidate*, before the approved Call Reify tagged extension. It is not a cast
into an unknown preexisting registry sort.

The completed source fragment of this candidate is the **pre-Call spine**: the ordinary
formal and its entry interfaces, source SharedPositions anchor, callee
Name/Result, literal Data/Result and ChildCode, and the source-generated Return-image schemas and any finite locally declared
consumer schema at these occurrences whose entire application has the constructor
interface defined in §4.1. This interface is a NEW part of the candidate, not
a theorem about every unspecified original kernel. No declared arm is removed
to make an incompatible declaration fit. The complete Application, checking
origin, argument compatibility, result/effect/protection image, O0/O1,
admission and solving are not manufactured. In particular the separately
unadopted `RuleCall_L`/`CertCall_L` provides no constructor here. A pre-Call
bootstrap is useful even when the eventual constraint family is inconsistent.

The [approved q2 direction](../design/2026-10-10-call-reify-construction-direction.md)
adopts four choices from the [Reify proof](2026-10-10-original-call-reify-constructor-proof.md)
§§2–7. It still requires actual old-registry construction/conformance. Its
new Arg/Lit sorts are kept separate below. This candidate adds a fifth,
currently unadopted, choice: the old source registry's representation and
staged interpretation. Independent review and any subsequent adoption remain
separate from the mathematical construction in this note.

## 2. Inputs that remain genuine local inputs

Fix the actual resolved finite source occurrences:

```text
L = the invoke callable source occurrence
d_f = the actual ordinary unannotated formal declaration of L
u_f = its callee Name occurrence in body Call c
a = the integer-literal occurrence with payload 1
epsilon : ArgumentChild(c,a)
resolve_f : Resolve(u_f,d_f), the actual lexical edge
```

Keep the original binder tree B, scope inclusions, joint ordered context X,
lexical capture graph and one whole dependent tuple `xi=(nu,K,D)`. Source
occurrence identity and resolution are inputs, not inferred from equal endpoint
strings. In this closed nonrecursive example the callable capture graph is
empty; the body's lexical telescope will be constructed by the formal entry.
The source graph/identity may be kept open under lawful renaming.

Here B/X/xi have two explicitly different uses. Their finite **syntax**, binder
identities and dependency expressions are source input to Seal. Their actual
semantic values, including any registry-indexed worlds/descriptors/evidence,
remain parameters under their original ordered binders. They are not fields
of the raw registry and are never required to exist before Seal. Write
`I_syn=(S,B_syn,X_syn,xi_syn)` for the former and `Gamma_0(p)` for the unchanged
original parameter context of the latter, formed from the complete local
declaration signatures and original preceding binders. Static decoding builds
schema/formation families under Gamma_0(P), not a closed runtime valuation.
Specialization to a particular well-typed xi happens after Seal at its original
scope. The new candidate does not solve a semantic world/evidence inhabitance
obligation by assigning its syntax a value.

The semantic leaves are the same local inputs required by
[Source Generalize](2026-10-08-source-generalize-definition-and-proof.md)
§2 L1–L5, §3.1 Parameter/Name/Literal/Result and §3.3, and by
[Call input](2026-10-07-call-input-construction-proof.md) §3:

1. The actual Int primitive declaration with its inert literal formation
   constructor, original provider identity, complete ordered parameter/event/
   witness/guard/future schema and lawful action. The token `1` identifies its
   payload; it is not a membership proof.
2. The original Return/prefix and entry/Force/rebind declaration schemas and
   their static local constructor operations. Their genuine semantic laws
   remain separate inputs when interpreting observations.
3. Independently declared joint-world, reference, scope and authority schemas
   required by those local constructors. Their current-event witnesses are
   not inputs to static formation.
4. For an additional primitive/image/consumer clause actually used, its whole
   independently typed local signature and original local law, including each
   W/Z/Option 2 arm and its opaque complete telescope. A missing such local
   clause has no instance here; no generic law is invented to replace it.

These are local declarations, not whole-program success certificates. A
declaration can have empty semantic fibers. Its static formation operation
must accept symbolic ports and scoped descriptor variables; if a foreign
operation instead requires a runtime receipt or current guard witness merely
to declare a port, that foreign operation is outside this static fragment.
This distinction is the existing static/semantic distinction in the
[original owner definition](../design/2026-10-07-original-call-owner-definition.md)
§§2–3 and [native id formation](2026-10-09-native-id-original-wholearg-construction.md)
§3. This theorem does not assume that unknown foreign interfaces share it.

The candidate's source-owner constructor interfaces in §4.1 specify exactly
which arguments are available while a source schema is formed. The selected
source notes establish the introduction scopes and the displayed source-rule
operands, but do not state the complete hidden signatures of every opaque
primitive. Accordingly raw-registry specialization of these previously
unspecified interfaces is part of this NEW definition. Applicability to a
separately fixed original declaration is a declaration-conformance obligation;
it is not supplied by a rank certificate or inferred from lack of a displayed
decoder call. Local semantics are reused only at an actually well-typed whole
application of the complete original declaration, including all its arms.

No leaf has type `Code(P)`, `Reg_f`, `ReifyOrigin`, `WholeArgCompatible`,
`SpecCall`, `LegalSource`, `CertCall`, or an exhaustive registry/consumer
certificate. A local declaration mentions its own primitive semantics and
complete operand schema; it cannot silently assert the target conclusion.

## 3. The missing owner definition: recipes before registry-indexed proofs

### 3.1 Nominal source addresses and finite role expansion

Let v be the actual resolved source version. Source keys are finite nominal
addresses `(v,owner,role)`. Endpoints, inferred assignments, Code proof
identities, semantic witnesses and dynamic worlds are absent from these keys.
This candidate allocates one complete **bundle** per role; internal ports
are typed field projections of that bundle, not extra hidden registry rows.

For this exact source the role expansion is:

| Source owner | Key role | Bundle constructed |
| --- | --- | --- |
| Each independently used local declaration delta | `Law(delta)` | Entire local signature and its static constructor/action operations |
| L,d_f | `Formal` | Desc, ordinary Value role, formal/root, carrier/receipt/Force/rebind ports, complete entry schema, registration and SharedPositions anchor |
| u_f | `DataName` | Actual binding-route and Data-Name formation |
| u_f | `ResultName` | Actual Result port and Code-Result of that same Name |
| a | `DataLiteral` | Actual primitive instance and literal Data formation |
| a | `ResultLiteral` | Actual original literal Result port and Code-Result |
| a and u_f | `Image` | Source-generated Return image from the Data relation and whole original Return/prefix declarations, with all declared alternatives |

The actual Call c/edge epsilon is retained as **source incidence** in the
literal bundles, not a completed Call registration. No `Application`,
`CallResult`, `ArgReify`, new `LitImageRoot` or `CertCall_L` row is introduced.
There is no binding row for `invoke`'s completed Lambda: its body contains the
uncompleted Call. There are exactly **seven source rows**. If m is the number of distinct actual
local declaration tokens reached by the specified traversal, the exact total
is **7+m**. m is computed from the supplied local declarations, not granted
as an exhaustive list; signatures sharing one declaration do not duplicate
it. The selected notes give abstract local interfaces rather than a concrete
numbered kernel declaration graph, so no universal numeric value of m is
fabricated. This is the full candidate pre-Call domain, not the full source
program's completed registry.

Law keys range over the finite declaration occurrences actually mentioned by
these bundle templates, including Int, Return, Prefix, Value-entry/Force,
rebind, world/reference/scope and any actually declared additional local arm.
Multiple uses of the same declaration share its law key. That finite set is
computed by traversing the templates and their declaration imports; an opaque
primitive is retained as one whole local-signature bundle. Its possible
worlds, providers, witnesses and event histories are never enumerated.
If a declaration import introduces another declaration token, it is collected
once. Such tokens must come from the finite input declaration graph; an
unbounded generator of new declaration tokens is outside the finite fragment.

The fixed role constructors above, rather than a supplied exhaustive list,
define `Keys(S)`. Equality of keys compares the finite nominal owner/role
tokens only. Field projection `(k,path)` carries a typed path through the
ordered bundle; this is an accessor, not an enlargement of `Keys(S)`.

The concrete old-input law inventory for this pre-Call fragment is:

| Local semantic owner | Whole row/interface retained | Immediate use |
| --- | --- | --- |
| Actual Int primitive at a | Literal static formation, value/provider identity, every primitive alternative/guard/telescope/future and typed port catalogue | DataLiteral and its image operand |
| Original pure Return | Static Result-port formation and full constructor relation, current-world/result/provider/root incidence and hereditary result fields | ResultName/ResultLiteral and both Return images |
| Original zero/administrative prefix | Typed phase/state/environment/code/Result/pending/future envelope and all declared alternatives | Both Return-image prefix branches |
| Ordinary Value parameter entry | Parameter/header port formation and complete Receive/Receipt/Force/Rebind schema with original dependent maps | Formal |
| Original designated one-layer Force and rebind | Independent complete carrier challenge/receipt/scope/result fields and local static operations; no recursive force | Formal entry schema |
| Original lexical/scope/reference rules | Exact Empty/ValueBind and actual Resolve/ref-path/schema operations, local static license leaves and scope inclusions | Formal/Name/Result and image references |
| Original joint-world/current-context/authority declarations | Their full independently typed live-event hard envelope and lawful action, without current witnesses | All foregoing event/observation schemas |

When several operations above belong to one actual complete declaration they
are field projections of its one Law row, not invented separate semantic
declarations. Distinct actual declaration occurrences retain distinct rows
even when their text is equal. Original HCall, WholeArgCompatible, WF_Dec,
VIncl and CIncl declarations are **not silently inferred from this inventory**.
If they are genuine local declaration imports of a retained interface, the
same finite token traversal registers their complete signature rows too,
without semantic witnesses. If they are first used by a later Code-Call/
Call-demand owner, that later formation must introduce its actual complete
local declarations. DC below is not closure of those unformed Call consumers
or a claim that this pre-Call P is the total completed invoke-program registry.

### 3.2 Recipes and their independent static typing

A recipe contains a source constructor tag, its actual source fields,
nominal typed references and whole local declaration schemas. It contains
neither a registry value nor a completed source registration/Code proof.
The recipe constructors for this fragment are:

```text
Law(delta, complete local signature)
Formal(L,d_f,Unannotated,scope/type-scope/dependency inclusions)
Name(u_f,resolve_f,FormalKey)
Literal(a,1,epsilon,IntLawKey)
Result(owner,DataKey,ReturnLawKey,original scope/incidence)
Image(owner,ResultKey,DataKey,ReturnLawKey,PrefixLawKey)
```

Each recipe carries its actual finite schema syntax and typed declaration
tokens. A schema is an ordered dependent telescope, constructed from original
binders, typed fields, original constraints/guards, sums, scopes, source
references and opaque **whole** local declaration applications. It is not a
flat record reordered by category. An opaque application stores the entire
signature and its argument map; all of its original hidden internal fields
remain in that application. The law is about this full supplied signature,
not a guessed subset of it.

Static schema checking uses the ordinary dependent context rules: a field's
type is formed in the exact preceding context; source scope maps must exist;
a declaration application supplies every argument in its complete declared
telescope. Guard expressions have their declared types without having true
instances. An eventual field `g:PRed(P,h,...)` is a dependent field that may
have no witness. It is not an earlier guard-success premise of the recipe.
Receipt/current-world/provider/body/future witnesses likewise remain fields
under their independently declared event binders.

This candidate adds a raw nominal registry sort formed solely from finite
recipe syntax. Its constructor needs no wellformed source proof. Let
`RawRegistry` have fields source/key/recipe syntax and raw nominal lookup;
`P:RawRegistry` therefore exists before typed decoding. A refinement
`WellFormed(P)` records the subsequent source-rank construction, and the
candidate's source registry is that same immutable P with a separately
constructed static judgment WellFormed(P). WellFormed is not a value field
whose construction recursively changes P. Its actual proof is retained in
the formation derivation, not discarded as irrelevant evidence.

Recipe signatures are templates: at rank i their context may bind earlier
decoded-output variables, with their full types, without supplying their
values. Instantiating that template at the actual earlier decoder outputs
happens only in §4. An abstract raw-registry value p may occur in the template
as a parameter of a local guard/domain/consumer signature. The raw key-domain
and lookup API exists without Code(p); the typed field/decoder API is derived
by rank induction, not assumed in a recipe leaf. **Every argument needed to
form a field type counts**, including arguments to unevaluated predicates,
opaque signature applications, binder domains and result types. In particular
`g:G(p,decode_p(k_a))` at Formal cannot be formed when G requires an Image
bundle: the Image value is a later formation dependency even if g has no
witness and G is never evaluated. An abstraction over a missing value does not
close this application. No new event binder is inserted to fix it.

At formation the available registry operations are raw keys/recipes/lookup
and the earlier typed bundles explicitly listed in §4.1. `FullRegistry`, when
it includes a typed decoder for all keys, becomes available only after
Theorem B. It cannot be an argument to a rank-1 field-type application. An
opaque declaration can retain its complete unapplied signature, including
its own original parameters, at Law; applying that signature still requires
all of those parameters with their actual types. Retaining a signature token
does not supply an argument value. A source instance whose complete signature
application requires a later/self typed value has no instance of this strict
candidate. Its whole declaration remains retained; no arm, guard, field or
original parameter is deleted or moved. No equation recursively defining a
type by executing an observer is admitted.

### 3.3 Seal and lookup

The source recursion is concrete:

1. At L's parameter occurrence emit the Formal recipe and its local-law
   declaration tokens. At the actual u_f emit Name with resolve_f to that
   FormalKey, then its Result and source-generated Image recipes. At actual a
   emit Literal with epsilon, then its Result and source-generated Image
   recipes. Recursively collect the finite declaration tokens these recipes
   mention, including the Name image's Return/Prefix dependencies. No body
   Call is elaborated in this pass.
2. Check finite source scope/header syntax and rank templates as in §3.2,
   retaining the original ordered scopes and symbolic endpoint declarations.
   This binds earlier-output variables; it does not invent their values or
   grant a typed decoder. No guard truth is evaluated.
3. Seal the immutable recipe vector R, nominal key list Keys and actual source
   incidence/context skeleton into

```text
P_old^src = Seal(I_syn,Keys,R).
```

`Seal` stores finite source/context/schema syntax, symbol identities, nominal
keys and independently declared whole-signature tokens. It stores no
completed xi/world/descriptor/evidence valuation, no typed source bundle and
no Code(P) proof. Its domain is this raw finite syntax type, independently of
Gamma_0(p). `Seal` yields the actual registry value P_old^src with raw source
recipes.
Theorem B then constructs WellFormed(P) and its typed decoder theorem at
that same value. The candidate registry API has exactly these source/schema
fields and derived operations; it does not contain a recursively constructed
Code/WellFormed value field. Consumer formation retains the actual WellFormed
proof when its typing needs it, without making that proof an unformed data
field of P. Every semantic registry observer receives the entire same P.
No semantic family is interpreted at a prefix or a different registry value.
Its payload is the recipe vector and whole schemas, not an already elaborated
table. Lookup is defined
by finite nominal selection:

```text
lookup(P,k) = Found(R[k])    if k is the corresponding emitted key;
lookup(P,k) = Absent        otherwise.
```

For typed `k:Keys(P)` the first branch always applies. An external nominal
query retains either its exact Found branch or the exact absence witness.
No function or guard is compared for equality. A second semantic alternative
of the same local declaration is stored inside that row's complete schema;
it does not allocate a new key. Replay reads the same recipe object. There
is no equality decision on proof alternatives or dependent functions.

Seal does not certify dynamic consistency. It is a formed source registry
even if its generated constraints have empty solution fibers.

## 4. Strict source rank and a terminating complete decoder

### 4.1 Concrete formation dependency order

The dependency relation includes every value needed for **typing**, as well
as every source formation used to construct a derivation. A mention of a raw
nominal address needs only RawRegistry; a typed field projection needs its
complete antecedent bundle. An unevaluated guard requiring that projection
has the same typing dependency. Truth of the guard is a separate question.

Here are the candidate interfaces from which the actual ranks will be proved.
They complete the previously unspecified source-owner argument presentation;
they are not presumed consequences of every opaque original signature.
`I=(S,B,X,xi)` below abbreviates the original **context template** under
Gamma_0(p), not a prerequisite closed tuple installed in Seal or an argument
that makes all later fields available simultaneously. Header operations use
its static source/scope projections. Within an event telescope, an actual
projection of X/xi is an argument only after its original binder is reached.
The notation `Fam_delta at (p,I,...)` retains this same ordered parameter
placement; it does not lift an event parameter before Desc.
`Fam_delta(Gamma)` means the **entire** original ordered declaration telescope
in its declared
operand context Gamma: every field type is formed at its original predecessors,
every sum arm and opaque application is present, and every imported signature
is used at its complete arguments. The genuine local declaration supplies
this typed telescope and any local semantic/action law. It supplies no source
registration. Actual primitive catalogues and operator result/phase port maps
are independent parts of the genuine complete local input, as required by
SIG §3.4; no catalogue or whole-C0 proof is inferred from the bare telescope.

The minimal NEW owner rules are these. Their output types are indexed by raw p,
source occurrence, endpoint and scope fields; they have no implicit WF(p) or
typed-lookup premise.

```text
Header-Parameter:
  actual (L,d_f,Unannotated), Empty captures, original sigma_f/Delta_f/I
  -> h_f : OwnerHeader_src(p,L,d_f,Value,sigma_f,Delta_f,I)
     Desc(C,d_f,value,sigma_f,Delta_f), A_f, intrinsic r_f

Declare-Owned-Port:
  h : OwnerHeader_src(p,owner,role,scope,I), actual declared local port tag j,
  complete Fam_delta at (p,I,h,endpoint,source-incidence),
  the actual source-scope map for that declared port
  -> port declaration, its Parameter/Result/etc. source origin,
     OwnerPortLicense_src(h,j,that exact scope map,that whole declaration)

Assemble-Value-Entry:
  h_f, its complete owned carrier/Receipt/Force/Rebind port declarations,
  whole original Entry family at (p,I,h_f,A_f,those port declarations)
  -> original ordered Receive;Receipt;one-layer Force;Rebind schema,
     T_c = ValueBind(Empty,d_f,r_f,A_f,that entry/rebind origin)

Register-Parameter:
  h_f, Desc, all owned declarations/licenses, that entry schema and T_c
  -> reg_f : Reg_src(p,(d_f,R_f)), H_f, SharedInvoke((d_f,R_f))

Data-Name:
  that entire Formal bundle, actual Resolve(u_f,d_f)
  -> q_f and its binding/reference formation at the same T_c/root/A_f

Data-Literal:
  actual (a,1,epsilon,I), T_c from Formal,
  whole Int family at (p,I,a,1,epsilon,T_c,Delta_c)
  -> q_a and its entire original primitive relation/typed port catalogue

Header-Result / Declare-Owned-Port / Register-Result / Code-Result:
  actual owner and source Result role, its entire Data formation,
  whole Return family at (p,I,owner,T_c,Data,Comp(empty,A),incidence)
  -> source Result header, its port/origin/license, q_result,
     and ChildCode when owner=a

Generate-Image / Catalogue-Provenance:
  entire Data and Result bundles at owner, genuine full Int/Name catalogue,
  whole Return and Prefix families at (p,I,owner,T_c,Data,Result,incidence)
  -> full constructor-image/Union/Scope/Ref clauses, catalogue and provenance
```

`OwnerPortLicense_src` is defined by the displayed Declare-Owned-Port rule;
its eliminator returns h, j, the complete local declaration and the exact
scope map. It is the candidate's static **owner declaration** permission,
not a fabricated original contribution license or event authority. Where a
selected original static origin judgment was previously unspecified, this
rule supplies its candidate case. Any additional independently fixed original
license needed by a local port constructor must come from its genuine local
declaration or an earlier source derivation; this rule does not prove it.
In particular a native SIG licensed contribution requiring C0 still has
that original independent evidence field; its schema/catalogue/provenance
can be built without asserting an inhabited L or A fiber.

The Entry family's challenge/receipt/provider/current-world/future parameters
are its **original** ordered parameters. They are neither witnesses needed
to apply Assemble-Value-Entry nor newly introduced variables standing for
later source bundles. Its binder domains and every later field type are
already typed in `(p,I,h_f,A_f,ports)` and their actual preceding event fields.
This is the exact candidate local interface. The Return/Prefix and Int
families have the same discipline in the operand contexts displayed above.
They may use all raw p operations, arbitrary independent W/Z parameters and
all their original local alternatives. They cannot silently specialize a
typed decoder parameter absent from those contexts. If a supplied original
declaration needs it, this is a failed whole application/conformance obligation,
not permission to retain only its easier alternatives.

An already declared typed object at an **original preceding** local/event
binder remains usable with its entire original type. For instance, if z was
already bound in the original telescope and its binder domain is formed at
those actual predecessors, `G(p,z)` is a valid field type there. It need not
be a decoder output and adds no source formation edge. Its own domain still
must be checked; a domain containing an unavailable decode argument cannot
be excused. This retains independent W/Z/provider/world/opaque parameter
families at their actual binders. The exclusion is the missing argument
value in `G(p,decode_p(k_later))`, not every typed event argument or every
mention of a later nominal key.

**Formation argument lemma.** For these defined owner interfaces at the actual
resolved source, every argument of every pre-Call source constructor and
every type occurring in its complete output telescope is available from
original input scopes, raw p, genuine local declarations, the owner's newly
formed intrinsic fields, original preceding binders, or strictly earlier
source bundles.

**Proof.** Header-Parameter uses the actual source introduction and Empty
capture edge; SRC §3.3 puts sigma_f/Delta_f before the challenge. Desc and
intrinsic root symbols are outputs of this rule, so no received witness or
registration is needed to type them. Declare-Owned-Port applies the complete
local family to that already formed header/endpoint/incidence. The scope map
comes from the actual source binder inclusions retained in §2. Its license
is the displayed constructor proof, with no reg premise. Assemble-Value-Entry
then supplies h_f, A_f and every owned port argument; ordinary dependent
telescope formation types its original challenge and every later field in
that same context. Register-Parameter packages these prior outputs; OShared
consumes that newly formed reg. Data-Name's complete binding argument is this
Formal bundle, and Resolve is the actual input lexical edge. Data-Literal's
T_c is the same Formal projection; all its other static arguments are actual
literal/source fields or the genuine complete Int declaration. In each
Result case Data and T_c are available, the source role forms its header,
and its Return family receives that Data and the formed owner port. Thus
Code-Result has both of its displayed operands. Image receives its formed
Data/Result and the entire local Return/Prefix application. The primitive
catalogue is the local Int catalogue or the earlier formal reference catalogue.
SIG's operand, local-result, Union, Scope and Ref injections use those same
typed operands and original field maps; they introduce no later bundle
argument. Every opaque local field application is type-checked at its actual
full arguments in the declared Fam context; ordinary application and telescope
rules therefore give its type at the original predecessors. No hidden
supplied operand is excused as semantic. These exhaust the defined constructors.
QED.

This proves the following ranks for the **explicit candidate interfaces** at
the actual source. It does not replace the lemma by a supplied RankCertificate:

| Rank | Recipes | Earlier decoded source formations needed |
| --- | --- | --- |
| 0 | Law | No source formation; retains the complete supplied local signature |
| 1 | Formal | Only Law outputs and the actual empty-capture source header |
| 2 | DataName and DataLiteral | Constructed Formal/T_c plus relevant Law outputs |
| 3 | ResultName and ResultLiteral | Their corresponding constructed Data plus Return/Prefix Law outputs |
| 4 | Name Image and literal Image | Their corresponding Result/Data bundles and local Law outputs |

Law-import declarations may have a finite cyclic *signature reference* graph;
their whole already typed local signatures are tokens, not recursively
decoded source proofs. A complete unapplied signature can, under its original
parameters, describe an operation requiring the eventual full decoder. Law
does not instantiate that parameter. Such an operation cannot be applied to
form an earlier row. A law whose actual source-constructor application demands
decoding an unformed source Code has no such instance here. No
receipt/body/invocation witness is decoded to form Formal. Its schema has the
Desc before the challenge and future fields beneath their original event
binders. A guard that reads all raw recipes, lookup or absence of P is typed
at final raw P and need not be true. A guard receiving the all-key typed
decoder is a post-B consumer; it cannot be retained as an earlier applied
field merely by declining to execute it.

The maximum source rank is 4. No appeal to unknown recursion wellfoundedness
is necessary for this source. The Call is not an earlier dependency because
epsilon and its parent c are actual syntactic incidences; neither is a
Code-Call derivation.

### 4.2 Decoder rules and the actual formal registration

Define `decode_P(k)` by increasing rank, applying the following local
operations to R[k]. A decoded bundle consists of its whole ordered schema,
its source formation derivation family and its field projections. More
precisely, each constructor returns a **whole schema bundle** D_k: it retains
the complete declaration family and a function assigning a complete source
formation record to every permitted original local proof choice and every
predecessor's corresponding choice. Those choices are the existing rule
parameters/alternative tags at their original scopes, not added event fields.
An original local choice includes its complete original local argument and
premise record, including distinct opaque proof alternatives; retaining only
a tag would not suffice. The candidate constructor copies that record rather
than deciding equality of its proofs. Earlier source premises are supplied
only by the earlier families. No choice parameter is a completed registration
or source Code proof for the row being built. Dynamic guards/witnesses remain
the original semantic telescope fields, not prerequisites for static decoding.
For Name, for example, D_Name is dependent on the chosen member of D_Formal;
it never chooses a canonical formal witness. The combined choice family is
the **original scoped** dependent family of finite source-rule applications
specified by the stored recipes and entire local declarations. Its environment
extends at each actual owning rule's choice binder, retaining the original
binder tree; it is not one unstructured tuple hoisted before all events.
References to k_f reuse the same Formal choice and original descriptor/entry
schema, including when Name and both image expressions refer to it. They do
not freshen a choice or challenge per use. It exists by the rank
construction below; no completed source record is a recipe field. A displayed
`reg_f`, `q_cf`, `q_ca` or `J_owner` denotes the appropriate projection in
this family, with its original free endpoint and rule-choice parameters.
Original local constructor calls are at the same p=P, scopes and xi throughout.

At Formal, the actual `UnannotatedFormal(d_f)` syntax selects Value, following
[charter §21](../design/2026-09-29-scc-intrusion-redesign-charter.md#21-user-decision-parameter-roles-follow-the-outer-source-annotation-2026-10-03)
and [typed core §6](../design/2026-10-02-typed-computation-core-elaboration.md#6-source-result-synthesis-under-user-selected-forwarding).
Allocate the ordinary flexible descriptor symbol from the source introduction:

```text
A_f = DescSymbol(v,L,d_f,ValueEndpoint)
desc_f = Desc(C,d_f,value,sigma_f,Delta_f)
```

`sigma_f,Delta_f` are exactly the actual Parameter type scope and earlier
free dependencies, before its invocation challenge. They are not chosen
from an eventual received argument. The raw symbolic root and ports are
source addresses of this same recipe bundle:

```text
r_f = FieldRoot(k_f,FormalValue)
r_in = FieldPort(k_f,ReceivedWholeCarrier)
receipt = FieldPort(k_f,Receipt)
force = FieldPort(k_f,DesignatedEntryForce)
rebind = FieldPort(k_f,RebindResult)
k_f = (v,(L,d_f),Formal).
```

Here is the explicit missing source-owner case that supplies the prior origins
consumed by Entry-Value; raw slot presence cannot supply them. Define
`FormalOwner-Header` on the actual `(L,d_f,Unannotated,sigma_f,Delta_f)`
source/scope derivation. It creates the owner-header derivation together with
Desc and the intrinsic root/port declarations above. Define its
`FormalOwner-Ports` constructor to form `ParameterOrigin(L,d_f,Value(A_f),r_f)`
and the received-carrier/receipt/designated-Force/rebind origin declarations
from that header, the Value role and the genuine local static port/scope
formation operations. Its candidate **owner declaration** licenses are the
Declare-Owned-Port outputs of §4.1, with actual header/port/source-scope
arguments. Any further required original static license/scope premise is
supplied by its genuine local declaration operation or retained earlier
source/reference license derivation at its actual index; it is never
reclassified as a future dynamic guard. If a foreign port rule requires the
completed reg_f here, that rule
has no instance of this pre-registration constructor. This note defines the
source-owned header/port case in the candidate interpretation, not a shortcut
to that foreign judgment. Elimination of FormalOwner-Ports returns the full
header and original local static-license formation trees.

Using these formed Parameter/port origins, the Value-entry and scope declarations
form the complete symbolic
entry interface with order Receive; Receipt; designated one-layer Force;
Rebind. Its challenge and all receipt/provider/current-world/result evidence
are dependent fields under that actual invocation event.

The source descriptor is the original Desc record before that event. Future
receipt/response/rebind/current-configuration/body/pending fields keep their
original Event/EventField schemas; a proof about that same tuple keeps its
EventProof schema at the original position. This constructor forms those
binder/field **types**, not receipt/current-world/body witnesses. It moves no
event field to the Desc region and does not flatten a dependent future.
Form the binding:

```text
T_cap = Empty
T_c = ValueBind(T_cap,d_f,r_f,A_f,the constructed entry/rebind origin)
R_f = FormalContractRoot(k_f), with its complete registered Value(A_f)/entry schema
beta_f = (d_f,R_f)
```

Here R_f is the shared source-contract/root object, retaining its complete
original role, endpoint/root, scopes, annotation
absence, entry and dependency fields; it is not asserted Function-shaped.
This candidate's new **Register-Parameter** constructor records the actual
Parameter formation just built:

```text
desc_f, Value-entry schema, T_c, actual d_f/source/scope/incidence
---------------------------------------------------------------- Register-Parameter
reg_f : Reg_src(P,beta_f).
```

This is a source registration definition, not a granted `Reg_f` premise.
Its eliminator returns those exact fields. Apply the existing positive
OShared-Register constructor of the original owner definition to this actual
registration, at the candidate's interpretation of Reg:

```text
H_f = SharedPositions(reg_f)
anchor_f = SharedInvoke(beta_f) : SharedPositionSchema(H_f).
```

The anchor is a static address schema. It is not membership in Slots, a
Function realization, Own, O0, SeedExposure or a receiver activation. The
complete decoded Formal bundle retains desc_f, every entry field, T_c,
reg_f, H_f and anchor_f. Reg_src supplies the indicated original static
case in this candidate; identification with an independently fixed stronger
Reg predicate is not asserted. The exact formation order is
`source header -> Desc/intrinsic root/ports -> ParameterOrigin/static licenses
-> Entry-Value/T_c -> Register-Parameter -> OShared`. No step reads its own
completed reg_f. Raw nominal lookup only finds the recipe/source header;
it never inhabits a typed registration or license judgment.

At DataName, decode k_f and follow the actual resolve_f derivation. Construct
`Name(T_c,u_f)=(binding_f,resolve_f)` and apply Data-Name at the same binding,
root and `Value(A_f)`. At ResultName, form its source Result port through the
local Return static constructor at actual u_f and apply Code-Result:

```text
q_f : Data_src(P,T_c,name u_f,Value(A_f))
q_cf = Code-Result(q_f,o_f) : Code_src(P,T_c,result(name u_f),Comp(empty,A_f)).
```

No latent forcing is added if a later endpoint substitution makes A_f a
computation value. Value and Computation tags are never guessed from shape.

At DataLiteral instantiate the Int inert-formation declaration at actual
`(a,1,epsilon,T_c,Delta_c,xi)`. Retain the original primitive identity and
complete schema, giving q_a:Data_src(P,T_c,literal(a,1),Value(Int)). The actual
T_c formation is read from rank-1 k_f, so DataLiteral is rank 2 even when
the primitive needs only its lexical schema. There is no same-rank decoding
call, supplied acyclicity or optional rank refinement in this exact target.

At ResultLiteral this candidate's **Register-Result** constructor forms its
original source Result port from that literal's Data formation and the actual
Return declaration, using exactly the source/parent/role/scope indices of
[Original-ResultLiteral](2026-10-09-original-literal-result-owner-extension-candidate.md)
§3. Its historical Draft wording does not supply the registry interpretation
or a bootstrap proof; this note defines the operation in its candidate sort
and uses no N evidence. The later selected literal construction direction
remains unchanged:

Result registration has the same staging discipline as Formal: construct its
source owner/header from the actual child Data formation and Result role;
apply the genuine local Return static port/scope/license formation operations
at that header; assemble the Result registration; then apply Code-Result.
Any required primitive/reference/Return static license tree is retained in
these steps. Raw key presence is not a license. An original rule requiring
its own completed Result registration to produce its first port has no
instance of this explicitly new header-before-registration case. The defined
direct judgment uses these same source owner/port constructors.

```text
o_a : ResultPort_src(P,owner=a,role=ResultOfLiteral,
                    Comp(empty,Int),Delta_c,xi,epsilon)
q_ca = Code-Result(q_a,o_a)
     : Code_src(P,T_c,result(literal(a,1)),Comp(empty,Int))
chi_a : ChildCode(a,q_ca).
```

chi_a is the actual normalization incidence derived from this same child,
not a cast from a Code proof at a different occurrence. This is the literal
pre-Call constructor. Its port is not ArgReify, and o_a is not o_f.

At Image, perform the explicit local source-rule recursion of
[Source Generalize §4](2026-10-08-source-generalize-definition-and-proof.md#4-generate-the-open-source-rule-program),
using primitive relations, whole conjunction/union, constructor image,
scoped binding and registered references. There is no completed Image or
ReturnImage input. Write B_a for the primitive relation graph formed by the
actual Literal/Int clause, including **all** originally declared conservative
alternatives at that leaf. Write B_f for the actual Name reference to k_f's
whole formal relation at resolve_f, with its original dependency/guard/schema
arguments. An unassigned endpoint is a bound descriptor parameter of B_f;
it is not an assumed valid formal value.

Let C_Return be the actual full independently declared Return constructor
relation and C_Prefix its original zero/administrative-prefix constructor
family. Apply their original dependent operand/result field maps, with the
actual Result port and source incidence, to build finite clauses

```text
J_owner = Union(
  ConstructorImage_Return(B_owner, C_Return at P/T/xi/o_owner),
  ConstructorImage_Prefix(B_owner, C_Prefix at P/T/xi/o_owner)).
```

Union means the original tagged whole alternatives, with their original
logical binders. ConstructorImage means the independently specified local
Return/prefix relation on the same complete operand/output tuple, not an
execution-set operator. If the original Return/prefix catalogue presents
further independent arms, its entire catalogue is an operand family of the
corresponding clause; no W/Z/opaque arm is filtered by having no source
execution. Every original local guard/domain/evidence/future field remains
at its original position in that application. Conjunction joins shared
source/world/incidence fields on their original tuple. It does not reorder
all primitive fields before all Return fields. The original local dependent
field maps determine their placement.

The prefix constructor's own operand/phase maps determine which fields exist
before output. The notation does not conjoin a completed primitive/Return
member with a zero-step prefix or invent a prefix result; its original
schema/guard domains remain exactly those of C_Prefix. B_owner supplies its
source operand interface and original incidence at that point. Completed
value/provider evidence is required only at the original field position
where that operator clause requires it.

Register this finite clause graph at the source Image key. Its incoming
formation includes q_result, the actual source port and original T/xi fields;
its complete independent domain is the original constructor-schema domain
with those incidence maps. Its Port/IF catalogue is **constructed** by the
selected [native signature construction](2026-10-08-source-signature-incidence-construction.md)
§§3.2–3.4: primitive gives its whole genuine catalogue; constructor image
retains every operand catalogue and actual local operator result/phase ports;
Union retains both whole branches; Scope/Ref retain original binders and
source owners. This produces the complete incidence/provenance diagram,
including inherited primitive/formal owners rather than relabeling them as
Result-owned. This use of the SIG recursion does not take an unconstructed
registry/registration as an input: its actual source registrations are the
Parameter/Result outputs just decoded, and its primitive port catalogues are
the genuine rank-0 declarations.

Thus J_a and J_f are source-owned old Image rows **in this candidate**, formed
from original local primitive/Name and Return/prefix semantics. They are not
Comp(empty,Int)/Comp(empty,A_f), not J_lit, and not a supplied arbitrary fixed
ReturnImage renamed by endpoint equality. The new owner definition here
selects this source-generated root presentation. An independent old image
with an additional image-only guard remains a different root, requiring its
own conformance theorem. This construction preserves every actually declared
local alternative/guard; it cannot preserve an undeclared foreign image-only
arm by guessing it.

On this source-generated domain, the q2 proof's pi_J into the independently
typed code-event schema is formed by projecting the retained original
Return/prefix current-world/T/reference/code/Result/scope/incidence fields.
The constructor catalogue's original typed-field maps supply those fields;
there is no arbitrary H_T-to-H_J section. If a foreign local catalogue lacks
the required complete typed fields, its corresponding q2 applicability fails
rather than being repaired by this projection. A semantic all-arm typing
conclusion still uses each genuine original local tau law, separately from
static graph formation.

### 4.3 Noncircular bootstrap theorem

**Theorem B.** On §2's resolved nonrecursive source with the whole local
declarations applied at the explicit candidate interfaces of §4.1, source
recursion and Seal construct P_old^src. The decoder
then constructs reg_f, T_c, q_cf, q_ca, chi_a and the source-generated
J_f/J_a Image bundles from the local primitive/Name and Return/prefix clauses.
No target registry-indexed source formation is a leaf of this construction.

**Proof.** First form finite key/recipe/context syntax from source occurrences,
symbol identities and independent declaration tokens. Seal needs no actual
registry-indexed X/xi valuation and gives the immutable raw recipe value P.
Substitute this exact P for the raw parameter in the original context schema.
The formation argument lemma constructs all arguments and checks every output
field type, including all opaque/guard applications, in its exact predecessor
context. Induct on its resulting rank table: Law retains its unapplied whole
signature; Header/Declare-Owned-Port/Entry/Register form the Formal family;
Name uses its constructed Formal predecessor; Literal uses T_c and its entire
primitive application; Result uses its own Data and formed Return port;
Image uses its Data/Result and the whole Return/prefix application and
Union/Scope/Ref/SIG injections. At each step retain the whole original rule
choice family and form the constructor under its parameters. Specialization
therefore produces every allowed source record, with none supplied to Seal.
All source-bundle arguments of field types are earlier by that lemma; a
later typed argument cannot hide inside an unevaluated semantic application.
A recursive decode call always has lower rank. No guard/domain/consumer truth
is evaluated. Each local call constructs a derivation schema at P and the
whole original dependent indices.
The decoder constructs the finite source proof/schema syntax using the
displayed constructors and the genuine static local introductions; it does
not execute a semantic predicate or an opaque consumer to discover fields.
There is no equation P=table(completed-Code(P)) to solve: P stores recipes,
and Code(P) is formed afterwards by a terminating eliminator. QED.

This is honest staging, not a hidden call to an already completed decoder.
Raw-registry predicates can inspect this whole sealed P and can fail. The
all-key typed decoder API is produced only at the end of the rank induction;
post-decoding consumers may then receive it. No
interpretation of a prefix registry is used. Cyclic *semantic* references
are allowed only when their type formation does not require a cyclic source
bundle value: raw key/signature references can cycle, typed argument
dependencies cannot. No recursive semantic validity theorem is proved by
termination of the source decoder.

## 5. Exact lookup, inversion, soundness and source completeness

### 5.1 The previously missing one-formal square

Let b_f=R[k_f] be the emitted Formal recipe and D_f=decode_P(k_f) its bundle.
The constructor gives, with no representation premise:

```text
lookup(P,k_f) = Found(b_f)
decoder(P,k_f,b_f) = D_f
registration(D_f) = reg_f
formalBinding(D_f) = binding_f
Name(T_c,u_f) = (binding_f,resolve_f).
```

The first equality is finite-key lookup computation; the second is the
rank-1 Parameter decoder equation; the third/fourth are constructor
projections; the fifth is actual lexical resolution followed by DataName
decoding. Thus lookup returns the recipe whose decoder constructs **this
same entire reg_f** and interface. It does not return only an isomorphic
printed endpoint. Exact evidence is retained in that construction. Where
dependent typing requires transport along a key equality, the actual equality
proof and transport are retained; no UIP or proof irrelevance is used.

The equations with reg_f/binding_f are equations of these original scoped
families. Specializing to a particular formal source-formation choice yields
its actual complete registration and binding, and every use reuses that same
choice. Lookup itself always returns the same immutable recipe, independently
of the choice. Decoder elimination recovers the whole family; elimination at
a retained member recovers that member's exact source/choice/proof record.

### 5.2 Entry coverage and exhaustive inversion

**Theorem E.** Every candidate registry entry is generated by exactly one
source role occurrence or one shared local declaration occurrence in §3.1.
Every role occurrence generated by the fragment has its entry. Lookup and
decoder elimination recover its complete source recipe and the exact local
formation inputs/outputs. The theorem concerns finite declaration entries,
not finitely many semantic members.

**Proof.** The source recursion has exactly the six displayed recipe
constructors. Seal cannot introduce another row. Enumerating its key spine
and pattern matching each recipe therefore gives the required source/declaration
origin and tag. Conversely each source-recursion clause appends its unique
nominal key once; repeated references point to that key and cannot append
new rows. A law token is interned by its actual declaration occurrence, not
by extensional signature equality. Lookup selects that row. Rank induction
and elimination of its decoder constructor recover every input field and
earlier dependent bundle. The key-to-role and role-to-key maps are inverse
on emitted occurrences by their nominal constructor equations. QED.

The theorem is exhaustive for **this defined pre-Call registry**. It does
not assert that every possible original Call registry has this small domain,
nor that this is all entries of a completed invoke source. The source-generated Return images have their rows regardless of whether
their semantic domains have members. A separately fixed foreign image
root/domain is not identified with these generated rows.

### 5.3 Independent direct source judgment and reflection

For comparison define a direct source formation judgment F_src from the
actual resolved occurrences and the same local declarations: Parameter
introduces its Desc/Value-entry/registration at d_f; Name follows resolve_f;
Literal applies its primitive static constructor; Result forms its owner
port and applies Code-Result; Image applies the original local Return/prefix clauses through the
displayed independent conjunction/Union/constructor-image/Scope/Ref grammar. It has no lookup/Seal premise. Each rule retains its exact original
source/binder/scope/telescope tuple and local declaration arguments. This is
the indicated Parameter/Name/Literal/Result fragment of the selected source
schemas with Header/Declare-Owned-Port/Register-Parameter/Register-Result and
the raw-p operand presentation of §4.1 explicitly supplied as NEW candidate
definitions. Its complete local applications have those same ordered typed
arguments. Call is absent from the direct judgment.

**Theorem SR.** For this fragment, direct source formation and staged
recipe/decoder formation correspond in both directions, preserving the whole
ordered dependent derivation records and all local alternatives.

**Proof of soundness.** Induct on decoder rank. Each rule is the corresponding
direct source rule applied to the same earlier formations and complete local
declaration application. Source scope maps, primitive identities, original
ports and dependent arguments are copied. Name projects the actual formal
formation rather than selecting by endpoint. Result uses that Data and its
own port. Image uses that Result/Data and the exact original whole local clauses. This reconstructs
a direct F_src derivation, with no extra semantic success premise.

**Proof of completeness.** Induct on the finite direct derivation. Its source
constructor identifies the unique **already emitted** key. The immutable
recipe already retains the complete local declaration family; elimination of
the direct record exposes its original local choice/alternative and each
earlier source-premise record. By the induction hypothesis those earlier
records supply the corresponding parameters of their decoded families.
Specialize the existing D_k to these parameters and the direct record's
actual local choice. The displayed decoder rule then reconstructs that same
direct constructor with every field unchanged. This is family application,
never mutation of R, Seal, P or Keys(P); no completed Code is installed in a
recipe. Since every declared alternative was retained before sealing, the
direct choice is already in that family. No choice is selected by equality
search, and no new proof/event binder is introduced.

Erasure followed by reconstruction, and reconstruction followed by erasure,
are constructor equations on these retained records: at a leaf the original
local record is stored exactly; at a node the same tag, source fields and
earlier records are retained. This proves an intensional correspondence on
the generated records. It does not equate arbitrary proofs that have the
same runtime behavior. QED.

Free endpoint assignments are parameters of these source schema fibers.
Specializing a recipe to an assignment does not install another nominal row.
If an action changes the declaration/interface choice legitimately, it acts
on the entire corresponding fiber; it does not overwrite a globally fixed
view(root) based solely on endpoint equality.

## 6. Complete ordered schema and old-consumer dependency closure

### 6.1 A typed consumer-expression grammar

An actual consumer interface in this candidate is its original whole typed
declaration expression instantiated at the appropriate decoded bundle. The
following grammar describes how those expressions use the registry; it
does not assign new semantic operations to W/Z:

```text
t ::= original context variable
    | original field/port projection(t)
    | SourceRef(k,path) with its full dependent type
    | original dependent constructor/application(t_1,...,t_n)
    | OriginalLocal_delta(P, complete ordered arguments)
    | FullRegistry(P)
```

This grammar is for consumers **after** Theorem B. During source-row formation
only its raw-registry operations and earlier SourceRef instances are available,
as proved in §4.1; a whole typed FullRegistry term is absent then.
Original dependent binders, sums and scopes form such expressions in their
existing order. `OriginalLocal_delta` is opaque, retaining its **entire**
supplied signature and implementation/local law. FullRegistry supplies the
actual registry object, including full domain, lookup, absence and decoder
API. A local operation may quantify over all keys or inspect absence; it is
not required to disclose a narrower read set. It still receives precisely
P, not a filtered map. A foreign opaque local application whose registry
requirements cannot be typed against this candidate API has no instance
here. No theorem asserts that it is applicable anyway.

The source-owned ordinary consumers before Call are concrete: Name's same
binding lookup/projection; Return and its prefix envelope at o_f/o_a; the
formal's designated one-layer entry Force/rebind **schema** under its future
challenge; original world/reference/scope/license predicates used by these
interfaces; and the generated whole original Return-image clauses. There is no
invocation of an unknown actual callee U at this point. A symbolic formal's
future latent Function/provider interface remains a dependent schema under
A_f, not a selected consumer obtained from its printed shape.

### 6.2 Construction of closure without a hidden manifest

Compute dependency closure from the actual instantiated whole expressions:

* A variable/projection retains its original complete type and preceding
  telescope, with the same dependency edges.
* SourceRef adds its nominal key and every typed field dependency of that
  decoded bundle. Decoder inversion supplies those records; no key is
  invented from a solved endpoint.
* A dependent constructor retains all operands and every binder/domain/guard
  expression, in original order.
* An opaque OriginalLocal application adds its complete signature bundle and
  all actual arguments, including each supplied argument and dependency hidden
  by an opaque signature's notation. For an opaque implementation receiving
  P/its typed API, add the single full-registry node
  and all Keys(P). This deliberately retains everything it could observe,
  including global domain and absence; it does not guess hidden dependencies.
* FullRegistry adds P and all Keys(P). Each such key already has the whole
  recipe/schema/decoder interface from Theorem E.

The graph is finite because the key spine, actual constructor expression
syntax and supplied signature-token graph are finite. For opaque infinite
telescope fibers a graph node is the whole signature family with its original
binders, not its members. Stop graph traversal at an already seen node; cycles
of semantic references do not unfold infinitely. Nothing limits event
histories, proof alternatives, providers, independent W/Z worlds or futures.

**Theorem DC.** Every original field, guard, license, domain or operation
read by a well-typed pre-Call consumer expression is available in this
constructed closure with the same P argument and complete dependent type.
No supplied exhaustive manifest or global consumer-applicability assertion
is needed.

**Proof.** Induct on the typed expression derivation. A variable has its
original telescope position. Projection uses the same complete record; its
predecessor fields remain present by the induction hypothesis. SourceRef
uses Theorem E and the typed decoder path, recovering the same record, not
only its endpoint. A dependent constructor/application retains every argument,
binder and guard recursively. For OriginalLocal, its whole signature and
all its explicit argument records remain unchanged. If it can read the
registry, the supplied object is literally the complete P, so any hidden
inspection is on that same object. Quantification, domain size, absence,
lookup and decoder observations are therefore not narrowed. Its internal
operands are not decomposed or approximated. FullRegistry is the same case
without a local-operation wrapper. This proves complete typed availability,
not truth of an independent admission/license/validity predicate. QED.

This theorem deliberately does not promise that the registry supports a
foreign decoder for a different representation. Local typing is checked
against the specified registry API. The theorem does not remove a missing
semantic law by declaring an opaque foreign operation harmless.

### 6.3 Binder, guard and proof preservation

For a supplied local telescope

```text
Delta = (x_1:T_1; x_2:T_2(x_1); ...; x_n:T_n(x_<n)),
```

the stored/decoded telescope uses those same T_i at those same preceding
arguments, after substituting the same final P and source indices. Every
Sum arm, opaque family application, guard-evidence field, license path,
provider/current-world field, response/raw-resumption and output-dependent
future remains at its original position. Family syntax may itself be a finite
schema with infinite fibers; preservation is schema induction, not event
enumeration.

**Theorem T.** The maps storing and eliminating the ordered schema preserve
every dependent field and all evidence alternatives. On a given retained
record they are inverse constructor projections; no extensional proof equality
or canonical witness choice is used.

**Proof.** Induct along the original ordered telescope. At position i all
predecessors are the same retained values by induction, so T_i has the same
dependent arguments. Store and project x_i unchanged. For a scoped dependent
family apply the argument under its original binder; for a sum preserve the
tag and complete selected arm; for an opaque declaration preserve the full
application object and its entire arguments. The suffix consequently remains
in the same fiber. An equality field is stored as its actual proof and is not
replaced by refl. Repeat under each original binder without reordering. QED.

## 7. Conservative interpretation, reflection and full registry observers

### 7.1 What is preserved before and after sealing

Recipes are checked under a symbolic final-registry parameter p. Their
interpretation is then at p=P_old^src. This preserves the original guard/
license/domain expression and complete argument map. It does **not** assert
that a guard true at an earlier prefix registry stays true at P. Prefix
registries are not used to type/evaluate semantic validity in this design.

For example a local guard `lookup(p,k)=Absent` is formed symbolically. At
final P it is true or false according to that exact lookup. If k was emitted,
its fiber is empty. Static source formation still exists. This is permitted
because registration is static, not a semantic SharedContract or a successful
check. This design makes no `H_oldext` theorem about active untagged extension.

### 7.2 Conservative and reflective theorem relative to the direct judgment

Interpret F_src of §5.3 at the same constructed registry P. Local semantic
clauses are the original functions/predicates at the exact full tuple
`(P,S,B,X,T,xi,live-world/event/other declared fields)`. Staged expressions
interpret by substituting that same P and the decoder's exact field records.
All substitutions of X/xi values occur under their original dependent binders;
P contains only their syntax. In-row field applications use §4.1's available
arguments. A full typed registry observer is applied after B on both sides,
so this comparison does not give an early row an unconstructed decoder.

**Theorem CR.** At P, every direct pre-Call guard/domain/license/consumer
fiber and its staged counterpart are the same dependent fiber. Complete
solution-and-observation records of this fragment map in both directions by
the field-preserving constructor maps of SR/T. This holds for arbitrary
well-typed full-registry observers, including absence and all-key quantifiers.

**Proof.** SR identifies the retained source formation records with the same
direct constructors. T identifies each complete ordered telescope field at
the same preceding values. A local predicate/operation on either side is
then the same original function at the same P and complete tuple. For a
registry observer, lookup/domain/decoder are the specified operations on
this identical P; DC retains that full argument rather than a filtered
approximation. Hence every guard/domain/license/consumer is evaluated on
the same object, even if nonmonotone in P. Field identity gives both
preservation and reflection of witnesses and all alternatives. No stronger
semantic law or true guard is used. QED.

CR is a conservative/reflective representation theorem for the explicit
source judgment and registry API defined here. It is not universal
conservativity over an independently fixed old registry model. Changing the
meaning/domain of an old registry sort can affect an arbitrary old observer;
entry equality alone would not prove otherwise. This note leaves that exact
foreign correspondence statement unproved, rather than disguising it as a
representation certificate.

### 7.3 Composition with the approved tagged Reify direction

Within this explicitly defined candidate the q2 tagged-registry construction
can form

```text
Pdagger = (P_old^src,N_arg,N_lit),  pr_old(Pdagger)=P_old^src.
```

The [Reify proof](2026-10-10-original-call-reify-constructor-proof.md)
§7 applies to old predicates at their actual P_old^src argument. Adding
N_arg/N_lit then preserves that whole old interpretation by unchanged
projection, including DC's FullRegistry node and absence/domain observers.
This is not a snapshot: the source registry is a static source object and
its whole lawful action transports it. Runtime worlds remain live fields
at their original event positions. Adoption is not a premise of this internal
mathematical composition. Applying it to a separately fixed original source
owner still needs the pending q3 adoption/declaration conformance and actual
remaining Reify local premises; this note does not assign them by name.

The already constructed chi_a/q_ca/source edge/reference schemas can feed
that proof's source-directed AllocateArg rules at the constructed
candidate J_a, retaining every required original local image/operation typing
law and its typed field maps. R_a alone is not J_a. Identification with a
separately fixed original ReturnImage remains an image-conformance obligation,
not a new missing image-row supplier or formal registry/lookup square.
No `RuleCall_L` declaration is used to fill it.

## 8. Whole action, substitution and domain boundaries

A legal whole action theta acts on S/B/X/T/xi, source versions/occurrences,
every original declaration token and complete schema, each source resolution/
scope/reference derivation and all endpoint and event/witness/future fields.
Nominal source renaming is injective and capture-avoiding. Endpoint
substitution may be noninjective; it cannot merge nominal source keys.
This is the same whole-action boundary used by the Reify proof §6 and
Source Generalize's original local laws. It does not assert arbitrary
semantic maps are lawful.

Define theta on recipes by acting on their source/declaration fields and
rebuilding the same constructor tag. On a source key act only on its nominal
source occurrence/role; roles remain fixed. Seal acts on the whole vector:

```text
theta(P_old^src(S)) = P_old^src(theta S)
lookup(theta P,theta k) = theta(lookup(P,k))
decode_(theta P)(theta k) = theta(decode_P(k)).
```

**Theorem A.** These equations hold, including exact absence under bijective
nominal renaming, all binder/license/guard/future fields, and identity/
composition. For domain-changing actions they hold on the transported
source fragment and declared local interface domains, with exactly the
original action's domain/observation coverage laws when semantic universal
transport is claimed.

**Proof.** Source role expansion commutes constructor by constructor with
source renaming/substitution; it never inspects endpoint equality. Injective
nominal renaming preserves key uniqueness. Seal stores the acted-on vector.
Lookup is finite nominal selection, so Found selects the corresponding acted
recipe; under bijective renaming external absence is reflected as well.
For a merely injective source embedding, absence is preserved only for
queries inside its transported image; extra target-source keys can alter
absence at other queries, so no full-domain reflection is claimed.

Decoder commutation follows rank induction. The original primitive/entry/
Return action equations rebuild the corresponding local formations, and
the earlier decoded premise commutes by induction. The formal Desc remains
before the challenge; receipt/Force/rebind order and source role remain
fixed. Name follows the acted resolve_f to the same acted formal. Result
and Image use their same acted Data/Result and complete clauses. T's
telescope induction transports every dependent suffix with its predecessors;
equality proofs are acted on as proofs. A full-registry observer receives
theta P and its whole transported API, not an old saved P. Its semantic
transport is exactly its original local action law, not monotonicity inferred
from entry retention. Thus no universal target-demand coverage follows merely
from positive witness transport.

Identity/composition follow constructor induction from the original local
action identities. No witness/functions are compared extensionally. QED.

Aliases are source references to the existing k_f, so monomorphic reuse
cannot introduce a second descriptor/event binder. A finite imported binding
can be added as a distinct Import recipe retaining a supplied **whole local
declaration schema**, its actual source capture edge and earlier declaration
key; this needs its own explicit rank when the imported source formation is
not primitive. The present theorem has Empty captures and does not assume a
completed imported Reg. Recursive source registration/Code formation requires
simultaneous symbolic registration and the selected recursive local laws;
strict rank B does not prove that case. State, operations with unresolved
local laws, annotations and arbitrary completed Lambda/Call rows are likewise
outside this pre-Call fragment. These exclusions bound the theorem, not the
language's acceptance or natural inference behavior.

## 9. What has been constructed and what remains open

| Obligation | Result in this NEW candidate |
| --- | --- |
| Actual ordinary formal reg_f | Constructed from Parameter/Value-entry, not granted |
| Formal old key/payload/lookup/decoder square | Explicit nominal k_f, recipe, exact selection and complete decoded reg_f |
| Source bootstrap q:Code(P) | Seal recipe syntax first; terminating ranked decoding then forms q at that same P |
| Actual Name/literal pre-Call spine | Constructed q_cf, q_a, o_a, q_ca, chi_a at the actual occurrences |
| Ordered binder/scope/license/guard/evidence preservation | T/SR/CR retain entire local schemas and final P argument; no guard truth manufactured |
| Exhaustive entry coverage | E for the explicitly defined pre-Call role domain and finite local declarations |
| Actual pre-Call consumer dependency closure | DC from complete typed expressions; whole P retained for arbitrary registry observers |
| Source-owned old J_a/J_f | Constructed from whole local primitive/Name and Return/prefix clauses; independent fixed-image identity remains unproved |
| Approved q2 new tags | Composition available with this candidate P; old whole interpretation unchanged by pr_old |
| Independently fixed original registry representation | No equality/correspondence asserted; candidate adoption/realization remains open |
| Opaque original declaration using later/self typed arguments | Whole declaration retained, but earlier application not derived; exact source-owner/declaration conformance remains open |
| Complete invoke/Call emission, O0/O1 and complete slot inventory | Not constructed by this pre-Call theorem |
| C0/admission, solving, inference/principality, export, publication and F5 | No new closure or authority |

The construction has therefore moved the one-formal representation cut
**within this explicit source-owner candidate**: its header, port declarations,
registration and lookup/decoder are constructed, not supplied. The largest
completed fragment of its displayed constructors is the seven-row pre-Call
spine. The selected source notes alone do not prove every opaque original
declaration conforms to its raw-p argument presentation. That exact remaining
conformance boundary is separate from the constructed registry and is not
closed by the rank lemma. Extending the candidate to a completed
invoke registry needs the actual complete Call formation rules, not more
rows declared by fiat. q3 remains a genuine adoption decision.

## 10. Verification and commit-ready packet

Producer checks are mechanical and do not certify the mathematics. The primary
obtained separate independent mathematical and specification reviews, accepted
their initial findings, and assigned one fresh researcher the batched repair.
The original frozen revision
`e5ace463964b407815aa57d19eae3a6ccfada4542ad79d976d55808f1f28beed`
had an accepted major typing dependency defect and a minor missing Name-image
traversal clause. This batched repair counts all field-type arguments,
provides the explicit NEW owner interfaces and their formation lemma,
postpones full typed registry consumers, emits both images, and defines SR
specialization of the immutable original choice family. It also separates
raw source/context syntax from actual X/xi valuations. Both fresh independent
delta reviews passed on frozen SHA-256
`b6a8680bdb1589ac6f0b4a06c7db62d1797d98f6437e1061ccc5a08b7395044c`.
The [review record](../progress/2026-10-10-original-registry-construction-review.md)
states the exact candidate/contextual-family scope and the primary's
metadata-only integration changes. Producer repair is not self-certification.
No producer code, test, build, solver execution, checker, runtime source probe,
Git mutation or question-board edit was performed. Primary Git integration is
recorded separately. There is no finite model
enumeration masquerading as all-domain evidence. The proofs share genuine
local primitive semantics and the explicitly NEW owner definition; they are
not independent production correspondence evidence.

Read/check resource envelope: sequential bounded source reads; at most one
lightweight shell process at a time; no heavyweight process. Direct dependency
hashes and baseline/current equality, relative file links, fence balance and
whitespace were checked on the frozen artifact. Repository-wide foreign
kernel search and production conformance were not attempted. Any truncated
combined source read is not used as sole evidence for an unread section;
the focused governing sections cited above were read separately.

Commit packet:

* Exact path: `notes/theory/2026-10-10-source-owned-original-registry-construction.md`.
* Baseline: `d0f62c3bd97b11bc9eb6b46390a2cf1d9702a861`.
* Claim/review status: repaired constructive research candidate; fresh
  independent mathematical and specification delta reviews PASS; no
  authoritative or aggregate theorem-gate promotion.
* Proposed checkpoint message: `research: construct staged source-owned registry for invoke pre-Call spine`.
* Shared-record deltas deferred until immediately after the proof checkpoint:
  primary updates `tasks/current.md` and `notes/design/INDEX.md` with the
  reviewed candidate and q3 adoption/conformance boundary, retaining full
  Call/image/local-law/inference/cutover residuals. No canonical DAG closure
  is proposed here.

### Direct semantic dependency SHA-256 snapshot

All 18 direct semantic dependency files below match the pinned baseline's
recorded hashes at repair freeze. Policy reads and task navigation supply no
mathematical premises. The primary reports that HEAD advanced by an inspected
unrelated fast-forward to `c32ff7c0980e8844803cc7638cfdc34b06900a51`;
the producer's text checks revalidate these direct dependency bytes, without
performing Git operations or claiming an independent audit of that range.

```text
850a6a035d0e4b6ad3be761205d24c51b4b894fcc5e795c4dc30415e529c5a30  notes/design/2026-10-10-call-reify-construction-direction.md
795afb2c2204731becc770e2e7d05c309881db2d9e8e6fc89fb5614533857716  notes/theory/2026-10-10-selected-source-p-old-construction-attempt.md
6d382a248ad7f1c4bbcf7b14231f21448e957640d96b35e7efec333bc019e564  notes/theory/2026-10-10-original-call-reify-constructor-proof.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240  notes/theory/2026-10-08-source-generalize-definition-and-proof.md
b8bdf720e50bcfab691f70c08fee8cb32fb2b34f3817099faba512378ebdcb24  notes/theory/2026-10-09-native-id-original-wholearg-construction.md
f7c1b1eb23acb33ab98487097ab67617e1af84964b012874b1c951a8805dd9f6  notes/theory/2026-10-07-call-input-construction-proof.md
0b86e367cf8170f4f9d095f0afe8e9f6003209189dc358e294941727962ff110  notes/design/2026-10-07-original-call-owner-definition.md
9841aebaf56bd862c0301c9ca9436035cf0ab8263f1772aff81241d4c4b61da2  notes/theory/2026-10-07-call-owner-construction-proof.md
0c5c58022c6834651fedff6c14d8cdf96002831c0c2d25292843abbae64d3924  notes/theory/2026-10-09-original-literal-result-owner-extension-candidate.md
547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed  notes/design/2026-09-29-scc-intrusion-redesign-charter.md
0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e  notes/design/2026-10-02-typed-computation-core-elaboration.md
fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a  notes/theory/2026-10-08-call-semantic-input-realization.md
1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186  notes/design/2026-10-05-source-contracts-and-common-allowance.md
e6c6cf995a3618172e45b4f8cdf4578313c057c6ec1e3e118c4dc11b6f162ab9  notes/design/2026-10-08-native-signature-formation-definition.md
7367ce8eb69376583386c6d675d067712ec6fa173e96f458ee34ce390dc8901a  notes/theory/2026-10-08-source-signature-incidence-construction.md
0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0  notes/design/2026-10-08-contextual-function-membership-definition.md
06e81fcc5b5d8f3cbf23edf6e343b81cc17c12874aaeb8c0ec42cd3136c519ba  notes/theory/2026-10-10-original-literal-call-emission-construction-attempt.md
4e21b99e486ae949bd9fd10f1573690d4b882a77c0e376ca4a57551271f5eddd  notes/theory/2026-10-10-native-argument-registration-extraction.md
```
