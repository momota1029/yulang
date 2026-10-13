# Source formal-port declaration proposal

Date: 2026-10-13
Status: Draft; not adoption ready for the actual original invoke application
Scope: structural source-owned ParameterOrigin and entry-port introduction
Baseline: `research/simple-sub-intrusion@040a05a187e513b2ad4f59cddc257491fa0a45e2`
Prepared-by: primary from architect `construct_source_formal_ports_declaration`, including its scope/order repairs
Reviewed-by: independent spec_auditor and compiler_referee; dependent-output and substitution repairs passed fresh delta review
Approved-by: none
Implementation / actual original source application / F5 authority: none
Supersedes: none

## 1. Responsibility and preserved source meaning

The Parameter owner introduces source identity, the ordinary flexible Desc,
intrinsic root/port addresses and static entry declarations. Entry-Value
consumes those declarations. Actual argument checking, Receipt, Force,
Return/rebind, body and invocation Return require their own evidence at their
original scopes.

For `my invoke f = f 1`, `L,f,u,c,a` are the actual Lambda, formal, resolved
Name, Apply and literal occurrences. Identifier spelling supplies no identity.
Declaration ownership supplies no later semantic witness or stronger license.

The core source rule has no RawRegistry, Reg_src, typed decoder or pending
candidate-inventory premise. The adopted old-component adapter has its own
route-specific conformance gate. The genuine complete source/Entry/Call
semantic requirement and native correspondence remain OPEN.

## 2. Concrete structural inputs and addresses

At the actual Parameter scope, propose these structural source-data types:

```text
v       : SourceVersion
C       : SourceComponent(v)
L       : LambdaOccurrence(v)
f       : FormalOccurrence(v,L)
sigma_f : ParameterTypeScope(C,L,f)
deps_f  : PriorDependencyTelescope(C,L,f,sigma_f)
src_f   : UnannotatedValueFormal(v,L,f,sigma_f,deps_f)
cap_f   : CaptureSource(L,Empty)
```

Their intended inhabitants are the actual source records and binder
inclusions; they assert no program success. NEW header equation:

```text
SourceFormalHeader :=
  (v:SourceVersion;
   C:SourceComponent(v);
   L:LambdaOccurrence(v);
   f:FormalOccurrence(v,L);
   sigma:ParameterTypeScope(C,L,f);
   deps:PriorDependencyTelescope(C,L,f,sigma);
   source:UnannotatedValueFormal(v,L,f,sigma,deps);
   capture:CaptureSource(L,Empty))

h_f = (v,C,L,f,sigma_f,deps_f,src_f,cap_f)
```

The selected Parameter rule supplies its complete original dependencies:

```text
A_f    : ValueDescriptorAt(sigma_f,deps_f)
desc_f : Desc(C,f,ValueEndpoint,sigma_f,deps_f,A_f)
```

Empty captures imply no empty effect/profile/world or dependency telescope.
Proposed intrinsic source addresses retain the bounded registry's nominal
owner convention, without requiring that registry to be constructed:

```text
k_f       = (v,(L,f),Formal)
r_f       = FieldRoot(k_f,FormalValue)
r_in      = FieldPort(k_f,ReceivedWholeCarrier)
r_receipt = FieldPort(k_f,Receipt)
r_force   = FieldPort(k_f,DesignatedEntryForce)
r_rebind  = FieldPort(k_f,RebindResult)
```

NEW `IntrinsicValueEntry(h,A)` retains those five addresses, the source Value
entry mode and actual annotation absence. Address sorts declare source
incidence; they assert no inhabited carrier/event or Function shape/purity.

## 3. Independent original semantic signature

Use cumulative predicative universe levels appropriate to each original
field. A type-valued field raises its containing universe. The original
declaration supplies its actual binder tree. At each node `b`:

```text
Gamma_b = Gamma_original, Ancestors(b)
Gamma_b |- T_b : U_(ell_b)
```

All original arguments, scopes and quantifier kinds remain in these literal
types. Universal response/future nodes, proof choices, alternatives and
recursive interpretation retain their original constructors. This proposal
selects no fixed J/provider/carrier/world order.

Direct original typed families are permitted. For example, an original
carrier signature can supply, at its actual full predecessors:

```text
Gamma_car |- Carrier_orig : U_i
Gamma_car,t:Carrier_orig |- Car_orig(t) : U_j
```

`Gamma_car` contains the original root/provider/J/event and every other
operand at its original position. This is a required signature input, not an
instantiated invoke declaration. Receipt, Force and Rebind likewise need their
literal complete declarations and applicable genuine local laws. They retain
the same carrier/port/receiver, current or resumed world, returned value/provider,
operation instance, response domain, raw continuation, unfinished suffix and
compatible futures.

These independent families may have empty fibers. Their formation supplies
no semantic witness or complete-correctness certificate. Schema-term
elimination is one optional representation when an original signature
actually supplies it; it is not a source requirement.

The [open C_J package](2026-10-13-open-typed-carrier-interface-proposal.md)
may form at an actual J predecessor from independently typed declaration and
argument families. Its [formation lemma](../theory/2026-10-13-open-declaration-package-formation.md)
supplies no inhabitant, original-domain equivalence or coverage theorem.

## 4. Proposed static constructor and its actual gap

The shared input retains the complete dependent argument family. Choose
cumulative predicative levels `h0,a0,d0,i0` for the displayed header,
descriptor, Desc and intrinsic-address families respectively; set
`b0 = max(h0,a0,d0,i0)`. NEW shared base:

```text
SourceFormalHeader : U_h0
ValueDescriptorAt(h.sigma,h.deps) : U_a0
Desc(h.C,h.f,ValueEndpoint,h.sigma,h.deps,A) : U_d0
IntrinsicValueEntry(h,A) : U_i0

Base : U_b0 :=
  Sigma h:SourceFormalHeader.
  Sigma A:ValueDescriptorAt(h.sigma,h.deps).
  Sigma desc:Desc(h.C,h.f,ValueEndpoint,h.sigma,h.deps,A).
  IntrinsicValueEntry(h,A)
B = (h,A,desc,intr) : Base
Gamma_static(B) = Gamma_static(h,A,desc,intr)
```

`ScopedSchema(Gamma)` denotes finite retained declaration syntax: each
complete field type with its predecessor context, original binder/alternative
constructor, full explicit/implicit operand expressions and source-scope
references. It carries genuine type formation, not a semantic success law.
For the actual finite input signature choose `s0` above every retained
field-type universe level (including the rise for type-valued fields), and
`q0` sufficient for its original scope-map family. These bounds do not erase
or equate the original field levels. The four tags refer to the already
specified intrinsic ports:

```text
PortTag : U_0 := {in,receipt,force,rebind}
address(B,j) = B.intr.j
Schema(B) := ScopedSchema(Gamma_static(B)) : U_s0
Scope(B,T) := SchemaScopeMap(T,SourceBinderTree(B.h)) : U_q0
p0 = b0
r0 = max(b0,s0,q0)

SourceParameterDecl : Base -> U_p0
SourcePortDecl : (B:Base) -> PortTag -> U_r0

SourceParameterDeclared :
  (B:Base) -> SourceParameterDecl(B)
SourcePortDeclared :
  (B:Base) -> (j:PortTag) ->
  (T:Schema(B)) -> (s:Scope(B,T)) -> SourcePortDecl(B,j)
```

`SourcePortDecl(B,j)` retains `address(B,j)` through its index; `j` is a
port tag, not a replacement untyped address. These NEW structural families
have only the displayed constructors. They are wrappers of the input
records, not the independently fixed original ParameterOrigin or port types.
For each port, the input must be its actual complete original static schema
application. NEW constructor telescope:

```text
Delta_in : U_r0 :=
  (B:Base;
   T_in:Schema(B); s_in:Scope(B,T_in);
   T_receipt:Schema(B); s_receipt:Scope(B,T_receipt);
   T_force:Schema(B); s_force:Scope(B,T_force);
   T_rebind:Schema(B); s_rebind:Scope(B,T_rebind))
```

Each schema retains every original ancestor and static license argument.
No event inhabitant is needed to declare its type. For `mu:Delta_in`, write
`B=mu.B`. NEW structural constructor types and equations:

```text
parameter_origin : (mu:Delta_in) -> SourceParameterDecl(mu.B)
parameter_origin(mu) = SourceParameterDeclared(B)
owned_port_j : (mu:Delta_in) -> SourcePortDecl(mu.B,j)
owned_port_j(mu) = SourcePortDeclared(B,j,mu.T_j,mu.s_j)

intro_formal_ports : (mu:Delta_in) ->
  SourceParameterDecl(mu.B) *
  SourcePortDecl(mu.B,in) * SourcePortDecl(mu.B,receipt) *
  SourcePortDecl(mu.B,force) * SourcePortDecl(mu.B,rebind)
intro_formal_ports(mu) =
  (parameter_origin(mu),
   owned_port_in(mu),owned_port_receipt(mu),
   owned_port_force(mu),owned_port_rebind(mu))
```

For any motive level `m0`, the dependent eliminators retain these indices
and every constructor argument; their beta equations are structural only:

```text
M_parameter : (B:Base) -> SourceParameterDecl(B) -> U_m0
k_parameter : (B:Base) -> M_parameter(B,SourceParameterDeclared(B))
elim_parameter :
  (M_parameter:((B:Base) -> SourceParameterDecl(B) -> U_m0)) ->
  (k_parameter:((B:Base) -> M_parameter(B,SourceParameterDeclared(B)))) ->
  (B:Base) -> (p:SourceParameterDecl(B)) -> M_parameter(B,p)
elim_parameter(M_parameter,k_parameter,B,SourceParameterDeclared(B))
  = k_parameter(B)

M_port : (B:Base) -> (j:PortTag) -> SourcePortDecl(B,j) -> U_m0
k_port : (B:Base) -> (j:PortTag) -> (T:Schema(B)) -> (s:Scope(B,T)) ->
  M_port(B,j,SourcePortDeclared(B,j,T,s))
elim_port :
  (M_port:((B:Base) -> (j:PortTag) -> SourcePortDecl(B,j) -> U_m0)) ->
  (k_port:((B:Base) -> (j:PortTag) -> (T:Schema(B)) -> (s:Scope(B,T)) ->
    M_port(B,j,SourcePortDeclared(B,j,T,s)))) ->
  (B:Base) -> (j:PortTag) -> (p:SourcePortDecl(B,j)) -> M_port(B,j,p)
elim_port(M_port,k_port,B,j,SourcePortDeclared(B,j,T,s))
  = k_port(B,j,T,s)
```

These declare ownership only. They introduce no inert license, contribution
permission, C0, actual Receipt, completed Force or live authority.

For the actual source:

```text
B_f = (h_f,A_f,desc_f,intr_f)
mu_f = (B_f,
        T_in_f,s_in_f,T_receipt_f,s_receipt_f,
        T_force_f,s_force_f,T_rebind_f,s_rebind_f)
```

The source suppliers of the four components of `B_f` are identified. The
genuine original schema applications and source maps are **not supplied**
here. Thus `mu_f:Delta_in`, equality with an independently fixed original
ParameterOrigin and the actual original entry application remain OPEN.

## 5. Ordered entry, actions and dependency traversal

Original Entry-Value consumes the authentic original ParameterOrigin and four
complete original ports to declare Receive ->
Receipt -> one source-designated argument Force -> same-result typed Rebind ->
body -> invocation Return. Body binding retains `r_f,A_f`; actual Rebind needs
the original Return/result-check evidence for that same decorated value and
provider in the Return's current world. Consumption of the NEW structural
wrapper outputs requires independently established genuine typed introductions
or maps into those original input families, retaining the complete dependent
arguments. Those introductions/maps and the actual original application remain
OPEN; the structural constructors and eliminators alone do not supply them.

Request retains its operation, dependent response domain, raw resumption and
ordered unfinished suffix. Resumption uses its actual resumed world. Static
declaration produces no event witness.

For a genuine typed original context substitution `rho:Gamma' -> Gamma`,
assume the original substitution actions supply these contextual typing
judgments for the complete retained inputs:

```text
Gamma  |- B=(h,A,desc,intr) : Base
Gamma  |- j : PortTag
Gamma  |- T : Schema(B)
Gamma  |- s : Scope(B,T)
Gamma' |- B[rho]=(h[rho],A[rho],desc[rho],intr[rho]) : Base[rho]
Gamma' |- j[rho]=j : PortTag
Gamma' |- T[rho] : Schema(B)[rho] = Schema(B[rho])
Gamma' |- s[rho] : Scope(B,T)[rho] = Scope(B[rho],T[rho])
Gamma' |- address(B,j)[rho] = address(B[rho],j)
```

The families at `B[rho]` on the right are interpreted in `Gamma'`, with
all their contextual parameters substituted. The action on `s` includes the
original action on `SourceBinderTree(h)`. The address equation requires the
applicable original intrinsic-address action. These genuine typed actions
remain external input premises; this proposal supplies no original semantic
law. The four structural tags are fixed by substitution.

The NEW wrapper action is ordinary metatheoretic substitution of the entire
contextual typing derivation into `Gamma'`. In particular, substituting the
constructor applications and all their premises gives:

```text
Gamma  |- SourceParameterDeclared(B) : SourceParameterDecl(B)
Gamma' |- SourceParameterDeclared(B)[rho]
          : SourceParameterDecl(B)[rho] = SourceParameterDecl(B[rho])
SourceParameterDeclared(B)[rho] = SourceParameterDeclared(B[rho])

Gamma  |- SourcePortDeclared(B,j,T,s) : SourcePortDecl(B,j)
Gamma' |- SourcePortDeclared(B,j,T,s)[rho]
          : SourcePortDecl(B,j)[rho] = SourcePortDecl(B[rho],j)
SourcePortDeclared(B,j,T,s)[rho]
  = SourcePortDeclared(B[rho],j,T[rho],s[rho])

rho*(Sigma x:T. B) = Sigma x:T[rho]. rho+*B
rho*(Pi x:T. B)    = Pi x:T[rho]. rho+*B
```

These equations express substitution of the NEW constructor syntax under
the given original typed action premises. The internal dependent eliminators
in §4 operate within their own typing context; this argument does not apply
an eliminator in `Gamma` to a motive containing operands available only in
`Gamma'`.

The lifted map fixes the new binder and substitutes its predecessors;
alternatives retain all branches and shared witnesses. Applicable original
primitive action laws remain inputs. No endpoint equality merges owners or
proof choices.

Compute retained Delta from finite typed schema syntax: start from every
constructed origin/port field type and incidence expression; traverse every
application operand and implicit typed argument, binder domain and alternative;
record each referenced actual introduction and traverse its type/dependencies.
Process each syntax/reference node once with a visited set. An imported
primitive retains its token and complete application arguments; semantic
inhabitants are not enumerated.

The output is the induced original dependency graph, retaining shared
introductions once, each ancestor position and branching event scopes. An
unavailable operand fails formation rather than being omitted. Body/Apply
demands are introduced by their later owners; a reference to an unavailable
later body declaration has no Parameter-prefix application. No fresh
effect/profile operand or empty/pure Delta is selected here.

## 6. Exact residual and review boundary

The first actual application not supplied by this pass is the original
carrier declaration's typed source application:

```text
Gamma_source,OriginalPred(car)
  |- theta_car : Gamma_source,OriginalPred(car) -> Gamma_car
Gamma_source,OriginalPred(car)
  |- Carrier_orig[theta_car] : U_i
```

The actual incoming carrier must inhabit that type, or the original owner
must provide its genuine typed same-carrier incidence map. This Draft
introduces no conversion or substitute carrier sort. Receipt/Force/Rebind,
body and complete Call obligations remain open after this input.

The structural equations are separately reviewable new definitions; they
supply no unknown original typed application. Invoke use of the canonical
id/pick inlet would also be a new extension requiring compatibility and
complete supported-domain coverage. No fixed new binder order or source
restriction follows from this Draft.

Mode M3: compiler_referee for predecessor typing/licenses/operational
incidence; spec_auditor for authority/inlet scope/old-route separation. Resolve
all accepted major findings before presenting any genuinely new decision.
**Adoption as the actual original invoke declaration is not ready.**

Actual source substitution, original domain coverage, primitive laws and
native semantic correspondence remain OPEN. No implementation, complete
source acceptance, theorem closure or F5 cutover follows. This text uses
static checks only; zero tests, builds, semantic probes and measurements.

## Governing inputs

- [Inference principles](2026-10-11-yulang-inference-top-level-principles.md).
- [Source Generalize definition](2026-10-08-source-generalize-definition.md).
- [Uniform inlet](../theory/2026-10-08-uniform-value-entry-constructor.md) §4.
- [Original Entry input](../theory/2026-10-07-call-input-construction-proof.md) §3.2.
- [Registry adoption](2026-10-10-original-registry-constructor-adoption-proposal.md) §§1–3, for its optional route only.
- [Registry dependency correction](../progress/2026-10-13-old-registry-production-proof-edge-retirement.md).
- [Checked-inlet field cut](../theory/2026-10-13-checked-inlet-field-formation.md).

## Primary review and consumed handoff

The M3 conformance review passed within this Draft's declared structural
scope. Semantic review found an omitted predecessor context in the proposed
output families and eliminators. The repair retains the full
`B=(h,A,desc,intr)` index and every schema/scope argument, and explicitly
requires authentic original introductions/maps before original Entry-Value
can consume these structural wrappers. Fresh delta review closed those
findings and identified a separate substitution error: a target-context
family was used as a motive for a source-context internal eliminator.

The focused substitution repair now substitutes the complete contextual
typing derivations metatheoretically. It displays both source and destination
judgments and retains the genuine original action premises. A fresh independent
`compiler_referee` delta review passed with no remaining findings at frozen
SHA-256 `e911d49fda4ecf99b54269507df818589bfd9d0a719917f7e901cc95b596f0b1`.
That hash precedes this primary-owned review metadata. One earlier delta
reviewer inadvertently made a read-only Git diff call outside its no-Git
packet; it produced no output or mutation. The final reviewer made no Git calls.

The primary consumes these results only as formation and substitution of the
NEW structural wrappers given their complete typed inputs. The original
carrier-domain declaration/application in §6, authentic port schemas and
source-to-native semantic correspondence remain unsupplied. The separately
reviewed [check-closure result](../theory/2026-10-13-check-closure-compatibility-proof.md)
derives endpoint insertion and displayed activated compatibility, not those
inputs or exposed-arm readouts. Neither result establishes actual invoke
adoption, original L4, complete Call, inference soundness/principality or F5
replacement. Static link/fence/whitespace checks passed; zero tests, builds,
semantic probes and measurements were run for this Draft.
