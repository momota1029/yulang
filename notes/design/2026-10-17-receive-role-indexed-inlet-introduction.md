# Original c2: candidate whole-inlet introduction and provider-indexed roles

Date: 2026-10-17  
Status: **Draft; unselected candidate clauses and bounded preservation result**  
Author: `/root/receive_role_indexed_inlet_introduction`; sole author, no descendants  
Sprint: `receive-role-indexed-inlet-introduction-20261017`, contract revision 1  
Contract SHA-256: `c2422818a92a6666ab9672b45d4d8bf1abf069116c82d4a91228374fc07e10cc`  
Supersedes: none. No semantic adoption, implementation or theorem certification.

## 1. Result and exact parent

This packet expands the predecessor's `SharedComponent` and inlet instruction
into explicit **candidate core formulas**, their source operands, and
their dependent binding positions. It constructs a syntactic inlet expression
and a graph of the actual provider's role/entry metadata. It does **not** prove
that those formulas are the original complete inlet of F2. That identification
is a semantic obligation, not a consequence of native Function allocation.
The first precise choice is whether universal designated-execution typing at
the incoming ports is already required by that inlet, and whether it and the
independently fixed contextual guards exhaust the inlet. It could add a
restriction, or miss an original relational clause. Neither inclusion is
established; the alternatives below are unselected.

Keep:

```text
receive(f : Unit -> alpha+) = let g = f(Unit) in g(Unit)
alpha+ = ([ctrl]Unit) -> [ctrl]Int
c1 = f(Unit); c2 = g(Unit)
g: original result binder r_b_g, endpoint A1
c2: original F2 at sigma2, Delta2; checked invocation target Comp(E2,A2)
xi = (nu,K,D), jointly shared at all original incidences
```

The parent remains FORWARD-FIRST-CALL §§1–2 at
`notes/theory/2026-10-16-first-call-joint-forward-preservation.md`, SHA-256
`f71cc442bcccb23f7e6f1aa6221b089abb8c24d1c4ce01fecef37995541c16b6`.
Its local forward conclusion is already reviewed under MODEL. This packet
addresses the independent c2 context/formation seam; it neither reopens that
conclusion nor proves MODEL existence. Universal alpha, every original A1
value, actual decomposition/capture, compatible punctured context, current
world, pending response/raw continuation and finite future remain unchanged.
The displayed alpha+ is the contracted example, not a replacement quantifier.

## 2. Stage 1: actual operands and candidate introduction

### 2.1 Source operands, before interpretation

Use the original resolved Apply occurrence q=c2, its Name(g) occurrence n,
argument occurrence a=Unit, local binding identity r_b_g, and original native
demand/argument/result/effect addresses. Write `B_in(theta)` for the expression
`Comp(E_in(theta),A_in(theta))` at **F2's original incoming computation ports**.
Theta assigns the already declared descriptive coordinates and their original
dependencies. It is fixed before a hypothetical g value or challenge is chosen.
This notation creates neither fresh endpoints nor equality with c2's outgoing
`Comp(E2,A2)`. Port address correspondence alone does not establish the complete
semantic interpretation of B_in.

The source introduction has these concrete inputs:

1. `Apply(q,n,a)` and the resolved `Name(n,Local(r_b_g))` records, with their
   original scopes and component endpoint incidences.
2. The source argument's actual ground-Unit constructor and its original
   effect and Delay/reify incidences. This supplies a diagonal carrier instance,
   not the whole inlet's domain.
3. The declaration/definition/use graph at these incidences: the f annotation,
   c1 result and Bind target A1, the Name(g) use, and c2's ordinary unsolved
   component bounds. A1 remains its original endpoint. The graph is not
   interpreted as restricting the hypothetical g input to c1's reachable image.
4. The existing independent semantic kernels for full computation typing,
   licensed inert-carrier formation, designated execution, compatible context
   and finite future development. These are generic original meanings, **not**
   a completed I2, L2, role package, R2, IF2, WF_Dec, VIncl or Q. Each opaque
   primitive keeps its actual complete local contract; an unavailable contract
   is an open input, not a default true predicate.

Items 1–3 determine the source addresses and the fixed SAT/RG expression forms
without evaluating q or solving constraints. Expanding every guard reference
and interpreting the formulas requires item 4. In particular,
retained source metadata alone does not certify the whole contextual guard
inventory in item 4 at arbitrary c2.

### 2.2 Expanded whole-carrier candidate

For notation, h is an original punctured challenge environment, k its registered
whole carrier, and e its current event. All shared evidence coordinates are
explicit components of theta and the original dependent h/k tuple. Conjunction
evaluates on that one tuple; it does not existentially choose a separate
context/world/provider witness for each conjunct. Existing description witnesses
stay before challenges, and existing event-proof witnesses stay below their
actual events. Writing T_B as a predicate does not move its original binders or
identify residual/provider lineages. The following abbreviations refer to
existing independently interpreted primitive sorts, with their full tuples:

- `G_q(theta;h,k)`: the conjunction of original hole registration and incidence,
  independently valid other bindings/current world, scope and capture validity,
  typed argument/receipt/receiver paths, profile/licensing preconditions, and
  the original ordered continuation/context compatibility clauses. Include
  every applicable primitive's actual contextual clause at its original slot.
  It omits tested callable membership, actual-provider acceptance/output safety
  and Q. It does not assert that a receipt transition already happened.
- `Form(k;e)`: independently licensed inert formation with the actual carrier
  object, captured environment, scope and reify/primitive license. The alternatives
  are the original carrier formations, including independently licensed ones
  without a source Delay witness.
- `Dem(k,h)`: every independently admitted designated execution demand of k
  in h, with its response, raw continuation and finite future tree. It is fixed
  before testing the formula below.
- `Obs(k,delta)`: the original complete observation universe at that carrier
  and demand, including complete/pending/administrative/zero-step actual
  observations, admitted developments, and all independently licensed
  production alternatives with their original full tuples. It is fixed before
  testing T_B, and is not the source execution image or a success-filtered set.
- `T_B(delta,O)`: full original computation membership at B, including its
  dependent value/provider, request/response, world, latent/future, path and hard
  envelope fields. It is not merely effect support or four-port compatibility.

The candidate equation is:

```text
HC_B(k,h) := Form(k;e_h)
            and forall delta in Dem(k,h).
                forall O in Obs(k,delta). T_B(delta,O)

I_sat[q,theta](h,k) := G_q(theta;h,k) and HC_B_in(theta)(k,h).       (SAT)
```

This supplies an explicit universal whole-carrier clause. It does not take
HC or I_sat at this incidence as a certificate premise. The formula is emitted
while unsolved; its satisfaction is a later obligation. Its free inputs are
the original incoming endpoints and listed primitive contracts. In particular,
it does not accept a desired full inlet as an input under another name.

`G_q` is a conjunction construction, not permission to invent an unspecified
new guard. To instantiate it, every conjunct must have its original primitive
owner/operand occurrence. IF-Insert/IF-Use can place those actual clauses;
neither supplies missing clause meanings. A missing inventory or owner blocks
the claim that this is a *complete* inlet. No complete R/IF is constructed here.

All independently admitted divergent/requesting/resumed carriers remain in
the quantified universe. SAT admits each exactly when its **whole** original
contract meets the displayed predicates. It does not test only actual Unit,
require a Return, require source-generation evidence for O, or quantify over
only carriers accepted by the tested provider. A pending observation has no
fabricated return value. Extra Option 2 observations retain their original
complete predicates in T_B and Obs.

**Admission boundary.** The current carrier/challenge/observation universes are
retained verbatim as the ambient domains of these formulas. SAT proposes a
predicate on them; it does not replace the selected original admission
predicate. In particular `HC_B` is an extra proposed requirement until an
original inlet constructor proves it. If an originally admitted retained-entry
carrier lacks the demanded universal T_B property, SAT excludes it and is too
narrow. A computation that will not be forced at entry cannot acquire such a
property merely from that fact. Conversely, missing original correlated guards
can make SAT too broad. No `D_in(F2) subseteq I_sat` or reverse inclusion is
claimed. No existing carrier is rejected by this unselected research proposal.
`Dem` is never reduced to successful executions or observed source demands,
and no proof-producing source derivation is required of its members.

### 2.3 Source-built role/entry relation

Write `Act(v,U,p)` for a genuine decomposition of the same decorated value v
with provider U and root p. Write `role(U)` and `entry(U)` for that decomposition's
existing actual metadata, not new runtime queries or metadata inferred from a
type. If an external provider's contract does not supply that projection, its
correspondence is open; no default metadata is assigned.

Construct a graph of source occurrences with these local equations:

| Actual source constructor | Generated relation or retained edge |
|---|---|
| Actual closure/definition | Retain the role and entry supplied by **that** original closure constructor, its true formal identity, captures and body. No generic definition is assigned Pure without its owning law. |
| Formal registration | Retain `(owning Lambda, real parameter, annotation occurrence, entry classification)`. Outer computation annotation selects retained entry for that Lambda; ordinary value entry is its other selected case. This says nothing about the role of a callable stored in the parameter. |
| Name/immutable alias/capture | Retain the same binding value and every genuine Act decomposition; route the metadata projection of that same value through the original typed map. Do not merge description endpoints or witnesses merely because values agree. |
| Bind result | Under the actual Return, route the returned decorated value/provider into its original result binder. For the punctured suffix, retain the *hypothetical* binder variable without demanding a preceding actual c1 Return. |
| Call use | Retain callee, argument and incoming-port incidences and emit ordinary use constraints. No role equation is generated from argument shape or comparison success. |

At original c2, the Name/Bind graph therefore gives this provider-indexed
relation, with n and r_b_g referring to one hypothetical value v:

```text
RoleGraph_2(v,U,p;rho,mode)
  := Act(v,U,p) and rho = role(U) and mode = entry(U).               (RG)
```

The original Name/Bind incidence equations accompany RG; they are not erased
by its short display. Existing annotation/definition metadata equations remain
at their own source nodes. There is no extra c2 equation `rho=Pure`,
`mode=ValueEntry`, or `mode=entry(f's enclosing Lambda)`.

RG is deliberately a graph over every actual decomposition. It is not
`exists rho,mode; forall v ...`, which would impose one actual mode on a
possibly heterogeneous A1. Nor is it an independent per-port selection.
It supplies indices for a proposed role-indexed descriptor family; it does
not itself construct that family's body, observation or membership clauses.
The shared inferred relation consists of this graph and the *same* component
constraints on theta/xi. At c2 the graph is neutral about which role occurs.
It does not pretend to solve the separately required provisional
Handler/NonHandlerFormal inference rule.

### 2.4 The local generation clause and unsolved constraints

The proposed rule, marked as unselected, is now finite syntax construction:

```text
original Apply/Name/Bind/argument/declaration incidences at q
original typed port declarations and their scopes/dependency edges
original primitive clause references at those incidences
---------------------------------------------------------------- GEN-INLET-ROLE?
emit at the original F2:
  the expression I_sat of SAT;
  the component incidence graph and provider-indexed expression RG;
  original ordinary endpoint/effect/use constraints, still unsolved.
```

In particular retain the callee-use obligation at original A1/F2, the
argument-to-incoming-computation obligation, invocation/result obligations
at original E2/A2, and enclosing residual/world/profile joins. Generating an
ordinary native bound is not proving its full VIncl or CIncl interpretation.
No local satisfiability precheck, execution, alternate typing search or
early successful comparison is inserted. Levels, extrusion, qualifying
intrusion, accumulated constraints and ordinary Generalize retain their roles.

**What is constructed:** the displayed symbolic formulas and their operand
graph. **What is not implied by existing selected rules:** their designation
as F2's complete inlet/role interpretation. The mandatory obligations are:

```text
SAT2: D_in(F2;theta,xi) = { (h,k) | I_sat[q,theta](h,k) }
RG2:  F2's role-indexed clauses use RG on the same actual (v,U,p)
      and all original correlated theta/xi coordinates.
```

These are proposed identification laws, not emitted constraints whose
assertion makes them true. The descriptor owner must prove them for the fixed
meaning or obtain adoption of the exact new meaning. No WF_Dec is concluded.

## 3. Stage 2: telescope, domains and the exact semantic choice

### 3.1 Binder/record audit

The candidate uses the original dependent telescope; it adds formulas, not a
chosen provider, actual role or future Return at the outer F2 scope.

| Field or binder | Owning record and position |
|---|---|
| Original source occurrences, r_b_g, q, paths, static slots | Original intrinsic/incidence references. A source path is not a dynamic receipt. |
| Existing incoming/outgoing endpoint declarations | Their original `Desc(C,q_i,sort,sigma_i,Delta_i)` records, if introduced by their actual inference owner. No classification is inferred merely from a native term's sort. F2 retains sigma2/Delta2. |
| Installed imports/captures, prior boundary evidence | Original Established/Mono/Shared/OneShot dependencies as applicable. No new shared witness is created by calling a relation “shared.” |
| SAT and RG | Derived description expressions referencing those records; no additional existential role or inlet witness. |
| Hypothetical g value v and Act(v,U,p) | Bound by the original punctured context/provider quantifiers. On an actual c1 Return the matching rebind is EventField at that event. No such runtime event is manufactured for the hypothetical suffix. |
| h, whole k, current event, receipt operands | Original challenge/event telescope; dynamic fields are EventField. The independently formed description precedes them. |
| delta and O in SAT | Universal dependent semantic domains below h/k. They are neither generalizable Desc variables nor chosen actual executions. |
| Value-entry result a,p_a,C' | Only under the actual Force Return branch; original EventField incidence. A logical proof of its typing, if introduced by a checking rule, is EventProof below that event. |
| Computation-entry binding | The retained same k and current event, with its actual formal binding only when that provider supplies one. No Force-result binder exists at entry. |

Every free coordinate of SAT is in its incoming port declarations or original
guard/kernel references. Every free coordinate of RG is in the source incidence
graph or provider telescope. Thus the candidate expressions are scoped **when
those original operand records are supplied**. This is a local syntactic
well-scoping result, not an audit certificate for missing complete F2 fields.

In particular r_b_g is the callee binder, not the callee's parameter. There is
no real parameter identity to introduce from c2's Local(g) Name. A later actual
provider may supply its own formal, or an opaque entry operation without a
source formal; both retain their original contracts. A descriptive binder for
an entry result is not permission to synthesize a fake HirParameterId.

### 3.2 Provider membership and Option A/Option 2

The selected contextual membership meaning has the order:

```text
one original description assignment theta, xi;
forall v in the original A1 domain;
forall genuine Act(v,U,p);
forall independently admitted challenges h,k of the checked descriptor;
actual U accepts that same k, and every complete/pending/future observation
satisfies the complete observation contract at the same joint tuple.
```

This is an obligation, not a conclusion here. RG exposes actual metadata under
the second universal quantifier. SAT's admission uses no U-acceptance premise.
A descriptor may inspect registered hole metadata through its original
independent guard, but cannot admit only challenges on which U succeeds.
Keeping those two layers separate prevents a vacuous membership construction.

Option A fixes full typed observations and independent admission. Option 2
does not require all observations to have source constructors. Neither selects
SAT2, nor proves that incoming computation typing contains every needed
correlation. RG does not filter out any genuine provider; the later body and
observation constructor must still cover all applicable role/entry branches.
No W/Z grammar or exhaustive joint DescMem representation is selected here.

### 3.3 Exact alternatives for adoption or refutation

The candidate's unresolved equations have a concrete discriminant:

| Unselected completion | Relational equation | Observable consequence and required evidence |
|---|---|---|
| Whole-carrier saturation | `D_in(F2)=I_sat` | Every original-context-compatible carrier satisfying full B_in is an admitted challenge. Membership must ensure acceptance and complete behavior for all of them, including independently licensed non-source cases. Prove all original inlet clauses follow from SAT; endpoint shape is insufficient. |
| Additional original correlation | `D_in(F2)=I_sat and Psi_q(theta;h,k)` | A carrier can meet the same incoming computation endpoint and visible guards but fail a separately justified dependency/authority/provider correlation. Psi must be expanded at its actual source/primitive owner, with its complete telescope and actions. It cannot be a new opaque completed inlet or chosen after Q. Any actual behavior difference requires review/adoption. |
| Original admission does not require HC_B | Keep `D_in(F2)=D_original(F2)`; do not adopt SAT2 | A witness `D_original(h,k) and not HC_B(k,h)` refutes the forward inclusion into SAT. The original entry/consumer contract, not a successful source designation or a changed challenge universe, determines whether such a carrier is admitted. Its existence at c2 is unproved; this option records the precise narrower-behavior risk. |

For example, a whole-interface clause can correlate a carrier's retained latent
provider with a context-owned provider, while both satisfy identical marginal
value/effect endpoints. If that correlation is not already a conjunct of G_q
or full B_in, SAT admits both matching and mismatching tuples; the correlated
equation distinguishes them. This is a **logical discriminating configuration**,
not evidence that such a clause occurs at c2, and not a proposed new restriction.
If the correlation is already in G_q/B_in, the two equations coincide for it.

For roles, RG keeps every actual role/entry graph point. The unprovided bridge
must give a complete descriptor family at those points. Choosing one shared
actual role before v would exclude a heterogeneous A1 assignment if one is
independently permitted; choosing ValueEntry from Unit would change entry
behavior. Value entry forces the whole carrier before the body; retained
Computation entry binds the carrier and delays execution to its designated
consumer. A divergent/effectful carrier and a body that ignores the parameter
distinguish those entry rules whenever independently admitted. No claim is made
that such a provider is realized by this particular source. These differences
explain why neither replacement is selected.

## 4. Stage 3: local actions and the preservation attempt

### 4.1 Description substitution is constructible

Let mu substitute well-sorted endpoint terms at the existing Desc binders,
capture-avoidantly and with their whole dependency telescope. Define its action
recursively on SAT/RG: substitute every incident endpoint/guard operand; retain
intrinsic origins; retain Established/OneShot fields; act once on the shared
component tuple; alpha-rename only bound h/k/delta/O names to avoid capture.
Do not substitute actual provider/receipt/response identities with endpoint
terms. Every alias routes to that one description frame.

For an assignment theta' to the target terms, direct expression substitution
gives

```text
I_sat[mu](theta';h,k) = I_sat(theta' composed with mu;h,k),
RG[mu](theta';v,U,p;rho,mode) = RG(theta' composed with mu;v,U,p;rho,mode).
```

Proof: apply substitution to each listed conjunct; binders are dependent
universal binders, so their domain expressions are substituted at the same
time as their bodies. Both sides evaluate the same original primitive on the
same whole tuple. No observation is chosen or discarded. This is evaluation
of the *candidate syntax*, not a transport theorem between independently
fixed world/admission kernels or arbitrary satisfying descriptions. It does
not assert that a previously satisfying theta stays satisfying after an
arbitrary term replacement.

Application at c2: the original incoming ports can be instantiated jointly
without changing r_b_g, A1, F2, xi or the provider quantifiers. No need exists
to allocate one inlet/role witness per port or challenge. SAT2/RG2 remain
unproved, so this substitution result does not become F2 preservation.

### 4.2 Event graft and later-event restriction

For a legal source event graft, use the original key
`(event origin, actual parent path, occurrence)`. Map all incident runtime fields
once to that event; retain one actual U/k/world/continuation tuple. At a Value
Force Return, append exactly the actual rebind/body/invocation suffix and put
its result binders below Return. At a Request, retain the raw handle and actual
resumed world; append only the unfinished suffix. Retained entry binds k and
has no eager Force/rebind-result branch. These are the selected source entry
actions applied to the candidate's indexed fields; no full body descriptor is
supplied by this action.

There is a concrete restriction action on an already supplied original future
tree. If b is a lawful finite development from h to h', map a tail delta' to
the concatenated development `b;delta'`. Restrict a universal SAT certificate
by evaluating its old strategy there; use the original suffix/observation
restriction action on the same raw handles and provider fields. On that
subtree, every new quantified branch is an old branch with a fixed prefix,
so universal coverage is preserved. Receipt/path/authority guards are checked
at h' using their original compatible-event actions; static identity cannot
revive expired authority. Unknown State transitions supply no instance of this
action. No universal foreign-context law follows from this subtree argument.

### 4.3 Why forward maps alone do not prove arbitrary graft preservation

For an independently changed event/kernel, preservation needs a typed lifting
of **each new demand and observation** to an old one, together with the actual
guard and full T_B actions. Schematically, for every new delta',O' there must
be an old delta,O with the original complete tuple action producing delta',O',
or an independent constructor proof for the new case. A mere forward map from
old challenges proves no such coverage.

The logical falsifier is finite: old demand set `{d0}`, new demand set
`{d0,d1}`, forward map d0↦d0, with T_B true on d0 and false on d1. The old
universal clause holds and the new one fails. This is a countermodel to the
*forward-map-only inference*, not a source-qualified counterexample and not
a claim that an allowed Yulang substitution has these domains. It shows the
exact extra law a purported unrestricted transport proof must exhibit.

Changing method from syntactic substitution to this domain-coverage test
exposes a genuine remaining premise rather than another Generalize wrapper.
At c2 no complete original challenge-lifting constructor for the proposed
SAT/RG bridge has been supplied. Actual fixed-domain subtree restriction is
available only with its original event laws. F1/FK1 and independently supplied
foreign continuations remain independent quantifiers.

### 4.4 Generalize is downstream

After a real owning rule supplies the complete active clauses and their local
laws, the selected Build/ScopedClosure/allocate rules retain these formulas
with their actual classifications. Desc eligibility still follows the fixed
dependency walk. Shared remains once; ViewLogic, if later introduced by a
description-checking rule, remains once per incoming frame; actual event fields
remain shared at one event; EventProof may vary only below that same event.
No new initializer/provider is executed by instantiation.

This gives no new Generalize theorem and no actual publication event at F2.
The absent SAT2/RG2, complete guard inventory and unrestricted primitive
transport cannot be obtained from Generalize's L1–L5 premises by inversion.

## 5. Stage 4: original c2 application and source evidence

At c2 the candidate can emit SAT over the original incoming ports and RG over
the original hypothetical g binding. Unit contributes its actual carrier
construction; it does not prove every guard or whole-inlet compatibility.
The selected original first-call inclusion `S_alpha subseteq S_A1` provides
neither a converse nor `S_A1 subseteq S_F2`. Actual c1 returns cannot replace
the universal A1 input required for the open suffix.

| Required original premise | Outcome |
|---|---|
| First local inlet/role syntax | Explicit candidate SAT/RG and source-incidence generator supplied. Complete semantic introduction is still open at SAT2/RG2 and the original guard inventory. |
| Complete R/IF and joint WF_Dec(F2) | OPEN. Strict consumes real I/R/IF and fixes Pure/ValueEntry; it is not the general c2 constructor. |
| Actual membership, including all genuine decompositions | OPEN; RG preserves indices and proves no acceptance or observation safety. |
| VIncl(A1,F2), every original A1 value | OPEN, distinct from local formation and actual trace membership. |
| Whole-inlet compatibility | OPEN; the diagonal Unit derivation does not prove SAT2 or all original contextual conditions. |
| Complete invocation-image CIncl to Comp(E2,A2) | OPEN, including every pending/raw/future and independent alternative. |
| Enclosing Bind/residual/world/import/profile/path joins | OPEN; no marginal witness assembly or lineage collapse. |
| Source T, anchored MODEL, principality, production/cutover | OPEN; no code or implementation authority supplied. |

The following are **read-only code facts**, not execution or full source/native
correspondence:

| Owning symbol | Exact evidence and limit |
|---|---|
| `HirSourceIdentity::record_parameter`, `record_inline_parameter`; `LocalSourceExpr`, `LocalSourceParameter` | Parameter identity has an actual source owner. Source expressions, local bindings and parameter records are distinct retained objects. |
| `emit_candidate_source`, Lambda registration at `candidate_source.rs:593` | `FormalRegistrationInput` retains owner/Lambda/parameter/scope; its `FormalRole` is Value or Computation according to the formal's outer annotation effects. This enum is not semantic Pure/Handler. |
| `emit_candidate_source`, formal Name at `candidate_source.rs:650`; local Name at `:968` | Only `LocalSourceResolution::Parameter` creates a `FormalNameInput`. Local Name routes through `Action::Link` or `Action::Local`; it is not a formal by spelling. |
| `emit_candidate_source`, Apply at `candidate_source.rs:980` | Stores original callee/argument/effect/result/occurrence inputs and `formal_name` from the authenticated formal-use map. The experimental scoped path explicitly refuses a Local callee there; that route supplies no c2 theorem. This is a code-path limitation, not an authorized source restriction. |
| `candidate_call::observe`, `CandidateSourceCall` | Validates original Apply/Name/parameter identity and native port shape. The formal route requires a Name resolving to that real parameter. The `(None,None)` case does not synthesize a formal. Original Local(g) therefore has no supplied callee-formal identity through this API. |
| `CandidateSourceCall::pending_construction` and `OriginalGenCall0Input` | Expose pending complete construction inputs including ArgumentInterface/CompleteDemand/Delta. Their enumeration is not construction or validation of SAT2. |
| `FreshUse`, `RetainedFreshUseMaps`, `capture_candidate_graph` | Retain structural scope/row/term/effect/context/evidence maps. Their existence does not prove complete admission lifting or preservation of SAT/RG. The full returned-function route is left to Luna's separate trace. |
| `RuntimeProgram::from_hir`, Lambda arm at `runtime/program.rs:382`; closure dispatch at `runtime/machine.rs:693` | Runtime ParameterRole comes from the actual Lambda annotation. Value dispatch executes the delayed argument before its ValueEntry frame; Computation dispatch retains/binds it. This corroborates the entry distinction, not Pure/Handler semantics or arbitrary c2 source identity transport. |

No source constructor inspected emits the proposed SAT/RG formulas as complete
active descriptor clauses. No probe was run and no compiler result is inferred
from reading these branches.

## 6. Handoff obligations and falsifiers

**F2-SAT-INTRO-20261017 — source-inference/descriptor owner, Luna adjudication.**
At original F2 and its incoming ports, expand the actual contextual primitive
inventory and decide/prove SAT2 against the fixed meaning. Inputs are the
original c2 Apply/Name/Bind/argument graph, original A1/F2/sigma2/Delta2/xi and
the independently selected local primitive contracts. Output is an exhaustive
original inlet introduction, an exact additional source-owned Psi clause, or a
witness that SAT adds an inadmissible restriction, with scoped actions and any
observable difference returned for adoption.
Falsifier: a tuple admitted by the original inlet is lost (including failure
of an extra universal designated-execution obligation), SAT admits a tuple
forbidden by an original relational clause, a guard is inferred from Q/U
acceptance, or a complete desired inlet is passed as a renamed primitive.

**F2-RG-INTRO-20261017 — role-indexed descriptor/source owner.**
Use RG's universal same-provider indices to give complete role/entry branch
clauses at F2 without choosing an actual role before v. For a selected local
Lambda, use its genuine formal/entry route; for original c2 use the actual
call-result interface and provider contract. Falsifier: Local(g) becomes a
formal, an outer formal's entry is assigned to a stored callable, Unit chooses
Pure/Handler or Value/Computation, or a genuine decomposition/Option 2 arm is
removed. Complete R/IF and joint DescMem remain separate dependent work.

**F2-SAT-TRANSPORT-20261017 — same primitive owner, Generalize consumer.**
Provide original guard actions and either complete demand/observation lifting
or independent proofs for newly admitted cases at each actual legal graft.
Falsifier: the d1 case in §4.3 has no lift/proof, fixed evidence becomes a
template, aliases receive different event keys, or a later receipt reuses
expired authority. Do not reassign this to another generic Generalize proof.

**LOCAL-FORMAL-TRACE-20261017 — Luna's existing source-trace lease.**
Follow the selected returned `step` case through its actual formal identities,
capture/local-use/fresh-use maps and runtime Lambda classification. Preserve
the distinction between the returned local binder and step's parameter.
Required output is a field-level map or the first producer/consumer gap.
Falsifier: endpoint/row identity is substituted for a missing formal origin,
or runtime entry mode is promoted to semantic Pure/Handler. This requested
evidence does not assert that selected step closes arbitrary original g.

There is **NO_SAFE_CODE_SLICE** in this assignment. The inspected construction
owner `emit_candidate_source` supplies incidence/port records, while
`candidate_call::observe` consumes those records without constructing complete
admission. A code patch to enforce SAT2 would select semantics before the missing
law is established. No provisional implementation is requested merely to test
an assumed transition. After semantic selection and proof, Luna can assign
the minimum producer-to-consumer retention delta with the falsifiers above;
this note grants no such lease.

## 7. Reuse, checks and resource record

Reused within actual premises: predecessor's original c2 coordinates and
obstruction; selected contextual same-provider meaning; Strict's full entry
composition and pending branches; IF/signature incidence; Generalize's record
classification and whole-frame allocation; the original first-call result
under MODEL. Rejected as closure: source-image-only admission, actual-return
restriction of A1, Unit-derived role, formal/callee confusion, endpoint-only
acceptance, complete-field oracle premises, arbitrary forward-map transport,
Strict without operands, and Generalize as inlet formation.

Checks consist of source reads, current-byte SHA-256 comparisons, four-stage
author binder/quantifier/domain audit, the explicit finite logical transport
falsifier, and final artifact inspection. These are not independent review.
No tests, builds, source execution, executable probes, Git, external contact,
scratch files or descendants. The first hash command used unavailable `python`;
`python3` then successfully computed all hashes. No conclusion relies on the
failed command.

Requested role/model/effort: astra_prover / gpt-6-astra / medium. Observed
effective model/effort: UNKNOWN; separate opaque runtime/session ID: UNKNOWN.
Actual canonical worker and author are the header identity, current session.
ACTIVE-WORK receipt: 2026-10-17 02:10:56 UTC. Cap: four substantive stages,
840 seconds; no increase. Freeze/STOP, conservative charge and unused budget
are recorded in the exact assignment handoff. No waiting/background work is
claimed after STOP. Only this artifact and that handoff are writable.

## 8. Frozen input manifest

All 21 direct dependency hashes in the frozen sprint contract were recomputed
before reliance; all matched. The contract's exact table is incorporated as
the immutable direct manifest at the header hash. Source/proof author and
review provenance remain those of those pinned originals; no effective model
identity is inferred from historical labels. Main predecessor authors are
Luna (proposal) and `/root/receive_function_introduction_proposal_preservation`
(obstruction). Current-source authors are not identified by this read-only audit.

Additional **inherited governing authority** pins below were already present
in the predecessor dependency table and were recomputed before use; these are
not newly adopted semantic dependencies:

| Input | SHA-256 |
|---|---|
| `notes/design/2026-10-08-contextual-function-membership-definition.md` | `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/theory/2026-10-16-first-call-joint-forward-preservation.md` | `f71cc442bcccb23f7e6f1aa6221b089abb8c24d1c4ce01fecef37995541c16b6` |
| `questions/2026-10-05-production-function-denotation/approved-answer.md` | `7e7f3c717b16a70fc754c930a1654666c8b61a89a4861fca27b0ae3fa5f1890a` |
| `questions/2026-10-05-production-function-bound-membership/approved-answer.md` | `d9ddea04a44d2307cf587bc4ae9b2a1c50d062c4077306a5bf9ea9da00eca179` |

Dispatch baseline supplied by Luna: `5c386bbbf`; preparation baseline in the
contract: `b89ed524f`. Neither was inspected with Git. The present result is a
single-author candidate for fresh Luna-appointed review, not a reviewed theorem.
