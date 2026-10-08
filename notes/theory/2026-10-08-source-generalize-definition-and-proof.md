# Source Generalize: scoped rule closure and lawful-use completeness

Date: 2026-10-08
Status: independently reviewed source-rule subsystem theorem under the selected native definition
Scope: source-side Generalize for finite original source/contract graphs, relative to the explicitly listed local semantic constructors
Baseline: `7eab2767fe6d555470e7a7c5d6e728cf2d990031`
Producer: researcher; producer inspection is not independent review
Reviewed-by: fresh independent compiler_referee and spec_auditor; both PASS after the batched joint-use/recursive-anchor repair
Implementation / production resolver / aggregate gate authority: none
Definition authority: [selected native source Generalize](../design/2026-10-08-source-generalize-definition.md), under the user's current explicit authorization
Supersedes: completes the missing native source Generalize judgment; no fixed local semantic meaning is redefined

## 1. Result and claim boundary

The proposed native Generalize operation closes the **source rule program**
for an actual binding result, at its final source formation root. It retains
the program's complete scoped residual and its original runtime anchors.
It does not start with a supplied `g_b`, infer eligibility from locality,
or replace the source by an independently chosen Function relation.

Two distinct judgments are defined below. Declarative source checking chooses
endpoints and witnesses by local source rules. Symbolic source generation
constructs an open rule program from the same source occurrences, leaving
ordinary inference endpoints and permitted local choices unresolved. Legal
checking is not defined as membership in the generated program. The direct
induction proves that the two judgments coincide at their original scopes.
Closing the program then gives soundness and completeness of Generalize for
every finite derivation of that independent source checking judgment.

This class includes nonidentity result checking, structural width and union
checks, certified domain restriction, and actual locally admitted method or
adapter choices. It is larger than the PG-1 identical-kernel class. It is a
**proof-directed source class**, not all semantically valid Function views.
The theorem does not establish an effective solver for its open predicates
or show that the production `Direct` resolver accepts every source checking
certificate. These remain different obligations.

The local inventory matters. An unprovided State law, annotation realization,
method conversion, or general recursive introduction is not assigned an
arbitrary successful meaning. The theorem applies when that local constructor
has an independently specified rule and its genuine semantic law. It does
not authorize rejecting forms lacking a proof in today's selected subsystem.

## 2. Governing sources and exact prerequisites

The baseline authority was located through `notes/design/INDEX.md`; the
following actual sources govern the indicated scope:

| Source | Used contract |
| --- | --- |
| `2026-10-05-inferred-function-call-views.md`, §§1.1–5 | One source-selected joint view; fixed source slots, annotations, paths, roles, captures, original `nu,K,D`; admission independent of Q. |
| `2026-10-06-directional-inferred-effect-protection-addendum.md` | Source-scoped upper exposure and unchanged lower/provider information. |
| `questions/2026-10-05-source-annotation-boundaries/approved-answer.md`, decisions 2–3 | A boundary exports its actual target and local realization evidence; a later boundary uses that endpoint and retains earlier evidence. Individual successful comparisons do not imply a direct original-to-final comparison. |
| `2026-09-29-scc-intrusion-redesign-charter.md`, §§19–24 | Uniform generic arm, one complete packet opening, source parameter entry, guards on every derived comparison, variable-only levels, actual receiver role. |
| `2026-10-02-source-result-synthesis-choice.md`; typed core §§6–7,9 | Source synthesis and explicit consumption; same-value checking is distinct from actual conversion; complete invocation is distinct from body Result. The wider typed core remains Draft. |
| `2026-10-05-source-contracts-and-common-allowance.md`, §§2–3.3,3.7 | Independently interpreted local relation constructors, separate admission rules, complete descriptor conjuncts, and every Option 2 alternative. Its generalization/transport theorem is not an input here. |
| `2026-10-08-native-signature-formation-definition.md` | Selected source-owned port/provenance/license constructors, including complete constituent partitions and original placement. |
| `2026-10-08-contextual-function-membership-definition.md` | Same actual callable, independently formed complete challenges, and immutable binding certificates. |
| `2026-10-08-native-recursive-interface-definition.md` | Selected original two-closure interfaces and finite source prefixes; independent original leaf obligations remain. |
| `2026-10-08-captured-closure-constructor-definition.md` | Selected complete Strict entry, captured step, original source prefixes, and independent captured-callee premises. |
| PG-1 source eligibility note and RS/LX supplier | Original occurrence and lexical maps; repeated identity endpoint and captured projection endpoint. Neither supplies Generalize eligibility. |
| `2026-10-08-generalize-export-constructor-candidate.md`; `2026-10-08-pg1-generalize-direct-evidence.md` | Exact previous open `g_b`, eligible selection, complete designated root and query seams. Their conditional packaging conclusions are not premises. |

The five baseline DAG nodes have these exact relevant scopes:

- `RS_LX` supplies occurrence/lexical correspondence, not semantic eligibility.
- `PG1` supplies original projection endpoints, not an export event or all checks.
- `INTRO` requires classification and introduction scope of actual coordinates.
- `MEMBER_DISCHARGE` requires joint actual recursive member/world validity,
  including every independent CompleteMem/KV conjunct.
- `GENERALIZE` takes the complete simultaneous source relation, fixed captures,
  imports, non-generic/world coordinates and original quantifier tree, and must
  construct eligible placement, admission/reflection and lawful future coverage.

Here the subsystem premises are **local**, not that last conclusion:

**L1.** Each authentic primitive has its independently fixed typed relation,
full operand telescope, declaration/operation identity, guard, effects,
provider/future/admission laws and permitted rule schema. No `LegalSource`,
`Generalize`, `Ext`, or successful-Q predicate is a primitive.

**L2.** Ordinary source constructors use the original Return, Request, Bind,
Call, closure, delay, elimination and handler laws. The selected native
signature and closure constructors are reused. A supplied foreign constructor
needs its actual original identification; it is not defined by this proposal.

**L3.** A source checking constructor has an independently valid **local**
same-value/computation inclusion proof or actual conversion law. In particular,
a Function check must prove checked-domain inclusion and observation inclusion
on that domain for the same actual callable. No final query success is a law.

**L4.** Original initial-world, primitive, annotation/profile and recursive
introduction laws needed by an actual source derivation have their genuine
evidence. For recursion this means the actual joint original member/world
constructor, not validity of each member in a separately selected world.
The selected pair and captured-step theorems supply only their stated cases.

**L5.** Independently admitted compatible future contexts and actual lifetime
rules are those of the original constructors. Unknown State compatibility is
not inferred from immutable compatibility. All Option 2 W/Z arms retain their
actual complete law and hard envelope, including unanchored arms.

There is no assumption that the source program is principal, that every
semantic view has a finite derivation, that a generated export is adequate,
or that every substitution satisfies these local premises.

## 3. Independent declarative source checking

Fix the resolved source graph `S`, the original binder tree `T`, the original
declarations and immutable/State contracts, and one **actual initialization
event**. Let `a_b` be the event's returned value or retained carrier, its actual
provider, current world, allocation identities, source result path and existing
evidence. For an unevaluated inert definition the corresponding anchor is the
actual source closure/delay together with its fixed capture environment.

Write

```text
rho; T |- S @ a_b : R ! C [d]
```

for a finite declarative proof `d` assigning local endpoints, preserving
`a_b`, and establishing the final source interface `R` with jointly scoped
obligations `C`. This is a judgment about original source constructors and
decorated semantic values. Its definition mentions neither a scheme nor
export generation, freshening, an instance map, or Q.

### 3.1 Source constructor rules

These are the native rule schemas. Their operands are the original source
occurrences, not an endpoint-shape search. A rule with a genuine additional
primitive is added through its independent local contract, not an opaque
whole-source truth assertion.

| Rule | Independently selected fields and required premises |
| --- | --- |
| Literal / authentic primitive | Actual declaration and whole local typed relation, including all original conservative alternatives and guards. |
| Name / immutable projection | Resolved binding and the same actual value/provider; restrict its existing joint certificate. No new provider or introduction classification. |
| Record / tuple | Original field occurrences and actual shared provider tuple. Formation does not force latent fields. Fieldwise premises share the original world and dependencies. |
| Parameter | Source outer annotation determines Value or retained Computation entry. An unannotated value parameter gets an ordinary flexible value endpoint at its source typing scope. Explicit existential inference and request opening use their separate rules below. |
| Lambda | Actual role and source entry, original captures, body checking under the actual formal binding, body consumer and complete invocation. Value entry includes receipt, designated argument Force, actual Return/rebind, body and invocation return. Retained entry omits that Force. |
| Operation | Actual declaration-instance map, complete packet fields, native delimiter and declaration-derived result consumer. |
| Result | Return the same descriptor/provider in the actual current world; a known source computation is consumed by its designated consumer. A solved latent shape adds no consumer. |
| Delay / explicit inert introduction | Original computation and license; independent inert formation and universal designated execution obligations at its original typed port. |
| Elimination | One actual source-designated port/consumer and its full premise. |
| Bind / sequential local binding | Actual RHS prefix and Return/rebind; same value and current-world witness used in the suffix; original ordered pending suffix when the RHS requests. |
| Call | Original callee computation, inert whole argument, actual returned callee, current receiver/receipt, actual entry, designated consumer and invocation return. No source-side equality of body and invocation ports. |
| Branch / shallow handler | Original test/selection and ordered branches/guards, outer evaluation of guards/arms/defaults, shallow expiry, complete packet and original resumption suffix. |
| Recursive reference / introduction | Registered monomorphic roots inside the component. One actual simultaneous member/world introduction with all original local conjuncts; descriptor/source finite developments use their original least/greatest interpretations. |
| State / allocation, when independently specified | Actual one-shot allocation/update identity, installed store contract, lifetime and compatibility proof. An unresolved State law supplies no instance of this rule. |

These schemas retain source effects, full-protection and annotation permissions,
typed paths, ownership, primitive operation witnesses, receiver and continuation
identity, and the whole original `xi`. In particular the Lambda rule requires
the body proof for the independently admitted challenge; it cannot form the
challenge by assuming body safety or callee acceptance.

### 3.2 Checking and actual elaboration rules

The independent checking grammar contains the following proof constructors.
They operate at an actual source check occurrence and keep its original source
and target endpoints. They are not successful concrete query edges.

1. **Identity and logical composition of inclusion proofs.** These compose
   semantic implication proofs on the same whole operand tuple. They do not
   compose successful concrete Function comparisons.
2. **Structural checking.** Record width retains the selected actual fields;
   depth checking uses their same decorated values. Union injection and finite
   case elimination retain the actual alternative; intersection introduction
   checks the same value in both premises. Top/Any checking uses its existing
   membership meaning. Every structural child carries its complete latent
   provider and scope obligations. These rules follow directly from the
   ordinary conjunction/union/record interpretations, not effect support.
3. **Same-value / same-computation checking.** Use a finite inclusion derivation
   at the complete original interfaces; preserve the executable source graph,
   target annotation slot and receipt/evidence. `Value`/`Computation` tags are
   not exchanged by inspecting latent shapes.
4. **Complete Function checking.** Retain the actual callable. The proof
   establishes `D_checked subset D_source` and, for each checked challenge,
   `P_source(h) subset P_checked(h)` on the whole joint tuple. A narrower
   checked domain is allowed. A domain proof can restrict by an independently
   typed conjunction, structural argument inclusion, or another actual local
   challenge constructor. The observation proof can use result structural
   checking, genuine guarantee weakening, constructor congruence and finite
   original recursive equation pairing. Nonpositive children require their
   actual equality/domain proof; positivity is not guessed.
5. **Method/adapter choice.** Choose one actual registered method/adapter
   constructor at this source occurrence. Retain its code, source boundary,
   effects, full input/output relation and original evidence. A proof-only
   check executes nothing; an actual cast executes its admitted conversion.
   Distinct admitted choices remain alternatives. An unselected method law
   is not filled with a generic conversion axiom.
6. **Annotation / final formation.** Check the actual completed value against
   its written target and retain both endpoints and all local realization
   evidence. The final source root is the target when that boundary exports
   the target. The target is not replaced by an interior synthesis root.

For Function checking, the displayed inclusions are **conclusions** of the
finite local proof tree, not an inclusion oracle leaf. The grammar permits
any further independently established local constructor, with its full
premises, when it is adopted. It makes no assertion that all true inclusions
are derivable by this grammar or that the current production resolver has
every corresponding proof alternative.

### 3.3 Owning rules, declarations and event telescopes

An ordinary flexible endpoint is declared by Parameter, an annotation-hole
formation rule, or another independently specified inference introduction.
Its record is `Desc(C,q,sort,sigma,Delta)`: validating source component C,
actual introduction q, sort, original type scope sigma, and free dependency
telescope Delta. Parameter's type scope precedes the invocation challenge;
its type does not depend on an argument witness selected after entry. A body
inference declaration can be inside an invocation telescope if its owning
rule actually introduces it there. Explicit inference existentials retain
their own inference scope and guards. Request opening creates the original
rigid packet telescope once and checks a uniform arm there. Neither is an
ordinary Desc declaration. Every derived comparison uses the actual guard.

The following typed records are outputs of the indicated source rules. They
are proof/compiler construction data, not added runtime tags. A field edge
retains the target record and its complete dependent telescope. Tags are never
recovered from identifier spelling, solved endpoint shape, or Q success.

| Owning rule | Record / edge supplied at construction |
| --- | --- |
| Simultaneous recursive world installation | `MemberEntry(C,r)` with fixed raw closure/provider/allocation fields and `Internal(C,r)` for its inferred complete description/certificate. Other installed environmental entries retain `Established` edges. |
| Recursive-group registration and its resolved recursive Name | `Live(C,r)` and `Internal(C,r)` pointing to the complete joint component relation, not an environmental scheme. All recursive occurrences use its one monomorphic description tuple. |
| Parameter / inference introduction / written hole | `Desc(C,q,sort,sigma,Delta)`; references to it use `Description(C,q)`. Written constants, slot identities and annotation permissions are separate `Intrinsic` fields. |
| External immutable import/capture / monomorphic rebind | `Mono(h,Contract_h)` with `Established(h,field)` edges for the entire installed certificate, including its free descriptive, admission, latent/future and dependent evidence fields. |
| Published polymorphic Name | `Published(p,Sigma_p)` for a prior source publication, or `Family(d0,T0,R0)` for an independently typed polymorphic declaration/family. A real source instantiation produces `Instance(p,i,r)` or `Instance(d0,i,r)`. Family-bound parameters remain bound, not free import fields. |
| Alias / projection of a monomorphic value | `Alias(h,r)`; the same h and existing certificate, with no instantiation event. |
| RHS evaluation, actual conversion, allocation, role/code selection | `Executed(b,arm,tuple)` with `OneShot(b,field)` edges for the actual selected arm and complete return/world/allocation/installed-contract/evidence tuple. |
| Initializer / installed environmental evidence introduction | `Shared(p,q,sigma,Delta)`; retain its one original binder and every dependency, even when its value is not yet assigned. |
| Interface-description / logical checking witness introduction | `ViewLogic(C,q,sigma,Delta)` inside that rule's source description region; one binder per independent incoming frame, retaining its position relative to Desc parameters and challenges. |
| Lambda / Delay / handler's later source-event binder | `Event(e,parent,Delta)` and `EventField(e,q,Delta_q)` for actual receipt, response, rebind, current configuration, runtime body witness and pending continuation fields introduced under that event. |
| Body / checking certificate inside a source event | `EventProof(C,e,q,sigma,Delta_q)` for description-owned latent proof witnesses; these remain inside the original event telescope, with the same actual event operands, and may differ between independent incoming description frames. |
| Local logical checking / authorized delayed specialization | `Check(q,sigma,Delta)` / `Specialize(q,mechanism,sigma,Delta)` with their actual local proof premises. Specialize exists only when its source dictionary/template rule provides it. |

`Executed` records the actual computation, not a successful type check. A
Check can select another proof about that same execution; it cannot alter an
Executed field. Actual conversions use Executed at their source boundary.
The interface-description/checking rule introduces ViewLogic for a logical
certificate of its description tuple; initializer/rebind installs Shared for
its actual retained evidence tuple; receipt/response/body rules introduce
EventField under their Event; body/checking proof introductions use EventProof
inside that event. Operational return/response witnesses and their fixed
executed evidence are EventField/OneShot, while a proof about the same tuple
is EventProof. These are distinct constructor outputs even for
the same existential quantifier syntax. A view-owned `exists s; forall h;
exists body` therefore has one s per independent incoming description and one
body strategy under h. Its s remains below any template a in its dependency
telescope and above the challenge. Latent checking evidence is a
Check/ViewLogic/EventProof at its actual scope. A shared
initializer witness is OneShot/Shared even if its descriptor happens to be
Function-shaped. Thus these distinctions require no lifetime oracle.
An actual return of an inert own-component closure records its raw value in
OneShot, with a separate Internal edge to its inferred interface. Its local
logical membership proof is ViewLogic/EventProof, not an executed runtime
dictionary. An actual installed monomorphic dictionary/contract chosen by
evaluation records that contract as Established/OneShot, with all its free
dependencies fixed. Recursive world installation uses MemberEntry exactly
at its simultaneous owning rule: it cannot turn the current component
relation into an external established certificate by following the world's
back-reference. These field classifications apply equally to current member
and live peers in the same C.
An opaque primitive contributes its full operand telescope with the same
explicit external/shared/event field classes as part of L1; no unspecified
classification is silently guessed for it.

### 3.4 Finite clients and independent joint legality

A finite client is an ordinary resolved client source graph U, with the
constructor/checking grammar of §§3.1–3.2, together with its source-directed
binding handles. The following handle syntax makes its finite-use structure
explicit. The source lexical scope and all operands accompany each form:

```text
new(p,i,r); U       real source instantiation of published member/family r
alias(h,j); U       bind j to exactly monomorphic handle h
view(h,q,V); U      source checking/annotation at q, starting at h's root
run(h,e,c); U       source Call/Force/response/resumption at actual event e
join(U1,U2)         structural tuple/record/conjunction on a shared context
bind(x,U1,U2)       source sequential Bind with its actual pending suffix
```

These forms are annotations of actual source rules, not additional executable
operations. `new` occurs only at the source's polymorphic instantiation rule;
`alias` and use of a still-live recursive member cannot invent one. Independent
new events i and j may be different descriptions of the same actual published
provider. An alias of i uses i's single description tuple. A later lawful
publication of an alias can create a new scheme through its own source
publication rule; it is not inserted by Alias itself. A source conversion in
U has its actual independent constructor and new result handle; its input
continues to refer to the original binding object.

Write

```text
rho; T; actual(b) |- U with S_b : V ! C_U [d_U]
```

for the **independent joint source judgment**. Its defining rules are the
source rules above, with these operand conventions:

* At new, independently derive the source definition/component's description
  and final formed root for the same actual binding, by §§3.1–3.2. Ordinary
  Desc choices owned by that definition can be chosen at their original type
  scopes. All Internal edges use one simultaneous component description for
  this new event. ViewLogic binders belong to that description instance at
  their original scopes; aliases and its challenges share them.
  Established/OneShot fields and Shared binders remain the original ones.
  For an imported Family use its independently typed declaration/derivation d0
  with its original binder tree, not a test that this exporter succeeds. A
  prior source publication can alternatively supply its prior independent
  derivation in source order. This premise is a source rule derivation, not a
  Generalize,
  Build, closure-instance or successful-query premise.
* At alias and Name, restrict that very existing joint certificate. They
  retain its complete inference tuple, not just its provider key. view uses
  the independent checking rules on its actual root. An independent check
  can assert a weaker view without freshening the source description tuple.
* run uses the actual event's current configuration and history, receipt,
  provider/receiver and unfinished suffix. Event fields belong to that
  event's source telescope. References to the same actual event share them;
  distinct invocations have their own event fields. Description-owned body
  proofs may have per-frame EventProof witnesses under those same events;
  their actual runtime operands remain shared. Shared binders enclosing
  those events are not copied.
* join proves both premises in **one** scoped context; their common declarations
  and witness strategy are literally the same. bind derives the suffix from
  the RHS's same returned value/current world, or under that RHS request's
  same response/resumption telescope with its ordered pending suffix.

An arbitrary typed client predicate W can be conjoined at its original scope
on any public, fixed, instance or event fields. It may correlate different
new events and aliases. Its own logical binders and dependencies are retained.
A legal joint use is a derivation of this judgment plus W on this **one**
scoped tree. It is not a list of separately legal views. In particular,
`exists s. P1(s)` and `exists s. P2(s)` do not establish a legal join requiring
`exists s. (P1(s) and P2(s))`.

A finite derivation here can be a finite presentation of the independently
specified recursive proof grammar, with registered equation references and
local rule telescopes. Each finite development is checked by those local
rules; a recursive hereditary certificate additionally uses the genuine L4
introduction. An inclusion derivation can introduce arbitrarily many local
intermediate proof terms through such a finite grammar. The client is not
required to enumerate a fixed number of intermediates in its source syntax.
This allows a finite allocation schema below to act uniformly on every
finite development. It does not turn arbitrary extensional inclusion into
an opaque proof leaf.

A scoped strategy assigns each existential/choice at its original telescope
as a function of just its preceding universal/dependent inputs. There is one
strategy on the entire joint tree, including W. An actual history is a legal
development of that tree, with actual current configurations at each event;
it is not an independently selected world per view. Joint legality quantifies
over the independently admitted challenges/futures at the original binders,
without deriving their domain from the body or from a pending comparison.
This judgment mentions no generated program or export test.

## 4. Generate the open source rule program

Define `Build(S,T)` by recursion on the source constructors in §3.1. Allocate
one symbolic declaration per actual inference introduction, one reference
per resolved Name/recursive edge, and one symbolic **local rule-choice node**
at each independently allowed checking/elaboration choice. Repeated endpoint
occurrences refer to the same declaration. A choice node stores its actual
rule alternatives and their operand telescopes, not a Boolean promise that
some legal source typing exists.

For a fixed rule instance with premises `P_1,...,P_n`, generate the original
whole-tuple conjunction of their programs and the local rule's explicit
constraint/evidence clause. A source choice generates a union of those
instances. A source binder generates that binder around the child's program
at exactly its original position. A registered recursive reference generates
an edge to the original simultaneous equation, without unfolding.

The generated clauses are precisely primitive local relations, conjunction,
union, constructor image, scoped binding and registered references. There is
no additional `SourceTyping(S)` or `CompleteRelation(S)` atom. Source checking
constructors are similarly generated by their explicit proof grammar; an
inclusion proof variable denotes a finite derivation of those rules, never
an arbitrary extensional containment predicate.

Every node additionally retains the owning-rule records and dependency edges
from §3.3, including base, view-description and actual-event binder regions.
A union whose choice was already executed is specialized once to
that actual recorded arm at event b; that choice and its dependent tuple
become fixed anchors. Only authorized delayed choices and proof choices
remain open at a use. ViewLogic choices remain in their original description
regions; invocation choices remain under their original invocation/history
binders. Thus the program does not turn every local
inference alternative into a fresh runtime alternative per alias.

The program is intensional and finite as a source/rule schema graph when the
available local constructor catalogues are finitely presented. An open method
or provider catalogue is a fixed independently typed interface parameter,
not a closed-world enumeration and not a declaration that every method is
valid. A finite legal use supplies a finite actual rule choice from it. This
does not prove an effective finite symbolic representation for every such
catalogue or an inference complexity bound.

Every Option 2 source, W and unanchored Z alternative is generated from its
actual declared arm. Its original `G`, parameters, future-provider obligations
and independent admission clauses stay incident to the same tuple. Absence
of a source witness for Z is allowed; no reverse source-execution proof is
demanded of it. The local law of that arm remains an independent leaf.

## 5. The source Generalize event and eligible placement

An export event is the actual immutable binding publication, SCC publication,
or source boundary publication prescribed by the source. It is not every
Name lookup and not an event inferred from a successful comparison. A member
export and an actual jointly exported tuple are different events. The event
selects the **final formed source root** `R_b` by the source FinalRoot rule:
first use the actual target of the final annotation/source boundary and all
preceding realization evidence; otherwise use the selected common root if
an actual common formation exists; otherwise use the complete synthesis root.
A conversion executes only at its actual source boundary and fixes its actual
resulting provider; later checks operate on that result. The final target is
never replaced with an earlier Lambda or computation synthesis root.
Its complete `D_b,M_b`, ordinary
descriptor membership, admission and original residual belong to that root.

### 5.1 Publication-indexed dependency closure

Let p be the publication event and C its actual validating source component.
C is provided by recursive-group/definition registration. A member publication
p_f and a joint tuple publication p_fg can select different roots while using
the same component C. Define fixed closure by a typed walk with two modes,
`retain` and `fix`, using exactly the records of §3.3:

1. Seed retain with the actual whole component relation and selected final
   root(s), source slots, original scope/provenance records and constraints.
   Seed fix with the actual binding/provider identities, OneShot initializer
   tuple, external Mono/Established contracts, intrinsic declarations and
   actual world/allocation/lifetime fields. Shared records seed their **one
   retained original binder**, not a fresh existential per use.
2. A fix edge to an Established, Intrinsic or OneShot record traverses its
   complete dependent fields in fix mode, including free description fields,
   latent/admission/evidence/provider dependencies. The separate Internal
   description field of MemberEntry/own returned closure follows rule 3
   even when its raw provider was reached in fix mode; it is not an
   Established field. Dependency on a Desc
   declaration therefore marks that declaration fixed. A bound parameter
   inside Published(p0,Sigma_p0) or an independent Family is not free: retain
   that closed scheme/family and
   follow only its actual free anchors. When a prior scheme has already been
   instantiated to Mono(h,...), fix traverses the instantiated contract and
   its free fields; copying its original scheme would be a different rule.
3. In retain mode, Description(C,q), and in either mode Internal(C,r),
   traverse the **entire**
   joint component relation in retain mode. Internal recursion is not an
   Established environmental edge. All current members and live peers in C
   receive this treatment. Raw same-component provider identity is fixed as
   an operational object, but its separate relation edge is Internal, not
   Established. A Description reached through an actual Established/OneShot
   contract dependency is still fixed by rule 2; Internal traversal does not
   undo that mark.
   Desc fields owned by another component, when referenced as external Mono
   operands, are traversed by rule 2. In both modes external fixed edges are
   followed by rule 2. The walk never drops a relation or a conjunct.
4. A ViewLogic record retains its binder inside the original description
   region, below its Desc dependencies and before any enclosed challenge;
   each incoming frame gets that region, while aliases share it. A Shared
   record retains its binder, telescope and dependencies once. Fix
   any free Desc field in its established dependent contract, as in rule 2.
   Event/EventField/EventProof records retain their original event binder and
   exact dependency telescope; they are not promoted into p's outer free-variable
   set. Check/Specialize records retain their original proof grammar, scope,
   mechanism and premises; actual executed subfields still use rule 2.
5. Eligible declarations are exactly the ordinary `Desc(C,q,...)` records
   reachable in the retained source program which the fix walk did not mark.
   Introduce a template for each at **its original type scope** with all its
   dependencies and original constraints. Inference existentials, rigid
   openings, operational identities and logical Shared/ViewLogic/EventField/
   EventProof witnesses are never template declarations. Cyclic Internal edges are visited once
   as registered graph edges. Eligibility is a constructor test plus a finite
   dependency walk, not a guess from component-wide free-variable occurrence.

Fixing a field means sharing its existing assignment or original binder, not
asserting that its contract has a ground printed type. Every constraint to a
fixed field remains active. A Shared binder's witness is chosen once in the
joint interpretation at its original scope; it cannot vary with later i,
challenge or history unless that variable is in its original telescope.
No initializer, role choice, cast or allocation is repeated by a type view.
Descriptions/checking certificates of an actual execution can vary only at
their marked source scopes, retaining the one actual trace/evidence tuple.

The walk is indexed by p,C. It does not relabel a prior external capture as
own merely because traversal returns to a familiar provider. Provenance is
produced at the owning rule. A value can have fixed operational edges and
schematic description edges simultaneously; their different typed fields
have different construction responsibilities.

### 5.2 ScopedClosure and its explicit finite-use operation

Let N_b be the retained complete program, including the component relation,
fixed closure, original binder tree T and final root R_b. Define the stored
closure constructor

```text
Generalize_source(S,b)
  = ScopedClosure(p,C,T,anchors_b,templates_b,N_b,R_b).
```

It contains the rule graph and its binder/edge classification, not a named
promise of future safety. Interpret a finite client through the following
**allocation judgment**, selected before assignments or histories:

```text
G_b; U; E |- allocate m : J_m(U,W)
```

E is a finite source checking/elaboration proof grammar over the local rules
of §3.2, with its original telescopes. m consists of the finite client handle
map, template declaration map, original/shared binder incidences, event binder
routing, local proof-grammar nodes and final-root incidences. A supplied E
need not already be valid: its local clauses are checked in J_m. Allocation
is syntax directed by these rules:

| Client / record | Allocation rule |
| --- | --- |
| new(p,i,r) | Open one **whole component** N_b frame indexed i. Give every eligible declaration its `(i,q)` occurrence at the translated original scope. Internal edges refer to this one frame. Select member r's final root, keeping all background/member conjuncts. The source type-scope node precedes its challenge subtree. |
| alias(h,j), monomorphic Name, same instance reused | Route j and every occurrence to h's same frame/declarations/binders. Do not open N_b again. |
| Established / OneShot / Intrinsic / Shared | Reference the original field or the original single binder in the shared base tree. Conjunction never copies that binder. If a constraint has operands in several frames, its scope is its original shared client scope, with just its legal dependencies. |
| ViewLogic | Allocate one binder in its incoming frame at its original description-region position. Preserve its whole dependency telescope, including template declarations preceding it. All aliases/challenges of that frame share this binder. |
| Event/EventField | Graft its local telescope under the **actual source event constructor**. Its key is `(original event origin, actual parent event path, event occurrence)`. Aliases referencing that event route to the same key; new actual events have distinct keys. Actual runtime body witnesses are shared for that event. A fixed initializer event routes to the base tree, not to a new i. |
| EventProof | Allocate `(i, actual event key, q, original proof-region path)` under the original event telescope. Share actual runtime EventField operands; retain per-description latent certificate witnesses and their dependencies. No OneShot/Shared binder is copied by this rule. |
| Check / Specialize | Graft the actual finite local proof grammar at its source check or authorized specialization scope, with all operands. Each introduced intermediate has the owning rule's scope and dependency telescope. |
| join / bind | Conjoin children on the same declared context; glue the actual Return/rebind/current configuration or Request/response/pending suffix fields. No independent worlds are existentially joined. |
| W | Append the unchanged W at its original scope, using those same field incidences. |

The declaration map can contain endpoint **terms** in the client scope, not
merely constants. They must have the declaration's sort and dependency
telescope. The map is fixed before evaluating those terms. To interpret a
finite recursive proof grammar, allocate its nodes/edges once; each binder
introduction at a finite unfolding uses the deterministic key `(node, incoming
frame, event/proof unfolding path)`. Recursive references reuse registered
equation operands. The rule determines fresh local proof intermediates and
event fields uniformly without enumerating all finite unfoldings in m. Shared
keys never acquire an unfolding suffix; template keys retain their frame i.
EventProof keys have both frame and actual-event incidence: distinct
certificates of a shared actual invocation do not duplicate its runtime
response, configuration or continuation. These keys are constructor paths,
not a lookup on a subsequently observed execution history.
ViewLogic keys are `(i,q,original description-region path)`; their
pre-challenge witnesses are chosen once per frame, not once per unfolding or
challenge. No rule consults a solution, successful query, or future history
to choose a key. An allocated E preserves all its actual local premises
and recursive interpretation; it cannot manufacture a recursive inclusion/introduction law.

J_m is a concrete scoped graph of original primitive clauses, source
constructor clauses, local checking clauses, conjunction/union and the
original binders/references, with the allocation above. Its satisfaction is
ordinary **global scoped evaluation of these clauses** (§4): one assignment
and one strategy on the glued tree, respecting every telescope and actual
configuration/history transition. It is not defined by joint source legality.
`Sat(J_m;v,s)` means every active clause and W is satisfied under that one
strategy s and public assignment v; universal challenge/event branches use
their independently fixed domains. Thus it explicitly excludes separately
chosen Shared witnesses or histories for separate uses. m describes a finite
schema even when this satisfaction quantifies over arbitrary finite source
developments and future contexts.

There is no admission/observation marginalization. Omitted formatting fields
remain in this one original scoped package. Any semantic hiding still needs
its separate original-scope certificate. The allocation here constructs
source clauses and joins; it is not a Pack/Decode or alpha-transport theorem.

### 5.3 Recursive pair, external capture and publication lifecycle

For the selected pair `my f x=g; my g y=f`, registration gives one C,
`Desc(C,x)=A_x`, `Desc(C,y)=A_y`, live roots f,g and Internal edges in both
directions. The complete relation is

```text
F_f = Strict(I_x,x:A_x, Comp(empty,F_g), IF_f)
F_g = Strict(I_y,y:A_y, Comp(empty,F_f), IF_g)
```

with the original full interfaces, world and independent CompleteMem/KV
conjuncts, not just this displayed skeleton. Its selected native introduction
is used under its genuine background/guard inputs. The exact walk results are:

| Publication | Fixed records | Eligible ordinary descriptions | Retained relation |
| --- | --- | --- | --- |
| Member f at p_f, component C | Actual f,g closures/providers, installed world and intrinsic external background, original one-shot/shared evidence and all their free dependencies | A_x and A_y, unless an actual external/one-shot dependent field constrains them into the fixed closure | Whole two-root relation, selecting final F_f |
| Member g at p_g, same C | Same fixed records | Same A_x,A_y by the same walk | Whole two-root relation, selecting final F_g |
| Actual joint tuple at p_fg | Same fixed records plus actual tuple/provider and source formation evidence | Same A_x,A_y; tuple formation itself adds no Established edge | Whole relation with the actual tuple's final formed root |

In the bare selected pair there is no external contract containing A_x,A_y,
so both are eligible at each of those publications. Within one incoming frame
i, every recursive f/g reference uses that same `(i,A_x),(i,A_y)` and relation.
Another independent source new event can choose a different lawful pair of
descriptions, with the **same actual closures**. No member is separately
validated in a newly chosen world. Different member views can be correlated
by client W; an alias of a single incoming frame cannot select another pair.
Joint tuple formation does not itself introduce type equality A_x=A_y.
Any final annotation/common formation root and its retained checks replace
the selected public root in this example according to FinalRoot, never the
complete underlying relation or the actual providers.

For a genuine external monomorphic capture, let `my k x=z` capture established
`Mono(h_z,Contract_z)` with result field B. The fix walk follows Contract_z
through admission, provider and future/evidence fields: B and every free
Desc dependency of that contract are fixed. Its own `Desc(C_k,x)=A_x` remains
eligible unless one of those fields actually depends on it. Capturing an
externally monomorphic callable h works the same way, through its **whole**
contract, not just its printed ports. Capturing `Published(p0,Sigma_p0)` or
independent `Family(d0,T0,R0)` fixes
its actual anchors and scheme identity while retaining its bound parameters;
a source new from it creates its lawful fresh frame, whereas capturing a
previously monomorphic instance fixes that instance's free description fields.

Before SCC publication, Live(C,r) is monomorphic in the one validation tuple;
internal recursion performs no new. Publication closes the eligible
Desc declarations, installs Published(p,Sigma_p), and retains the raw runtime
objects and original fixed package. Later resolved recursive edges inside
N_b remain Internal. Later external Name uses see Published or an actual
Mono instance according to the source rule that created their handle; they
cannot reclassify those edges from provider identity. This is the explicit
live-to-published transition, with no production implementation claim.

For `my apply f={my step x=f x;step}`, local step publication sees the actually
rebound formal f as external Mono and fixes its full contract. The outer
publication retains this dependent step formation **under the original outer
invocation event**. The outer formal's Desc declaration is at the outer type
scope before its challenge; its instantiated value/certificate is supplied
by the actual entry/rebind, never by a new inner f. This distinction lets the
outer description vary lawfully while every returned step shares the same
captured f within its actual event. A nested executed prefix is not relocated
to an outer initializer, and a stored initializer witness is not moved under
a later step invocation.

## 6. Direct rule-adequacy lemma

**Lemma SRC.** Evaluate the open program `Build(S,T)` using its independently
specified local clauses and original scopes. For every assignment/evidence
strategy, the following are equivalent:

```text
the program has that complete original-scope solution
iff
there is an independent declarative source derivation of §3
with precisely those source operands, endpoints, choices and witnesses.
```

The equivalence preserves final formed root, actual `a_b`, original binder
dependencies, admission and complete observations. It does not concern Q.

**Proof, construction to source.** Inspect the outer source occurrence and
its generated clause. A literal/primitive clause is its authentic local rule
with the same complete witness. A Name clause has the original resolved root,
so its premise is the existing binding certificate for the same provider.
A record clause gives all original field premises on their shared tuple.
The Parameter clause retains its source tag and declaration; the body clause
then checks under that binding. Lambda applies the actual closure constructor
to that body proof and its fixed captures. The body is not substituted for
entry: the complete source clause still has Force/rebind/body/return and
every pending suffix. Operation and elimination use their actual declaration
and consumer operands. Result keeps the actual provider/current world.
Delay uses its two separate original obligations. Bind takes the actual RHS
prefix, returned value/current state or pending continuation, and supplies
those same operands to the recursively obtained suffix. Call takes the same
actual returned callee and inert carrier, then its receiver/entry/consumer;
it cannot choose a callee from the checked type. Branch and handler take the
actual selected source alternatives and their original outside contexts.
An allocation clause uses the one anchored actual state transition. An
initializer or conversion clause is a proof of the single retained actual
execution trace/prefix at event b, with the same actual returned value. Its
choice, allocation and return witnesses are fixed by that clause's lifetime
index. Reading this proof at another type assignment is another certificate
of that execution, not another execution or a new returned object. A delayed
method choice must use its actual retained specialization mechanism. The
definition contains no operation replaying an initializer at a use.

At each checking node the generated rule tag and all premise proofs select
exactly the corresponding independent rule of §3.2. Structural width does
not recreate discarded fields; union retains its actual alternative;
intersection uses the same value twice. Same-value checking changes its
asserted contract, not the provider. A Function node's domain and observation
subproofs establish the two inclusions at that very root; by the selected
same-callable meaning, every checked-admitted challenge is admitted by the
source contract and its actual developments meet the checked contract.
Method/adapter nodes contain the actual conversion constructor and its
independent law. Final-formation nodes yield their recorded target root.
There is no case turning endpoint coincidence into a typing rule.

For source recursion, source occurrence recursion creates a finite equation
graph. A finite prefix/membership development uses finitely many recursive
rule unfoldings, so the argument above is induction on that development.
For hereditary descriptor/world introduction use the actual original
simultaneous introduction constructor, with its independent immediate leaves
and fixed challenge domains. No own-member validity is added as a primitive.
Its source equation references and all CompleteMem/KV conjuncts remain in
the same node. This uses L4 at the existing constructor seam; it does not
prove all general recursive introductions from finite source syntax.

At a logical binder, evaluate premises under its original legal assignments.
The rule has that same telescope and supplies its witness under precisely
those dependencies. Thus an `exists shared; forall challenge; exists body`
subtree gives one shared witness and its dependent body strategy; the
induction never exchanges them. The four admission constructors separately
retain initial context, typed response to its original request, original
raw handle, and future use of the actually returned provider. A divergent
carrier supplies prefixes without Return. Option 2 arms use their own local
law and guard, including Z without a source anchor. This completes the
construction direction at the whole tuple.

**Proof, source to construction.** Invert the last independent source rule.
Its source occurrence identifies the corresponding generated node. Record
its ordinary inference endpoint at that declaration, its original resolved
binding at each Name, its actual local rule choice at each choice node and
its own original witnesses in the same telescope. Apply induction to every
premise and conjoin their solutions with the last rule's local clause.
An already executed choice must be the anchored recorded choice by the
independent rule's origin/lifetime premise. All of its dependent evidence
is reconstructed from that same recorded tuple. A genuinely delayed choice
can supply its own local specialization proof. Conjunction uses the
independent derivation's already shared operands;
it never combines arbitrary independently solved worlds. A union uses its
actual chosen arm. A binder stores its original strategy, not separate
witnesses per later observed challenge. Recursive finite developments and
the actual original simultaneous introduction are handled as above.
Exhaustive inversion of the **defined local rule grammar** accounts for
every case, including nonidentity checks and actual conversions. No premise
says the independent derivation is kernel-identical to a generated export.
Its occurrence map is built by this inversion. QED.

The recursive/member and primitive dependencies of this proof are precisely
the original source constructor dependencies, not assumed Generalize laws.
SRC proves source/program equality by the explicit inventory; it does not
take global source adequacy or complete future safety as an input atom.

## 7. Joint Generalize soundness and lawful-use completeness

### 7.0 Direct joined source/program correspondence

**Lemma SRC-J.** For an allocation of §5.2, satisfying J_m on one original
scoped assignment/strategy constructs a single independent joint source
proof of §3.4 with the same public fields, actual source operands, selected
local rules, fixed tuple and witness dependencies. Conversely, inversion of
an independent joint proof constructs the corresponding allocation clauses
and their original-scope satisfying strategy. Neither direction starts from
separately chosen per-view solutions.

**Construction direction.** Traverse the finite client source/proof grammar.
For new, use SRC's construction direction on the whole component frame,
with the assignment inherited from the global J_m strategy. Its fixed fields
reference the base tree, ViewLogic uses the frame's one original region,
and every Internal reference uses the frame's simultaneous relation. The
obtained proof is exactly new's independent source-definition premise.
The final root is R_b (or the actual selected member of the final formed root),
not an interior inference endpoint. At Alias, take the already obtained
certificate for that handle; no second SRC application creates a fresh tuple.
At view, its allocated local checking grammar gives each actual rule premise
and its independent conclusion by the §3.2 induction. Intermediate proof
terms are introduced by their own rules at the retained scopes. At run,
SRC supplies the local Call/Force/response/resumption constructor on the
actual event, current configuration, argument and pending suffix.

At join both premise derivations are under the same restriction of the
**one global strategy**. Equal key incidences are the same assignment/function,
so apply the declarative joint rule on that one shared context. At sequential
Bind, its actual Return/rebind/world operands supply the same suffix premise;
for Request the original response/current resumed configuration telescope
supplies exactly the unfinished suffix. Later events therefore cannot choose
new histories, worlds or shared witnesses independently of earlier events.
The actual primitive transitions and future compatibility are local L1/L2/L5
clauses, not a conclusion assumed for the entire joined client. Retain W at
its same scope with the same assignments. At each original universal binder,
perform these constructions for its fixed independently admitted domain using
the inherited strategy; at each existential use that strategy's one witness.
The `exists shared; forall challenge; exists body` order is unchanged in each
base or description region, as appropriate to its owning rule.

For a finite recursive proof grammar this is induction on each finite proof
or source development, using its registered references; the rule derivations
assemble the same finite grammar. An actual hereditary recursive introduction
uses the original simultaneous L4 constructor and its genuine leaves as in
SRC. This establishes the joint certificate, not merely a list of views.

**Inversion direction.** Invert the independent outer client rule. new's
independent source-definition premise is inverted by SRC to its complete
source clauses; its original owning records identify template declarations,
base Shared binders, frame-local ViewLogic regions, actual event fields and
per-frame EventProof witnesses under those events. Alias
points to its antecedent certificate; its rule cannot introduce a new frame.
view is inverted constructor by constructor through its finite proof grammar.
run yields the actual event constructor and its full shared operand tuple.
Join and Bind inversion give precisely the already-common context, result or
request/resumption telescope, so allocation glues those existing incidences.
All constituent proofs use the original single strategy of the joint source
proof. W is retained unchanged. Recursive references retain the finite proof
grammar's nodes and uniform binder introduction paths. This yields all J_m
clauses without guessing identity/scope from successful comparison. QED.

**Theorem GS (joint soundness).** Under L1–L5, for every finite allocated
client U, arbitrary well-scoped client predicate W, and one global satisfying
assignment/strategy of J_m(U,W), there is an independent **joint** legal source
derivation of U with W. Every alias and incoming event has its original
sharing partition; all uses retain the same actual binding object, initializer
and installed external contracts. Actual conversions in the client retain
that input and their independently authorized result object. Admission and
complete observations use the actual final roots and original scopes.

**Proof.** The closure was built from the selected source rules and the typed
walk of §5.1; allocation §5.2 retains those local clauses without changing any
operational field. Apply SRC-J's construction direction to the global
satisfaction. In particular a Shared witness is taken **once** for the whole
base tree; a ViewLogic witness is taken once per independent description
frame; an EventField witness is taken at its actual invocation/response
event, and a latent EventProof witness at that event inside its original
description frame. Source joins and sequential constructors glue them according to their original
keys and dependencies. The independent proof is formed by those joint rules.
There is no step combining `exists s.P1` with `exists s.P2`: J_m already
requires the one original binder's strategy to meet both clauses. L3 proves
each local checking conclusion for its actual same provider/domain; the
constructor proof keeps complete entry Force, Return/rebind, body, invocation
return and original pending suffix. All Option 2/W/Z arms keep their genuine
complete local laws and independently formed challenge/future domains.
These local facts establish the entire joined source proof by SRC-J, including
arbitrary finite histories and W. QED.

For example, suppose an initializer-owned Shared s has domain `{0,1}` and
W requires the first view's retained clause `s=0` and the second's `s=1`.
Both individual views can be satisfiable in isolation; their J_m join has
one s and is unsatisfiable, exactly as the independent joint source judgment.
If instead the two witnesses are ViewLogic s_i,s_j at distinct real new
events, independent choices are permitted (subject to every shared constraint
and W). Replacing the second new by alias(i,j) identifies its frame and s_i;
the inconsistent pair is again unsatisfiable. These are binder/handle rules,
not consequences of keeping just the same raw provider identity.

**Theorem GC (joint lawful-use completeness).** For every finite independent
joint client proof grammar d_U of §3.4, including arbitrary well-scoped W,
there exists a finite allocation schema m_d of the single preconstructed
Generalize_source(S,b), chosen before public assignments, challenges and
histories, whose public solution-and-observation fiber is exactly that of
that joint proof grammar. It retains all original scoped witness strategies,
including any Shared, ViewLogic, EventField and EventProof dependencies.
It selects R_b, including its actual final annotation/common formation, at every use.

Here a public fiber includes the client's designated public endpoint fields
and approved whole-observation fields at their original indices. It consists
of their values for which **one** original scoped strategy satisfies the whole
independent proof grammar and W. The corresponding fiber of J_m is defined
by global clause satisfaction with the same public coordinates. Private
proof fields stay retained internally; fiber comparison is mathematical
forgetting to those designated fields, not a new source hiding operation.

**Proof: construction before solutions.** Invert the finite syntax of d_U
by SRC-J's inversion direction. At each actual new event i, make one component
frame; record the symbolic endpoint term chosen at each eligible source Desc
introduction as the map `(i,q) -> t_(i,q)`. Terms can contain public variables
and earlier dependencies, but no later challenge/history variable absent from
the introduction's telescope. At Parameter the map is therefore installed
at its type scope **before** challenge formation. Internal references use
that same component frame, including all peers and residual conjuncts.
At Alias route its antecedent handle, with no new declarations or ViewLogic
binders. At each actual event store its constructor/original-parent routing;
keep original Shared and OneShot references in the base tree. A ViewLogic
binder remains under its template dependencies and above its challenges.
The map records binder incidences, not their eventual witness values.

Invert every actual source/checking choice into its local rule tag and full
premise grammar. m_d adds the corresponding tag/endpoint-term clauses to the
open alternatives in N_b; when d_U itself has a symbolic locally guarded
choice, retain its same guarded alternatives and selector fields. This is a
use's choice, not removal of another licensed alternative from the stored
closure. The local grammar can be recursive and can introduce intermediate
proof terms. Store its finite nodes, registered references and binder-key
constructors of §5.2 rather than enumerating its developments. Its scope
maps act uniformly on every development. These finite syntactic data and the
client's actual new/alias/event partition determine m_d without inspecting
a ground assignment, a challenge, a history, a source safety outcome or Q.
Retain W with its same shared variables and original binders.

**Forward fiber inclusion.** Fix any public solution and original strategy
of d_U. SRC-J inversion supplies each source clause and local proof clause
with that same strategy. Use its one Shared witness once across all frames,
its ViewLogic witness once per original frame, and its EventField strategy at
the corresponding actual event telescope, and its description-owned latent
EventProof strategy there with the same runtime operands. The constructed
endpoint terms have exactly their d_U values. Every conjunct, internal recursive relation,
actual sequential world transition and W is thus satisfied in J_m_d. The
public endpoints, final target evidence and whole observations are unchanged.
No fresh initializer value, captured provider or external Mono assignment
is supplied by this step. Imported Family bound parameters are filled only
through their actual independently typed instantiation rule.

**Reverse fiber inclusion.** Fix a global solution/strategy of J_m_d. The
stored tag and endpoint-term clauses enforce d_U's same local proof grammar,
including its branch guards, recursive references and operand incidences.
Apply SRC-J construction **following those tags** to obtain that independent
joint grammar with its shared source operands and original binders. W is
still a conjunct. It therefore supplies a strategy of d_U with exactly the
same public endpoints and observations. This is stronger than merely showing
that some unrelated source view exists: the constructed clauses select the
actual d_U grammar, so no extra public fiber appears through a different open
source/checking choice. Both directions preserve every original strategy's
binder dependencies; no proof-irrelevance assumption is needed. QED.

The quantified statement is

```text
forall finite independent joint d_U and well-scoped W.
  exists finite allocation schema m_d, before assignments/histories.
    Fiber_independent(d_U,W) = Fiber_clauses(J_m_d(U,W)),
    with both directions retaining the original scoped strategies.
```

GC does not assert satisfiability of inconsistent W, one ground substitution
for every caller, or a witness selected after each challenge. It concerns
finite independent rule/proof grammars and all their finite developments;
it does not assert that every semantic Function inclusion has such a grammar.

### 7.1 Nonidentity checks are covered

Consider the actual unannotated identity closure. Its synthesis keeps the
single repeated endpoint. An independent view can select its parameter
endpoint `Int`, obtaining the complete source root whose body returns the
same Int. A result check `Int <= Any` proves that this same return belongs
to Any; the complete Function check retains the admitted Int carrier domain
and proves observation inclusion at the actual source root. GC retains
`a:=Int` and that checking proof. It never changes the synthesized result
endpoint independently to Any.

A narrower checked carrier domain is handled by the checked-domain proof:
given an independently admitted challenge in that domain, inclusion supplies
source admission, and the same original body/entry proof supplies its checked
observation. Record width and union checks use the actual structural checking
nodes; actual casts use their effectful conversion nodes. The proof does not
require all these targets to have an identical complete membership graph.

### 7.2 Source evidence and the actual query boundary

GC constructs the finite original source checking evidence for the actual
submitted pair `R_b^use,R_V`, together with its complete D/M and target
formation references. Semantic same-callable containment follows from that
proof. Where the native ordinary query accepts these exact local certificate
constructors, the same proof graph is a direct certificate for that single
whole-root query. Intermediate semantic implications inside its proof do
not authorize composing concrete successes at other endpoints.

No theorem here establishes that the existing production resolver accepts
every constructed certificate. Source-contracts §9 explicitly shows why
source conformance alone cannot imply such effective resolver completeness.
That gap remains even for a source-lawful widened identity view. It is not
put into independent legal use as a successful-Q premise, nor is it repaired
by returning to a hidden interior root when final formation exported another.

## 8. Scope and adoption

This is a direct source-side definition/proof of the missing event, root,
anchor closure and eligible scoped-description constructor. It supplies a
native `g_b` as **output**. It proves GS/GC relative to explicitly specified
local source constructors, by constructing and inverting their rule proofs.
It does not repeat the existing Pack/Decode or whole freshening theorem.

The [selected definition](../design/2026-10-08-source-generalize-definition.md)
adopts §§3–5 as the missing native source Generalize definition and uses
§§6–7 as its source-lawful subsystem theorem. Both fresh independent reviews
passed the repaired construction at precisely that scope; see the
[review record](../progress/2026-10-08-source-generalize-review.md#4-frozen-theorem-reviews-and-integration).
GENERALIZE's source selection/placement/reflection seam now cites this result;
the production all-authorized-use/query obligation must remain open until
the actual resolver/evidence consumer is connected. `INTRO` obtains a native
ordinary-flexible inference-site classification only; full existential,
extrusion and guard coverage are not closed. `MEMBER_DISCHARGE` keeps its
general original local-law obligations; selected pair/step results are reused.

Completeness for every semantically valid contract, normalization of every
accepted adapter to the listed local grammar, all-language State and recursion,
effective symbolic closure of arbitrary open catalogues, source principality,
ROWS inhabitance, production emission/solving and lifecycle are not proved.
None is silently converted into a source restriction, mandatory annotation,
restricted recursion or a closed-world method catalogue.

The initial review identified missing joint-use allocation and ambiguous SCC
anchor classification. One batched repair supplied explicit definitions and
direct arguments at those two seams; fresh mathematical and specification
delta reviews both passed. No negative source counterexample was established.
The native source-lawful target is the specified local-rule scope;
the stronger semantic/effective targets remain distinct claims. In particular
an abstract hiding countermodel or a sound-but-incomplete resolver is not
reported as an independently legal source counterexample.

## 9. Verification and frozen packet

Only bounded baseline `git show`, `rg`/section reads, policy reads and static
proof inspection were used. The committed five DAG nodes were inspected via
Python JSON decoding. No compiler changes, build, Cargo/test suite, numerical
probe, solver/oracle experiment or source acceptance measurement was run.
No subagents were spawned. No Git mutation or shared record/authority edit
was performed. The original producer pass and this single batched M1/M2
repair write only
the exclusive leased file; neither is an independent review.

The repair additionally used bounded direct section reads and a Python
whitespace/heading/fence inspection; no proof checker was run.

Static inspection checked that both SRC directions have explicit constructor,
check/choice, binder, recursive, admission and Option 2 cases; SRC-J
constructs and inverts one joined client proof; GS uses one global
strategy with distinct base/description/event regions; GC constructs a finite
allocation schema and its exact public fiber from the independent derivation;
final targets and direct-query limitations are
explicit. This is producer verification and supplies no independent verdict.

The independent reviewers checked the frozen repaired artifact with SHA-256
`cf105b27c22c8756077305e90f74efe191a0068221ce42b44480771083442335`.
Primary integration changes this metadata and the adoption/verification
sections; the reviewed mathematical body, §§1–7, remains byte-for-byte.
The review record records both frozen inputs, accepted findings, repair,
independent verdicts, exact remaining dependencies and integrity checks.
Task, design-index, theory-map and DAG updates are navigation to that exact
result, with no aggregate status, prerequisite or production-authority change.
