# A finite ordinary Value-entry protocol and import-free `id` introduction

Date: 2026-10-08
Status: independently reviewed native semantic construction and direct constructor proof
Scope: research-only native immutable Value-entry/Pure-body descriptor
Baseline: `4b5215320587e94acf286ff49267a00515e8812e`
Branch: `research/simple-sub-intrusion`
Exclusive write lease: this file only; frozen on submission
Production implementation, foreign-kernel equivalence and aggregate closure: none
Review: independent mathematical and specification reviews passed; one minor
outer-phase/future-development clarification was adjudicated by the primary.
Record: [review and integration](../progress/2026-10-08-projection-public-export-review.md)

## 1. Result

This note supplies the previously missing ordinary invocation phase meaning
for the import-free immutable source `my id x = x`. The public constructor is
generic: `VP(I,A,B,IF)` describes Value entry at the independently fixed whole
carrier interface I, followed by a pure body returning B. It describes every
well-typed protocol record in §4, rather than the executions of a stored
source term. `I.result=A`; `IF` is the original finite registry of formal,
receipt, body, invocation-result and future-port incidences. Neither parameter
is a hidden source relation. For `id`, use `B=A`.

The new direct result is **Theorem ID**: the actual import-free source closure
realizes `VP(I,A,A,IF)` at every independently admitted challenge, including
before receipt, pending or divergent entry, every raw resumption and every
compatible returned-value use. The proof derives actual acceptance by inlet
constructor inversion, obtains Force typing by eliminating the independently
given carrier certificate, and proves the body by actual Return/rebind and
immutable Name. It does not assume that the `id` closure already has Function
membership, or that its invocation is safe.

The ordinary descriptor does not assert result equality with the input.
An optional finite refinement `Echo` adds that equality at completed result
ports. The same direct proof establishes `VP+Echo`, and a finite conjunction
projection establishes `VP+Echo <= VP` on the unchanged domain. Neither choice
is represented as already selected for an independently fixed source/public
production root. This gives the primary both a concrete ordinary guard and a
concrete finite equality clause if source-lawful evidence translation needs it.

The complete native production meaning is the exhaustive finite rule inventory
of §4. Its Return-any-B clause and its partial-phase clauses are independent
unanchored abstraction laws. Thus Option 2 is retained concretely: a final
member need not have a source execution. The note does not replace any
already-fixed foreign W/Z arm with those new native laws. Adoption on a source
synthesis root and its actual public root, proof-query recognition, full
Generalize fiber preservation and principality remain primary-owned work.

## 2. Authority, inputs and what is newly defined

All reads used committed baseline bytes. No other worker's unfinished output
is a premise. The current task explicitly permits natural missing semantic
definitions; this artifact proposes such definitions without self-certification.

| Source | Reused meaning |
| --- | --- |
| [Function views](../design/2026-10-05-inferred-function-call-views.md) §§1.1–2,5 | Original roles, source entry and joint scope; independent admission; actual public-root obligation. |
| [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md) §§2–3.7 | Whole-tuple relational operations; source receipt/Force/rebind order; independent complete histories; Option 2 and its full hard envelope. |
| [Contextual membership](../design/2026-10-08-contextual-function-membership-definition.md) §§2–3 | Every genuine decomposition of the same callable; carrier acceptance plus all actual observations; hereditary immutable meanings. |
| [Complete closure constructor](../design/2026-10-08-captured-closure-constructor-definition.md) §§2–3 and [its construction](2026-10-08-captured-call-closure-introduction.md) §§3–4 | Selected Strict Value-entry composition, actual registered inlet equality, current-world Bind, receipt and invocation frame actions. |
| [Input realization](2026-10-08-call-semantic-input-realization.md) §§2–4,7 | Independent two-hole challenge records, hereditary value/carrier eliminators, immutable world extension, Name and pure Return/prefix cases. |
| [Positive immutable introduction](2026-10-08-simultaneous-immutable-root-introduction.md) §§2–3 | Fixed independent demand domains; V/W/T/Car interpretation and original current-world/incidence guards. |
| [Result synthesis](../design/2026-10-02-source-result-synthesis-choice.md) §§2,4 | Unannotated x has Value entry; `Result(Value(A))=Comp(empty,A)`; substitution does not execute latent results. |
| [Native Generalize](../design/2026-10-08-source-generalize-definition.md) and [source proof](2026-10-08-source-generalize-definition-and-proof.md) SRC/SRC-J/GS/GC | Native source allocation is already selected; it does not identify this proposed public production meaning with a foreign source root. |
| [Root-policy decision](../../questions/2026-10-08-successor-generalize-root-policy/approved-answer.md) items 1–5 | Displayable scheme plus finite necessary use data; publication may inspect source; no renamed full source relation at use time. |

New here: the explicit *ordinary* finite phase-record cases, exhaustive native
production law and optional Echo residual in §§3–4. The selected Strict
construction supplies the underlying source receipt/Bind/frame operations;
the new protocol makes their ordinary descriptor checks concrete. This is not
an adoption of all open clauses of any Draft computation package.

### 2.1 Legitimate independent semantic parameters

Use the selected global immutable semantic meanings, not new predicates named
after the desired conclusion:

```text
V(A,a,p,e)   hereditary membership of the actual decorated value a/provider p
W(C,w,e)     valid immutable installed world with joint registry/scope/authority
Car(I,t,p,e) inert carrier validity and all designated executions at I
T_I(o,e)    complete/pending observation relation of independently fixed I
```

These are the V/W/T/Car sorts of the selected positive interpretation.
Ground/external leaves retain their original independent contracts. A supplied
carrier certificate has an inert-formation field, a restriction action to
each independent compatible demand, and a universal execution field:

```text
Car(I,t,p,e) + independently admitted designated demand d at current e'
  => every actual Force(t,d) observation/development belongs to T_I at e'.
```

At a completed I Return, `T_I` supplies `W(C',w',e')` and hereditary
`V(A,a,p_a,e')` at that *same* original result incidence. At a Request it
supplies its actual operation instance, typed argument/response/raw-handle
contracts, live world and complete continuation obligations at later
independently compatible demands. These are eliminators of the given carrier
contract; they are not assumptions that this particular `id` invocation is
safe. An unprovided external primitive law supplies no certificate.

I may have arbitrary permitted effects, divergence and its own Option 2
members. For an unannotated value parameter, a carrier's whole argument
interface and its payload A are retained together. No empty entry effect is
inferred from the body's pure result. If a source formation leaves I symbolic,
the entire symbolic I and its constraints remain parameters of VP; this note
does not invent a new default effect row or freshen I per challenge.

The finite IF record consists of the actual role/entry/consumer declarations,
static registered ports and scopes, the formal-rebind edge, receipt/receiver
edge, invocation-return edge and their joint original `nu,K,D` incidence map.
Immediate original guards remain active. For the owned Pure closure, insertion,
borrow-or-fresh re-entry and removal of its invocation occurrence are the
selected Strict actions. They add no handler. A valid frame insertion has no
formal result binding yet; adding an actual result binding uses its V proof.
Removal projects the same valid world and removes exactly its own occurrence.
No dynamic grant is recovered from a static identifier or historical world.

## 3. Concrete independent challenge and history records

Fix the original binder tree, `xi=(nu,K,D)`, one original assignment and one
legal complete IF incidence map before challenges. Dynamic event fields remain
at their dependent event scopes. Repeated receiver activations get their own
actual occurrences; this does not instantiate the type binder again.

A VP initial challenge is a dependent record containing:

1. the independently valid typed punctured caller context, including its
   declared callable hole at VP and whole-carrier hole at I;
2. its independently valid other values, joint original references, paths,
   live registry, current world and actual authority;
3. the actual registered callable, carrier and receiver fillings of those
   holes, with the same IF incidence fields;
4. the same carrier's independent whole-interface admission/Car certificate
   at I and the IF receipt/context preconditions at the live event.

No field is callable realization, actual-U acceptance, successful Q/Direct,
execution safety, receipt already established or existence of a returned
value. In particular a carrier that never returns is included. The constructor
is the selected independent challenge assembly, with `F=VP`, not an opaque
`InitialOK` oracle.

The other three independent history constructors are these records:

| Extension | Required original fields; next live event |
| --- | --- |
| Response | One previously exposed actual request q, its operation-instance witness and declared response interface; response checked there, independent compatible context/current-world action, original history incidence. |
| Raw Resume | One previously exposed original raw handle k, its declared demand/response interface and scope/lifetime; actual compatible current event and history incidence. Multiple lawful uses branch from this same original handle. |
| Future | One actually returned value/provider and original declared port; an independent compatible punctured demand context checked at that port's contract, its valid other fields, original incidence, current authority and lifetime. |

These constructors check registered request/handle/provider occurrences,
typed demands and independent context compatibility. They do not check VP
membership or ask whether an actual result is safe before admitting its future
demand. At a Function/carrier future port, the tested provider hole is declared
at its contract without assuming realization of its filling, just as for the
initial two-hole context. Realization of that same provider is later discharged
by hereditary V. History domains are fixed before the positive membership
operator. No universal quantifier over a growing production relation occurs.

Consequently the admission presentation is finite (four record constructors)
but admits arbitrarily long finite histories. A world with an unresolved State
transition is not made compatible by these immutable records.

## 4. Exhaustive ordinary phase-record meaning

### 4.1 Record fields and checks

A protocol record has the original complete challenge/history, current event
and world, IF incidence map and one of the following phase payloads. A field
listed as absent cannot be justified merely by its endpoint type. Fresh local
witnesses have their actual dependent event scope.

| Phase | Required payload | Absent until a later phase |
| --- | --- | --- |
| `Start` | Actual registered holes, current W, receipt preconditions | Established receipt, formal binding, body/result value |
| `Received` | One actual receiver receipt token at IF's receipt edge; valid current invocation occurrence and W | Entry result/formal binding, body/result value |
| `Forcing` | Same receipt, designated I-demand; one `T_I` prefix/pending observation and its current W | Formal binding and body/result until completed I Return |
| `EntryValue` | Same receipt; completed I Return `(a,p_a,C',w')`, its V(A) and W; exact formal-rebind edge | Body/result value before body return |
| `Body` | Same rebound `(a,p_a)` at formal port; W and that V(A); pure administrative prefix | Completed body/result until its actual result record |
| `BodyValue` | Same entry witness/binding, same current W, a hereditary `V(B,b,p_b,e)` and original body-result port | Outward completed invocation return until its return edge |
| `Done` | BodyValue fields transported through IF's lawful invocation return; same `b,p_b`; W at current return event and original outward result/future port | No live historical invocation occurrence retained as a grant |

Every field is checked against the original joint map, scope and active
authority. `Start` never requires established receipt. `Received/Forcing`
never install x. `EntryValue` is evidence of a completed argument Force;
it is not inferred from a later returned payload. IF bounds/guarantee
equations check the same whole tuple in every phase. Body administrative
steps cannot request or execute a latent provider. Entry events are checked
by I's complete T contract. After Done, future events belong to the actually
returned B-provider's independently fixed contract at their live event.
Forcing includes administrative and pure-divergent prefixes with no exposed
Request. Those records require neither an operation instance nor a raw handle;
the Request/Resume checks activate only if a Request was actually exposed.

No phase check mentions source code, a source observation relation or query
success. This is the explicit ordinary Interface/Endpoint/PhaseBounds guard
that the predecessor left unsupplied: it is the tagged dependent sum of these
seven cases, with the displayed required fields, absences and whole guards.
It admits a well-typed record regardless of which source, primitive or abstract
license produced the record.

### 4.2 Finite constructors for complete production observations

The native complete observation relation P_VP consists **exactly** of finite
derivations of these rules, at original scopes. The seven record cases of §4.1
are the outer invocation phases. VP-Future additionally gives the explicitly
declared dependent future-development case, retaining the outer Done and its
returned-provider incidence; a nested request is not a new outer Forcing phase.
No additional root arm is implicit.

```text
VP-Start:  independently admitted initial record; W; IF joint guards
           ---------------------------------------------------------
           Start (zero-step prefix, no established receipt)

VP-Receipt: Start or its administrative prefix;
            IF's lawful actual receipt/frame image, same registered holes
            -------------------------------------------------------------
            Received (one receipt token; no formal result)

VP-Force: Received; independently admitted designated I-demand;
          arbitrary independently licensed T_I prefix/pending record o
          at the SAME carrier/port/receipt/current-event incidence
          ---------------------------------------------------------------
          Forcing(o), with no formal result unless o is completed Return

VP-Entry: Received/Forcing with completed T_I Return(a,p_a,C',w');
          its W and hereditary V(A); IF formal edge; actual result-rebind
          ---------------------------------------------------------------
          EntryValue and Body, binding exactly (a,p_a) in C'

VP-Body: Body; any finite sequence of pure administrative record images
         preserving W, joint incidences, receipt and SAME formal binding
         -------------------------------------------------------------
         Body prefix, no new request/result/latent execution

VP-BodyReturn: EntryValue/Body; any hereditary V(B,b,p_b,e)
               in the SAME current W and lawful body-result incidence
               -------------------------------------------------------
               BodyValue(b,p_b) (pure Return, no latent execution)

VP-InvocationReturn: BodyValue; IF's lawful invocation-return image
                     removes only its current own occurrence
                     ---------------------------------------------
                     Done with that SAME (b,p_b), live W and result port

VP-Restrict: a derived phase record; an original finite observation
             restriction including zero/administrative/pending prefixes
             ----------------------------------------------------------
             its correctly typed phase restriction; no fabricated later field

VP-Develop: a Forcing Request(q,k) record; an independently admitted
            Response/raw Resume at q/k; its T_I continuation development
            at the actual current event with the SAME receipt and suffix
            --------------------------------------------------------------
            the corresponding Forcing record; if it returns, VP-Entry follows

VP-Future: Done(b,p_b); independently admitted future demand at its
           original B-port; hereditary V(B,b,p_b) elimination at current e'
           -------------------------------------------------------------
           the complete/pending provider-contract observation there
```

The pure administrative record image is identity on live store, registry,
authority, bindings and result fields; it may only advance an inert lookup/
Return administrative position or leave a finite prefix open. Arbitrarily
many such abstract positions are allowed. This is a conservative prefix law,
not permission to change a world while calling it administrative. Other
world changes in the grammar occur only through I's original observation/
response action or IF's original invocation actions.

For a Request, the remaining suffix is the single typed protocol recipe
`Entry(rebind); Body; BodyReturn; InvocationReturn`. VP-Develop retains q's
original raw k and performs `k(response,C_current)` before that suffix. If k
requests again, only that same still-unfinished suffix remains. There is no
receipt replay. Borrow-or-fresh invocation occurrence re-entry belongs to
IF's existing current-world action; a historical receipt token is not a live
activation snapshot. For finite branching raw-handle histories, apply the same
rule to each independent lawful demand at that original handle. Finite
derivation does not bound future demand length or resumption count.

The grammar is a finite set of same-tuple conjunctions, tagged unions,
original-scope bindings, images and positive finite recursion. Its source-free
parameters are I, A, B and finite IF. The recurrence uses no universally
quantified growing production relation; the fixed hereditary V/T meanings are
the selected independent semantic parameters.

### 4.3 Actual independent Option 2 alternatives

VP-Force admits every licensed member of T_I, including its production-only
members; no Force execution witness for the actual carrier is requested.
VP-BodyReturn admits *any* valid B-provider after an independently typed
entry-completion record, with its complete future certificate. These are
explicit unanchored native production alternatives. They have their own typed
record witnesses and no source anchor. No root `W` or `Z` placeholder remains.

For example, when A=B is Bool and both ground constructors are valid, take an
independent completed entry record returning true. VP-BodyReturn permits a
body/result false at that same world. Its future interface is the ground Bool
interface. This satisfies every VP guard and is not an execution of `id` on
that true-returning entry. The example is a semantic ground-instance
derivation, not a claim about an executed compiler program or an independently
fixed primitive implementation's production relation. It demonstrates that
the native production meaning is not secretly source-tight.

If no second B-value exists at a particular assignment/world, the rule remains
present and applies to the values that do exist; nontrivial model inhabitance
is not claimed for every arbitrary equation system. VP's original guarantees
remain mandatory at all final records, including unanchored ones. Arbitrary
B membership alone cannot license a changed operation instance, scope,
authority, receipt or inlet domain.

### 4.4 A finite retained equality refinement

Define `Echo` by exactly these phase-dependent clauses:

```text
Start, Received, Forcing: no result-equality assertion;
EntryValue, Body: retain the same formal (a,p_a) from completed I Return;
BodyValue, Done: require (b,p_b)=(a,p_a) as DECORATED values/providers;
Future: its registered provider is that same actually returned (a,p_a).
```

The last clause selects the provider of the *outer* returned-value demand.
It never requires a nested call/Force's own returned value to equal a; those
observations satisfy their provider's independent B contract. It likewise
does not equate a typed response to an operation request with the id input.

The equality is on the original dependent tuple, including shared provider and
required original incidence/evidence operands, rather than erased payloads
or coincident endpoint IDs. Define `P_VP+Echo` by adding this clause to each
corresponding grammar rule. The independent history domain is unchanged.
The input carrier's Option 2 members and pure unfinished prefixes remain;
BodyReturn becomes its same-value subcase. This is a finite result-dependency
refinement, not the stored source `Name x` relation.

By forgetting the Echo conjuncts in a finite derivation, one obtains the
identical VP derivation, whole observation, scope and witness. Thus the
unchanged-domain comparison `VP+Echo <= VP` has a direct finite proof.
Echo is not silently made a hard guard of any foreign production root. A
pre-existing provider-replacement arm violating Echo would prevent that
identification, even though it could be a valid VP arm. This is the genuine
S/T boundary; the local source proof below supplies both views, so it does not
need to settle that foreign-policy question.

## 5. Direct actual source admission and introduction

### Lemma A: exact actual acceptance

Let the actual import-free closure be the source constructor

```text
v_id = Closure(Pure,ValueEntry(I),result(name x),emptyCaptures;IF).
```

The authentic source Lambda/parameter construction creates I and IF before
body execution. Actual decomposition yields that same U, actual receiver r,
formal port and `CarrierContract(U)=I`, by registered constructor inversion.
It does not infer them from the printed arrow.

Take any independent VP challenge. Its carrier certificate is at I, and its
original receipt/context preconditions are the U/IF ones. Rewrite that very
certificate by the constructor equality, retaining carrier, current event,
original root, scope and joint witness. Pair it with the same preconditions.
This constructs `ActualAdm(v_id,U,d)`. The proof establishes acceptance;
receipt remains absent until the actual receipt transition. It uses no output
membership or assumed safety. It applies uniformly to every retained genuine
decomposition; constructor inversion fixes U for this ordinary closure.

### Lemma B: every actual invocation record is typed

For the same arbitrary admitted challenge, prove the statement for every
actual observation and finite independent development by case analysis on
the selected source receipt/Bind/Name/Return rules, followed by induction on
the number of response/raw-resumption/future extensions.

**Before receipt.** The zero-step record has only original registered holes,
independent W and IF preconditions. VP-Start types it without receipt,
formal/result or Return requirements. An inert administrative prefix preserves
those fields and is its VP-Restrict/administrative case.

**Receipt and Force.** Lemma A supplies actual preconditions. Selected Strict
receipt establishes its one token and lawful invocation occurrence, so
VP-Receipt applies. The actual designated Force demand is at I's original
whole-carrier port with current W/authority; receipt has not introduced a
new handler or executed the carrier earlier. Restrict the given Car
certificate to this independent demand and eliminate its universal execution
field. Every actual zero-step, pending, divergent prefix and complete Force
observation belongs to T_I, including its W/operation/continuation fields.
VP-Force therefore types the corresponding full entry prefix. This step
derives local Force image typing from the carrier certificate, rather than
assuming that the whole invocation was already in VP.

**Pending Force and raw continuation.** A Request retains its original q,k.
The selected Bind equation is

```text
Request(q,C,k) >>= S
  = Request(q,C,lambda(response,C'). k(response,C') >>= S).
```

T_I's Request eliminator supplies the exact typed response/raw-handle and
current-world continuation contract. On an independently admitted development,
its restriction/execution field supplies the actual `k(response,C_current)`
observation before S. VP-Develop types this same continuation and appends only
the unfinished suffix. The induction handles another Request or a later
Return. A divergent k has all finite Forcing prefixes, no fabricated x/body.
No receipt is replayed; current occurrence re-entry is the selected IF action.

**Completed Force, rebind and pure body.** T_I's Return eliminator gives
`V(A,a,p_a,e')` and W at the actual C', with original result edge. Immutable
world extension installs precisely this returned decorated value at x by
the selected rebind constructor. VP-Entry applies. Lookup of the resolved
formal uses the same installed projection. Selected hereditary Name/Return
typing gives the pure body Return of `(a,p_a)` at actual C', and every inert
unfinished/zero-step prefix. Choose b=a in VP-BodyReturn. Its required
V(B) is exactly the same V(A), because B=A under the one original assignment.
The body requests nothing and forces no latent descendants. Its original
pure Return does not manufacture an invocation return prematurely.

**Invocation return.** Selected IF return removes only the invocation's
current own occurrence and retains the actual live world/store and same
decorated result. World projection and hereditary restriction preserve the
V(A) evidence at the outward result incidence. VP-InvocationReturn types it.
This same source result also satisfies Echo. An exited maker/receiver is not
revived by retaining original provenance.

**Future demands.** Return retains the hereditary V(A) certificate at its
actual port. For each independently admitted compatible future demand,
eliminate that certificate at the later live event. Its same-provider
Function/carrier/ground case supplies every actual complete or pending
observation there, with original operation/scope/authority fields. VP-Future
applies. Nothing executes that latent provider at the original id Return.
Future calls with arbitrary independent arguments, repeated Force and raw
resumptions are covered by the provider's hereditary field, not by an extra
implicit entry force or a snapshot of C'.

These cases exhaust the actual source graph's own invocation observations:
one receipt, designated Force, actual rebind, resolved Name/pure Return and
invocation return. Finite history induction covers all independent extension
lengths and branches. No arbitrary root production arm is reclassified as
an actual source execution. QED.

### Theorem ID

At every original jointly valid immutable assignment and lawful event,
the actual import-free `v_id,U,r` realizes `VP(I,A,A,IF)` and `VP+Echo` in
the selected same-provider contextual Function meaning.

**Proof.** Inert source closure formation supplies actual registered role,
entry, ports, scopes and empty captures; it executes nothing. Lemma A supplies
actual acceptance for every independently admitted complete challenge.
Lemma B supplies every actual complete/pending/admin/zero-step observation
and its independently admitted developments at those same indices. Apply
the three selected Function membership clauses. Restriction to later
compatible events repeats the proof with their actual current world and
unchanged static assignment/IF/captures. Echo holds in each completed
body/result case by the same Name projection, and is vacuous at earlier
prefixes. This proves the refined realization too. No premise is
`ValueMem(VP,v_id)`, invocation output safety, Q or a source-execution definition
of ordinary descriptor membership. QED in the proposed native interpretation.

The theorem is parameterized only by legitimate independent carrier/context/
world/primitive contracts and the selected source constructor laws, as every
ordinary source soundness theorem must be. It contains no unsupplied local
`Interface`, `PhaseBounds`, `ResultPolicy`, `Guard`, source accessor or exhaustive
root-production predicate. A false external primitive/State/world assumption
does not get repaired by this proof.

## 6. Finite public boundary and precise export limit

The constructed native descriptor's use information is finite:

```text
display: forall a. a -> a
ordinary data: VP tag, actual Pure role/Value-entry/result-consumer profile,
               original I/IF incidence and scope parameters,
               once-shared binder a and original nu,K,D residual operands
optional refinement: Echo result-dependency clause
```

I and IF contain only independently interpreted interface clauses, scoped
operands and finite public dependency references. The public descriptor has
no source Lambda, Name/body code, source-base graph, source relation accessor
or lookup of a hidden original root. When I's actual symbolic inlet has
additional residual/effect/profile data, that data remains counted in the
boundary; this note does not claim the printed arrow is sufficient alone.
The VP rule library is global and fixed, not copied from each source graph.
There are no captures or import summaries for this id instance.

Whole legal renaming/freshening acts once on A, all incidents in I/IF,
original equations and optional Echo. Each rule is a dependent-record
constructor/equality/image with precisely those operands. Applying the whole
action to a rule instance yields the corresponding renamed instance; inverse
restriction gives the opposite direction. Induction on finite grammar proofs
establishes equivariance of domain and P_VP (and P_VP+Echo), with no per-port
witness freshening. This derives local substitution compatibility. It does
not select source Generalize eligibility, independently hide shared binders
or supply a public solver/query rule.

VP may be adopted as the missing ordinary synthesis meaning on both the
source-formed complete interface and its actual transformed public root.
Then equality of those *descriptor contracts* follows from the same concrete
constructor operands and this equivariance, not from equality with source
executions. Source introduction is the separate Theorem ID. Such adoption
requires independent review/adjudication outside this artifact.

For a separately fixed source descriptor, exact preservation needs its actual
constructor/equations and all fixed licensed alternatives. VP's Return-any-B
cannot be asserted equal to a source contract that exposes Echo. Conversely
adopting Echo may exclude a previously licensed result-provider replacement.
Unknown W/Z arms are neither dropped nor certified here. Their unchanged
original complete contract can be conjoined/referenced only when it is
actually provided; each such arm needs its real inclusion/embedding law.

Client constraints can observe shared *evidence* in addition to the displayed
endpoint and value. A source proof's particular Name/entry/result evidence
must be retained or reconstructed by its actual finite typed producer map
when that evidence is exported to W. Theorem ID constructs that canonical
same-value proof; it does not assert that every VP membership derivation has
the same proof object. Thus full SRC-J/GS/GC solution/evidence-fiber transport
is not an automatic corollary of ordinary source safety or Echo equality.
The primary owns the concrete source cut and actual-root Direct law.

## 7. A bounded fixed-capture specialization

For the next projection `my pick ignored = z`, a fixed variant is immediate
**when its actual public capture contract is provided**. Let `J_z` be an
independently fixed finite public contract at the original captured z-port,
including B_z, actual decorated `(z,p_z)`, its rigid/shared dependencies,
scope/lifetime, hereditary value/future fields and every transitive public
interface reference. Its interpretation is the original capture restriction
of `V(B_z,z,p_z,e)` at each independent compatible live event. It contains
neither the source of z nor a retained source relation. This is a precise
external contract parameter; existence of such a finite summary for every
possible source z is not asserted.

Define `Fixed(z,J_z)` by changing only Echo's completed BodyValue/Done
equality to `(b,p_b)=(z,p_z)` at the original capture incidence. Start,
Received and pending Force assert no body/result equality. EntryValue/Body
still require the actual forced A-value installed at the ignored formal,
and the fixed capture's own valid binding restriction in the same current
world. Future selects the same outward returned z-provider; nested future
returns retain their own independent contracts. Whole freshening changes
eligible local A incidents once and preserves the rigid z/J_z coordinates.

**Theorem PICK-J.** An actual registered immutable
`Closure(Pure,ValueEntry(I),result(name z),capture(z);IF)` realizes
`VP(I,A,B_z,IF)+Fixed(z,J_z)` when its authentic capture construction supplies
that same J_z hereditary certificate and original incidence.

**Proof.** Lemma A is unchanged: source closure inlet inversion gives I,
and every independent challenge includes that I carrier and original receipt
guards. All entry/pending/Force cases of Lemma B remain unchanged, including
the designated Force of an unused argument and no formal before its Return.
At completed entry, rebind the actual A-result at the ignored formal. Capture
restriction of the same J_z certificate along the compatible entry/world
history supplies `V(B_z,z,p_z)` at this current world; retaining a lexical
capture grants no historical receiver/handler activity. Resolved Name z and
pure Return yield that same decorated z at the original body result. Use it
in VP-BodyReturn and the Fixed equality clause. Invocation return projects
the same result/world, and hereditary J_z supplies all independent future
demands at the actual returned z-port. Apply contextual Function introduction
as for ID. This proves the bounded specialization without assuming pick's
Function membership or an already safe pick invocation. QED.

The source-free extra is one fixed-result incidence and the actually supplied
J_z public interface graph. An endpoint or provider ID without this contract
does not instantiate PICK-J. A general capture-summary construction or
necessity/minimal-size theorem belongs to a later supplier. This small theorem
does not reopen that missing summary seam or relabel it as completed.

## 8. Claim, checks and frozen integration packet

Claim class: a newly explicit native ordinary phase/production constructor,
direct source membership/admission theorem in that interpretation, finite
Echo refinement and comparison, and rule-by-rule whole-action equivariance.
Independent mathematical and specification review passed this scope; the
review record above gives the frozen input and minor clarification. The note
claims no adoption at source/public roots, foreign grammar
conformance, solver completeness, full public Generalize adequacy,
principality, production routing or aggregate gate closure.

Method: documentary constructor proof using independent carrier and hereditary
value eliminators. No assumed-transition checker, enumeration or source-vs-
source differential machine was used. Logical independence is explicit:
VP observations are generated without source operations; actual source
operations enter only the introduction proof and are checked against VP.
The ground Return-any-B example is a native grammar derivation, not a machine
oracle. Coverage is the immutable import-free nonrecursive id envelope,
arbitrary independently compatible carrier effects/divergence and arbitrarily
long finite response/resumption/future developments. Omitted State,
general capture-summary formation, general recursion and foreign-kernel identification are not
presented as counterexamples or source rejection rules. The sole pick claim
is the bounded explicit-J_z specialization in §7; general capture-summary
formation remains omitted.

Resources: zero executable semantic probes, zero builds/tests, zero children,
zero Git mutations. Reads and final integrity checks are lightweight. The
assigned optional probe bound (one process, 30s, 512MB) was unused. Research
wall time and peak RSS were not instrumented. Only the exact leased path is
written; shared task/index/authority/question updates belong to the primary.

Original producer submission packet (historical; subsequent review is recorded above):

- Exact path: `notes/theory/2026-10-08-id-public-phase-constructor.md`.
- Baseline: `4b5215320587e94acf286ff49267a00515e8812e`.
- Status: research-only, unreviewed native constructor and scoped direct proof;
  no producer self-certification.
- Proposed checkpoint message: `research: construct ordinary id invocation phases and introduction`.
- Primary/curator deltas if accepted: predecessor's initial-phase guard gap is
  replaced by concrete VP cases; record Theorem ID's precise native scope;
  retain foreign W/Z identification, actual-root Direct and source/public
  evidence-fiber transport as separate work. No canonical status is changed here.
- Final integrity/hash and dependency-byte checks are reported on submission.
- Writing stops at submission; subsequent repairs require explicit renewed lease.

### Frozen direct dependency bytes

All eleven semantic dependency files below equal the pinned baseline bytes at
submission. The newly arrived Draft invocation proposal was inspected only for
its Force-without-Request clarification; it supplies no authority or new premise.
Markdown newline, whitespace, fence balance and local-link integrity checks
passed. These are document integrity checks, not independent proof review.

```text
4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1  notes/design/2026-10-05-inferred-function-call-views.md
1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186  notes/design/2026-10-05-source-contracts-and-common-allowance.md
0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0  notes/design/2026-10-08-contextual-function-membership-definition.md
6292b778e804988b32d48df663061d01e1593340ccb584fb6a8c0565bd817cfd  notes/design/2026-10-08-captured-closure-constructor-definition.md
0f8adcf70a72d1f46bd4ca95f3984554d8cf2ff6af6434b679e991e346ffd50f  notes/theory/2026-10-08-captured-call-closure-introduction.md
fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a  notes/theory/2026-10-08-call-semantic-input-realization.md
a5efa7056b12f931892548ecf3366d66156627ec44577c99d20ca48596438ae6  notes/theory/2026-10-08-simultaneous-immutable-root-introduction.md
71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992  notes/design/2026-10-02-source-result-synthesis-choice.md
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38  notes/design/2026-10-08-source-generalize-definition.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240  notes/theory/2026-10-08-source-generalize-definition-and-proof.md
e358a5d796f0a26b2d7dbe5891b3d1f21d0ac9089ab655796fa0b696a13194e5  questions/2026-10-08-successor-generalize-root-policy/approved-answer.md
```
