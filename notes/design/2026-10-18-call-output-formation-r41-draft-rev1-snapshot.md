# R41 draft: joint Call output and operation formation

Status: **Draft; proposal only; frozen revision 1 on submission.** Independent
review NOT_RUN. No rule is adopted and no semantic preservation, source/native
correspondence, principality or production theorem is certified.

Assignment: `R41-CALL-OUTPUT-FORMATION-PROPOSAL`. Sole author and writer:
`/root/r41_call_output_proposal`; no descendants or coauthors. Requested
Sol/high; observed effective model/effort UNKNOWN/UNKNOWN. Current-session
evidence is Luna's delivered assignment to this worker; opaque session ID
UNKNOWN. Contract revision 1:
`tasks/agent-loop/sprints/call-output-formation-20261018-r41.md`, SHA-256
`1ff014a662f02e4c5e6d5fd084da88f7af6fd993b85437a063fb65807ae745f4`.
Baseline supplied by Luna: `887eed4370278cd9e789fb2b9b10ff58369da540`;
no Git observation was made.

## 1. Actual result and application to the parent

This packet specifies one **schematic joint formation rule**, JOF, whose
premise order is acyclic: form the input context and operand interfaces;
declare the ordinary output description; register the result-indexed original
interfaces; construct all original clauses; then assemble complete `Q_q`.
The premise is not an already formed `Q_q`, nor an already formed telescope
of its arms. The dependent signature below specifies where each original
header must be instantiated and where each of its binders remains bound.

The exact q instance cannot yet be authenticated against the existing source
contract. The original Application/Call owner must supply a **uniform
output-header law**: its complete original result and arm schemas must form
under the candidate's output binder, at the chosen prefix, with the same
constraints and original scoped witnesses. The inspected sources supply no
such q-indexed law. Thus this is an explicit rule proposal with an exact
unproved owner law, not a derivation from adopted rules or an approval-ready
claim of equivalence. The limitation also prevents printing concrete types
for missing q-specific primitive-header fields; names for their required
types below are typed interface projections, not invented original types.

Applied to the original parent in R40's **Parent and fixed outcome** and R36
§1, the proposal identifies the order in which the missing source owner could
produce `Desc` and complete `Q_q`. It closes no original condition: **0 → 0**.
Keep the full inference/evaluator theorem and Simple-sub A/B claims, every
source, provider, assignment, component, world, context, occurrence, event,
guard, continuation, interaction, future and history quantifier, arbitrary
well-scoped W, both independent incoming frames and their aliases. F1's
finite frame/image obligations and FK1's independent foreign-continuation
contracts remain separate. N-Transport, complete Call/effects, soundness,
required principality, termination, actual C/D CopyScope, Generalize,
source/native correspondence and production remain OPEN.

## 2. The exact occurrence and proposed insertion cursor

The unchanged specimen is:

```yu
my outer = { my loop x = { my direct = loop x; my helper y = loop y; my first = helper x; my second = helper x; helper x }; loop }
```

Select outer's local binding `helper`, its lambda body Apply, its callee Name
resolved to the registered local `loop`, and its argument Name resolved to
that helper's formal `y`. This is q. The `loop x` RHS of `direct` is t; the
three `helper x` applications are h1, h2, h3 in source order. They retain
separate origins. The fixture at
`crates/yu-solver/tests/candidate_local_self_recursion.rs:106–122` and R40's
reviewed partial derivation corroborate this structural selection. No numeric
runtime occurrence or pair of observed FreshUse routes is claimed.

Write `C_g` for helper's authentic source description registration, distinct
from `C_f` for loop. This is a candidate validating-owner selection, not a
deduction from their Value-reference SCC. Existing recursive Name resolution
still references f's single monomorphic registered interface. The two child
schemas are exactly R40's:

```text
cf = result(name loop) : Comp(empty,A_f)
ca = result(name y)    : Comp(empty,B)
```

Here B is y's earlier ordinary Parameter description at its own pre-helper-
challenge scope; reading y introduces no second B. The lexical capture
certificate is not B's or A_q's ordinary dependency telescope.

Define `sigma_q` as the original body-description cursor immediately after
these two child interface schemas are available and before opening **q's own**
callee-result, receiver, receipt, response or returned-value binders. Let

```text
Gamma_q = (d_1:S_1, ..., d_n:S_n(d_1,...,d_(n-1)))
```

be the entire authentic input telescope there. Each d_j retains its original
owner o_j, record class k_j and original scope sigma_j, and its actual typed
inclusion into this cursor. Every free dependency of S_j precedes d_j.
Nested child schemas remain nested; their internal event/proof telescopes
are not flattened into Gamma_q. Any enclosing outer/helper invocation,
receipt, rebind, current world or proof binder already in this prefix remains
there. None is removed, exchanged with B, or guessed from a native level.

This is the earliest insertion cursor **specified by JOF's complete-input
convention**: every d_j is declared a retained input, and both actual child
schemas must first be available. It is not a proved earliest cursor of the
existing language. The actual full q-specific list of d_j, S_j, o_j, k_j and
sigma_j has not been supplied. In particular no claim is made that Gamma_q
is empty, just a lexical capture list, or before g's challenge.

## 3. One joint signature, with binder-before-use explicit

### 3.1 What the proposed rule consumes

JOF consumes the resolved q, original binder tree, input cursor and two
actual operand schemas. It also uses the original primitive declarations,
their complete typed headers, original clause/reference syntax and scoped
operand maps, and L1/L2's independently specified operator/phase signatures.
These are original source inputs, not an extra runtime dependency.

For an original primitive alpha, write its header exactly as in IF §3.1:

```text
P_alpha = (p_1:U_1, ..., p_m:U_m(p_<m))
P_alpha |- T_alpha = (t_1:V_1, ..., t_k:V_k(p_*,t_<k))
P_alpha |- w : Prim_alpha(h,y;xi)
```

`U_j` and `V_j` mean the **actual declared types** projected from that
independently typed header. They are not fresh predicates chosen to make
Call work. All licenses, guards, admissions, changed-provider contracts and
lawful actions remain its genuine original inputs. For a root reference use
retain its actual registered header and typed substitution m. No premise
requires alpha's interface already placed at q; IF-Insert/IF-Use construct
that placement after the output binder exists.

In particular, the rule does not take a package saying “all Q_q arms already
form.” If the original atomic/root headers or the operand maps needed for a
particular arm cannot be supplied independently at the cursor specified
below, that arm's formation fails and JOF has no complete q instance. The
original arm stays required; it is never removed from the accepted domain.

### 3.2 Declaration and registration order

The candidate's ordered signature is:

```text
T ; Gamma_q
  A_q : ValueDescription
  E_q : OriginalApplicationEffectDescription
  R_q : RegisteredCallHeader(q, Comp(E_q,A_q), original source indices)
  G_q : OriginalClauseGraph formed against R_q and original registered headers
  F_q : FrameCall(q, assemble(R_q,G_q))
  ---------------------------------------------------------- JOF, proposal
  Q_q := assemble(R_q,G_q)
  I_q := Computation(E_q,A_q)
  Desc(C_g, rho_A, ValueDescription, sigma_q, Delta_A)
  Description(C_g,rho_A) at q's output-value coordinate o_q
```

This is construction order, not a flat existential telescope of execution
witnesses. `rho_A = (C_g,q,output-value-description)` is the proposed actual
declaration address; `Delta_A := Gamma_q`, with identity typed inclusion.
The ordinary logical declaration A_q is after all Gamma_q dependencies and
before every q-local use of A_q. It is a fresh flexible source endpoint,
not a definition A_q := an eventual returned provider. E_q is the existing
Application symbolic effect coordinate: the proposal retains that coordinate
and requires its original effect formation/scope evidence. It does not create
an ordinary Value Desc for E_q, equate it with invocation effect, or move an
original effect dependency. If that evidence requires a later binder, this
candidate fails at E_q. A_q's type has no E_q dependency.

`RegisteredCallHeader` declares ports and complete result-indexed **types**;
it is not membership, solved constraints, or an executed Call. At this stage
only signatures are registered; clause bodies and contextual inclusions
follow. Finite recursive graph nodes reference their declared interfaces,
as in IF §6. No node's signature may use an unintroduced value binder.
Simultaneous root registration permits recursive references to declared
interfaces; it supplies no recursive member/world validity or solution.

The proposed classes and scopes are fixed as follows:

| Declaration/field | Owner and class | Scope, order and typed dependency |
| --- | --- | --- |
| Existing d_j | Original o_j/k_j, including Intrinsic, Internal, Established, Desc, Shared, ViewLogic, EventField or EventProof as actually supplied | Original sigma_j and S_j(d_<j), retained without reclassification; not a new JOF declaration |
| A_q | Proposed Application/Call output owner in C_g; ordinary Desc, source sort ValueDescription | sigma_q; all Gamma_q in order; before any q-local event, arm parameter or return |
| E_q | Original Application effect owner/class | Original effect scope and dependencies, referenced before result header; authentic evidence presently required, not manufactured |
| R_q and graph nodes | Source operator/declaration registration; static interface records | Under Gamma_q,A_q,E_q with exactly the original indexed header types; no field of G_q/F_q is a premise |
| Operand/arm parameters and evidence | Their original primitive/operator owner and original class | Each original P/T telescope under its actual root/use substitution, in its original region; never promoted into Delta_A |
| Actual receipt/response/rebind/provider/world fields | Original Event/EventField, Shared/OneShot where originally installed | At their actual event/return binder; actual event fields shared when the event is shared |
| Latent logical certificates | Original ViewLogic/EventProof | At their original description/event proof position; independent description frames do not merge them |
| F_q and Description edge | JOF plus IF contextual constructors; construction data | After all required headers/clauses form; references the previously introduced A_q, not a new binder |

This candidate does not infer the listed existing classes from names. Where
their original tags/types are absent, the candidate remains uninstantiated.

### 3.3 The complete dependent structural and alternative signature

For any formal `a:ValueDescription` and original effect `e`, define the
proposed registered result header by **symbolically plugging** a and e into
the output-coordinate slots of the original operator signatures. This forms
schemas under a formal parameter; it supplies no actual observation or
inhabitant for any a. Its legality against the original source owner is the
missing law in §5. JOF instantiates it with a=A_q, e=E_q only after declaring
them. Every other old coordinate, constraint and dependency remains intact.

The structural branch has this ordered dependent schema:

```text
Gamma_q, A_q, E_q
  cf : IF(CalleeRef_q)                           [actual callee operand]
  arg : WholeCarrierSlot(WholeArgRef_q)           [latent/capture schema bound]
  (actual_f,C1) : OriginalCalleeReturn(cf)
  recv : IF(ExecuteCallable(actual_f,arg,C1))
  (actual_result,C2) : OriginalCallReturn(Comp(E_q,A_q),o_q; recv)
  future : OriginalFutureInterface(actual_result,C2)
```

These type expressions are projections of the original operator headers;
`OriginalCallReturn` includes its original ordered Bind/result relation. It
does not introduce an equality between a description and a provider. Each
field remains a suspended dependent schema rather than an assertion that the
callee returns or that the carrier terminates. The actual receiver's role,
entry, captures, receipt, Force/rebind if Value entry, body, native return,
designated consumer and invocation return are the original ordered fields
inside recv. Retained-computation entry omits its original entry Force.
Invocation effect, callee effect, whole-argument effect and E_q remain separate
ports linked only by their original constraints.

The complete graph also retains the following **sibling and nested schemas**;
they are not conjunctive execution witnesses required on a structural return:

| Original region | Binder order and full retained dependency |
| --- | --- |
| Callee pending | Original request/current configuration/raw callee continuation; then original response and resumed C'; then the unreached receiver/argument/entry/body/consumer/return/future suffix under that response. The structural `(actual_f,C1)` is bound only when that suffix obtains it. No receiver receipt is reported before it occurs. |
| Receiver/argument pending | Actual receiver/entry/receipt prefix; original request/raw continuation; original response/resumed C'; remaining Force/rebind/body/native-return/consumer/invocation-return suffix at C'. Receipt is not replayed. A retained carrier keeps its own original phase alternative. |
| Return and future | Original actual returned provider and current C2 before that provider's latent interface, admitted future-use/response schema and evidence. Provider-indexed future types cannot be hoisted above their provider. |
| Conservative W clause alpha | Entire original P_alpha[m] followed by T_alpha[m] in declared order, one whole changed/unchanged witness tuple, guard and original license/admission fields at their actual positions. The original map to Call result uses A_q only as output description. Every changed or introduced provider has its own dependent future/admission contract. |
| Z and all other original alternatives | Same P_alpha/T_alpha rule at the actual callee, receiver, whole-Call or future root and actual typed reference. Preserve each arm's own source/root origin and substitutions. Unanchored whole-Call Z is not forced through a structural callee prefix. An infinite family stays a whole parameterized schema. |
| Source/index fields | Exact original q, CallEff occurrence, lexical u_f, checking u, exposure, ElimOrigin and all Idx(q) data. Their final frame projection does not move their original declaration scopes. |

The formal completion is a registered relation graph using precisely IF
§3.2's grammar: Prim retains P/T under m; Union retains both contextual
operand interfaces and original tagged result maps; Conj uses one original
shared whole tuple; Bind uses the first result/current world before its
second schema; Delay binds its original latent/capture schema; Scope binds
at the original location; Rename substitutes the same legal whole map; Ref
uses the registered declared interface without unfolding. Nested Call uses
the same full signature. Original Return, producer and consumer cases keep
their actual interfaces. IF-Insert and IF-Use then emit the slots/inclusions.

Consequently the outer frame order is the original IF order
`callee; arg; callee_result; receiver; return; future; arms; source`, with
all internal binders still nested. No linear order across incompatible
branches is invented. The arm index is the **entire actual original clause
graph**, not a finite guessed list of W/Z witnesses. Predicate bodies may
remain opaque; their complete typed headers and actual references may not.
Without those headers no table entry is claimed to be a formed q arm.

Finally synthesis A is unchanged:

```text
I_q = Computation(E_q,A_q)
n_q = Normalize(I_q,reify(call(cf,ca)))
Result(I_q) = Comp(E_q,A_q)
helper body skeleton = Fun(Value(B),Comp(E_q,A_q))
```

The helper body's forwarded interface is not helper's complete invocation
interface. Loop's final body forwards h3's separate output A_h3, not A_q.
No extra pure layer, implicit Force, result-interpretation parameter or
solved-row selection is introduced. Simple-sub generates and accumulates
the original constraints with open endpoints, then propagates, performs
levels/extrusion, qualifying intrusion and generalization as before; no
satisfiability or successful query is a formation premise.

## 4. R38 comparison and the precise scope of erasure

R38's actual equation is `Delta_R := Gamma_q` (the reverse spelling in the
R41 contract's introductory paragraph is not another candidate). JOF retains
this as an explicit **full-context proposal convention**. It repairs R38's
premise “child interfaces and all complete Q_q arm schemas formed” by placing
A_q before registration and construction of those schemas. R38's provisional
`C_A=C_g` selection is likewise retained as a proposal, not established fact.
Neither full-context placement nor its Generalize consequences are accepted
as existing language behavior.

Let `erase_op` remove only JOF/Desc retention metadata, contextual frame
records and inclusions, and identify the candidate symbolic names A_q,E_q
with the existing Application row's output-coordinate names. Keep every
original clause, arm tag, bound variable, header substitution, license,
constraint, provider, world, raw continuation and source origin. In particular
**do not erase an independent choice of A_q from a strategy**; coordinate
renaming is not elimination of a quantifier.

Two syntactic results can be checked from this proposal:

1. Erasing its code gives exactly the existing expression construction
   `reify(call(cf,ca))` and its known Computation normalization. The operands
   and the complete invocation program have no added dynamic operation.
2. Erasing the contextual records of its clause-graph construction gives the
   original clause syntax with the same formal output parameter, by induction
   on that syntax. Prim keeps its declaration and m; Conj/Union keep their
   shared tuple/tagged operands; Scope/Bind keep their binder order; Ref
   keeps its registered root and substitution. No arm or dependent evidence
   is deleted. This is a formal-schema identity, not proof that those formal
   substitutions instantiate the authentic q declaration.

For any *already matched* original typed Q with these exact headers and
substitutions, the old operation and erased candidate therefore use identical
transition operands. The pending equations are the original ones:

```text
Request(r,C,k_f) >>= S
  = Request(r,C,(response,C'). k_f(response,C') >>= S)
Request(r,C,k_arg) >>= S_after_entry
  = Request(r,C,(response,C'). k_arg(response,C') >>= S_after_entry)
```

The same raw continuations, resumed current world, once-only receipt and
provider-indexed future operations occur. Opaque arm evidence is retained
verbatim at its own original interface. This reuses the operation-erasure
argument of IF §10 and Owned Call §§4–5,9 **only under their authentic
original-contract premises**. It supplies no comparison of unmatched typed
source derivations or active Generalize/Contrib/Inc consumers.

## 5. The exact unproved preservation law, and where it fails to follow

There is no established preservation direction between the **whole new
formation rule** and the existing accepted source contract. The first open
judgment is at the original Application/Call output-parameter owner:

```text
T ; Gamma_q ; a:ValueDescription ; e:original effect coordinate
  |- the actual original result/receiver/return/future and every arm header
     at q form by the original scoped substitutions with output coordinate a,
     using no free binder below sigma_q,
     and instantiate the same authentic original SpecCall_q declaration.
```

Call this `R41-UNIFORM-OUTPUT-HEADER`. It is not licensed by endpoint sort,
native child Result, successful inference, IF's frame constructor, or L1–L5
as merely named premises. IF starts from authentic complete Q; it cannot
independently supply this missing owner instance. A root signature copied
from an already formed Q without authenticating its parameter scope would
reintroduce R38's circle. JOF instead exposes the missing instance here.

More explicitly, fix the original full Call relation `R_U_all`, whose
authentic reference is `EvalCall(Q_q,h,y)` under SpecCall_q, not merely
ExecuteCallable's receiver relation. For any original finite joint client U,
well-scoped W and original public coordinates, let D_old(U,W) be its original
typed proof/strategy set and D_JOF(U,W) the proposed one. Raw deletion of
JOF metadata and output-coordinate renaming defines a map pi into **raw
decorated graphs**, not yet into D_old. The desired soundness direction is
`pi(D_JOF(U,W)) subseteq D_old(U,W)` preserving the complete Call witness;
the desired lifting direction is that every d in D_old(U,W) has a preimage
in D_JOF(U,W) with the same public fields and original scoped strategies.
Neither statement is proved here. The syntactic identities in §4 do not
type pi's codomain, supply a preimage, or eliminate the new binder. Equality
of accepted/public fibers, even if later established, would still not by
itself establish principal inference or native solver completeness.

If that formation is supplied, two additional source preservation obligations
still require proof at the same owner and Generalize consumers:

| Direction | Required evidence, with original quantifiers intact |
| --- | --- |
| Candidate to original | An original well-formed output declaration/reference corresponding to this A_q and the whole generated constraint graph; forgetting the new Desc registration must yield an original source derivation with the same complete observations and scoped witnesses. A fresh candidate Desc cannot authenticate its own old counterpart. |
| Original to candidate | For every original source derivation/strategy at q, a lift selecting A_q at sigma_q using only Gamma_q, preserving every original arm, event, witness, admission and future, uniformly before q-local challenges. One old returning observation with some result type is insufficient. |
| Original active consumers in both directions | Classification, dependency and eligibility actions for the retained Desc must agree with the original source's introduction and publication; preserve both independent frames, aliases and arbitrary W. Extra allowed dependence or a newly eligible binder must not add or remove original fibers. |

Writing the proposed source strategy order as

```text
Gamma_q ; choose A_q[Gamma_q] ; q-local event/arm telescopes
```

does not justify replacing an old `choose A ; helper challenge h ; ...`
by `helper challenge h ; choose A(h) ; ...`, nor an old
`q-return p ; choose A(p)` by a pre-return choice. These differences can
respect untyped code erasure and still change typing or joint-use fibers.
R36's total coordinate definition c:=P cannot repair this: this proposal
introduces a fresh flexible endpoint and has no already authenticated P at
the required scope. Its definitional-extension proof is inapplicable here.

No source-qualified counterexample is constructed. Exact falsifiers are:

- an authentic original arm/header needs a free q-response/returned-provider
  dependency in A_q below sigma_q, or an original effect header cannot form
  at the specified position;
- an authentic original source law places A_q before an inherited challenge
  present in Gamma_q, so the proposal admits a new challenge-dependent
  strategy, or the converse lift cannot preserve its original dependencies;
- an actual primitive/root header or typed arm reference cannot be instantiated
  without a field of the not-yet-formed complete Q_q;
- a W/Z arm changes provider/admission data but retains another provider's
  license/future contract; a whole-Call Z is forced through the structural
  prefix; a pending suffix drops a raw continuation, resumes in an old world,
  or repeats receipt;
- erasure deletes a constraint/arm, alters a result consumer, treats A_q as
  an event witness, or exchanges q with t/h1/h2/h3 or an invocation-effect port.

The selected method changed R38/R40's attempted existing-rule derivation to
an explicit proposal signature and an erasure/quantifier audit. It did not
rename the same missing premise as a successful conditional theorem. Further
formation or acceptance claims require the source owner or an authority
decision through Luna; this assignment stops at that boundary.

## 6. Native boundary, reusable evidence and mutual TODOs

Inspected read-only owners corroborate the distinction:

- `ConstraintBatch::emit_candidate_source`, `candidate_source.rs:1316–1360`,
  retains q's Apply input/recipe, exact occurrence/checking cause, result Value
  position and separate application-effect position. It emits no logical
  output scope/ordered dependent declaration header in those fields.
- `CandidateSourceCall::pending_construction` and
  `PendingCallConstruction::suppliers`, `candidate_call.rs:380–427`, request
  original Gen-Call-0, whole carrier and complete receiver/result/future
  suppliers. Requests do not instantiate the required source header law.
- `InferenceSession::admit_candidate_fact`, `shadow_apply.rs:1763–1880`,
  checks q's recipe/input positions and builds a negative Function demand
  whose fourth field is Result. `NativeInterface.result` is that Value term;
  `.demand` is the Function. Fresh invocation effect is a separate field.
- `candidate_function_port_admit`, `candidate_context.rs:3375–3440`, preserves
  Result with `Dependency::FunctionPort`; its source/scoped-flow retention
  does not construct a logical Desc telescope.

R40's reviewed trace supplies the remaining structural chain: typed Result
child at `lib.rs:12655–12705`; Preserve admission and FunctionPort dependency;
Transport/Context/Dispatch drain at `:12354–12436`; helper Lambda recipe/body
endpoint at `candidate_source.rs:1409–1425` and `lib.rs:11342–11361`; actual
extrusion rewrite/context dependency at `lib.rs:12588–12622` and
`candidate_context.rs:3351–3372`. This packet reuses that frozen trace; it
does not independently certify it or equate retained copies by raw ID.

`NO_SAFE_CODE_SLICE`: the inspected source emitter and pending-supplier owner
do not supply the missing original law. No instrumentation can create its
authority. After a source header is justified, the minimal provisional
implementation TODO would retain its exact declaration/context reference in
ApplySourceInput, carry it to NativeInterface and Result propagation, and
reject occurrence/result/scope mismatch. It must also retain the whole
effect/provider/future tuple; a Value row alone is insufficient. No such
patch is authorized here.

| Stable mutual TODO / owner via Luna | Inputs and first missing evidence | Output and exact discriminator |
| --- | --- | --- |
| R41-UNIFORM-OUTPUT-HEADER / original Application/Call source-rule owner | Original T/Gamma_q with typed field provenance; original effect/header formation; all independent primitive/root signatures and actual references | Authentic q-indexed ordered signature and old-owner parameter law, or a concrete inaccessible dependency/required new decision. Reject reliance on preformed Q or solved rows. |
| R41-SOURCE-ERASURE-LIFT / source-rule and Generalize owners | Frozen candidate plus the preceding law; original complete source strategies and both independent frames | Both source derivation/strategy directions and original active-consumer preservation; falsified by changed strategy dependency, eligibility, W fiber or dropped arm. |
| R41-RESULT-COMMUTATION / source/native bridge owner | Authenticated source declaration and complete result tuple; frozen R40 native trace and R41 owner map | Typed source-to-Apply/demand/Result/copy correspondence; wrong occurrence, effect field, provider or unavailable dependency rejects it. |
| R41-COPY-PUBLICATION / actual CopyScope/Generalize/F1/FK1 owners | The preceding source and map outputs, actual two copy contexts and original component registrations | Separate real copy scopes and lawful publication actions; no inference of foreign-continuation transport from one local Call frame. |

Luna's independent R41 owner map may continue while this packet is frozen.
It is not an input to this artifact and cannot supply the missing source law
by native interpretation. Fresh review is Luna's responsibility; this author
is ineligible to independently certify a combined result.

Reused: R40's exact-q symbolic Application derivation and CLEAN bounded review;
its corrected reviewed native structural trace; IF's complete contextual
constructors and finite registered graph **under their original premises**;
Owned Call's full evidence preservation under authentic SpecCall/C0;
Generalize's record classes and scoped action under L1–L5; synthesis A and
top-level Simple-sub principles. Rejected as missing-law substitutes: R38's
preformed-arm premise, a row/level, Value SCC merger, supplier names, successful
queries, assumed-transition tests, and R36's proof for genuine definitions
applied to a fresh flexible declaration. No withdrawn bypass is restored.

## 7. Frozen inputs, authors, checks and stop receipt

All 18 direct R41 input hashes and the R41 contract hash matched before
construction; all are revalidated at freeze. Historical embedded pin lists
are not silently upgraded: R38's shadow_apply pin differs from the current
R41/R40 pin and is used only as historical provenance, never as this audit's
native-byte premise.

| Input | SHA-256 | Provenance |
| --- | --- | --- |
| R40 contract | `a1ca3da89e79c7722f2f4e4a228086db360f0279ea1ee7e31ae6b970315eaa45` | Luna |
| R40 proof | `fedca7cc54b8a552cfa1f3fee9ad396dc4646e28e4ebbfa0f5b93c26f3669275` | /root/r40_application_result_proof |
| R40 proof review | `a6575438f13815cd62c052e1daa94d9fc00986c90595d7f3be9db84861c2f4a5` | Luna receipt of /root/r40_proof_review |
| R40 native trace | `71b7cae74f965f08e8c2877072ca179e47de5d4e05b335c19d95c7deb53ca2ea` | /root, primary; review scope in artifact |
| R38 candidate | `63ba5b3fe053b8ced790f089ab0a6defcf554b440114b94a9f901cec3176af92` | /root/r38_call_result_proof |
| R38 contract rev2 | `f119bf4f031ab8b28fd060921723ddb235bf208ff3b48a87bc169aa1b7fa0421` | Luna |
| Call source definition | `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c` | Primary selection; reviews recorded there |
| Owned Call construction | `ead206bff341c82993acbaecda25ae1d3a760397796bbbbb53ba3ef917a53fb1` | Original individual producer UNKNOWN; selected reviewed scopes |
| IF construction | `278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98` | Original individual producer UNKNOWN; selected reviewed scopes |
| Typed computation core | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` | Primary design; selected synthesis scope only |
| Generalize definition/proof | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` | Researcher; selected independently reviewed scope |
| Result synthesis A | `71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992` | User approval, primary transcription |
| Top-level principles | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` | User decision, primary transcription |
| candidate_source.rs | `66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c` | Unknown-author dirty input; read only |
| candidate_call.rs | `e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479` | Unknown-author dirty input; read only |
| shadow_apply.rs | `d5e6b179fd4f6fbca579b0fa4d479d8bd11b520d774acbf27f414451c4691137` | Unknown-author dirty input; read only |
| lib.rs | `2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee` | Unknown-author dirty input; read only |
| candidate_context.rs | `42f89dcf5fa6d7095db1e220c89308a2a35f4e74b05c3e8821d4fb2e3e32b0ca` | Unknown-author dirty input; read only |

Paths are exactly those in the R41 contract; Rust names are under
`crates/yu-solver/src/`. Supplemental existing evidence: R36 parent locator
`notes/theory/2026-10-18-apply-scope-publication-r36.md`, SHA-256
`43edea46d93a8b7eac6a68e6544aa34cc36797c59e232fd31599d8eec15ef5a9`,
author /root/r36_proof, candidate only; structural fixture
`crates/yu-solver/tests/candidate_local_self_recursion.rs`, SHA-256
`47ced76fe8f0f136c42802b2376ca09f7cadec0fc8e5b1b3d4c6acc7bc613e55`,
author UNKNOWN, read only. Neither is an added semantic premise.

Checks: static bounded source/authority reads, symbolic binder-order and
erasure audit, SHA-256 verification and output-format inspection. No proof
checker, tests, Cargo, compiler CLI, runtime, source-acceptance measurement,
Git, external contact or nested CLI. No claim of independent verification.
Concrete q header instantiation, all original semantic owner laws, strategy
preservation/reflection, actual native commutation, copies, both-frame/FK1
transport and production remain omitted/open as explicitly assigned above.

Resource grant: 1200 seconds charged in full, no renewal, refund or transfer;
observed exact active duration/CPU/RSS UNKNOWN. Astra 0, descendants 0,
probes 0, heavy verification 0. Only written/new paths: this file and
`tasks/agent-loop/inbox/20261018-call-output-formation-r41.md`. Scratch and
generated paths: none. No central/shared record, foreign artifact, production
code, fixture/test/expectation, semantics, rule/config/manifest/lockfile or
question was edited.

Writer-stop receipt: revision 1 becomes immutable at submission of its byte
hash in the one assigned inbox. Both leases then stop writing; no descendant
or generated-output lease exists. The assignment ends at the exact missing
original source owner-law/authority boundary. It is not RUNNING while awaiting
Luna's intake or fresh review. The only next action is Luna's frozen-candidate
review/adjudication and assignment of the named source-owner evidence.
