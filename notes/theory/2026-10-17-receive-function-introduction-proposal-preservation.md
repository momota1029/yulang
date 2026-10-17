# Preservation attempt for the frozen c2 Function-introduction proposal

Date: 2026-10-17  
Status: candidate source audit and exact obstruction; not independently reviewed.  
Author: `/root/receive_function_introduction_proposal_preservation`; no descendants.  
Sprint: `receive-function-introduction-proposal-20261017`, revision 1.  
Contract SHA-256: `eeca47fc455c5aac9b5f9bb4e5ce6b10b7921599a07a693e2c4ac668442a7503`.  
Dispatch baseline supplied by Luna: `9f0d1d2d0`; contract baseline: `3f159b109`. Neither was inspected with Git.  
Authority: preservation attempt on the frozen candidate only; no semantic selection, implementation, production or parent-closure authority.

## 1. Result and unchanged parent

The frozen proposal does **not yet supply a concrete mathematical source
rule** whose complete telescope or preservation can be proved. Its first
unprovided output is the local source introduction of the complete inlet
`I2/L2` and its shared parameter/role/entry relation. Proposal §3(2) says that
this relation must be generated from an applicable constructor and independent
admission laws; it supplies neither that constructor instance nor those
clauses. `LocalSourceLaws` and `SharedComponent` name the required inputs but
do not expand this missing leaf. This is a missing definition/input, not a
counterexample to the original source program or a proof of impossibility.

Four stages below distinguish this first failure from two later failures:
the particular `Strict` specialization lacks its actual role and complete
operands, and transport lacks the missing rule's primitive actions and owning
records. The already selected interface, signature and Generalize rules do
useful work on their supplied local inputs; they cannot produce this leaf by
inversion. No replacement conditional parent theorem is asserted.

Preserve the original source coordinates:

```text
receive(f : Unit -> alpha+) = let g = f(Unit) in g(Unit)
alpha+ = ([ctrl]Unit) -> [ctrl]Int
c1 = f(Unit); c2 = g(Unit)
g's binding root = r_b_g; g's original value endpoint = A1
c2 descriptor occurrence = F2 at sigma2, Delta2; c2 target = Comp(E2,A2)
xi = (nu,K,D)
```

The original parent is FORWARD-FIRST-CALL §§1–2 at dependency hash
`f71cc442bcccb23f7e6f1aa6221b089abb8c24d1c4ce01fecef37995541c16b6`.
Its universal alpha, xi, actual providers/decompositions/captures, independent
punctured contexts, current worlds, responses, raw continuations and all finite
future developments remain unchanged. This packet concerns the c2 formation
premise in the independent-context construction, not a new proof of the
already reviewed local forward conclusion under MODEL. Its displayed alpha+
is one contracted case. Neither MODEL existence nor F1/FK1 or other independent
foreign-continuation quantifiers are discharged here.

## 2. Stage 1: telescope and source record audit

The reviewed predecessor retains original F2 allocation, Name/Bind identities,
ground Unit carrier construction and symbolic ReceiveSchema. Reuse those exact
fragments at their original incidences. They give addresses and ordered source
dependencies, not a complete interpretation at those addresses.

Generalize proof §3.3 requires a declaration to be the output of an actual
owning rule. Its sort, scope and complete free telescope are recorded there;
they cannot be recovered from field spelling or a Function-shaped endpoint.
Applying that requirement to proposal §3 gives this audit:

| Proposed output | Available fact | First unprovided evidence |
|---|---|---|
| Existing F2 occurrence | Original c2 allocation and sigma2/Delta2 are retained | Local inference introduction for the complete dependent fields, including their typed owning records |
| I2/L2 and parameter/role/entry relation | Actual argument source endpoint and shared source occurrences; Unit has its own ground carrier derivation | A local clause with declared operands and binder that constructs the complete inlet and shared role/entry relation before their challenges |
| IF2 | Selected IF-Insert/IF-Use retains genuine original clauses and their whole scoped references | The original complete operand/alternative contracts being inserted; incidence alone does not supply them |
| beta2, Slots, Flow, owner/receiver/profile fields | Selected native signature rules construct provenance and placement from their actual graph and primitive inputs | The complete actual inventory and independent primitive/profile/annotation laws used by this candidate |
| R2 and full observation family | Selected Strict specifies how a supplied dependent body interface participates in complete entry | No body-family introduction for an arbitrary c1-returned g; no complete local observation clauses at F2 |

The relevant source order is a dependent tree, not a flat tuple with every
field at sigma2:

```text
original component and fixed/shared anchors
  description declarations at their original sigma2, Delta2
    description-owned logical choices at their actual subscopes
      independently admitted challenge
        receipt / entry / actual Return or Request / later events
          event-local proof witnesses
```

This is a necessary shape check, not a constructed telescope for the missing
rule. A descriptor can contain a family under a binder without its outer
description depending on a future value. In Strict specifically, R is under
the formal-result binding; its instantiated R uses the actual Force-return
value/root/current world only after Return. The pending Force branch has no
such returned value. IF's later result/future interfaces likewise stay
dependent on their actual result and event. Putting a particular future
return into an outer Desc would violate this order.

The proposal's instruction to retain sigma2/Delta2 must be read together with
its instruction to retain every field's own scope. It is not permission to
flatten these dependent binders. Nor does it determine which new witness is
Shared, ViewLogic, EventField or EventProof. Generalize supplies that
distinction by owning constructor, not by existential syntax. For example,
actual rebind evidence and a description-owned proof about that same rebind
have different records even when their operands coincide.

**Stage 1 outcome.** The retained source identities are usable. Full telescope
correctness is OPEN at the first inlet/role introduction. No proposed field
has been certified merely because the proposal instructs its future producer
to supply a well-scoped field.

## 3. Stage 2: test the selected Strict constructor directly

The selected constructor record §§3.1–3.2 defines

```text
Strict(I, formal:A, R, IF)
 = ContextualFunction(Pure, ValueEntry(I),
     receipt; Force_I(wholeCarrier) >>= (a,r_a,C').
       typed-rebind(formal,a,r_a,C');
       R[formal:=(a,r_a),current:=C'];
       original-invocation-return)
```

It provides a genuine complete composition when its inputs have their stated
independent meanings. Its challenge domain uses the whole I/IF contracts and
original context/receipt guards before actual acceptance. Its observation
cases include initial and administrative prefixes, Force Return, Force/body
Request with original raw continuation and unfinished suffix, final Return,
future uses and every independently declared alternative. Positivity of its
hereditary occurrences does not establish an immediate guard or license.

There are three distinct checks at c2:

1. **Constructor operands.** I must already have its complete whole-carrier
   admission, result endpoint and dependent operations. R must be a body
   descriptor under that actual formal-result binding. IF must contain complete
   entry/return/future and alternative interfaces. SourceArg's particular Unit
   carrier does not define I's entire domain. IF placement does not type the
   inserted contracts. These genuine operand inputs are absent in the frozen
   candidate; accepting their completed values as opaque inputs would defeat
   this assignment's source-introduction requirement.
2. **Specialization at the original inferred relation.** Strict fixes Pure and
   ValueEntry. The candidate keeps role/entry relational; the original c2 facts
   do not derive the actual Pure/ValueEntry facts needed to justify this reuse
   for the original call-result domain. No rule permits using Unit's shape for
   that derivation. Constructing an abstract Strict term, if its operands were
   supplied, would still not prove that it jointly represents this original
   F2 relation or that g belongs to it. Formation, specialization and actual
   membership are separate judgments.
3. **Joint descriptor interpretation.** Even correct field declarations would
   require all their projected equations to hold at this one F2 simultaneously.
   Source-contract §2.2 makes active interpretation an additional hypothesis
   and retains the independent DescMem conjunct. It cannot certify the desired
   map by naming that predicate. Strict's introduction supplies its own complete
   interpretation only within its actual operands and selected scope.

Two operand confusions are ruled out by the actual constructor, without a new
semantic law. Original `g` is the c1-result binder whose Name supplies the c2
callee. Strict's `formal` is the callable's parameter receiving the argument
after entry. The proposal §2 illustration `Strict(I2,g,R2,IF2)` cannot literally
use original r_b_g as that parameter: it would conflate callee and argument
rebind incidences. A schematic alpha-renamed formal would need its own genuine
parameter incidence; using the spelling g proves none. This concerns the
proposal's already rejected illustration, not an adopted rule.

Similarly, c2's `Comp(E2,A2)` is the checking target for the complete invocation.
It cannot be substituted for R merely because both mention a result. R is
interpreted after Force at the callee's dependent body tuple; complete entry
may contribute effects and pending prefixes before R is reached. Its own
result/future interface and the external c2 target remain separately checked.

**Stage 2 outcome.** No WF_Dec(F2;xi) or joint embedding is derived. The exact
Strict constructor is reused as a discriminating operand contract. The failure
does not prove that the existing universe lacks a suitable general constructor,
that any non-Strict provider is actually reachable in this source, or that
the source should be restricted. It proves only that the supplied clauses
do not justify this specialization or fill its operands. Option A's complete
observation basis and Option 2's independently licensed production-only
observations remain intact; no W/Z grammar is selected.

## 4. Stage 3: substitution, graft, restriction and Generalize/use

Attempt the preservation induction at the actual owning-rule boundary. For
each primitive clause P on its original telescope, a lawful source map must
provide P's certified action on the entire incident tuple, including domain,
world and observation fields. A renaming is not evidence that an arbitrary
primitive is stable under a nontrivial substitution or a later-event map.
The inlet leaf in §2 has neither a clause P nor its typed action, so the
induction cannot start there. This is a specific missing base case, not a
request for a new global Generalize axiom.

Where the original inputs exist, the selected rules already give the
following conditional consequences, now applied to the candidate's intended
positions:

| Operation/owner | What the selected rule preserves | Limit at c2 |
|---|---|---|
| IF-Use, source-interface definition §2 | One original whole interface under its original scoped substitution; insertion/use incidences and licenses stay at their actual roots | Does not provide an unsupplied original interface or admission action |
| Native signature definition §§2–4 | Actual constituent partition, owners, receiver routes and whole-family actions; one hidden row at its original binder when hiding is certified | Does not turn support into a license, invent annotation realization or change a foreign profile meaning |
| Build, Generalize proof §4 | Original local clauses, all conjuncts, actual rule alternatives and owning records | Gen-CallView's inlet clause is missing, so Build cannot instantiate that node from the displayed schema alone |
| FinalRoot and scoped closure, §§5–5.1 | Actual final formed source/annotation root and full dependency closure | An internal F2 allocation is neither a completed root nor a new publication event |
| allocate, §5.2 | Whole eligible Desc frame per real new event; aliases share that frame; Shared and fixed dependencies remain original | Eligibility needs the absent owning records; it cannot be guessed from field names |
| Event graft and EventProof allocation, §5.2 | Actual event key `(origin,parent path,occurrence)`; EventProof can vary per frame under that same event while runtime operands stay shared | No fresh invocation, receipt, world or response is introduced by a description instance |
| SRC/SRC-J and GS/GC, §§6–7 | Construction/inversion and lawful finite joined uses under actual local premises L1–L5 | These theorems consume a provided local source law; they cannot establish its existence |

The same distinction applies to later-event restriction. Immutable certificates
restrict to the actual later compatible event; static origin does not restore
an expired authority. Request composition retains the original raw handle,
uses the actual resumed world, and appends only the remaining suffix. Any new
role-indexed bridge must supply the inlet/observation actions that commute with
those existing operations. The proposal states this obligation but provides
no such action for its missing primitive.

**Concrete preservation check.** If a completed local rule eventually supplies
one ViewLogic description witness s before its challenges, allocation places s once in
the incoming frame and routes every alias to it. The original form
`exists s; forall h; exists event-proof(h)` remains in that order. It cannot
be replaced by `forall h; exists s_h; exists event-proof(h)`. Shared s would
instead remain once across all incoming frames. This follows directly by
tracing the two different selected allocation cases, not by assigning the
unknown c2 witness to either case. It identifies the exact information its
owning introduction must supply. Thus no independent per-field, per-alias or
per-challenge witnesses can be used to complete F2 here.

**Stage 3 outcome.** Existing transport machinery remains available on its
genuine inputs. Preservation of this candidate's complete generated program
is OPEN at its inlet/role primitive and record introduction, and subsequently
its full joint embedding and primitive actions. No additional conditional
theorem is proposed as closure of that missing base case.

## 5. Stage 4: apply every available fact at original c2

Keep the original Name equation at r_b_g/A1, the ground Unit carrier, and
ReceiveSchema. The schema's received-carrier and complete-call addresses remain
distinct; no actual provider or receipt is manufactured. The audits above
then give the following exact parent application:

| Original c2/parent premise | Result |
|---|---|
| WF_Dec(F2;xi) | OPEN: first missing inlet/role introduction and then joint interpretation; no replacement F2 or xi chosen |
| Actual g membership/decomposition | No new membership result; the hypothetical A1 binding is retained, with every genuine decomposition |
| VIncl(A1,F2) | OPEN over all original A1 values; descriptor formation alone would not establish it |
| Whole-argument compatibility | Ground carrier derivation reused; checking against complete L2 remains OPEN |
| ReceiveSchema | Existing symbolic construction reused; semantic instantiation still requires original descriptor/profile laws and actual provider |
| Complete invocation-image CIncl into Comp(E2,A2) | OPEN; independent of F2's formation and its own contract |
| Enclosing Bind, residual, joint world/import/profile/path joins | OPEN; the existing structural reconstruction may consume a genuinely completed c2 at these same coordinates |

The original first-call inclusion `S_alpha subseteq S_A1` gives no converse
and no `S_A1 subseteq S_F2`. An actual c1 Return cannot establish an open
suffix for every hypothetical A1 input. No pending prefix is assigned a
return witness, and no frame action here closes F1/FK1.

The parent therefore remains open at its original scope. The useful change
is a concrete rejection of treating the frozen schema as a completed local
rule: the next input must contain an actual inlet/role clause and owning
telescope, followed by a complete constructor interpretation. Re-running
Generalize or another first-call preservation proof cannot fill that input.

## 6. Exact handoff to the owning construction

**F2-INTRO-1 / required delta.** Luna assigns the source-inference-introduction
owner of `Gen-CallView?` §3, governed by Function-view direction §§2,5(1),(4).
Required input is the actual resolved c2 component, original A1/F2/sigma2/Delta2,
argument derivation and independently supplied original local contracts.
Required output is the first actual clause deriving complete I2/L2 and the
shared parameter/role/entry relation, with every operand, binder, record class
and source incidence explicitly introduced. It must state how that clause
is generated before solving constraints; it cannot accept the desired inlet
or role package, WF_Dec, VIncl or Q as an opaque premise.

Exact falsifier: when this purported clause is expanded at c2, its inlet or
role field has no owning introduction, requires a future actual Return or
successful comparison, takes its entire desired field as input, uses Unit to
select actual role/entry, or loses an independently admitted requesting or
divergent whole carrier. This is evidence to inspect in the revised producer,
not an instruction to run a source-rejection test.

**F2-EMBED-1 / required delta.** After that introduction, the descriptor owner
must exhibit one constructor interpreting all emitted fields at original F2.
Strict reuse requires its genuine complete I/R/IF and justified Pure/ValueEntry
specialization; its formal is the actual parameter incidence, not r_b_g.
Any general role-indexed alternative must supply its complete interpreted
guards and Option 2 cases for review and the appropriate adoption decision.
Falsifier: a generated tuple is lost under DescMem, an admitted tuple evades
its complete contract, an independently licensed arm disappears, a projection
uses a different witness, or the embedding needs an unproved role cast.

**F2-TRANSPORT-1 / dependent delta.** The same local source owner must supply
the primitive typed substitution/graft/later-event actions and record outputs
needed by Build and allocation. Falsifier: a fixed dependency becomes a
template, a Shared/ViewLogic witness is copied at the wrong scope, actual
event keys differ across aliases, or expired authority/receipt is replayed.
These are local inputs to the existing selected Generalize theorem, not a new
global preservation premise.

Luna's TODO is to adjudicate this frozen obstruction, assign a changed producer
input/owner and handle any semantic alternative before new writing. This
producer has completed the four contracted stages and stops. Independent review
must assess the frozen proposal and this audit; neither author can certify the
bundle. No code evidence is needed to expose this missing mathematical clause,
so no implementation TODO or provisional code slice is invented.

## 7. Evidence, reuse and resources

This is source-definition evidence from the pinned constructors and consumers,
not newly established compiler/native correspondence. The inspected source
owners are `Gen-CallView?`, `Strict`, IF-Insert/IF-Use, native signature
provenance, and Generalize's Build/FinalRoot/ScopedClosure/allocate. Production
generation, accumulation, propagation, levels, extrusion, qualifying intrusion,
generalization and active consumers were not executed or edited. Source T,
anchored native MODEL, production conformance, principality and cutover remain
OPEN.

Reused within their actual premises: the predecessor's original c2 fragments;
selected Strict complete composition; IF and signature incidence constructors;
selected same-provider membership; Generalize's record construction, lawful
allocation and L1–L5-relative results. Rejected as closure routes: Unit-based
role inference, g/formal conflation, body/checked-result conflation, opaque
completed fields, active DescMem by citation, arbitrary field assembly,
source-only membership, unselected W/Z grammar, and Generalize as formation.
No historical failure is treated as a source counterexample or proof that a
future concrete bridge is impossible.

Checks: bounded source reads, all frozen input SHA-256 comparisons, four-stage
author premise/quantifier/binder audit and final artifact read. One attempted
read used nonexistent `notes/design/2026-10-08-inferred-function-call-views.md`;
the correct pinned October 5 file was then read. No conclusion uses that failed
read. No tests, builds, probes, compiler execution, Git, external contact,
scratch files or descendants. Only this artifact and the exact assignment
inbox are written. Author checks are not independent review.

Requested model/effort: Astra/medium; observed effective model/effort: UNKNOWN.
Actual canonical worker is the author above; separate runtime/session ID:
UNKNOWN. Current-session ACTIVE-WORK receipt: 2026-10-17 01:58:15 UTC.
Cap: 600 seconds and four contracted substantive stages; no effort increase.
Exact freeze/STOP timing and conservative resource charge are in the handoff.
Writes cease at that handoff; no worker remains running to await review.

## 8. Frozen dependencies

All following current-byte hashes were recomputed before reliance. The selected
Strict historical theorem-body hash `76d54ceb51de6836c3ecff1e520fa0ce99b881e10ccca85d75c8a4599b33b410`
is recorded provenance in the current pinned constructor/selection; it was not
independently reconstructed using Git. No new semantic dependency was added.

| Input | SHA-256 |
|---|---|
| `notes/design/2026-10-17-receive-function-inference-introduction-proposal.md` (Luna) | `a021cd088a9b0bab768a3fd509602012dae061c54b13a1353045aa80c15b71d4` |
| `tasks/agent-loop/inbox/20261017-receive-function-inference-introduction-proposal.md` (Luna) | `f999ac5f90c98cccfad271bd8729381afdb8442e201c61ef3a16babf737ff3f1` |
| `notes/theory/2026-10-17-receive-inferred-function-view-formation.md` (`/root/receive_inferred_function_view_formation`) | `7cb867df64f1d931b1667f33a6c323448d687c5d0d7fdcf9bac7535577f72590` |
| `tasks/agent-loop/inbox/20261017-receive-inferred-function-view-formation.md` (same author) | `a60a7ca1e5ea6b9d30adff7f1141b183bc8b9c8f6b8eda1302664721e7081e3a` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-08-captured-closure-constructor-definition.md` | `6292b778e804988b32d48df663061d01e1593340ccb584fb6a8c0565bd817cfd` |
| `notes/theory/2026-10-08-captured-call-closure-introduction.md` | `0f8adcf70a72d1f46bd4ca95f3984554d8cf2ff6af6434b679e991e346ffd50f` |
| `notes/design/2026-10-08-call-source-interface-definition.md` | `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c` |
| `notes/design/2026-10-08-native-signature-formation-definition.md` | `e6c6cf995a3618172e45b4f8cdf4578313c057c6ec1e3e118c4dc11b6f162ab9` |
| `notes/design/2026-10-08-contextual-function-membership-definition.md` | `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `notes/theory/2026-10-16-first-call-joint-forward-preservation.md` | `f71cc442bcccb23f7e6f1aa6221b089abb8c24d1c4ce01fecef37995541c16b6` |
| `questions/2026-10-05-production-function-denotation/approved-answer.md` | `7e7f3c717b16a70fc754c930a1654666c8b61a89a4861fca27b0ae3fa5f1890a` |
| `questions/2026-10-05-production-function-bound-membership/approved-answer.md` | `d9ddea04a44d2307cf587bc4ae9b2a1c50d062c4077306a5bf9ea9da00eca179` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |

Historical dependency authors/review attributions remain those recorded in the
pinned originals; current effective model telemetry is not inferred from those
attributions. This artifact is a new single-author preservation attempt only.
