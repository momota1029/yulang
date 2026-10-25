# Force normal-leave applicability: exact frontier criterion

Status: **frozen candidate, revision 1; outcome 3 (exact source obstruction)**.
The conditional mathematical propositions below are new author results awaiting
fresh independent review. `accepted_force_leave_entails_result_transport` is
neither proved nor refuted. No complete clause-model separation or semantic
underdetermination is claimed. N1, O-NORM, O-RESULT, source/native correspondence
and the original semantics/inference parent remain OPEN.

## Contract, author and unchanged parent

Sprint: `FORCE-LOCAL-APPLICABILITY-20261025`, contract r12.1,
`tasks/agent-loop/sprints/force-local-applicability-20261025-r12-rev1.md`, SHA-256
`b2082b6aedf6d97f0a89eb467f6eab46155a4b54b0fed4fdb55a6a0ce63fab4d`.
Luna supplies baseline `44a61f3ba5a7e0ec36612de6bf022071d093f6c2` and contract
commit `25358f96bb297750d29ff52c228c9daf21657a1b`; no Git verification occurred.

Sole author: `/root/force_local_applicability_sol_r12`, session
`FORCE-LOCAL-APPLICABILITY-20261025/root-turn-5`. The NEW_TASK and current-state
launch receipt grant the sequential leases after Astra's confirmed STOP with no
output. Astra is not a coauthor of this artifact. Requested model/effort:
`gpt-6.1-sol`/`high`; effective observed model/effort: UNKNOWN/UNKNOWN. No model
switch, descendant, reviewer appointment or independent certification occurred.

The parent question quantifies over **each** retained refined typed Force/Delay
derivation D, one consistent packet/type/owner interpretation, an **actual finite
normal return** of operand `t : U(E,A)` with body-result packet `r : A`, and
**every finite typed suffix p of that result instance**. Recursive, nominal,
instantiated, aliased, captured and returned latent values remain included.
There is no ground-type, depth, termination-of-all-runs or local-owner restriction.
Requests/failures are not normal returns. F1/FK1 and foreign-continuation
quantifiers are not discharged by this local normal-leave analysis.

The route component inherited from r10 is

```text
FR:  Flow*_(G+leave)(x,a; o,p)
       iff Flow*_G(x,a; r,p)
           or Flow*_G(x,a; t,force.result · p)
```

for every old endpoint `(x,a)` and every such p, where o must be the **actual,
source-authorized** output occurrence. This route formula is only one component
of the required whole-packet constructor; inherited witness/predicate identity,
profile domains, owners, allocation and the actual underlying result also need
their source justification.

## 1. Typed suffixes and the finite graph interface

**Proposition T (typed suffix distinction).** For the retained instantiated
signature `U(E,A)`, a finite typed result suffix p has the tagged operand suffix
`k(p)=force.result · p`. Prefixing preserves its entire suffix and is injective
as a tagged path operation. In particular, for `A=U(E2,B)`,

```text
p = force.effect
k(p) = force.result.force.effect
```

is distinct from the operand's `force.effect`. This follows by the signature
child labels and the retained instance, not from equality of terminal type
nodes, effect families or path colors (operational paper 1193–1209, 1245,
1300–1317). T defines no Flow edge. Abstract binders require the retained
descriptor/instance before their finite paths can be inspected; T does not
pretend a delayed shape is absent or enumerate an infinite nominal unfolding.

For the following propositions fix a common interpreted history G. Let O be
its finite set of occurrence vertices; endpoint ports can still range over
infinitely many finite typed paths. Write R for its **reflexive, transitive**
Flow relation on old typed endpoints. Each edge denotes its actual typed path
relation, with both occurrence and port required to match. Old aliases are
distinct unless the retained interpretation actually identifies the occurrence;
underlying pointer equality adds no edge. `t,r` belong to O; they need not be
unequal, and their source indices remain distinguishable.

The **extension hypotheses H** are explicit and conditional:

1. The actual administrative normal-leave extension has a finite set N of
   newly allocated occurrences, disjoint from O. It preserves all old rows.
2. Its entire new Flow relation is the row batch Delta. Every Delta edge has
   its target in N and respects the allocation order. Sources lie in O or N.
   Thus no new edge enters an old occurrence, including through an alias.
3. The actual source output is an identified occurrence o in O union N, with
   the authorized result signature A. The common interpretation and exact
   typed endpoints are fixed during this factorization.

H is a graph interface, not a selected Force rule. New boundaries, receipts,
observations and non-Flow packet operations are not characterized by H. An
accepted-source use must audit those operations separately. The chronological
fresh-target discipline at paper 553–575 supports H for the Flow rows actually
recorded; it does not identify the Force batch, o, or its path relations.

Define the leave **frontier relation B** from old endpoints to result paths:

```text
if o is old: B(y,a;p) iff y=o and a=p;
if o is new: B(y,a;p) iff a nonempty Delta-only path leads (y,a) to (o,p).
```

In the second case the path's first source is old and all its later vertices
are new. B includes **all** such paths, not selected boundary/profile witnesses.
Its domain is the set of old endpoints admitting this formula; its image is
the p in `P_A` admitting a witness. These domains/images are defined from Delta,
not yet computed for the actual source leave. A finite DAG has finitely many
occurrence routes; their finite-template compositions describe B without
bounding or enumerating the typed suffixes.

## 2. Conditional mathematical propositions and both directions

**Proposition F (frontier factorization).** Under H, for every old `(x,a)`
and every `p in P_A`,

```text
Flow*_(G+Delta)(x,a; o,p)
  iff exists old (y,b). R(x,a; y,b) and B(y,b;p).
```

*Proof.* If o is old, a path ending there cannot contain a Delta edge: after
entering N it cannot return to O. Thus the left side is `R(x,a;o,p)`, precisely
the right side with B's old-output identity. If o is new, the path has a first
edge entering N. Before it all edges are old, giving R; from it onward no edge
can be old, since old edges have old endpoints and Delta cannot return to O.
That nonempty suffix is a Delta-only path, giving B. Conversely concatenate
the R path and the B path, using the identical intermediate occurrence and
port. For old o the B segment is empty. This proves both directions. No path
color equality or unrecorded alias is used. The argument quantifies over each
finite port p and does not require finitely many ports. QED.

Define three conditions on this **actual** B:

```text
SOUND:
  B(y,b;p) implies R(y,b; r,p) or R(y,b; t,k(p)).

COVER-ACTUAL:
  for every p, exists old (y,b). R(r,p; y,b) and B(y,b;p).

COVER-OPERAND:
  for every p, exists old (y,b). R(t,k(p); y,b) and B(y,b;p).
```

All displayed quantifiers range over the complete typed domains just defined.
SOUND covers every incoming frontier route, even one whose endpoint currently
has no Boundary or effect seed. Coverage must be established independently for
the actual result and the operand-result subtree. Neither source is erased
because the other happens to carry the same family or underlying value.

**Proposition C (exact route criterion).** Under H, FR holds for all old
endpoints and all finite typed p **iff** SOUND, COVER-ACTUAL and COVER-OPERAND
all hold.

*Necessity.* A B pair is a path of the extension by F with an empty R prefix.
Apply FR at its old source to obtain SOUND. Apply FR at `(r,p)` and use
reflexivity of R on its actual-result disjunct; F yields COVER-ACTUAL. Apply FR
at `(t,k(p))` and use reflexivity on its operand-result disjunct; F yields
COVER-OPERAND. These arguments remain valid if `t=r` as occurrences, since
the indexed ports and the two uses of reflexivity are retained.

*Sufficiency.* Given a path on FR's left, F factors it into `R(x,a;y,b)` and
B. SOUND supplies an old route from `(y,b)` to `(r,p)` or `(t,k(p))`.
Transitivity of R gives the corresponding right disjunct. Conversely, extend
an old route to `(r,p)` with COVER-ACTUAL, or one to `(t,k(p))` with
COVER-OPERAND. Transitivity gives an R prefix into a B pair; F yields the
left-hand route. QED.

Equivalently let C0 be the indexed union of the actual-result identity
`(r,p)->p` and operand prefix removal `(t,k(p))->p`. Then the criterion is
`R ; B = R ; C0`, or equivalently `B subset R ; C0` and
`C0 subset R ; B`. Relations here test existence of routes. The source tags
and original path witnesses must still be retained by a whole-packet
implementation; existence equality alone does not certify witness-lineage or
predicate-ledger equality.

This criterion is **presentation-independent at fixed interpreted endpoints**:
one direct row, several fresh intermediate rows, or another licensed batch
may have the same R-saturated frontier. It is not invariant under changing the
actual output, interpreting raw-equal aliases as identical, changing owners,
or replacing packet components. It does not demand that B literally equal C0.

**Corollary R10 (sufficient special case).** If the source establishes
LOCAL-LEAVE's one fresh o and exactly the two incoming rows, B=C0. Its indexed
domains/images are `P_A -> P_A` for r and `k(P_A) -> P_A` for t; for profile
incidence restrict to effect paths, and for dependency incidence retain its
own typed domain. Allocation is one fresh output and no intermediate output.
SOUND holds by reflexivity and both coverage conditions hold by the direct
rows. C proves FR for all finite suffixes. This reuses r10 without promoting
LOCAL-LEAVE to an accepted premise. Literal two-row exhaustiveness is sufficient,
not necessary for the route law.

**Corollary OLD (authorized reuse of r).** Add the separate source premise
that the actual authorized output is the old occurrence `o=r`, without a new
incoming edge into r. Then B is identity at r, SOUND and COVER-ACTUAL hold by
reflexivity, and FR is equivalent to the single condition

```text
for every p in P_A: R(t,force.result · p; r,p).
```

*Proof.* Substitute B's old-output definition into the three conditions of C.
Only COVER-OPERAND is nontrivial and reduces to the displayed formula. QED.
OLD does **not** authorize reuse of r. In particular paper 582–583 prescribes
a fresh output for an executed return transport. Reusing a native handle is
not evidence that source occurrence identity is preserved. OLD is applicable
only after source authorization or a separately proved source/native
representation relation; no such premise is supplied here.

For a returned thunk, OLD requires
`R(t,force.result.force.effect; r,force.effect)`. A route merely from
`(t,force.effect)` does not satisfy it. The same distinction appears in both
coverage branches of C. No second Force is executed during this reasoning.

## 3. Inversion of the pinned Force/Flow clauses

All operational line numbers below are at the pinned hash. The audit tests
the **weaker exact frontier criterion**, not only r10's literal row batch.

**Proposition W (weak accepted-clause consequence).** Fix the retained D and
its one interpretation and actual finite normal return as above. Inverting
its Force decoration gives the executing `View(t,force.effect,M)` and a
separate result-transport operation L, whose normal return carries result-path
metadata. The body's normal-result interface retains r's value and all latent
ports. For **each Flow row actually emitted by L**, its target is a new
occurrence and its typed template has the permitted finite-prefix/terminal-pair
form. For **each actual returned-value transport operation** among these
operations, the row uses that operation's actual input view and a fresh output.
The normal ambient leave restores the saved outer observation packet.

*Derivation.* Invert Force's row at 1245 to obtain its View and separate result
transport; use 485–492 for normal result-path metadata. Invert the Delay/Ret/
Force graph rows at 1528–1532 and the all-latent normal interface at 1478–1489
for the body's result interface. Instantiate the universal recorded-Flow
condition 553–556 and the primitive-form restriction 611–624 on each row
actually emitted. Instantiate 582–583 on each operation that is an actual
returned-value transport. Finally use 1352–1356 for ambient restoration.
These are direct clause inversions under the same interpretation. QED.

W's per-row quantifier is deliberately explicit: it is not
`for every p, Flow(r,o,identity)(p,p)` or
`for every p, Flow(t,o,remove-force.result)(k(p),p)`. It does not identify every
operation's output with the actual Force output o or enumerate the whole
incoming batch. W does give the new-target part of H for its recorded rows,
and so makes F applicable **once their batch and actual output are bound**.
This is its exact use in the parent; it supplies neither coverage nor SOUND.

| Governing clause | Positive inversion consequence | What it does not establish for C |
|---|---|---|
| 215–227, 303–307, 995–1006 | Typed Force eliminates the actual thunk; a retained view/wrapper/guarded reference reaches its actual delayed constructor and body. | Underlying constructor/type preservation does not bind the normal-result Flow frontier. |
| 485–492, expose/return | Return carries result-path metadata; decorated elimination uses the actual underlying constructor and specified metadata. Force exposes its body. | No equation gives the indexed domain from t and r to o, or the matching of each finite result suffix. |
| 542–556, 569–575, occurrence/Flow | Alias occurrences are separate. Every **executed** typed transport has a finite fixed T and a fresh target; history respects occurrence order. | This yields F's chronological shape once the actual batch/output are identified, not either coverage condition or SOUND. |
| 580–583, transition rows | A returned-value transport uses its actual input view and a new output, with the specified template; structural outputs can have multiple inputs. | Even granting the strongest reading that the Force return directly binds r and a fresh o here, `Flow(r,o,T_r)` does not state that `T_r(p,p)` holds for every p, or supply the operand-result route. Nor does it enumerate all incoming sources. |
| 585–595, receipt and execution | Receipt makes its source Boundary once; Force executes its force-effect View. Delayed introduction does not execute a View. | A result return is not thereby a new receipt or an observation of its latent body. There is no new admissible grant or operand-result correspondence from this clause. |
| 598–624, Path/primitive template | Routes match both occurrence and intermediate port. Fixed-prefix substitutions preserve their residual suffix; no arbitrary descendant collapse. | Finite-prefix **form** does not select the prefixes, the typed domain, the actual endpoint batch or complete coverage. A terminal-port pair is not universal suffix coverage. |
| 1180–1222, retained input/profile | One instance and annotation occurrence control paths/profiles, including delayed shapes and unknown positions. | A source profile constrains permitted incidence; it is not the missing transition equation. Unknown does not remove a suffix obligation. |
| 1231–1252, full decoration table | Delay saves code/captures; actual Force enters `View(t,force.effect,M)` and has a **separate** transport involving `force.result`. Structural/adapter edges use their actual correspondences. | This is the decisive constructor label, but contains no formula for its actual r/o binding and all-suffix incoming relation. Calling it a result transport does not enumerate its domain or prove C. |
| 1255–1259, captures/user casts | Captured receives occur at actual invocation; user casts contribute only their executed structural edges. | Captured data, public callable views and raw-equal aliases cannot supply missing t-to-result edges by inference. |
| 1297–1329, complete cell | alpha uses the real shared world, route witnesses and actual name equalities; joint comparisons use one union diagram. | Cell coordinates cannot be chosen to repair a missing concrete route. |
| 1343–1421, finite transfer | Apply the primitive's specified coordinate formula; unknown coordinates keep all consistent candidates. Normal ambient leave restores the saved outer packet; frame observation differs from result transport. | This algorithm overapproximates an already specified primitive. It cannot choose a concrete B, or turn all-candidate abstract coordinates into concrete operand coverage. Ambient restoration supplies neither coverage condition. |
| 1473–1491, 1528–1532 | Ret carries its actual value and **all latent ports**; Delay stores its body graph; Force connects reobservation, enter, body and leave, separating effect/result. | Ret establishes the body-result interface r. It does not prove that every old operand-result route already reaches r, or define the leave's input/output path relation. |
| 1541–1559, graph closure | One eta, all joint tuples and all well-typed formal/constructor seeds are required; no empty-input evasion. | Horn closure propagates the relations actually supplied. Its universal eta quantifier does not supply a missing primitive relation. |
| 1634–1664, especially 1653 | View frame summaries separately transfer observation and result paths; compositions/union form finite cut summaries. | A context summary composes the result-path transfer; it does not define its concrete endpoint equation. It cannot supply B by referring to that same unspecified transfer. |
| 1720–1758, substitution/instance | The same packet/assignment and whole-instance substitution preserve all ports; new shapes require their retained contracts. | Substitution of a relation needs that relation first. It cannot identify missing aliases or create a result path from a type equality. |
| 1880–1896, simulation cases | The proof appeals to current-world reobservation and the actual View; normal results use result paths and requests use saved contexts. | This appeal reuses the same local rule; it supplies no independent construction of it or stronger inversion premise. |
| 1933–1939, 1994–1998, returned latent values | Normal results retain latent contracts; a returned thunk's effect executes only on its later Force with current activity. | This rules out erasing/executing latent effects as a shortcut. It does not instantiate the missing correspondence at `force.result.force.effect`. |

The joint clauses thus supply a positive **shape and separation requirement**:
actual typed body, result metadata distinct from execution observation, and
fresh targets for the transports actually recorded. They constrain the desired
constructor substantially. They do not in this audit yield its complete
endpoint/path frontier or the universal operand coverage premise. Even if
actual-result identity coverage and a fresh o are granted under the strongest
return reading, COVER-OPERAND and exhaustive SOUND remain unestablished.

The exact first missing source item is the interpretation of the separate
normal-result transport at 1245/1532/1653/1896 as an **applicable equation or
constructor on this D,t,r,o**, with its all-finite-path domain. Its result must
either yield an actual finite batch from which C can be proved, or directly
establish an equivalent interpreted frontier, with authorized allocation.
No particular representation or count of intermediate nodes is demanded.
This is an outstanding source construction/decision, not a theorem of
logical non-entailment of every conceivable formalization of the prose.

## 4. Why complete model separation is not delivered

Two deliberately different approaches were considered: accepted-clause
inversion followed by relational factorization, and a returned-thunk
separation attempt. The second cannot honestly be completed from these inputs:

- Dropping the operand-result contribution is not a clause model merely because
  the short Force table has no equation. Charter §13 still requires retention
  through the **corresponding** typed result path while its receiver is live.
- Mapping `force.effect` indiscriminately into a latent result changes the
  signature correspondence and conflicts with the no-descendant-collapse and
  no-unrelated-profile requirements.
- Varying abstract Unknown cells produces abstract alternatives, not two
  concrete worlds: alpha's routes and owner/profile predicates are fixed by
  each actual graph and common interpretation.
- Native preservation of r alone is not a complete source clause model. It
  neither establishes source authorization of `o=r` nor the all-suffix condition
  in OLD, and provides no full refined derivation/profile/alias allocation model.

Consequently there are no two complete, commonly typed/profiled models here,
and no source-qualified universal counterexample. No informal deletion/addition
of an edge is reported as one. Missing explicit construction is not by itself
semantic underdetermination. The finite monomorphic §6 candidate supplies
relations **when their applicability is assumed**; its scope cannot establish
the full retained, instantiated parent by silently restricting source types.

## 5. Parent application, source/native seam and handoff

Before this assignment, r10 supplied the sufficient LOCAL-LEAVE-to-FR proof.
Now F and C prove exactly what is required at the route level, including
implementations with multiple fresh intermediate outputs. The primary/source
owner can settle the parent route premise by proving SOUND and both coverage
conditions on the actual leave. It need not adopt r10's literal two-row
presentation. OLD isolates the exact extra source/native obligation if a
reuse-of-r presentation is independently authorized. This is a smaller
**specification interface**, not newly established source coverage.

Prior work reused with its premises:

- r10-R's conditional route cut, source authority trace and actual/operand
  distinction; its independent acceptance in r10 outcome is for that bounded
  claim only. No candidate applicability is promoted.
- Typed-boundary §6's indexed relational-image algebra, only after valid typed
  correspondences and owner/profile derivations. Its header, charter §13 and
  hygiene §3 expressly retain that premise. Its K/D/L identities remain shared;
  frontier existence equality does not replace those packet requirements.
- r9's frozen inspection report: `machine.rs` normal `RootCompReturn`
  (1087–1095, 2042–2052) preserves `ReceivedValue`; carrier formation
  (1189–1198) and `receiving.rs::delay` (208–223) do not export a generic
  typed result relation. This is inherited evidence at r9's pins, **not a fresh
  Rust inspection or a claim those source bytes were revalidated here**.
- r11's `abstract_focus_counted_run_iff` remains an abstract equivalence for
  supplied H, beta, inst, FocusResult and CountedRun with literal traces/wrappers.
  This assignment has not established a source encoding or an actual
  source-derived FocusResult. Therefore r11 is **not applied to actual Force**.
  Its arbitrary parameters cannot select the concrete leave or discharge
  source/native, completion, foreign-continuation or termination obligations.

The secondary source manuscript imports an older operational hash at lines
48–54 and declares its own unreviewed candidate scope. Its inventory/actual-route
clauses (618–640, 1120–1150) preserve actual typed evidence and exclude
pointer/family guesses. They do not choose a replacement Force leave for the
pinned operational source. No historical import or withdrawn bypass is restored.

**Mutual TODO FL12-SOURCE-1 (owner: Luna intake / d-expose-Force source owner).**
For the unchanged parent and D,t,r, common interpretation, provide the accepted
normal-leave constructor/equation at 1245/1532/1653/1896. Identify actual output
and authorization; enumerate/derive its complete incoming typed correspondences,
domains/images and allocation; prove SOUND, COVER-ACTUAL and COVER-OPERAND for
each finite p; retain packet source tags, K/D/L identity and profile/owner
conditions. If this requires adoption of an unapproved rule, return through
Luna's existing semantic authority process before implementation. **Falsifier
of this obstruction:** an accepted derivation binding those actual endpoints
and proving these conditions, rather than a renamed result-transport label or
an abstract cell inclusion.

**Mutual TODO FL12-NATIVE-1 (owner: Luna / later explicitly leased implementer).**
Only after FL12-SOURCE-1, align the source constructor with carrier formation
`machine.rs` 1189–1198 / `receiving.rs::delay` 208–223 and consumer
`RootCompReturn` 1087–1095. Minimal provisional evidence would export the actual
operand, body-result and output view identities plus the retained typed result
template to that consumer, under its approved source equation. If native reuse
is chosen, prove OLD's all-p route condition under a source/native map; native
handle equality alone fails. Exact discriminator: retain an independent live
boundary at `t.force.result.force.effect` and show its corresponding result
route without adding `t.force.effect`; also retain r's independent evidence and
reject a raw-equal unrelated alias. A test of manually supplied rows fails this
TODO's producer/consumer falsifier. No code slice or instrumentation is authorized
by this note; NO_SAFE_CODE_SLICE persists.

Next in-scope action: freeze and STOP, then Luna's already reserved fresh
nonauthor review of these bytes and source audit. There is no further author
stage in this grant. Do not issue another equivalent conditional proof packet
while leaving FL12-SOURCE-1 untouched. No Lean entry condition has been met.

## 6. Dependency pins, checks and cessation

The following direct dependencies matched before reliance and immediately
before writing. Artifact bytes and the one handoff's digest are supplied in
the frozen handoff/final message, avoiding self-hashes.

| Dependency | SHA-256 |
|---|---|
| operational manuscript | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| secondary source manuscript | `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166` |
| typed-boundary draft | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| redesign charter | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| hygiene integration 10-10 | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |
| top-level inference principles | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| r10-R handoff | `414b6c301d66bf1d331c8b4d4944f230ec1e886b1f5d4fcc74e046d61b99c12f` |
| r10 outcome | `5f445c4e693387496a3d9a232c9ed9f273509dd6c1f71aa6e6de8e890f80c62d` |
| r9 runtime trace | `208834c17ad78d4994cf9596bc9f6e9fd275691e9f60d2d10c7baaa9d2b321c4` |
| r11 ForceCompletion.lean | `6baeb9a786e916d0f7b60bd4d5c8286657da2adba4acdab36f2e45e0921aeb22` |
| superseded r12 contract | `6ee2d234cd7b4ba6317aa9b30ca472f9a1f1927a3e7594a73b55e0b7d4f08023` |

The exact paths for these pins are the frozen contract's authority list and
the handoff dependency table. Referenced historical authors: r10-R
`/root/force_return_entailment_r10`; r9-R
`/root/force_runtime_return_trace_r9`; r11 author identity UNKNOWN from the
inspected file. Luna authors/owns the sprint contract. Those historical inputs
are dependencies, not new independent validation of this artifact.

Checks: source-only `cat`, bounded `sed`/`nl`/`rg`, `wc`, `sha256sum`, leased
output nonexistence and clock reads; manual proofs of F/C/OLD in both directions
and typed returned-thunk substitution. Truncated initial broad reads were
followed by bounded decisive-clause reads, including 1653. No executable
transition check, Lean, compiler/runtime, build, test, network, Git or nested CLI.
No production, semantics, task/index/central-state, question, manifest or other
worker file was changed. Simple-sub generation, accumulation, propagation,
levels, extrusion, qualifying intrusion and generalization are untouched.

Resources: one sequential leaf, 1,200-second cap; first clock
`2026-10-25 01:39:26 UTC`, pre-write clock `2026-10-25 01:43:30 UTC`.
Exact launch-to-STOP duration, CPU and peak RSS are not instrumented (UNKNOWN).
Charge the full 1,200-second grant conservatively; this is accounting, not a
claim that 1,200 seconds of computation occurred. Astra's prior 300 remains
fully charged. Zero compute/checker processes or probes were used. Only the
two exact leased outputs are new; no scratch/additional output or descendant.

**Writer-stop protocol:** freeze this artifact, hash it, write the single
assigned revision-1 handoff, then cease all writes. Final read-only hashes and
the STOP receipt complete the assignment. Fresh independent review and Luna
adjudication remain pending; no author/coauthor can certify this result.
