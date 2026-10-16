# Guarded Catch images: finite structural reduction and exact residual frontier

Date: 2026-10-16
Status: unreviewed candidate/conditional mathematics; frozen revision 1 on handoff
Author: `/root/guarded_catch_image_normalization`; no coauthors or descendants
Assignment: `assignment-guarded-catch-image-normalization`
Sprint: `catch-consumer-and-f5-migration-readiness-20261016`, revision 1
Contract SHA-256: `4848ff79e71a391e24f576e5bad491c43be1591f01139a44495ffcdf36bc3b29`
Baseline supplied by Luna: `eeb7826a238848d219058f4f14e0948c115ae6ac`
Authority: research only; no architecture adoption, implementation or production authority

## 1. Original parent and actual outcome

The original Call/effect H1/H2 parent ranges over all originally admitted shallow
Catch instances, scrutinee/formal/arm binders, actual providers, complete Call
and future interfaces, raw resumptions and distinct residual lineages, in one
original scoped assignment. Protected, consumed, unmatched, outside-arm and
resumed contributions remain separate. Its original tuple is the `Idx(e)` of
[original Call formation](../design/2026-10-07-original-call-formation-definition.md)
§2; complete `CallMem` retains the whole witness before projection, by
[complete Call contributions](../design/2026-10-07-complete-call-contribution-definition.md)
§2. The source/native parent locator is
[H1-G §1](2026-10-15-call-native-correspondence-construction.md).
JOINT_DEC additionally requires exact effective joint solving or residual
meaning, preservation/reflection and natural inference on the admitted domain,
including independent future contexts; its current specification is
[JOINT-DEC](successor-proof-obligations.md#joint-dec). These are the parents,
not a theorem restricted to the examples below.

**Outcome:** a finite reduction of the selected structural once/twice image
and upper-demand clauses, relative to the original complete typed operands;
a precise unresolved frontier for the full normalization. The new reduction
specifies which dependent upper obligations arise, where the independent arm
request occurs, and how an authentic later provider adds obligations without
replacing any old tuple. It does not construct an effective native solver for
those obligations. The full parent is neither proved nor refuted.

The accepted source-record construction is
[construction §§3–8](2026-10-16-call-suffix-image-demand-construction.md).
Its bounded independent reviews justify reuse of its proposed source-to-record
map and structural suffix equations. The
[Draft §§5,7–8](2026-10-16-open-negative-formal-catch-image-design.md)
provides a conditional candidate language, not implemented semantics.
[Later-lower feasibility §§3–5](2026-10-16-catch-image-later-lower-feasibility.md)
supplies the stability/wakeup obstruction with its actual premises.
No FIRST-RESULT-ADEQUACY argument or emitter reconstruction is repeated.

## 2. Whole-tuple demand reduction

Fix the original graph, one `xi=(nu,K,D)`, original handler H, source use maps,
and source telescope T. A clause index z retains its whole provider, input,
request/response/current-state, profile/receipt, result and future witness.
Write `chi_i(z)` for its original branch/selection conditions and `J_i(z)` for
its original complete output computation. Neither is assembled from marginal
rows. `J : U` below means satisfaction of the original exact upper interface U
with its full evidence and future obligations, not just immediate support.

For a supplied finite outer family of guarded whole clauses, their union's
upper obligation has the following exact semantic decomposition:

```text
Demand({ chi_i(z) => J_i(z) }_i, U)
    iff  for every i and every original z:T_i,
              chi_i(z) => (J_i(z) : U).
```

Proof: a member of the left image has an original clause inclusion, its same
z and its guard evidence; apply the corresponding right obligation. Conversely,
restrict the left satisfaction derivation to each original inclusion. Retain
all evidence of the inclusion and U under that same z. All shared solution/evidence-strategy coordinates are fixed outside the
conjunction, and every local quantifier keeps its original source order. The
notation `z:T_i` does not rebind shared coordinates independently for each i.
No operation existentially chooses a fresh provider, response or common
evidence strategy to make the upper comparison succeed.
If the interface contains additional dependent evidence requirements, they
remain inside `: U`; this equivalence does not erase or solve them.

This decomposes an upper obligation, not source generation by execution.
Unknown `chi_i` remains an implication constraint. Contradictory guards may
only be removed with their actual proof. In particular an `if` construction
still accumulates both original branches; this calculation is no license to
constant-fold source constraints. All independent IF alternatives are retained.

**Parent application:** for H1, the consumed output obligation is now tied to
the very same provider/Call/Catch witness as the input. For JOINT_DEC, the
remaining problem is effective interpretation of these dependent implications,
not choosing a provider from a successful scalar effect comparison.

## 3. Structural once/twice and the outside-arm suffix

Use exactly the source records of construction §§5.3–7. Let `T1(r,C)` be
`Return(r,C) >>= Omega_p`; let `T3(r,C)` be q3's original complete remaining
family, including its original return frames. Let A denote the arm's own
`CompleteCall(a)`, retaining all of that call's interfaces. Source request IDs
q1, q2, q3 and q_a are distinct. Write g1/g2 for the *full* original predicates
selecting the displayed arm at q1/q2; they include the relevant branch and
visibility/matching facts. `OpCompat` is retained as a typing requirement;
its failure is a conflict, never permission to use the forwarding case.

For the selected structural clauses, with literal response 0:

| Provider and arm | Reduced complete structural image | Exact upper-demand clause |
| --- | --- | --- |
| once; `k(0)` | `T1(0,C_out)` | `g1 => T1(0,C_out) : U` |
| twice; `k(0)` | `Request(q3,C3,T3)` | `g2 => Request(q3,C3,T3) : U` |
| once; `Bind(_,k(0),A)` | `T1(0,C_out) >>= A` | `g1 => (T1(0,C_out) >>= A) : U` |
| twice; `Bind(_,k(0),A)` | `Request(q3,C3,lambda r,C. T3(r,C) >>= A)` | `g2 => Request(q3,C3,lambda r,C. T3(r,C) >>= A) : U` |

The table suppresses only printed state/binder arguments already retained by
the records. It does not identify C3 with a stale state before resumption.
`T1` and `T3` are not guessed empty effect rows. At the displayed once structural
return section, its original return frames reach A, whose designated result
consumer introduces q_a. At twice, q_a is a possible future introduction after
q3's continuation completes; it is not an additional immediate request.
All nonstructural alternatives of the primitives and return frames remain.

Derivation: substitute the original `Remaining(q1)` or `Remaining(q2)` into
RawInvoke; source Return-Bind eliminates only the literal response-entry
administration. Selection runs that arm outside H. For the fourth row, one
application of Request-Bind pushes the *same* A under q3's continuation.
No selected H wrapper is inserted. Apply §2 to obtain the upper clauses.
The source Bind laws justify this reduction without any new language rule.

A useful falsifier is a compatible context that receives q3 and discards its
continuation. The fourth row then never reaches A. A representation that
makes q_a an unconditional simultaneous event fails this source equation.
A context that resumes q3 and completes T3 reaches the arm's own q_a, which
cannot be deleted because it shares q2's family. This is a conditional source
context discriminator, not a parsed/native counterexample or a claim that
an effect upper bound represents only immediate events.

**Parent application:** H1's consumed-event removal and independent-survivor
obligations are simultaneously represented. The upper interface must account
for q3's entire future, including A when reached. A family-set subtraction or
independent union of marginal request lists cannot establish that obligation.
No complete Call alternative is discharged by these four structural rows.

## 4. Other guards and finite relative representation

For an original yielded request `(q,k)`, retain the full Draft equation:

```text
eligible(q):   MatchRequest_H(q,k) >>= Finish_H(q,k)
ineligible(q): Forward(q, lambda r,C. Image_H(k(r,C)))
```

Match success runs the original arm; NoArm forwards the original q with the
fresh-handler wrapper. If matching emits `(qg,kg)`, the retained output is
`Request(qg, lambda r,C. kg(r,C) >>= Finish_H(q,k))`, outside H. Thus failure
to prove g1 is not equivalent to a pure forwarding clause: matching itself
can have effects. Return uses the actual value-arm computation outside H.
All of these are original rules, not a Boolean decision table for eligibility.

For the displayed structural spine, finite relative reduction terminates:
there are finitely many constructor/arm sites; Return-Bind removes a displayed
administrative node; Request-Bind moves the fixed pending suffix into a shared
continuation reference; selecting H removes this H at the selected site.
For forwarding, the finite once/twice structural suffix has fewer remaining
provider operation sites. No unbounded response family is enumerated. Retain
matcher code, primitive alternatives, unknown invocations and original phase
families by their existing complete references when they are not reducible
by these structural equations. This is a finite *relative presentation*,
not a termination proof for executing those references or a principal scheme.
For finite L provider admissions and U upper admissions, the table contributes
O(L*U) fixed-size clause roots plus shared original payload; guard evaluation,
future observations, new use maps and opaque clauses are excluded from this
bound and remain explicit obligations.

**Exact frontier:** even in the once case the full interface includes
`OriginalAlternative(original_IF_clause_ref)` and potentially
`OriginalPhaseSuffix(original_complete_IF_clause_ref)`. An image-demand on
such a dependent suffix requires interpreting its original Request observation
and future family against U, uniformly in its original witnesses. The source
record supplies the reference and the whole tuple, but no effective elimination
law into native Value/effect relations. Keeping `Pending`, `Invoke`,
`OutsideMatch` or a phase reference in a finite graph preserves that question;
it does not answer it. The proposed language admits these references, so a
finite graph alone cannot refute feasibility either. There is no justified
finite-domain/decidability conclusion from source syntax alone.

This is the first unresolved full-parent operation after the bounded source
map. The full normalizer must supply a sound and complete effective residual
interpretation for these original guard/phase families, or demonstrate an
actual source-qualified obstruction. Neither a generic decision oracle nor a
new opaque 'successful image' predicate is introduced here.

## 5. Authentic later provider, evidence refinement and lawful maps

Before the provider lower, retain `Invoke(beta_cb,Delay(Unit))`, the Catch
image, original U, and the original open family. Its lack of discovered cases
is not an empty source interface. The authentic outer Argument/Replay route
of construction §4 supplies a joint InvocationCase for once. Its arrival adds
the first table clause for the selected structural section and all original
other sections. An authentic later twice alternative for *that same source
instance* adds its table clause with its own original branch guard. Independent
generic relay uses are not combined. A source branch's b and every dependent
output occurrence of b remain the same source coordinate.

For a fixed complete original environment, let C be the currently represented
whole clauses and Delta a newly admitted whole source alternative. The demand
reduction proves directly

```text
Demand(C union Delta,U) iff Demand(C,U) and Demand(Delta,U).
```

This law uses all original witnesses in each clause; it is not row-member
linearity. Applying it to once then twice shows why a once-only completion
receipt cannot certify the extended instance. A registration/admission protocol
must revisit every original U for Delta, even if no FunctionPort is newly
inserted. A later effect atom alone supplies no missing InvocationCase.

Later proof of a guard about an *existing* event is a different operation:
it refines evidence for the same retained implication, not a new source event
or an independent Delta. Generation-dependent solved receipts must invalidate
before reuse. No provisional unconditional E bound may be inserted and later
'retracted' by this proof. Ordinary constraints remain accumulated.

For a lawful coherent substitution theta preserving original typing, rigid
operands, source telescope and guard interpretation, each displayed reduction
commutes with theta: substitution acts jointly on q/k/H/A/U and every body,
state and future binder. This follows by substitution through Return-Bind and
Request-Bind and the original selection equation. The scope is exactly this
lawful transport; it does not prove arbitrary quotient/equality preservation.
FreshUse must map the whole relation, with independent generic instances
separate and aliases sharing their source map. Levels/extrusion retain all
free operands; qualifying intrusion equates only its actual parent/copy rows.
Neither equates permission, provider, witness or residual lineages.
[Source Generalize §2](../design/2026-10-08-source-generalize-definition.md)
retains actual event fields at their original scopes; the table gives no
permission to generalize the selected q or erase its pending family.

**Parent application:** H2 receives a local substitution calculation, not its
row-equality, extrusion, intrusion or complete generalization theorem.
JOINT_DEC receives an exact obligation-extension equation, not finite future
keys, an all-world quotient, foreign-continuation closure or native completion.

## 6. Actual source/native evidence and minimal next evidence request

The contract's current native source hashes were all checked. Direct reads
confirm these precise owners; no tests, builds or executable probes ran.

| Owning symbol | Actual evidence and missing edge |
| --- | --- |
| `candidate_effect::candidate_catch_operation` | slots64/65 propagate entry and **whole scrutinee** effect into raw return effects; its own comment calls slot65 provisional conservative full-S. There is no exact suffix consumer at this owner. |
| `candidate_source`, `LocalSourceForm::Catch` arm | scrutinee slot51 and each arm's slot51 forward effects to the result. Removing only scrutinee forwarding leaves raw full-S -> arm -> result. |
| `lib.rs`, Function dispatch `children` / `FunctionField::Argument` and `ResultEffect` | retains contravariant Argument and covariant ResultEffect pair orientations; this is the authentic native seam used by the frozen source map, not implementation of that proposed map. |
| `candidate_context::dependency` and `synthetic_source_support` | synthetic registration is test-only; source-support invalidation is triggered by FunctionPort. It does not implement a complete image/guard/effect-admission dependency footprint. |
| `candidate_context::transfer_replay_child`, `acknowledge_replay` | existing child transfer/completion ownership is explicit. Completing those existing children does not acknowledge an unimplemented guarded-image operation. |

Minimal provisional implementation TODO **GCIN-NATIVE-1**, for Luna's decision
only: at `candidate_catch_operation` and the Catch source consumer, retain one
original dependent raw family and its joint upper demand using the frozen
construction; demonstrate actual constructor-generated once/twice/raw-arm
clauses and later-admission invalidation in an isolated provisional slice.
Required inputs are the same original source record, full primitive/guard
interfaces and exact original maps. Required output is evidence that the real
source route produces and consumes the clauses in §§2–5; a checker accepting
prebuilt transitions is insufficient. No code lease or adoption is granted.

Exact falsifiers: once's selected structural phase still receives its handled
q1 through full-S; twice loses q3; q_a moves outside q3's future continuation;
a pending guard commits an unconditional handled/forwarded bound; later Delta
is suppressed by a completed receipt; or one copied image combines different
provider/witness substitutions. Current negative preflight must not be bypassed
to claim success. Production remains blocked even if provisional evidence works.

Proof TODO **GCIN-RESIDUAL-1**, owning `SourceInterfaceRef/Invoke ->
CatchImage/ImageDemand` consumer: give an effective exact interpretation of the
first retained original phase-family demand in §4 under the original independent
future/guard domain, including all alternative clauses. Inputs: the frozen
source-record map and this whole-tuple demand decomposition. Falsifier: two
lawful original whole witnesses with identical retained native representation
but different demanded future satisfaction, or failure to represent a lawful
future extension. This targets the remaining consumer, not another provenance
reconstruction or a theorem assuming the desired normalizer.

Mutual work: Luna assigns the residual owner and any provisional code authority;
the implementation inventory lane identifies the actual public consumer that
would need this exact relation and must not count a closed scalar observation
as its implementation. A fresh independent reviewer must assess these frozen
claims. The author cannot certify them.

## 7. Parent disposition, resources and freeze

H1/H2/JOINT_DEC remain OPEN with the exact frontier in §4 and owners in §6.
F1-FULL, FK1-FOREIGN, FIRST-RESULT-ADEQUACY, arbitrary recursion, general
aliases/copies/equality, current-world/profile formation, source/native MODEL,
required principality, soundness, F5 migration and production remain separate
OPEN gates. No local image action settles an independent foreign continuation.
No proof edge, accepted source behavior or ordinary inference operation is retired.

Prior work reused: the accepted bounded source association/suffix construction,
Draft shallow image rules, and later-lower stability audit, each within its
actual premises. Rejected in this derivation: nominal subtraction; immediate
support as complete interface; unconditional simultaneous q3/q_a events;
empty-frontier completion; guard evidence as a new event; finite stored syntax
as effective residual decision. No new all-source impossibility is alleged.

Seven substantive stages: authority/pins; whole-tuple demand; structural/arm
reduction; other-guard/frontier analysis; later-input/substitution; actual native
seam audit; artifact/handoff freeze. Cap 900 active seconds, eight stages.
Requested role/model/effort: astra_prover / gpt-6-astra / medium. Effective
observed model/effort: UNKNOWN (no runtime metadata supplied). Worker identity
is the delivered `/root/guarded_catch_image_normalization`; current session ID
UNKNOWN. No descendants. Zero tests/builds/probes/heavy processes/network/Git.
One unavailable `python` metadata command was retried with `python3`; it was
hash inspection, not an executable semantics experiment. CPU/RSS unmeasured.

Only this artifact and its one assigned inbox are written; no scratch paths.
The inbox records dependency hashes, conservative time charge, artifact hash
and stopped-writing receipt. The inbox hash is sent externally to avoid a
self-referential digest. Independent review and Luna adjudication remain pending.
The assignment stops at the exact residual-consumer obstruction; it does not
continue running while waiting for review.
