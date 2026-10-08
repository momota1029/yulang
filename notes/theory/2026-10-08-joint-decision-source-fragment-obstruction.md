# A source Function boundary obstructs checking only observed payloads

Date: 2026-10-08
Status: independently reviewed source-generated method counterexample
Baseline: `50d889a2d5f297bc20efef9e094db087adc3de34`
Branch: `research/simple-sub-intrusion`
Exclusive lease: this file only
Authority: research only; no production, semantic selection or gate-status change

## 1. Result and exact method attacked

The actual native identity callable cannot be checked against a complete
Function interface which admits the ordinary `Any` value-entry challenges
and requires an `Int` invocation result. An independently formed **actual
Bool argument** is an admitted counterexample. The result is independent
of which source description is chosen for an instance of identity.

This disproves the following concrete candidate mutation, **ObservedPayload**:

1. At a source Function annotation/checking occurrence, retain the same raw
   callable but validate its target using only the argument payloads of calls
   present in the finite source input, or calls already evaluated there.
2. If all those payloads produce results at the target endpoint, accept the
   Function boundary, using their successful local checks as its certificate.
3. Leave no obligation for other independently admitted target challenges.

A source input containing the annotated identity and only an Int call is
accepted by this mutation, although its mandatory Function boundary has no
sound same-callable checking certificate. This is a method failure, **not**
Yulang undecidability, a counterexample to EPR+ER, or a complete JOINT_DEC
decision theorem. No current implementation is alleged to implement the
mutation. A source-directed algorithm retaining the complete boundary and
all independent challenges is outside this counterexample.

The negative is at a genuine source checking owner. It does not add an
`Eq(J.payload,Unit)` observer, use an arbitrary client predicate W, or replace
descriptor meaning by actual source execution. One actual execution is used
to refute a universal Function-membership obligation; all other production
and admission alternatives remain present.

## 2. Selected constructors and ground dependencies

All references below mean the pinned baseline bytes.

| Source | Exact input used |
| --- | --- |
| [Source Generalize proof](2026-10-08-source-generalize-definition-and-proof.md), §§3.1–3.3,4–5,6 | Annotation/checking is a source rule; complete Function checking keeps the same actual callable and requires domain/observation inclusion. Build emits that local proof grammar at its original occurrence. FinalRoot is the actual target. |
| [Approved annotation boundaries](../../questions/2026-10-05-source-annotation-boundaries/approved-answer.md), decisions 2–3 | A boundary uses its current endpoint and returns its actual target with local realization evidence; later uses do not replace the target by a hidden synthesis root. |
| [Contextual Function definition](../design/2026-10-08-contextual-function-membership-definition.md), §§2–3 | Target membership requires this same actual provider to accept every independently admitted complete challenge and type every actual complete/pending observation and future development. |
| [Uniform value entry](2026-10-08-uniform-value-entry-constructor.md), §§4.1–4.3,5.1–5.2,6 | Complete gamma, Bool-to-Any same-value checking, bare Delta projection schema and exact PackGeneric injection; fixed raw generic identity inlet. |
| [Native phase constructor](2026-10-08-id-public-phase-constructor.md), §§2.1,3,4.1–4.4,5 | Independent seven-phase VP descriptor formation, full production inventory, all initial/response/raw/future domains, and identity's actual receipt/Force/rebind/Name/return behavior. |
| [Input realization](2026-10-08-call-semantic-input-realization.md), §§2,4.1–4.3 | Immutable world extension/projection, exact ReturnMem, and inert Name Delay with its universal independent-demand Car certificate. |
| [Selected projection](../design/2026-10-08-native-projection-public-export-definition.md), §§2–4; [export construction](2026-10-08-projection-public-export-construction.md), §§2–6 | Actual native identity and its ordinary VP+Echo public equations; target/source checking uses complete ordinary roots, with unchanged provider. |
| [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md), §5.3 | Queries retain the original scoped Gamma and allocation evidence. Relative logical inclusion is not an endpoint-only oracle. |

Ground dependencies are the genuine independent Int and Bool literal
contracts, their separation, and Top/Any structural checking. In particular,
`0` has hereditary V(Int), `false` has hereditary V(Bool), Bool has a
same-decorated-value inclusion into Any, and the decorated Bool literal has
no V(Int) certificate. These are ordinary ground-rule facts, not new
primitive predicates selected for the theorem.

Take an independently valid immutable caller world with the native registered
ports, scopes, reify licence and receipt/frame guards. Its initial JointWF
evidence is genuine caller evidence. Install a Bool literal binding using
the selected immutable extension constructor. This makes the Name Delay
construction below available in that **same** world. There are no State
updates or external-operation laws in the witness. The statement concerns
every genuine instantiation of these ground/native laws; it makes no
exhaustive foreign/model-formation claim.

## 3. The complete target and actual source boundary

Let `(v_g,U_g)` be the actual import-free native callable formed by the
source `my id x=x`. Its raw generic inlet and intrinsic IF0 are fixed at
Lambda formation. Its source/public descriptions may choose a flexible
parameter description a at sigma, before challenges; choosing a does not
replace `(v_g,U_g)`.

Form the target ordinary descriptor `R_bad` by the independently defined
native VP constructor, with fields:

```text
head          Function(Pure,Value,ValueResult/InvocationReturn)
inlet         I_q[Any; Delta_bare]
entry payload Any
result        Int
IF            the complete original native role/entry/consumer/port map
admission     every original VP initial/response/raw/future challenge
production    the complete VP phase/development grammar at A=Any, B=Int
```

`Delta_bare` is the intrinsic bare native projection schema, not an inferred
empty input-effect requirement. For each challenge it reads the complete J
image and original current context exactly as uniform entry §4.3 specifies.
All original xi=(nu,K,D), scope/lifetime, event, provider and port operands
are retained. The descriptor constructor has independently typed parameters
I,A,B,IF; its phase rules require V(Any) at EntryValue and V(Int) at
BodyValue/Done. Formation of this descriptor does **not** require proof that
the proposed value v_g realizes it. That latter property is the check.

No Echo equality is imposed on the target. Its VP-BodyReturn retains every
valid Int provider at the same lawful body-result world; VP-Force retains
every licensed member of the full checked inlet image. VP-Restrict,
VP-Develop and VP-Future remain exactly their original rules, with their
full independent guards and telescopes. There is no altered source/production
meaning, sampled future domain or omitted Option 2 arm. The target includes
every original non-child IF and incidence field rather than being the
two-endpoint skeleton `Any -> Int`.

The source owner is `Annotation(Name(id), target=R_bad)` with the ordinary
same-callable Function checking alternative. This is a concrete instance
of Source Generalize §3.2 rules 4 and 6; Build §4 emits that rule's full
premises at this occurrence. No actual conversion is selected at the
boundary. A conversion which builds a different callable is a different
source rule and is not this mutation.

To exercise ObservedPayload, add one source Call through the annotated
binding with a genuine Int literal argument 0. The displayed notation is
a source-rule schema, not a claim about a tested surface parser spelling:

```text
NativeId formation/publication
  -> same-callable Function annotation at R_bad
  -> one Call with Int literal 0 and its source-generated inert carrier
```

Source Call supplies the complete inert argument, actual current event,
receipt, consumer and invocation-return incidences. If the invalid Function
boundary is provisionally skipped, U_g's actual call on that 0 returns 0,
and its ground V(Int) result check succeeds. This explains precisely why
ObservedPayload accepts. It is not an independent legal source derivation
of the whole input: the missing boundary certificate is the defect.

## 4. Actual independent challenge construction

Construct the challenge before any tested callable membership or invocation
result check:

1. **Ground binding and carrier.** In the valid immutable caller world,
   install the hereditary Bool certificate for `false`. Use the actual
   Name projection and registered inert Delay constructor to form t_B.
   Input-realization Lemmas W and D produce genuine inert formation and
   Car at the original complete view `J_B=Comp(empty,Bool)`, including all
   designated demands, administrative/zero-step prefixes and compatible
   futures. The same stored Bool binding is used throughout.
2. **Checked inlet.** Form the full original gamma with J_B, its authentic
   formation record, its complete carrier certificate, the original
   Bool-to-Any structural proof as mu_result, the full port map, static
   Delta evidence, the bare whole-image Delta projection derivation and
   the current independent guards. These are supplied constructor outputs,
   not witness values selected to make id's body safe. The result proof
   changes neither false nor its provider.
3. **Independent context.** Use the genuine two-hole punctured caller
   context, its valid other bindings, registered callable/carrier holes,
   scope/lifetime and current-world evidence to assemble the VP initial
   challenge h_B at R_bad. Its admission clauses use the inlet, full gamma
   and intrinsic IF guards. They contain no premise V(Int,false), body
   safety, accepted-U, successful Direct or target Function membership.
   In particular B=Int is a **result requirement**, not a filter silently
   inserted into the target input domain.
4. **Actual raw admission.** Inject exactly this schema/gamma by
   PackGeneric into U_g's fixed GenericValueInlet. This is the selected
   native raw-inlet sum introduction. It supplies actual admission at
   the same current event, independently of any source instance a.
5. **Actual invocation.** Execute the actual receipt/Value-entry protocol.
   The designated Force of t_B reads its stored false and Returns that
   same Bool provider. Rebind installs precisely false. The actual Name
   body of U_g reads precisely that binding; pure Return and invocation
   return preserve its decorated value/provider and current world. Thus
   one actual complete invocation observation O_B has outward result false.

Each constructor uses preceding original inputs only. The target description
is fixed before h_B; its result is not reselected after the Bool challenge.
No historical receipt or completed prefix is replayed. This trace uses the
selected actual source operation to construct a counterexample observation;
it does not identify the complete VP production relation with that trace.

## 5. Theorem and proof

**Theorem OB (source-generated observed-payload obstruction).** Under the
selected ground/native constructors above, the original same-callable
Function boundary checking `(v_g,U_g)` at R_bad is unsatisfiable. This holds
for every source parameter-description choice a, every local checking proof
choice and every original-scope joint strategy. Nevertheless ObservedPayload
accepts the finite input whose only tested invocation of U_g uses 0. Thus
ObservedPayload fails accepted-result reflection at an actual source owner.

**Proof.** Suppose the boundary had a sound local source checking proof.
Native identity's source formation establishes membership of the actual
`(v_g,U_g)` at its source description, with that proof's chosen a. The
same-value Function checking rule's soundness would give Function membership
of this **same** callable at R_bad. The source anchor, provider, original
scope and all prior realization evidence remain unchanged.

Section 4 independently constructs h_B in R_bad's admitted domain. Contextual
Function membership must therefore cover U_g's actual invocation there.
Its actual complete observation O_B has outward result false. But the Done
case of the target's independently fixed production/descriptor grammar
requires hereditary V(Int) for that same outward decorated value/provider.
Ground separation excludes this certificate. Hence O_B is outside the target
observation contract. This contradicts Function membership, so the sound
boundary proof cannot exist.

The contradiction does not inspect or constrain a. If some a causes a
candidate domain inclusion to fail, that is already an unsuccessful proof.
If its whole domain/observation premises were soundly proved, the same-callable
conclusion would still yield the impossible target membership. Changing a,
selecting other inclusion/intermediate proof terms, or retaining the entire
original Gamma cannot change U_g's actual Bool result at this independently
legal challenge. No transitivity of successful concrete queries is invoked.

On the sole observed Int challenge used by the mutation, actual identity
returns 0 with V(Int). Its local result check succeeds. By ObservedPayload's
definition this is sufficient for acceptance, yet the original boundary has
no satisfying strategy. Acceptance reflection therefore fails. QED.

The counterexample already lies at the source-generated complete Function
check. It is not merely a failure of a separately postulated J-payload observer.
Build emits this owner's original local checking premises, so an algorithm
which erases the independent challenge obligation erases a real source clause.

## 6. Scope, minimality and the rejected literal variant

Only one nonrecursive native callable, one same-callable Function boundary,
one tested Int challenge and one separating Bool challenge are used. There
are no operations, continuation resumptions, recursive descriptors, State
cells, alias/new amalgamation failures or proof-observing client predicates.
The input still has the full original independent history and production
domains. A single bad admitted complete observation suffices to refute their
universal requirement; it does not certify the remainder by sampling.

Minimality is claimed only for this mutation shape: the counterexample needs
a target challenge omitted by the mutation whose result violates the target,
and a successful tested challenge if acceptance requires a nonempty sample.
One of each suffices. No global minimality among all source programs or all
possible inference bugs is claimed.

The tempting variant `0 : Any; id ...; result expected Int` is deliberately
**not** used as a source nonderivability theorem. Source contracts §5.3 makes
Le_Gamma relative to the original scoped environment, and Source Generalize
retains prior literal/realization evidence and raw one-shot anchors. A Bool
value cannot simply be substituted into a tuple already fixed to 0. Thus
the generic statement “Any is not contained in Int” alone does not prove that
every such anchored local check fails. The present Function boundary avoids
that problem: its actual callable is fixed, but its independently admitted
argument is not the later caller's fixed 0. h_B respects every original
anchor and is a genuine universal challenge to that same fixed callable.

This note establishes neither a finite representation of all legal challenges
nor undecidability. Finite submitted checking-proof recognition, positive
proof enumeration/semidecision and total exact residual decision remain
distinct. No one of those algorithms is constructed here. The previously
reviewed `8^N` pure structural search and conditional EPR/ER results retain
their exact scopes. JOINT_DEC remains OPEN-PROOF.

The result class is A correctness: a positive solver answer must reflect the
original complete source boundary. Retaining source owner/target/IF records
prevents D reconstruction debt. Retention alone cannot make ObservedPayload
sound, because its missing universal obligation is semantic.

## 7. Verification and frozen packet

This section records the original producer freeze. Its unreviewed wording
describes that historical packet; the independent acceptance in §8 now
governs this exact bounded theorem.

Verification used pinned read-only Git source reads, narrow constructor
inspection and manual derivation. No executable probe, Cargo/build/test,
network operation, source acceptance measurement or numerical experiment ran.
The assignment's one bounded-probe allowance remains unused. No children or
Git mutations were performed. Some early aggregate output was truncated;
the precise relevant source/constructor sections were subsequently read.
This is producer verification, not independent mathematical review.

Direct semantic dependencies at the pinned baseline:

| Dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-08-contextual-function-membership-definition.md` | `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0` |
| `notes/design/2026-10-08-native-projection-public-export-definition.md` | `aed6ef63b01f555a5f2804f87a599167c1a30fa999afc0b9d9f11b8ae974a919` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `notes/theory/2026-10-08-projection-public-export-construction.md` | `4cf84e7a38153b893f1d339780598e2b79084c747ecb883acf0e4fdaa49cf631` |
| `notes/theory/2026-10-08-uniform-value-entry-constructor.md` | `273e8dae447e9997d586fc07abf48883c76b90988c8906094dd428a48339c2e5` |
| `notes/theory/2026-10-08-id-public-phase-constructor.md` | `140c9c907f3ae27120acd84d96c75b2d9a64b437e3e0e71c540c0030864ebb6b` |
| `notes/theory/2026-10-08-call-semantic-input-realization.md` | `fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `questions/2026-10-05-source-annotation-boundaries/approved-answer.md` | `e1e2ff77b181fe42edd404ee0d69cfc6d3bb0fbc99ba7e7f092710025d11fb12` |

- Exact leased output: this file only.
- Baseline SHA: `50d889a2d5f297bc20efef9e094db087adc3de34`.
- Claim/review: unreviewed source-generated method counterexample; no theorem
  closure, independent certification or implementation authority claimed.
- Dependency changes: none to pinned inputs; current-path equality is reported
  separately at producer freeze and must be revalidated by the primary before
  integration.
- Omitted verification: surface parser/source acceptance, production solver
  behavior, full host/model embedding and independent review.
- Proposed checkpoint: `research: refute observed-payload checking at a complete source Function boundary`.
- Shared records/DAG/questions/production edits: none. Any accepted navigation
  update belongs to the primary/curator and preserves existing gate statuses.
- Recommended review target: target VP formation, Bool whole-carrier/context
  admission, original Gamma preservation and independence from source a. A
  failed proof at any of those seams invalidates this source counterexample;
  it must not be patched by inventing a new observer or removing a challenge.

## 8. Independent acceptance

The isolated `joint_obstruction_math_review` compiler referee and
`joint_obstruction_spec_review` auditor both reviewed the frozen mathematical
body with SHA-256
`d7a3da7b3ffe4119561f19d892d1cbefe75841494b78954ad28fe23d7a138cc2`.
Both returned PASS with no BLOCKING, major or minor finding. Neither reviewer
used the other's report or the producer's progress narrative as evidence.

The mathematical review checked independent complete VP target formation,
the actual Bool Name-Delay and complete gamma, punctured-context admission,
PackGeneric's independence from source a, same-callable checking soundness,
the original Gamma, and the retained whole production/future domains. The
specification review separately checked those owners against source Generalize,
the selected inlet/projection/context definitions and approved annotation
boundaries. Both restrict the result to the admitted declarative source-check
grammar; neither certifies parsed syntax or current compiler behavior.

All nine direct dependencies match the §7 digests. The mathematical reviewer
also verified their byte equality to the pinned Git baseline. The primary
revalidated those inputs after fast-forwarding to remote
`d69474d7286717d53aa7ede30ef2d3153a839040`; its intervening changes are progress
records, not semantic dependency changes. This acceptance adds no mathematical
premise and changes none of §§1–6.

The primary accepts Theorem OB in its stated native ground/immutable scope.
The failed method is now concretely refuted. General JOINT_DEC remains
OPEN-PROOF, and no production or gate-status authority follows.
