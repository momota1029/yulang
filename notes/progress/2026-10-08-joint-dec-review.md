# JOINT-DEC research attempts: review and adjudication

Date: 2026-10-08
Branch: `research/simple-sub-intrusion`
Status: reviewed conditional attempts and completed bounded native decision; JOINT_DEC remains OPEN-PROOF
Authority: no semantic or production authority added

## Scope and decisions

This record adjudicates the bounded constructive and falsification attempts at
the artifact snapshots below and links the later completed SD-NPB decision.
It does not certify a finite complete Yulang solver, establish undecidability
for Yulang or authorize F5 replacement. Canonical navigation now records the
reviewed bounded sublemma without changing any aggregate gate or dependency.

### Conditional residual decision construction

The [constructive attempt](2026-10-08-joint-dec-constructive-attempt.md) is at
SHA-256 `ea26c27bfadd05441a708aab150ddb26f7a1c39ae01bcaf4be4ae25d3b043a56`,
after repair commit `b9fe8f927`.

The initial independent compiler-referee review accepted a **MAJOR** finding:
EPR's semantic prefix map `q_n` did not let an effective strategy extractor
classify an actual universal challenge. Effective existential lifts alone do
not compute that map. The reviewer supplied the ordered example
`forall n. exists b in {0,1}. b = H(n)` for noncomputable `H`; finite abstract
truth evaluation and effective existential lifts can coexist with a
noncomputable winning response. This finding did not invalidate EPR's
truth-equivalence induction.

The repair added ER, an explicit finite encoding interface, terminating prefix
classifier, universal-challenge coding/replay, Boolean-prefix preservation,
and closure under subsequent effective lifts. The repaired extraction claim
requires ER; truth equivalence still requires only EPR. A fresh bounded
compiler-referee delta review found **no remaining BLOCKING, major or minor
finding**. It confirmed the countermodel and the separation between EPR truth
and ER effective extraction.

Adjudication: accept the repair for this conditional theorem only. EPR and ER
are not constructed for Yulang. The selected original predicates, scopes,
quantifier order, and prerequisite gates remain unchanged; `JOINT_DEC` remains
OPEN-PROOF.

### Pairwise witness-amalgamation falsification

The independent [falsification artifact](2026-10-08-joint-dec-falsification.md)
is at SHA-256
`5742dca297cc4fd942edf48ceb658e3b543bcd14216c780a810424b223ff90c3`, commit
`20375f34e`.

Its compiler-referee review found **no BLOCKING, major or minor finding** in
the finite three-witness/three-predicate counterexample, minimality proof,
fixed-arity family, experiment accounting, or stated scope. The example
refutes pairwise reuse of independently chosen witnesses. It does not refute
pointwise truth-preserving quotient reflection with a coherent lift, supply
an admitted Yulang primitive, or prove Yulang undecidability. The 682-profile
Python enumeration, exit status and resource report are recorded in the
artifact; the reviewer inspected the reproduction statically and did not
rerun it.

Adjudication: accept this as a bounded shortcut falsifier only. It closes no
canonical gate and supplies no implementation permission.

### Selected native id input-image owner cut

The [id inlet owner cut](2026-10-08-id-inlet-whole-output-image-owner-cut.md)
was frozen at SHA-256
`381371986bbf76490db5097a1efe1060bf5adb2be0c09f04cb222e982b8cf1c4`, commit
`d9f452ec3`. Its independent compiler-referee review found no BLOCKING,
major or minor finding within the original telescope, conditional prefix-local
image lift, and checker-boundary comparison.

The selected uniform-inlet construction supplies a concrete whole-image law
for bare native `id` at its original scopes, given authentic J/Car/context and
local-law evidence plus one coherent original strategy. This yields the
conditional prefix lift for those supplied inputs. It does not construct such
a strategy or decide arbitrary joint residual cells. The reference checker
validates external-law metadata and references, not the law bodies; submitted
finite proof recognition is not semantic proof search. The first missing
effective decision field remains joint preservation/reflection of possible
J/strategy witnesses. Production H7/F5 correspondence, foreign inlets and
general State/recursive cases were not certified.

Adjudication: accept the owner cut and conditional lift under their stated
premises. No semantic definition, source language, or production gate changed.

### Native id joint-witness representation and owner cut

The [relative finite-code transport](2026-10-08-joint-witness-representation-constructive.md)
was independently reviewed at SHA-256
`3f7fc08e07e497aab5d155abe2b87e4ee4d89b16ccbe1a37938c9dfd232fe21b` by a
compiler-referee. The review found no BLOCKING, major or minor issue in the
conditional transport theorem. It confirmed preservation/reflection for
arbitrary original residual predicates under the supplied effective input-code
and replay hypotheses, while confirming those hypotheses are not supplied by
Joint-ID, PE-ID or the native export. This is a relative transport result, not
a finite code construction for every admitted argument or a residual solver.

The independent [prefix-quotient mutation counterexample](2026-10-08-joint-witness-representation-counterexample.md)
was reviewed at SHA-256
`cdb0c2af8db72cd25193efc2002ddbb8916c0c14882b0d30fd71cf43d6f8a301` by a
compiler-referee. No BLOCKING, major or minor issue was found. Under H1–H4,
merging Unit and Bool description prefixes while retaining the original
`Eq(J.payload, Unit)` observer violates EPR clause 3's prefix-local lift.
The observer's actual source emission is not established; the counterexample
does not apply to bare `id` or refute JOINT_DEC.

The [native-id source-owner correspondence](2026-10-08-joint-witness-source-owner-correspondence.md)
was reviewed at its pre-repair SHA-256
`ad46e0959ef97e85427a423ec74a70ed0c303eed177210e1d3504ab38844feaf`. The
compiler-referee found no BLOCKING or major issue and one minor precision
issue. The primary corrected EPR.1 to require a finite layered presentation
and semantic map on legal original prefixes, leaving inhabitance/reflection
with EPR.3–4, and corrected the `ResolvedExpr::Lambda` locator. The final note
is a conditional source/implementation map; it does not claim that Rust
discarded a semantic witness it never constructed. The missing effective
inhabited-cell reflection, whole-prefix classification and replay remain A
correctness obligations; retaining genuinely constructed owner records may
prevent D reconstruction debt but cannot prove those laws.

Adjudication: accept all three research results within their exact scopes.
Retain `JOINT_DEC` as OPEN-PROOF and preserve its required-before-cutover
status. The source-owner audit used read-only Git inspection contrary to its
packet's no-Git instruction; no index or ref changed, and the artifact records
the deviation. No code, tests, builds or measurements ran.

### Cutover relevance and proof-economy classification

A separate read-only architecture audit checked the open witness obligations
against the canonical DAG, selected native projection and repository
proof-economy policy. It distinguishes the required
compiler properties from EPR/ER's particular machinery:

- Accepted-result reflection for every original active predicate and one
  coherent original-scoped strategy remains **A**.
- Effective completeness/termination for every satisfiable actual source
  residual needed by the approved language remains **B**, with answer validity
  an **A** obligation. The active domain is the actual generated relation, not
  automatically every unrelated semantic predicate.
- Same-prefix extension preservation is **A** for a quotient/prefix-game
  algorithm. The universal classifier/replay construction is not proved
  necessary for every possible algorithm.
- Simultaneous identity of active evidence, aliases, new frames and original
  dependencies remains **A/B**. Encoding every possible semantic strategy
  irrespective of active observations is **C**.
- Retaining genuine construction-owned evidence avoids **D** reconstruction,
  but the inspected compiler does not presently supply the complete semantic
  J/Car/context certificates.

The canonical DAG records a sufficient route rather than an Authoritative
mandate to use EPR/ER or decide arbitrary semantic predicates. A complete
alternative for the full approved source envelope is not proved. The later
[SD-NPB theorem](../theory/2026-10-08-source-directed-joint-decision.md) does
prove termination and sound/complete source-directed decision for its native
boundary envelope, with argument/check certificates constructed at their
owners. Extending that result to every required enclosing source judgment,
exact export/fresh-use behavior and a practical resource boundary remains
unproved. Any full alternative to the current JOINT_DEC route
needs a concrete reviewed algorithm, source-rule completeness, production
correspondence, principality/required observables, Oracle capability evidence,
resource/failure ownership and explicit user approval before implementation.
No gate is reclassified or closed by this audit.

## Verification and omissions

- Constructive review baseline: `6967ac589`; repair baseline:
  `20375f34eeae91c7f29473f3a787514c37c74abb`.
- All reviews were pinned to artifact hashes. The delta reviewer noted one
  process deviation: it used a read-only `git diff` despite the packet's
  instruction not to run Git commands. No index/ref mutation occurred, and
  this did not affect the mathematical review.
- No Cargo tests/builds or performance measurements ran. The bounded
  falsification artifact's own experiment is not a compiler test.
- Actual exhaustive Yulang primitive enumeration, effective residual
  construction, production correspondence, principal public projection and F5
  cutover remain outside review scope.

## Next evidence

The following research slices are frozen, separately checkpointed and reviewed
within their stated scopes:

- The [native-id observer inventory](2026-10-08-joint-observer-source-inventory.md)
  distinguishes bare-id Delta from checked admission: no fixed-ground
  `Eq(J.payload, Unit)` occurs in the selected bare-id Delta, while
  `mu_result` makes admission depend on A. Different concrete fibers alone do
  not refute a quotient. Exact H3 emission from constrained source syntax is
  still unproved.
- The [direct effective residual route](2026-10-08-direct-effective-residual-route.md)
  gives a conditional proof-producing alternative without EPR/ER challenge
  classification. Actual-atom coverage, faithful input interpretation,
  same-prefix joint reflection and terminating completeness remain unproved.
- The [source-route falsification](2026-10-08-direct-residual-route-falsification.md)
  separates native-id's parametric action on supplied witnesses from input
  construction and total negative decision. Its Identity/Compose family has
  unbounded retained proof size, not an unbounded minimum witness or actual F5
  emission. Independent compiler-referee and spec-auditor reviews found no
  BLOCKING, major or minor issue in these three conditional notes.
- The independently reviewed [complete Function boundary obstruction](../theory/2026-10-08-joint-decision-source-fragment-obstruction.md),
  commit `a3f90c020`, refutes the concrete ObservedPayload mutation: one
  genuine Bool challenge disproves an `Any`-input, `Int`-result boundary for
  the same actual identity callable, despite a successful observed Int call.
  It is not a complete JOINT_DEC theorem or a refutation of algorithms that
  preserve the full independent challenge domain.
- The [direct mu_result source map](2026-10-08-direct-mu-result-source-map.md),
  [kernel construction](2026-10-08-direct-mu-result-kernel-construction.md)
  and [falsification](2026-10-08-direct-mu-result-kernel-falsification.md)
  distinguish the selected Value-entry proof slot, Rust's missing complete
  gamma package, and conditional validation/application of a supplied finite
  proof. Their compiler-referee and spec-auditor reviews found no BLOCKING,
  major or minor finding. H1–H5 remain assumptions; rejecting one proof term
  does not decide proof existence or joint admission.
- The [SD-NPB theorem](../theory/2026-10-08-source-directed-joint-decision.md),
  commit `2590b3d07`, constructs complete source DataArg/Car/gamma evidence,
  decides the exact joint new/alias constraints, and builds actual ordinary
  proofs and a strategy for all independent native challenges. Its
  [independent mathematical/specification review and reference](2026-10-08-source-directed-joint-decision-review.md)
  (`c7c848489`) record the completed termination, soundness and
  satisfiable-strategy completeness proof, repaired same-world witness
  clarification, and separately bounded arithmetic implementation. No winning
  strategy, J/Car supplier or EPR/ER is a decision premise. The id case with a
  literal argument checked and exported at Any and a whole-result view Int
  is NO, retaining the independent Bool production alternative. This proves
  no parser/HIR occurrence mapping, enclosing CallMem/C0, arbitrary source
  residual decision, all-language principality, current F5 conformance or
  production cutover.
- The [annotated Function field map](2026-10-09-annotated-function-source-field-map.md)
  maps the declarative `Annotation(Name(id), target=R_bad)` and subsequent
  Call to tau/psi, original gamma/J/Car/context and binder scopes. Its
  post-freeze adjudication records the exact overlap with the new theorem and
  preserves the missing parser-to-typed-check correspondence. A specification
  auditor passed its exact-conformance review at the pinned `6ce074f1c` bytes.
  The [current compiler cut](2026-10-09-npb-current-compiler-correspondence-cut.md)
  separately traces ordinary/default-off HIR, collection and candidate paths:
  none produces the complete NPB input; it remains an unreviewed, scoped static
  crosswalk.
- The [JointWF-to-Parameter owner manifest](2026-10-09-jointwf-parameter-owner-manifest.md)
  maps named caller dependencies to Parameter `sigma_a/Delta_a` and later
  gamma/J/Car scopes, while preserving that the selected sources define no
  closed JointWF record schema or exhaustive `Delta_a` instance. Independent
  compiler-referee and spec-auditor review found and repaired one major
  quantifier issue: input-envelope premises do not imply successful data
  checks, Car/gamma evidence or a strategy; successful outputs are now
  conditioned on their local positive premises, and the joint strategy only
  on SD-NPB YES. Both delta reviews pass at `8a26b1a9a`. The manifest remains
  unreviewed for any broader source/compiler claim.
  The
  [source-bridge decision map](2026-10-09-sourcebridge-decision-dependency-map.md)
  inventories the four approved q1/d1 scopes and keeps caller API, authentic
  source producers/H-bridge, resource/failure policy and adoption separate.

No production code changed. The reference implements only finite
endpoint/frame arithmetic. Its final bounded Python process checked 30
boundary/input/output scenarios, 400 inclusion pairs, 301 countervalues,
33,600 bounded membership implications and the depth-360 complete-UNSUPPORTED
regression. Those checks are recorded in the integration report, not used as
mathematical completeness evidence. No Cargo, broad compiler tests or
production acceptance measurements ran.

The source-boundary obstruction rejects filtering to observed calls; SD-NPB
now supplies complete same-inlet Function checking proofs in its stated
source-owned envelope. The next complete-Call step needs each actual
anchored/unanchored production arm's original relation and output-dependent
typed-state/descriptor/guarantee evidence at the source consumer, preserving
same-provider admission, the whole continuation/future action and all
callee/argument/world/port/xi dependencies. That is not supplied by receiver
VP membership or the conditional mu_result validator. The ordinary source
bridge also needs an exact parser-to-typed-check occurrence for the
Function annotation and Call, authentic caller context and complete producer
outputs, with their source/HIR correspondence and emitted consumer
contribution. Keep the independent challenges/futures and Bool rejection.
General JOINT_DEC remains OPEN-PROOF until the required full-source decision
and correspondence are proved, either on the existing sufficient route or
on a separately reviewed replacement meeting the retained obligations.
No arbitrary-strategy encoding requirement or production cutover follows
from the bounded theorem.

### Complete-Call C0 follow-up (2026-10-09)

The [constructive native id/literal Call cut](2026-10-09-npb-call-c0-construction-cut.md)
now limits its result-consumer field to the forward structural receiver
branch under the displayed local laws. An independent compiler-referee review
found that the earlier draft claimed a typed Theorem IF frame without its
complete declaration/interface inputs. The repair retains only an untyped
operand/frame skeleton and makes typed IF conditional on authentic complete
declaration/primitive-interface typing and lawful whole-map actions. A fresh
specification delta review passed the repair. The exact artifact SHA-256 is
`d190bdc59778cca59678b6929e35210b6147543e43cb70351c0c6e2ce57ab5d2`.

The separate [bounded receiver-lift falsification](2026-10-09-c0-receiver-lift-falsification.md)
found no legal counterexample in the inspected selected rules: the exhaustive
complete-Call arm declaration is opaque and provides no concrete W/Z rule.
The conditional guard argument remains conditional on its stated complete
membership grammar. A spec review found one minor overstatement about domain
certificates; commit `8b697132f` qualifies this by changed coordinates being
live in admission. The [current producer correspondence cut](2026-10-09-current-c0-producer-cut.md)
passed bounded regression review: no ordinary/default-off HIR, collection,
candidate-solver or export path produces complete C0 input.

The bounded source inventory confirms the Authoritative complete-Call and
source-interface constructors preserve supplied opaque arms but select no
exhaustive primitive W/Z declaration. The reviewed §3.7 grammar is only a
conditional candidate and does not select those semantics. Thus the distinct
source Call result consumer rule and authentic exhaustive arm contracts are
still missing inputs; no `JOINT_DEC` status, compiler code, test contract or
cutover decision changed. All current research repairs are pushed on
`research/simple-sub-intrusion` through `8b697132f`; no F5 implementation
replacement is claimed.
