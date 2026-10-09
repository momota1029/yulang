# Literal Call emission: bounded constructor falsification

Date: 2026-10-10
Baseline: `6e0cabeb75cd616013be149eee49e700aa2ea8a8`
Branch: `research/simple-sub-intrusion`
Status: frozen research producer artifact; unreviewed, non-authoritative
Claim class: bounded constructor characterization and minimized missing-premise witness
Exclusive lease: this file only
Adoption, source rejection, emitted membership, implementation and gate closure: none

## 1. Objective, method and authority

Attack the selected tagged literal-emission direction for `my invoke f = f 1`
by constructor inversion, rather than repeat the earlier constructive map
attempt. The question is whether the original static origins, complete dependent
fields and local O0 input can be obtained before assuming the emission being
constructed. No executable probe, build, test or semantic enumeration ran.

The integrated `original-literal-call-emission/q1/d1` answer and receipt select
the direction in [the candidate](../theory/2026-10-10-original-literal-call-emission-extension-candidate.md)
§§1–7. They do not adopt its emitted judgment, complete O0, authorize acceptance
of `f 1`, implementation, C0/admission, solving, publication or cutover. The
complete Call contract and the rejection of the four-port approximation remain
fixed. The historical “Decision: not selected” header is supplemented by §7 and
the integrated receipt within exactly that direction-selection scope.

Other exact governing inputs are:

- [Application_N](../theory/2026-10-08-flat-application-owner-completion-decision-object.md)
  §§3–9: complete Old/Env/Integer/Kernel inputs, its own constructors and
  installation, whole action and conditional consumer applicability.
- [Original-ResultLiteral](../theory/2026-10-09-original-literal-result-owner-extension-candidate.md)
  §§2–5, supplemented by its integrated q1/d1 receipt: selected original
  literal Data/Result formation; no Call Reify, emission or kernel bridge.
- [Source-call generation](2026-10-06-source-call-generation-construction.md)
  §§3,4.2–4.4: actual Name/Name Gen-Call-0 and one joint original tuple.
- [Theorem S](../theory/2026-10-07-call-input-construction-proof.md)
  §§3.1,3.4,4: Code-Result, Carrier-Delay and Code-Call introductions.
- [Original Call formation](../design/2026-10-07-original-call-formation-definition.md)
  §§2–6 and [O0-selected](../theory/2026-10-07-adopted-call-formation-o0.md)
  §§2–5: actual emitted-record input, independent signature root and eight
  typed incidence projections.
- [Original ownership](../design/2026-10-07-original-call-owner-definition.md)
  §§2–4.1: actual Gen-Call-0 source domain, original Reg/Route, independent
  SeedExposure, and distinct lexical/checking facets.
- [Source-interface construction](../theory/2026-10-08-call-source-interface-construction.md)
  §2: bare Gen-Call-0 does not manufacture additional Application origins.

The requested research-lab, design-authority, git-concurrency,
orchestration-budget and compiler-engineering rules were read, as was the
question-board rule for committed decisions. The artifact is a bounded producer
lane; the primary owns review mode, adjudication and integration. No independent
review of this output is claimed.

## 2. Result and exact hypotheses

No contradiction of the selected extension direction was found in the inspected
clause set. The smallest discriminating failure is a circular recipe for its
origin producer: Code-Call consumes the very original Application/check/Reify
origins that the recipe tries to obtain by inverting Code-Call. Literal Data
and Result evidence cannot break that cycle. The candidate correctly lists
these as outputs still requiring producers; it does not itself make the false
derivation below.

Fix the actual finite resolved source artifact, binder graph and ordered
ambient context. Let `d_f` be invoke's immutable unannotated Value formal,
`u_f` its callee Name use, `a` the literal-1 argument occurrence and `c` their
Application. All fields must be formed in the actual `T_c,Delta_c` and at
one dependent `xi=(nu,K,D)`. Enclosing Lambda formation is supplied.

To isolate the Call-origin issue, grant the strongest earlier inputs:

1. Genuine original callee Name/Result derivations and compatible original
   `Reg(beta)` and same-root `Route` at `beta=(d_f,R_f)`. These are hypothetical
   grants for this attack, not conclusions from Reg_N or equal labels.
2. The selected Original-ResultLiteral derivation at the actual child, including
   `q_a`, its separate Result-port license and `q_res`. Its complete independent
   primitive and Return inputs are supplied at those same indices.
3. Complete well-scoped WholeContract modules and lawful component actions as
   required by Application_N §3. Also grant lossless child Return transport.
4. A declared symbolic complete Function demand `F_c`, with its local
   dependencies retained. No satisfying descriptor, check witness, seed,
   receipt, source-specific original emission or original Call origin is granted.

These are candidate assumptions. In particular, selection of Application_N
does not establish the semantic realization of all its imported WholeContracts.
The following result is a bounded missing-premise characterization under these
grants, not an impossibility theorem about any future literal constructor.

## 3. Minimized witness: the origin cycle

The semantic payload is only one formal, one Name use, one literal and one Call.
The source witness is the single binding `my invoke f = f 1`; its resolved shape
is assumed, not executed. No capture, annotation, State, recursion, adapter,
second Call or chosen operation trace is needed.

Invert Theorem S §3.4's actual Code-Call introduction. In addition to the two
child Code derivations, it requires:

```text
actual Application/Gen-Call-0 origin at c, with F_c,R_f;
original ReifyOrigin(o_arg,argument code,r_arg,Comp(empty,Int),
                     actual Call scope and incidences);
original complete Call-result interface and its result port;
actual emitted VIncl-origin(A_f,F_c);
actual emitted WholeArgCompatible-origin(J_a,CarrierContract(F_c)).
```

Carrier-Delay itself requires the original ReifyOrigin. Code-Result(q_a,o_a)
supplies the literal child's Return code and Result port, whose parent/role are
`a/ResultOfLiteral`; it supplies none of the Call-owned premises above. A
`Comp(empty,Int)` endpoint equality cannot change that port's owner or role.

Consider this explicit failed proof recipe:

```text
Construct E_lit by collecting the original Call origins from q_call.
Construct q_call by Code-Call using E_lit's original Call origins.
```

There is a two-node cycle after all child evidence is removed from the graph:

```text
E_lit introduction requires q_call
q_call introduction requires E_lit's unsupplied origin package
```

More precisely, if `O_c` denotes that static origin package, the failed recipe
uses `q_call -> O_c` by inversion and `O_c -> q_call` by Code-Call, without
an introduction for `O_c`. In a finite inductive derivation, inversion recovers
a proper premise: the Code-Call proof contains the proof of `O_c` at smaller
height. Defining that premise by inverting the same Code-Call proof therefore
cannot construct its first proof. If the emission constructor also consumes
`q_call`, the would-be proof tree has `height(E_lit)>height(q_call)` while
the Code-Call origin obtained from E_lit forces the opposite dependency.

This is the minimized missing-premise witness for that recipe, not an inhabited
semantic countermodel. Removing any consumer/inversion edge stops the cycle but
leaves the original origin introduction as a hypothesis. Supplying an actual
source-directed origin constructor before Code-Call breaks it. Inconsistent
predicate fibers do not prevent that static introduction: origin production
must form predicate codes, not require their satisfying witnesses.

The same warning applies to deriving `u_c` by first asking O0 for its
`upper` eliminator. O0 already consumes the complete emitted record containing
the distinct checking occurrence. It cannot be used to produce that input.
The new rule must allocate the checking use with its own callee-check incidence
at c. Renaming the lexical `u_f` or storing a fresh ID alone supplies no such
typed incidence. SeedExposure is a later independent input.

This attack differs from the prior literal-coordinate map failure: even after
granting an argument-polymorphic emission signature and every child bridge,
using Code-Call as the producer still leaves its own original origin premises
untouched. Further endpoint or Return models would not resolve this cut.

## 4. Remaining field tests and failure conditions

These are static discriminators, not executed mutations or a claim that the
unwritten constructor already violates them.

| Proposed field | Required producer/evidence; failing shortcut |
| --- | --- |
| Original registration and route | Actual original declaration/root registration and same-root source route under scope inclusion. Keep may return existing evidence; Reg_N/Name-N alone are in N. Construct or interpret any fresh original registration before the emission. Root-pair equality is insufficient. |
| `u_c`, callee and argument predicate origins | Source-owned distinct checking use, original incidence and typed predicate interfaces formed before Code-Call/O0. Origin truth is not required; using Code-Call inversion to obtain its own premise fails as in §3. |
| Argument Reify/Delay | Call-owned original ReifyOrigin plus the whole child code and lexical references. Literal Result's license cannot substitute for the Call's carrier license. Actual `J_a` remains distinct from `Comp(empty,Int)`. |
| One telescope/tuple | Declare dependent F_c/E_c/A_c and witness interfaces under their real earlier binders. One whole scope/assignment map acts on captured imports, worlds, providers, proof families and future slots. Independently matching port endpoints cannot join these packages. |
| Complete operation | Genuine generic complete-kernel use at c, open whole-carrier inlet, all declared arms, actual root/arm insertions, licensing and their own output-dependent provider/future fields. Q_N is a new N use; a typed original interpretation is still needed. Restricting membership to the source diagonal or successful execution drops independent contractual alternatives. |
| Result obligation and ports | Retain full operation-dependent CIncl code and its whole evidence interface in the emission even when Check projects only operand origins. Output/Reify/consumer ports remain separate. Neither Code-Call nor Check constructs CIncl truth. |
| Complete suffix | A dependent family over the actual provider/current world, including receipt, provider entry, body, designated consumer, native and complete returns. Value entry forces then rebinds once; operation suffix retains native Return of MakeRequestThunk and delimiter. Pending tails keep current state/handle and do not replay receipt. F_c is a demand, not that provider. |
| WholeContract actions | Actual component laws for identity/composition, domain/admission, evidence, license and output-dependent future maps. Constructor recursion proves only conditional transport once these laws exist. A domain-changing action needs the original domain certificate. No proof-choice quotient or arbitrary noninjective reflection follows. |

The candidate has no explicit completed constructor table yet. Its field list
is a requirement, not a proof of availability. The inspected N construction
shows a possible order inside N; adopting an original tagged emission still
requires exact original judgments or a proved typed interpretation at each
seam. This report invents neither a missing WholeContract law nor a negative
typing conclusion from its absence.

## 5. Old-family conservation and O0/O1 scope

Application_N §3 imports the **entire** old dependent family, including any old
case beyond the displayed Name/Name generator. Its §§7–8 Keep inclusion,
partial retraction and exact old action are the appropriate conditional model
for old-image conservation. Preserving only one example, endpoints, or the
Name/Name subset cannot meet that whole-imported-family requirement. Keep
must retain entries, lookup, registry evidence, alternative/proof fibers,
owners, scope and all actions. New tagged keys must not overwrite any old key.

Even exact old-image retraction does not preserve every formula quantifying
over the enlarged domain. This is an established boundary of the N proposal,
not a new required restriction: active consumers need their own preservation
proof. No counterexample to its stated old-image law was found. No concrete old
family or whole-action supplier was constructed in this falsification lane.

Existing O0-selected cannot be applied directly to a NewEmission_N record or
to a newly tagged original literal case. Its §2 domain is the actual frozen
Gen-Call-0 inventory and §3 inverts that construction. The adopted OC-CallEff
rule has the same explicit input domain. OSig-Demand can form the independent
immediate root for a properly scoped complete demand, but that alone cannot
introduce the source Call-effect occurrence at the new emission.

A local extension can preserve the selected invocation meaning conditionally:
first introduce the well-scoped original literal emission, then supply a
reviewed typed OC-CallEff literal case or exact typed map that licenses that
input domain. Reuse OSig-Demand's independent root and check all eight
eliminators: signature position, p0, upper occurrence, c, beta, Delta,
complete sourceOrigin and separate ElimOrigin/p_out. Preserve the original
root's full J_call/ExecuteCallable interpretation and all whole-index actions.
This is the exact extension premise, not a theorem established here.

On the Keep image, local O0 should return the unchanged old result for every
old record **where the imported O0 is defined**. Selected O0 never claimed
to cover every arbitrary member of an unspecified broader old family; retain
other old consumers as imported rather than extend that theorem by assertion.

O1 remains separate even if the new O0 is proved. Its authoritative positive
rules explicitly take actual Gen-Call-0, original Reg/Route and independent
SeedExposure. A literal-tag domain extension or typed realization into that
domain must be justified separately. Int, unannotated spelling, original
literal registration and Receive-N do not prove SeedExposure. Paired owner
facets retain `u_f/u_c` separately. No slot/profile/C0/admission conclusion
follows from listing more emission fields.

## 6. Evidence quality, coverage and resources

No oracle ran. The source documents, N candidate and this inversion argument
share the selected contract assumptions; documentary conformance is not
independent operational validation. A checker assuming the missing origin
introduction or OC literal rule would test the supplied model, not prove
those source rules. This output is not independent review of a jointly
authored construction and certifies no new theorem or production behavior.

Coverage is one resolved Name/Int source shape, the cited introduction clauses
and their immediate dependent consumer interfaces. No random seeds, numeric
ranges, executed mutants, semantic arm enumeration or successful typing run
exist. The failed recipe is analytic and conditional on using Code-Call as its
own origin supplier. There is no repository-wide absence search. An initial
large navigation capture was truncated; exact governing clauses were then
read in bounded slices, and no conclusion relies on the omitted navigation.

Checks: bounded cat/sed/rg reads; read-only `git show BASE:path` for committed
receipts; one sequential Python byte-integrity calculation using read-only
Git blobs and SHA-256; branch/HEAD and lease nonexistence checks; final
dependency equality and artifact whitespace/link checks. All fourteen direct
dependency files matched baseline bytes before writing. Final results are
reported in the handoff. No Git mutation, tests/builds/Cargo, executable probe,
formatting, measurement, child or interactive question occurred.

Resource envelope: one lightweight local command at a time; zero compute
probes and zero heavyweight processes. Exact CPU, peak RSS and total wall time
were not instrumented; no numerical resource claim is made. Only this leased
note was written. Unverified scope includes actual source parsing/emission,
all independent original kernel/action suppliers and Return realization,
literal-origin construction itself, complete O0 extension, O1 extension/seed,
primitive membership, C0/admission, solving, generalization/export,
principality, production correspondence, other operand families and cutover.

Recommended next action: construct the original static origin package directly
from the Call owner **before** Code-Call, with a typed output ledger for Reg,
Route, distinct `u_c`, both predicate codes, Call Reify, complete operation and
result/suffix interfaces; then review the local O0 input-domain extension.
Classify this cut as constructional source correctness/natural inference, with
reconstruction debt if earlier formation already owns the needed origins.
Do not repeat the circular inversion or an endpoint model.

## 7. Dependency snapshot and commit packet

SHA-256 values of the direct pinned dependencies:

```text
578193deb6bde5a3562874ff5bc96f6844809cf2006c7156fc382886ee723d50  notes/theory/2026-10-10-original-literal-call-emission-extension-candidate.md
61d5fd8e3a359c9ad7fce203ee7927553964b4eeae4a923319aca49a846f826a  notes/theory/2026-10-08-flat-application-owner-completion-decision-object.md
0c5c58022c6834651fedff6c14d8cdf96002831c0c2d25292843abbae64d3924  notes/theory/2026-10-09-original-literal-result-owner-extension-candidate.md
6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073  notes/progress/2026-10-06-source-call-generation-construction.md
f7c1b1eb23acb33ab98487097ab67617e1af84964b012874b1c951a8805dd9f6  notes/theory/2026-10-07-call-input-construction-proof.md
4940e031b83d3d0315f17beb51ba2e952ec64ae7d57d9ae0d086024c7305ca9f  notes/design/2026-10-07-original-call-formation-definition.md
71202a2ffeb5a4dcf62bbd7731fb20d923ea5626b67647fb1815302b6659e3d8  notes/theory/2026-10-07-adopted-call-formation-o0.md
0b86e367cf8170f4f9d095f0afe8e9f6003209189dc358e294941727962ff110  notes/design/2026-10-07-original-call-owner-definition.md
a746489caedbe7e0b1e11b27dcfa823b57da58f05c9a29ce614e909725635baa  notes/theory/2026-10-07-call-occurrence-construction-proof.md
278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98  notes/theory/2026-10-08-call-source-interface-construction.md
77855c8526e1c105d40fac4dfc58455560fcc6135d280f2302e9809de717c4a8  questions/2026-10-10-original-literal-call-emission/approved-answer.md
a8741d21a156cd5c01abeeab5ae5d3f4a83c60524c437d37ff39839ddae616a6  questions/2026-10-10-original-literal-call-emission/receipt.md
00abf1139b8d1cb4763ea659d90d32304cb3e695dbfc2fddb85071779752b9da  questions/2026-10-09-original-literal-result-owner/receipt.md
225782741e962b9993e489b26fab41ae2735c16b800afcd967897515922d7a91  questions/2026-10-08-flat-application-owner-family/receipt.md
```

Commit packet:

- Exact leased/changed path: `notes/progress/2026-10-10-literal-call-emission-falsification.md`.
- Baseline SHA: `6e0cabeb75cd616013be149eee49e700aa2ea8a8`.
- Changed dependency hashes: none by this producer; final revalidation in handoff.
- Claim/review status: frozen, unreviewed bounded research characterization;
  minimized circular-recipe witness, no semantic counterexample or gate closure.
- Checks already run: bounded clause reads, committed receipts, fourteen-file
  baseline byte equality/SHA-256, lease and branch checks; final static integrity
  results in handoff. Zero probes/builds/tests/measurements.
- Proposed one-line research-checkpoint message:
  `research: falsify circular literal Call origin reconstruction`.
- Shared-record deltas intentionally left to primary/curator: link the analytic
  origin-cycle witness and record the source-owned origin constructor as the
  next evidence; preserve O0/O1 source-domain boundaries and full-old-image
  scope. No task/index/authority/DAG/question bundle or code was edited, and no
  gate/status promotion is proposed.

Producer writes stop at handoff before frozen review; repairs require a renewed lease.
