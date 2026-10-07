# Zero-step Call prefix: constructor proposal and exact residual

Date: 2026-10-08
Status: Reviewed, non-authoritative research proposal
Reviewed-by: compiler_referee, spec_auditor, architect
Claim class: bounded source-contract characterization and conditional constructor proposal
Baseline: `ecf18d9d8f19579ba027ee4aa3b851375ec9fe61`
Exclusive write lease: this file only
Scope: `P.CallInitial` only; no production, fixed-E attachment, F5 replacement or gate closure

## 1. Objective, method and result

Determine whether the selected source laws uniquely supply the complete
decorated zero-step Call constructor. The method is a forward dependency
derivation at the smallest rule instance, separating what the laws specify
from the input telescope and observation maps they leave abstract. No solver,
descriptor-membership argument, emitted-rule assumption or executable model is
used as an oracle for source rules.

**Result:** the selected laws fix the required initial stage and its suspension
discipline. The inspected contracts do not supply the complete original
`P.CallInitial` observation/evidence telescope or its lawful map. The gap is
representation and original-contract supply, rather than an outstanding choice
of argument timing or source result meaning. A forward retained-input record
is proposed below, with the exact missing interpretation obligations exposed.
It is not asserted to inhabit the independently interpreted original `C_c`.

## 2. Baseline and governing sections

| Dependency | Exact use |
| --- | --- |
| `rules/design-authority.md` | Scope-sensitive precedence; Draft definitions do not select language meaning or implementation authority. |
| Source contracts §§2–3.5 | Conditional joint interpretation, original-scope witnesses, source emission inventory, four independent admission families and ordered Bind equations. Concrete formation clauses remain Draft. |
| Source-interface definition §§1–4 | Selected IF-Insert/IF-Use and full static Call frame; explicitly preserves independent original operator, hole/world and witness contracts. |
| Interface construction §§3–7 | Complete dependent slots, actual source formation, suspended dependent suffix and action of independently legal whole maps. Static formation may exist with unsatisfiable constraints. |
| Source-call scheduling choice §§1–5 | Callee first; whole-argument inert introduction; receipt and actual entry follow; no prefix of the argument runs to build its carrier. |
| Source-result synthesis choice §§1–5 | Known computation interface preserved; lookup/synthesis inert; no implicit extra result layer, public result-interpretation parameter or recursive force. |
| Pure-read result constructor §§3–5 | Initial/lookup descriptor stages precede actual Delay/challenge construction; `M_E` remains separate from `DescMem`. |
| Original-rule schema proposal §6 | The exact `P.CallInitial` residual, with independently valid event/environment; no actual carrier, challenge or receiver premise. |

The INDEX locates the source-interface, scheduling, result-synthesis and
source-contract documents. The exact pure-read and original-rule filenames
were verified directly; the inspected INDEX has no matching direct locator
for those filenames. This navigation omission supplies no semantic premise.
`tasks/current.md`, `tasks/research-lab.md` and the dirty INDEX were read only
for orientation. Concurrent compiler/shared-record edits are outside this
lease and are not inputs. All direct semantic/rule dependencies match the
pinned revision; the frozen hashes are in §7.

Accepted decisions are preserved: same captured `f`, actual local rebound
`x`, inert returned closure, actual provider's role/entry, one Value-entry
force versus Retained entry, no latent recursive force, fixed independent
challenge domain, original `xi`, scopes, sharing and all Option 2 alternatives.

## 3. Smallest rule instance and deductions

Use the assigned original-rule notation:

```text
n_f = name b_f                 q_f = result(n_f)
n_x = name b_x                 q_x = result(n_x)
c = call(q_f,q_x)
j = (B,X,xi,Delta_c; actual callee/argument/receiver/result/future incidences)
xi = (nu,K,D)
T_step = (original captured telescope, actual local b_x binding)
e = (eta0,h)
live fields = (C_e,w_e, original valid environment at e)
```

Fix genuine `Form(c)` and an independently valid initial event/environment.
No Name has yet returned. This is one Call rule instance with the two minimal
Name/Result operands; there is no receiver implementation, operation, request,
resumption, returned provider or abstract alternative to reconstruct.

The following bounded characterization follows from the governing sections:

1. The initial prefix has executed zero source steps. It cannot certify a
   callee Return or a lookup's completed membership elimination.
2. It retains both whole operands and their actual formation origins. The
   argument is suspended code, not an already formed runtime `t_x`.
3. The dependent suffix is the original ordered Call suffix. At a future
   actual callee Return `(v_f,C_1)` it inertly forms the carrier from the whole
   `q_x`, then invokes the actual provider. At zero steps this is code under
   its dependent telescope, not a value of `v_f`, `C_1`, or `U_f`.
4. There is no actual assembled `d ∈ D_c`, receipt, entry, Force, body result,
   request witness, raw handle, invocation return or future-use event.
5. Static receiver/result/future interface schemas remain in the suspended
   suffix. Their presence does not assert inhabitants of their dependent
   runtime fields. In particular the frame's generic result-provider slot is
   not an actual returned provider.
6. The initial event is the supplied `(eta0,h)`, and its live state is `C_e`.
   This rule neither extends history nor resets the world to `eta0`. It does
   not assume `h` is globally empty: this local Call can be reached in an
   existing admitted history.
7. The original environment, `w_e`, binders, scope, `K,D` and incidence remain
   joint. No independent witness selection per operand is justified.

Items 1–7 constrain any lawful forward proposal. They do not construct a
member of the original observation carrier. The selected staged descriptor
requires these prefixes, but its typing theorem explicitly starts with an
existing source-base derivation; it cannot supply that derivation.

This is the minimized unresolved-rule witness, not a source rejection or an
accepted-program counterexample. Removing `Form(c)` loses actual source
origins; removing initial validity loses the independent current-world premise.
Neither an executed child nor an actual argument carrier is needed to expose
the missing output construction.

## 4. Proposed forward representation, with no hidden execution

The primary could select an explicit dependent record as a new representation
of this bounded initial case. Its retained data would be exactly:

```text
(j,
 c and its genuine formation derivation,
 q_f and its genuine child formation derivation,
 q_x and its genuine child formation derivation,
 the original dependent suffix code under the actual ResultBind telescope,
 the original source/resolution/capture/Application/reify/result incidences,
 eta0, h, C_e, the original environment at e, w_e,
 the supplied independent event/environment validity evidence;
 zero executed steps, callee operand poised, whole suffix suspended)
```

Repeated fields above are references/projections of the **same** formation
and joint witness, not separately chosen copies. The suffix code is the source
law's `S(v_f,C_1)` under its binder:

```text
S(v_f,C_1) = inertly form the carrier of whole q_x with original references;
             ExecuteCallable(actual provider of v_f, that carrier, C_1).
```

No field holds an actual `v_f`, carrier or accepted challenge. No field contains
proof that executing the suffix returns. The complete open carrier and
provider interfaces are retained as schemas with their original dependencies.

This list is a **proposed representation specification**, not a complete formal
telescope over the original kernel: the inspected documents do not give the
types of the supplied initial validity evidence or the target initial
observation/evidence coordinates. Introducing a name for those missing types
would leave precisely the same premise untouched. Consequently this note does
not assert a rule with a head `C_c(record)` or invent `K_C0(record)` as a proof.

The proposed record action is structural: an independently legal original
whole map `g` acts once on every displayed field and dependent reference,
including the original formation evidence, `j`, `(eta0,h)`, live `C_e`,
environment, `w_e`, `K,D` and original scopes. It preserves zero steps and the
two suspended code positions. The suffix becomes `g(S)` under the transported
ResultBind telescope; it is not instantiated with a new returned provider.
For composition and identity this record action inherits the original laws
fieldwise, **conditional on** the original action on each supplied field and
its evidence. Theorem IF supplies the static incidence part only.

If an original observation embedding were supplied, the remaining exact law
would be that its value at the jointly transported input equals transport of
its value at the original input, for both observation and evidence. That
embedding and law are missing inputs, not new facts implied by this list.
Joint hiding or grafting is available only with its independently required
original-scope eligibility/admission certificate; this proposal adds no legal
map and grants no new authority.

## 5. Exact unresolved choices and consequences

| Decision/input | Distinct routes and exact remaining obligation | Observable, principal and admission consequence |
| --- | --- | --- |
| Initial observation representation | Retain the forward record in §4 as a newly selected bounded presentation; or reuse an independently defined original Bind-initial observation at `q_f` and its suspended `S` with a genuine Call embedding. The first needs an evidence-preserving interpretation into any fixed original carrier; the second needs the actual Bind-initial telescope/map, which is not supplied here. | Both must preserve the approved zero-step stage and timing. There is no authorized observable difference. Whole unprojected witnesses may differ, so principal/fiber or foreign-kernel equivalence is unproved until the corresponding maps/back laws are supplied. |
| Initial event/environment telescope | Retain the complete original independently typed initial tuple and its evidence; the actual field types and guards must come from its owner or be explicitly defined under proper authority. The four history-family inventory does not print them. | No new admission domain is selectable here. Requiring an actual `t_x`, assembled `d`, successful Q, receiver acceptance or a satisfying generated solution would narrow the premise and is unavailable. A proper retention changes no admission; its all-context adequacy remains independent. |
| Observation/evidence projections and action | Specify which original observation coordinates encode the poised callee/suspended suffix and how all original witnesses are retained; then prove whole-map commutation. Static IF inclusions cannot supply this original semantic map. | Equality after `Pi` alone proves neither same-witness original source adequacy nor preservation of admission-live fields. Dropping environment/provenance data can create reconstruction debt even if projected runtime traces coincide. No principality result follows from retaining those fields alone. |

These are exact representation/contract choices, not reopened language choices.
No distinct runtime behavior is claimed among representations once their
required correspondence is proved. Conversely, no equivalence theorem is
claimed merely because all have zero executed steps. The original sources
explicitly leave operator/witness laws independent, so the most this derivation
establishes is the invariant boundary in §3 and the conditional record action.

Source formation and raw-source initial typing stay separate. Theorem IF can
form a frame when generated constraints have no satisfying assignment. A
zero-step rule with a supplied genuinely valid initial tuple does not prove
that such a tuple exists for a parsed program, that arbitrary punctured callers
are typable, or that the fixed checked domain is inhabited. Failure to obtain
such an input is not permission to reject the source or restrict the domain.

## 6. Evidence quality, limits and next action

There is one documentary derivation and no executable reference/candidate pair.
Oracle independence is therefore not claimed. The interpretation inventory,
existing selected source laws and original valid initial tuple are shared
assumptions. The record-action statement is a conditional theorem of a
proposed representation, not proof of the original source transition rule.
The minimized witness isolates an absent original map; it does not exhibit
two accepted Yulang programs with different runtime results.

No seed, finite search range, mutation, probe, test, build or timing sample was
used. No exhaustiveness claim over the repository or foreign kernels is made.
The initial aggregate read was truncated; the governing sections were reread
in bounded chunks. Source-contract §§2–3.5 were visible in that read and
rechecked separately. Coverage is this one initial Call case; lookup prefixes,
carrier/pre-receipt, receiver V, admission/development A, other G maps,
recursive semantic validity, W/Z validity, raw-source typing, full C0,
principality, emitted-E attachment and production remain unverified.

Failure conditions: treating the proposed record as already in original `C_c`;
mistaking descriptor membership or IF slots for its formation; prematurely
installing a carrier/challenge/provider result; requiring source execution for
initial formation; changing initial admission; independent witness hiding;
or changed direct dependencies. No additional toy probe could discriminate
these missing original contracts. This attempt stops at that exact seam.

Resource limit: one leased note, documentary reasoning and lightweight reads;
zero heavyweight processes, probes, builds, tests, children, Git mutations or
question-board changes. The packet supplied no numerical CPU/RAM/wall-time
cap. Peak CPU/RAM and reasoning wall time were not instrumented. No resources
were spent on enumeration or performance measurements.

The independent compiler-referee and spec-auditor reviews found no defect in
the bounded constructor analysis; the architect review confirmed that a
generic Bind-initial certificate with a Call incidence embedding is the
preferred representation direction, while the fixed-original correspondence
remains unproved. These reviews do not select or authorize a new authoritative
presentation.

Recommended next action: extract the complete I0 telescope and lawful action
from their owning initial-event/environment contract, then construct the
generic Bind-initial certificate and Call incidence embedding against those
actual types. Do not claim an original-rule supplier until the observation
embedding is established. Keep V/A/G and all attachment gates independent.

## 7. Frozen dependency manifest

SHA-256, captured and rechecked at handoff; no dependency edited by this lease:

```text
5788a2ef1c2181b43a9f82116fe6c4cfd32419dc7098fb84fa7c0d46a0a88ca6  rules/research-lab.md
925f1c5cd4ca6ce7306b1375eb9c1a699a83d3491efba21b50271e176eee5ba5  rules/design-authority.md
e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e  rules/git-concurrency.md
1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186  notes/design/2026-10-05-source-contracts-and-common-allowance.md
20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c  notes/design/2026-10-08-call-source-interface-definition.md
278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98  notes/theory/2026-10-08-call-source-interface-construction.md
181e95a9d87d90c265f28ad87e0176f10dd11c3c84bd308e1b802c571ae8d568  notes/design/2026-10-02-source-call-scheduling-choice.md
71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992  notes/design/2026-10-02-source-result-synthesis-choice.md
8d1eb7ecea3e63d7ba0ae091dc673f3321e52fc0e31c5d824bdf4f1656b99488  notes/design/2026-10-08-pure-read-call-result-constructor.md
9ead9f9f373967c7748a05dac1ff3d5de23b0cbd2a777fb0b4438d42f4d0a00d  notes/theory/2026-10-08-readinvoke-original-rule-schema-proposal.md
```

## Commit packet

- Exact leased/changed path: `notes/theory/2026-10-08-call-initial-prefix-constructor-proposal.md`.
- Baseline SHA: `ecf18d9d8f19579ba027ee4aa3b851375ec9fe61`.
- Changed dependency hashes: none; direct dependencies match the baseline and final recheck.
- Review status: Reviewed Draft, non-authoritative; independent reviewers found no defect within the bounded analysis.
- Checks already run: bounded governing-section extraction; exact locator/existence check; read-only baseline/branch/status; SHA-256 baseline comparison and dependency recheck; narrow leased-output inspection. No code, tests/builds/probes, Git mutations or formatting.
- Proposed research-checkpoint message: `research: isolate the CallInitial constructor telescope and action residual`.
- Shared-record deltas intentionally left to primary/curator: link this bounded proposal and its initial-telescope/observation-map seam; retain `P.CallInitial`, H_rules, source-base, fixed-E, F5 and aggregate statuses. No task/index/authority/theory-map or question-board edit is included.

Writes stop at frozen handoff. Review repair requires a renewed lease.
