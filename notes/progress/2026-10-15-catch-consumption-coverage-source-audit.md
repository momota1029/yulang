# Catch consumption coverage: constructor/consumer source audit

Status: reviewed bounded research characterization and conditional derivation;
one minor U-boundary wording repair passed focused delta review.
No theorem closure, source admission claim, coverage-policy adoption, runtime
metadata proposal, or production authority.

Baseline: `146ca9d2a8713398c893a9cae026ae0c2fae593d`, branch
`research/simple-sub-intrusion`. Exclusive lease: this file only.
Method: static source/authority crosswalk, independent of the concurrent H1-L
constructive and falsification outputs; neither output was read or contacted.
H1/H2/U remain OPEN; H3/P activation remains disabled. The reviewed conditional
native primitive P is reusable evidence, not an enabled Catch implementation.

## Objective and result

Determine what the selected shallow-Catch source records establish about
**guaranteed operation consumption**, separately from original-request
eligibility, and identify the first missing construction output required to
apply a family-based native residual cut.

The sources retain resolved operation identities and ordered arm descriptors.
They do not construct a fact that every contribution delivered to a proposed
family cut is guaranteed to be consumed. Current Catch constraints directly
forward the full scrutinee effect row and independently join arm-body effects;
they perform no Catch subtraction. The first absent owner is the Catch
formation/selection correspondence at `candidate_source.rs::Work::CatchArms`
and its proposed residual-input formation: it has resolved arm declarations
and the original scrutinee endpoint, but emits packet typing actions, not an
operation-coverage/consumption result tied to the contributions entering a cut.

Family presence among operation arms cannot fill that gap: two distinct
operations of one family can have different coverage. This obstruction exists
even after separately assuming the original request is eligible. Protected
same-family contributions, outer arm emissions, and later raw-suffix requests
add distinct obligations; none is settled by the original operation's arm.

## Governing premises and scope

- Charter §§14–15 select outside pattern/default/guard and selected-arm
  evaluation, shallow raw resumption, and forwarding of an exhausted original
  request with only the prescribed wrapper around its future suffix.
- Typed-source-owner realization §6 supplies the selected outside-image
  equation and its bounded control preservation argument. Its semantic sketches
  are not executed Yulang fixtures, full Call, source acceptance, soundness, or
  principality proofs.
- Reviewed native-handler-residual-cut §5 requires U: authentic contribution
  provenance and typed path, family membership equivalent to eligibility **and
  guaranteed consumption** on delivered cut input, live bypasses for survivors,
  separate outer computations, and preservation through future transport.
- Top-level inference principles and compiler-engineering's A/B/D distinction
  forbid solving missing coverage by restricting the original source domain or
  inventing source/runtime meaning. No such choice is made here.

All statements below use one original scoped assignment `sigma`. Distinct
contributions retain their identities even when their resolved family is E.
The original all-admitted shallow-Catch parent domain is unchanged. The current
native preflight subset is evidence about current constructors only; its
restrictions cannot replace the parent quantifiers.

## Constructor/consumer crosswalk

Line locators refer to the pinned baseline.

| Fact or action | Owning constructor / retained data | Consumer and exact evidential limit |
| --- | --- | --- |
| Family and operation identity | `source_annotation.rs:31–65`: `SourceEffectId`; `SourceEffectDeclaration.operations`; `SourceOperationId { family, declaration }`; resolved declaration `Arc`. Declaration construction at `:264` uses the distinct member source node. | `local_source.rs:798–809` resolves family then member, rejecting ambiguity/private resolution. Family equality does not imply operation-ID equality. |
| Ordered arm descriptors | `local_source.rs:211–225`: pattern resolution, operation source key, payloads, continuation pattern, arm source and body. `catch` at `:827–891` appends arms in source child order. | The selected §6 `MatchRequest_H` uses ordered search. Native generation visits every retained arm; it does not execute that search or record which request must reach `Accepted`. |
| Limited pattern subset | `local_source.rs:200–208`, `catch_value_pattern` at `:811`: binder/wildcard; empty call syntax is `Payload::Unit`. | `Payload::Unit` explicitly does **not** impose Unit payload matching; `Work::CatchArms:443` creates no payload binder for it. It cannot justify a Unit discriminator or a new mismatch case. Guards/default computations are not carried by these particular native arm records; the broader selected source equations still govern them. |
| Current preflight | `candidate_source.rs:99–150`: resolved operation declaration, one payload slot, top-level Function signature with no computation row, monomorphic Catch-arm signature, and used-binder representability checks (`:177–199`). | This validates the current packet-typing subset. It does not compare the arm operations with all possible scrutinee operations, demand all family operations have arms, establish callback eligibility, or emit ordered coverage. |
| Arm packet typing | `Work::CatchArms:421–462`: creates binder representatives; emits `Action::CatchOperation` with arm declaration, owner, arm-body occurrence, payload/continuation slots, original scrutinee endpoint and its effect component. `execute_candidate_action:902` invokes `candidate_catch_operation`. | `candidate_effect.rs:806–870` types A payload and B response from the declaration and links a raw continuation. It consumes no scrutinee request operation identity and supplies no arm-success/coverage result. Packet-field compatibility alone is not guaranteed consumption. |
| Operation support | `candidate_signature_value:1494–1506` injects the declaration's family only at its outer operation Function result-effect interface; views retain operation provenance (`ViewOrigin::Operation`, `OperationOrigin` at `:146–156`). | This supports authentic operation flow. It is not a proof that the current Catch has an accepting arm for every operation represented by that family support. No extra request token is needed merely to establish this existing support flow. |
| Catch output | `candidate_source.rs:517–534`: slot 51 forwards original scrutinee effects to Catch result effects; separate slot-51 links join each arm body's effects. Slot 50 joins arm values; slot 52 preserves normal scrutinee value when no value arm exists. | This is current constraint behavior: full scrutinee effect forwarding, separate arm joins, no Catch residual filter. It does not demonstrate an existing subtraction bug or establish exact residual precision. |
| Raw-k effects | `candidate_catch_operation:834–865`: continuation receives declaration response B; its result uses original scrutinee value endpoint. Slots 64 and 65 send entry effects and full original scrutinee effects to a fresh returned-effect row. | The code calls this a **provisional conservative full-S bound**; exact suffix effects may be empty. It explicitly reinstalls no handler. This is not a precise suffix decomposition or proof of full raw-resumption hygiene. If k is invoked, its inferred effects can flow through the arm-body join. |
| Hypothetical plain family cut | `candidate_effect.rs:929–951` stores `Contribution { effect, origin, instance }`; `candidate_check_effect_operand:984–1014` checks concrete family membership in Allowance heads and otherwise forwards the same lower endpoint to the tail. | The membership branch tests `SourceEffectId`, not operation ID, arm cursor, eligibility, or consumption. `AnnotationMember` has only its view family member at this branch. Even retained operation provenance elsewhere is not consulted here. The reviewed P result is conditional on authentic U-certified input and successful native processing. |

## Conditional derivation and smallest obstruction

For an original request q at H's body boundary, keep two different judgments:

1. `Eligible_sigma(H,q)`: the actual typed-path/activation condition at the
   original yielding boundary. This audit assumes no missing callback premise.
2. `Consumes_sigma(H,q)`: after that eligibility test, the ordered request match
   completes as `Accepted(arm,bindings)` and executes that arm. An eligible
   request whose ordered search exhausts is forwarded, not consumed at H.

Under §6's selected equation, an actual accepted original match provides the
bounded positive derivation: H handles that original request via the selected
arm in the outer context. It does not grant visibility to new selector/arm
requests, or guarantee consumption of its raw suffix. If matching emits another
request, the ordinary bind keeps its remaining match/finish continuation; that
new request has its own outer-context eligibility. The existence of pending
matching, false guards or an exhausted search cannot be silently replaced by
an established `Accepted` result. No termination requirement is added here.

For the current unconditional binder/wildcard pattern shape, the retained arm
list can supply a structural candidate set of resolved operation IDs with an
arm. It is not itself a proved all-source consumption certificate: it does not
establish eligibility, actual OpCompat, complete Call/source admission, or the
general ordered selector's outcomes. A family-completeness check over the
declaration's `operations` vector would be one stronger candidate policy; this
audit neither requires nor adopts it. A particular cut could instead have a
source-established input containing only covered operations. Establishing that
fact, rather than inferring it from the family label, is the missing premise.

The smallest family-granularity obstruction is the following structural
witness, with no callbacks, guards or payload discrimination required:

```text
one resolved family E
two distinct resolved operations a=(E,decl_a), b=(E,decl_b)
H has one unconditional operation arm for a and no arm for b
q_a and q_b are distinct original scrutinee contributions under sigma
assume both separately eligible; family(q_a)=family(q_b)=E
```

An ordered operation match can accept q_a and exhaust for q_b. A family-only
head J={E} treats both alike if both reach the plain cut. Thus
`E occurs in an H arm` does not imply U's equivalence for q_b. One family, two
operations and one operation arm suffice to expose the operation/family loss;
a single covered operation cannot exhibit this particular mismatch.

This is a source-record/representation obstruction and conditional semantic
witness, **not** a newly executed or source-qualified accepted-program
counterexample. HIR/preflight have no family-exhaustiveness requirement, but a
complete successful compilation/admission derivation for an enclosing source
program was not performed. The assertion is about what the inspected facts
fail to imply, not a proof of all possible runtime match behavior.

## Same-family survivors under the same sigma

| Contribution | Required disposition at H | What family membership cannot establish |
| --- | --- | --- |
| q_c: eligible original scrutinee operation with accepting ordered match | Consumable at this H boundary | Its consumption does not authorize removal of other E contributions. |
| q_p: protected original scrutinee contribution of E | Retained through its authentic protected/bypass path | Arm presence does not establish its eligibility. H1's missing typed-path premise remains independent of coverage. |
| q_u: eligible same-family b request with no accepting arm | Bypass an E-headed consuming input and forward the original request/suffix with its prescribed wrapper | Family E is present in an a arm, but q_u is unmatched. An unmatched request whose family is absent from `J_H` can instead survive through P's existing tail. |
| q_arm: E request emitted by the selected a-arm body (including a new a request) | Outer contribution, independent of H's scrutinee cut | A's original acceptance does not put the selected arm inside H. Existing separate arm-effect joins are the correct visible boundary to preserve. |
| q_raw: later E request after the arm invokes raw k | Outer raw-resumption contribution; H is not automatically reinstalled | A's consumption does not guarantee consumption of the later suffix. The provisional full-S k bound is not exact suffix evidence. |

These are distinct contributions, not independently chosen marginal witnesses.
For example, the selected a arm may emit a fresh same-family a request, or invoke
k whose later suffix yields b. Both survive H according to the selected shallow
extent. Filtering the final Catch result after its arm joins would absorb
q_arm/q_raw if family E is a head. Filtering the whole undivided scrutinee row
can absorb q_p or q_u. Conversely, exhausted forwarding's explicit future
`H[k(...)]` wrapper enters a fresh occurrence; it is not the raw-k behavior of
an accepted arm and cannot transfer the original consumption fact to all later
requests.

## Exact missing construction fact and stopping point

Before feeding a proposed input I_H to plain family-head cut J_H, the owning
Catch construction must establish, for every contribution q actually delivered
there under the same sigma and activation:

```text
family(q) in J_H  iff
  q is an original-scrutinee contribution eligible at H
  and H's ordered matching guarantees its consumption there.
```

Every protected or independent same-family contribution, and every outer
arm-generated or raw-resumed contribution, must retain a live path outside
that consuming input (or a separately established consumer law). An unmatched
original request whose family is in `J_H` likewise needs separation; an
unmatched original request whose family is absent from `J_H` may survive
through P's existing tail without a new bypass. In particular, no two
delivered contributions with the same E label may require different decisions
at P's plain membership branch. Operation-ID coverage is a necessary
component of this formation fact, not a substitute for eligibility or
contribution partitioning.

The first absent native output is therefore **source-owned coverage/consumption
evidence associated with the proposed original-scrutinee cut input**, including
the covered resolved operation identities or an equivalent constructional
guarantee. Existing arm identities are available at `Work::CatchArms`; the action
currently emitted only types payload/k. No coverage output is constructed or
consumed there. Full general ordered matching needs its own source-directed
derivation; this audit does not invent its compiler representation, dynamic
metadata, eager execution, or a new coverage policy. Stop here: re-proving P or
running another family-membership toy checker would assume this same premise.

Recommended next action: assign the Catch formation/ordered-selection owner a
bounded constructive packet to derive that exact delivered-input guarantee
from retained resolved arm identities and authentic scrutinee provenance,
preserving all original admitted cases and the separate survivor paths; return
the first unresolved coverage case without enabling H3/P.

## Dependency freeze, checks and omissions

The following SHA-256 hashes pin the direct authority/source dependencies.
The explicit `git diff <baseline> -- <these paths>` was empty at audit time.
At final freeze HEAD had advanced concurrently to
`3b565213b517d5320ba1a63864f1bfe47268ac7d`; that same scoped baseline diff was
still empty, so the pinned input snapshot remains applicable.

| Dependency | SHA-256 |
| --- | --- |
| `rules/design-authority.md` | `e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1` |
| `rules/research-lab.md` | `3f70daf755fd6af59959fa48a35aa2d5153639621cc18edc58934246f2aabb69` |
| `rules/git-concurrency.md` | `2561a7168ba8b2d655cc928c8adac565755ec7e3b6b4175e8ac87be4bcdaa5e6` |
| `rules/compiler-engineering.md` | `4567cc0f6997c116114cba3322563cb0ddbe5c73ab3403e5272f0e638cb73ed9` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `notes/design/2026-10-02-typed-source-owner-realization.md` | `5cbd8110736ee4d43e0c65460fa9ecf700228bfdbe9fbaa7642ea0302d86f1aa` |
| `notes/theory/2026-10-14-native-handler-residual-cut.md` | `469677cc50b1dfd5327fa330e85bb83124c9e17cec391866dbf71ee23c40d50b` |
| `crates/yu-hir/src/module/source_annotation.rs` | `f8f8a1934d9961d443b2a0b55a79aa3272ec7cd820f7a40d9bd6217f3456ae38` |
| `crates/yu-hir/src/module/local_source.rs` | `afc91346af535529f973421bdbe2a43520c98946097cae545e4ae1a665146074` |
| `crates/yu-solver/src/candidate_source.rs` | `32a6d875b9e89af8192cf017fbeccc95e9648223490d72de64a6957c97aa6e1b` |
| `crates/yu-solver/src/candidate_effect.rs` | `f414efa7efdb17644f4dfa6b0bba621c1bb7cccd0f83735c33a0acb875da6b91` |

Checks: read-only `git rev-parse HEAD`, `git status --short`, scoped `git diff`,
`sha256sum` of the dependencies above; static `rg`, `sed`, and numbered source
reads. No compiler tests, builds, probes, mutations, measurements, Git mutations
or child delegation. No executable oracle was used: semantic premises come
from selected source equations and the reviewed conditional U/P record; native
source reads independently establish only what constructors/consumers retain
and do. There are no seeds, enumerated ranges or mutation counts. Coverage is
the listed constructors and direct consumer, not all source forms/lifecycles.

Budget: at most 15 minutes, static-only lane. CPU time, peak RSS and elapsed
wall time were not instrumented; actual values are unknown. No heavyweight
process was launched. Initial context `cat` of shared task records exceeded
the output cap; only the relevant small excerpts/locators were subsequently
used, and no exhaustive task-history inspection is claimed.

Unverified: accepted enclosing source fixture, execution/backend correspondence,
complete Call, general ordered pattern/default/guard coverage, callback
eligibility, all-path lifecycle transport, exact raw-suffix decomposition,
soundness/principality, and production cut admission. No shared records changed.

## Commit packet

- Exact leased path: `notes/progress/2026-10-15-catch-consumption-coverage-source-audit.md`.
- Baseline SHA: `146ca9d2a8713398c893a9cae026ae0c2fae593d`.
- Changed dependency hashes: none observed; direct snapshot hashes above.
- Review status: fresh M2 `spec_auditor` found one minor overstatement of the
  required bypass domain. The primary narrowed it to same-family head
  contributions and documented non-head unmatched survival through P's tail;
  focused delta review passed with no new findings. This remains a bounded
  characterization, not theorem or gate closure.
- Checks already run: scoped source reads, HEAD/status, dependency SHA-256 pins,
  empty baseline diff on those inputs; no tests/builds/probes/measurements.
- Proposed commit message: `research: audit Catch operation consumption coverage owners`.
- Shared-record deltas left for primary/curator: reference the first absent
  Catch coverage/consumption output; distinguish it from H1 eligibility;
  retain H1/H2/U OPEN and H3/P disabled. No shared task/index/authority or
  question-board changes are part of this checkpoint.
