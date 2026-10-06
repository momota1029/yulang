# CALL_TYPE: local closure package and duplicate-premise stop

Date: 2026-10-08
Baseline: `fd6434993f02d85221642ab2c4047eb63798f9ca`
Status: frozen research-only conditional lemma specification; compiler-referee reviewed, no findings
Gate / method: CALL_TYPE / factor the required local constructor consequences
Exclusive lease: this file only
Semantic and implementation authority: none

## Objective and result

At the approved nested source

```text
my apply f = { my step x = f x; step }
```

consider only `call(result(name f),result(name x))`. The constructive question
is whether the existing clauses prove independent ordinary typing of its
complete output and pending observations.

**Result:** no new derivation is obtained. The attempt reaches the same
independent constructor/typed-Bind premise as the previous attempts and stops
there. Sections below specify a sufficient conditional package with explicit
phase and quantifier restrictions. They neither supply that package nor prove
it follows from the source clauses. There is no basis to claim a globally
weakest lemma while the exhaustive ordinary predicate clauses remain open.
For the particular compositional proof described here, each hypothesis is
restricted to the actual terms, original incidences and admissible states it
uses; a universal law for arbitrary source terms is unnecessary.

This is premise accounting, not a new theorem closing CALL_TYPE, a
nonderivability theorem, a counterexample, or another transition probe.

## Baseline, authority and prior-method boundary

Exact governing sections:

- `successor-proof-obligations.md`: CALL_REL, CALL_TYPE, SEM_JOINT, with
  DESC_CLAUSES and ADMISSION_CLAUSES inspected as their open prerequisites.
- Typed computation core §§3, 6, 7, 9: structural translation, source tags,
  generated parameter skeletons, actual callable entry and complete consumer.
  This document is Draft; its conditional machinery is not promoted here.
- Source contracts §§2.1–2.2, 3.2–3.5, 5.3: independent simultaneous
  predicates, ordinary images, separate admission and assumed local typing.
  Status is Reviewed conditional package; concrete clauses remain Draft.
- Authoritative inferred Function call views §§1–5: approved formation
  direction, distinction between internal formal view and actual role/entry,
  original scopes and comparison-independent admission.
- Authoritative nested-block addendum §§1–3: exact captured outer `f`, local
  `step` binding, and returned inert closure. No alternate block meaning.

Retain the primary's accepted directional protection: receiver upper-output
protection does not propagate back to lower/provider effects. No Q-generated
path, admission, receiver or authority is used. No production cutover follows.

All four prior attempts were inspected:

1. `2026-10-07-call-type-local-law-constructive-attempt.md` already stops at
   Value-entry whole-carrier elimination and typed pending suffix.
2. `2026-10-07-call-type-local-law-falsification.md` rejects output-membership
   erasure because complete independent premises are uncertified.
3. `2026-10-08-call-type-computation-entry-attempt.md` already stops at
   computed-callee Return elimination/typed Bind, then retained binding and
   the actual body consumer.
4. `2026-10-08-original-association-direct-construction-attempt.md` supplies
   the exact Name/normalization skeleton but leaves complete independent
   callable/carrier typing unsatisfied before its separate owner-kernel stop.

The duplicate boundary is the implication from independently admitted
callee/carrier/world operands to descriptor and world facts after actual
elimination, and to descriptor typing of the composed pending suffix. Merely
listing these implications together cannot make them a new proof method.

## Fixed tuple and quantifiers

Fix one original source kernel `X`, original binder tree, original lexical
environment and providers, original Call/result/consumer incidences, and
`xi=(nu,K,D)`. The executable translation `X[c]` in typed-core §3 is distinct
notation from this source kernel. Fix one independently justified common
SEM_JOINT interpretation; this is a conditional parameter, not an arbitrary
interpretation of separately selected predicate names.

Then quantify over **every independently admitted initial operand/world
assignment** at that original scope. There is no assumption that this domain
is inhabited. For each such assignment quantify over every complete raw
Call output or pending observation and every original relational witness for
it. The desired conclusion is the existing
`DescMem(R_call,O,w;xi)`, without defining DescMem by the raw image.

Whenever a pending predicate requires response, raw-resumption or future-use
developments, quantify over every development in its independent admission
domain at the actual current state. Any permitted event-local extension must
agree with the original assignment on original coordinates and retain shared
operation/provider/consumer dependencies at their original binders. Local
witnesses stay inside the binders on which they depend. There is no choice of
one replacement xi, provider or world separately for each phase.

Statements below about a computation being typed abbreviate the proposition
that its observations satisfy the **existing** independently interpreted
descriptor and associated world/provider/continuation requirements. They do
not define an additional predicate, specify those missing requirements, or
postulate TypedCallCert or CompleteMem.

## Conditional package restricted to this cut

Assume the original operational CALL_REL interpretation. In addition assume
the following ordinary semantic consequences are independently established
under the fixed interpretation, with all original operands retained.

**1. Name/Return consequence.** At the admitted state of this inner Call, the
actual captured lookup `f` satisfies the ordinary callable/provider premises
at its original result port and actual state. Lookup `x` satisfies its
ordinary value/provider premises when its delayed code is consumed. Ordinary
Return preserves these facts, including latent returned-handle obligations.
Lexical identity alone does not establish either semantic consequence.

**2. Inert Delay and carrier consequence.** The actual
`Delay(X[result(name x)],original lexical references)` satisfies the original
whole-carrier requirements of the receiver's supplied Call contract at each
admitted state where this contract can consume it. This follows conditionally
from argument-computation typing only if an independently justified ordinary
Delay-introduction/transport rule supplies that implication. No incoming
effect purity, row formula, fresh computation port or eager execution is
assumed. The original argument-to-parameter obligations must already hold;
forming fresh symbolic endpoints does not solve them.

**3. Actual phase preservation.** For each admissible actual receiver reached
by this callee, its original receipt and boundaries preserve the required
joint world/provider facts. Value entry's designated Force supplies the
ordinary parameter facts needed by its actual rebind, or the corresponding
pending facts. Retained entry preserves the same carrier at its declared
view without entry Force. The actual body and its designated consumer supply
their ordinary result and world facts; each native/invocation return shell
preserves those facts at its own original outward port. These are hypotheses
for individual phases, not the assumption that the complete invocation
already satisfies R_call.

For an operation, the native return of MakeRequestThunk and the subsequent
declaration consumer need distinct phase consequences. A closure body result
cannot discharge the operation's declared result-port obligation. Unknown
`f` selects no particular actual body, role or entry here: the hypothesis
ranges over every actual admitted producer of that same original callee.

**4. Typed Bind and complete-prefix closure.** At each original Bind occurrence
used by this expansion, first-computation typing plus the following
pointwise suffix premise must imply typing of the composed observation at
that Bind's original target descriptor:

```text
for every actual Return(v,C1,w1) of the first computation:
  the ordinary result/world consequences hold at C1, and
  the original suffix S(v,C1) is typed there with compatible original witnesses.
```

For every first-computation Request, this closure must cover the existing
whole pending tuple

```text
Request(q,Cq,(response,C') -> k(response,C') >>= S)
```

at the composed descriptor, with the original operation witness and the
complete suffix. Its ordinary continuation obligations quantify over every
independently admitted response/raw-resumption development at current C'.
Typing k at the intermediate descriptor alone is insufficient. Any other
finite-prefix constructors required by the fixed ordinary clauses must have
their corresponding closure consequences too. Return/Request equations by
themselves are not an exhaustive prefix specification.

Only suffixes appearing in this actual expansion are required: callee to
Delay/ExecuteCallable; entry Force to rebind/body/consumer/return; body to its
remaining consumer/return; and operation native return to declaration
consumer. The target port changes with the original occurrence. The same
suffix term, current state and incidence operands remain fixed throughout
each implication. This hypothesis is a semantic constructor-typing law,
distinct from positive relation congruence in source-contracts §5.3.

These four requirements are candidate proof inputs. None is an established
local lemma extracted by this note. In particular requirement 4 explicitly
retains the missing typed pending closure; it does not replace it with a
successful comparison or full-image inclusion assumption.

## Conditional composition and exact specialization

Relative to those hypotheses, the operational expansion is

```text
J_f = X[result(name f)]
J_x = X[result(name x)]
J_call = J_f >>= ((actual_f,Cf) ->
  let t = Delay(J_x,original lexical references) in
  ExecuteCallable(actual_f,t,Cf;original complete view)).
```

Requirement 1 supplies the actual callable/world facts at a returning callee
branch; requirement 2 supplies carrier facts without execution. Apply
requirement 3 to the actual phase sequence. Apply requirement 4 to its
ordered compositions, retaining the complete pending suffix at every exposed
Request. Finally apply requirement 4 at the outer callee Bind. This derives
`DescMem(R_call,O,w;xi)` for every raw observation **conditional on the
complete-prefix clauses and semantic requirements just assumed**. It is a
composition argument using supplied typing laws, not proof of those laws.
Future-use obligations for returned latent providers remain in those laws.

At the exact approved cut, under valid lookup, J_f is Return of the captured
callable at the current state. It does not have a computed-callee Request
branch. Thus the outer Return-Bind reduces operationally to the actual
receiver execution. Hypothesis 4's callee-Request arm is needed for a more
general computational callee, not evidence exercised by this five-node cut.
Within the actual receiver, Value-entry/body/consumer Requests can still
require complete pending closure; purity of the two Name computations does
not eliminate those obligations.

| Phase | Original incidence and outstanding suffix |
| --- | --- |
| General callee Request, outside this exact Name slice | Callee prefix; suffix includes Delay construction and the complete invocation |
| Value-entry Request | Receiver invocation; rebind, body, designated consumer and return still pending |
| Retained entry | Same carrier binding; any execution occurs at the actual later body consumer |
| Operation native return | Its native delimiter has completed; declaration consumer remains |
| Body/consumer Request | Actual consumer incidence; only its original remaining shell is pending |

No row in this table gives callee-prefix requests receiver upper protection,
replays receipt, recursively forces a returned value, or snapshots the state
for raw resumption.

## Why this does not constitute a new derivation

Source-contracts §2.2 says a constructor typing lemma is required to keep the
independent descriptor conjunct from discarding a generated observation;
§3.5 assumes that lemma. Its §5.3 establishes congruence between fixed
relations with unchanged operands, not inclusion of a raw constructor image
in an independently interpreted descriptor. Typed-core §7 extracts membership
from supplied inclusion; its actual-Function condition already requires
complete invocation satisfaction. None supplies requirements 1–4 here.

On the exact pure-Name callee branch, assuming complete receiver typing
instead of the phase consequences would, after inert Delay and Return-Bind,
assume essentially the desired local Call conclusion. The phase package
exposes where this assumption would sit but supplies no independent proof of
it. The first unresolved Force/retained-binding/body-consumer fact and pending
Bind fact are exactly the prior attempts' cuts. Construction stops without
another equivalent identity example, erased-output model or larger probe.

## Independence, coverage, checks and limitations

No Oracle, checker, executable experiment, seeds/ranges, enumeration or
mutation run is involved. Operational reductions share the supplied source
equations; they do not independently validate those equations. A checker
assuming requirements 1–4 would establish their consequences only. No
source-admitted counterexample or competing complete interpretation was
constructed. Searches covered only the listed source/prior-attempt locators;
no repository-wide absence or nonderivability claim is made. Initial combined
captures were truncated; decisive computation/core and certificate sections
were reread in narrow extracts.

Failure conditions include an omitted ordinary finite-prefix rule, loss of a
shared witness, independently chosen port worlds, changed actual role/entry,
unsatisfied argument contract, pre-resume state reuse, omitted operation
post-native-return consumer, repeated receipt, shortened/reordered suffix,
or admission defined using Q. Such a failure invalidates the conditional
composition. An empty independent admission domain proves no inhabitance.

Unverified: exhaustive DESC_CLAUSES/ADMISSION_CLAUSES; SEM_JOINT realization;
all four semantic hypotheses; source-world inhabitance; recursive and latent
handle discharge; original association; generalized source coverage;
production-only Option 2 extras; principality and production conformance.

Checks already run: read-only `git rev-parse HEAD` matched the pin; bounded
`cat`/`sed`/`rg` source reads; `git diff BASE --` on the twelve direct inputs
listed above returned no changes; leased output absence was checked before
writing. No builds, tests, formatter, research computation process, Git
mutation, child delegation or shared-record edit ran. Only this note was
written. Assignment budget: serial bounded text work, at most 15 minutes,
zero probe/build processes. Lightweight source reads were initially batched;
no experimental process ran. Total wall time and peak CPU/RAM were not
instrumented; individual read commands completed in subsecond tool timings.
These checks are producer integrity evidence, not independent review.

Recommended next action: provide an independently justified ordinary typed
Bind/pending constructor consequence, together with the phase clauses it
consumes, in the DESC_CLAUSES/ADMISSION_CLAUSES/SEM_JOINT component. Another
CALL_REL expansion cannot supply the missing premise.

## Commit packet

- Exact leased/changed path:
  `notes/progress/2026-10-08-call-type-closure-construction-attempt.md`.
- Baseline SHA: `fd6434993f02d85221642ab2c4047eb63798f9ca`.
- Changed dependency hashes: none at pinned/live diff inspection; twelve
  direct inputs match the baseline. Final recheck is returned in the handoff.
- Claim/review status: frozen unreviewed producer research; conditional
  composition specification and duplicate-premise stop. No gate closure or
  independent review is claimed.
- Checks already run: governing/prior-attempt reads, baseline identity,
  exact dependency diff and leased-path absence. Final path integrity checks
  are reported with the frozen handoff. No executable semantic check.
- Proposed one-line research-checkpoint commit message:
  `research: specify conditional Call closure package and premise stop`.
- Shared-record deltas intentionally left for primary/curator: optionally
  reference this explicit local closure/quantifier package; retain
  DESC_CLAUSES, ADMISSION_CLAUSES, SEM_JOINT and CALL_TYPE open. No new language
  decision, DAG edge, shared authority rule or user-decision blocker proposed.

Writing stops before submitting this artifact for frozen review.

## Independent review

The compiler-referee found no blocking, major or minor issues. The review
confirmed fixed original `X`, binder tree and shared `xi`; universal admitted
assignment/output quantification; and explicit retention of unproved phase and
pending-Bind premises. The conditional composition does not claim a new
`CALL_TYPE` derivation. Exhaustive descriptor/admission realization,
source-world inhabitance, recursive/latent preservation and production
conformance remain outside review scope.
