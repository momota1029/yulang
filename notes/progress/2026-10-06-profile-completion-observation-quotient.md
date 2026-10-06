# Captured-step profile completion: observation-quotient route audit

Date: 2026-10-06
Baseline: `f93fb06cd40c12fed6caf5051e045f206c4b2da6`
Status: frozen on submission; unreviewed research-only route audit
Claim class: selected-kernel algebra and bounded exact-source obstruction audit
Scope: original no-annotation P for the exact captured-step source
Exclusive lease: this file only
Semantic / implementation authority: none

## 1. Result and boundary

This route does **not close the main source-generation gate**. No
Authority-derived equivalence of all original P completions was established.
No pair of source-certified P completions for this exact component, and hence
no exact-source counterexample to their equivalence, was established either.
The result is a precise account of what the proposed quotient must prove,
together with the selected visibility kernel's exact difference condition.

The proposed dynamic shortcuts have narrower valid scopes. An expired
receiver contributes no current handler incidence. A current receiver-local
concrete grant discharges older protection for the same event. Existing
common protection can make an additional no-grant profile dynamically
redundant at one candidate. None of these facts supplies an all-context,
all-world joint-relation equivalence, and a later Pure call or explicit
Thunk elimination need not introduce such common protection or a grant.

The exact source's introduction and receiving-view premises prevent turning
the last observation into a source-valid P separation. The currently missing
original applicability rule would be needed to certify the alleged extra
position; the actual receiver assignment would be needed to certify its
liveness. Choosing either premise to manufacture a witness would repeat the
already rejected supplied-profile method. This audit makes neither choice.

## 2. Fixed inputs and the required equivalence

The selected source and structural interpretation are

```text
my apply f = { my step x = f x; step }

lambda(f,
  bind(step,
    result(lambda(x,call(result(name f),result(name x)))),
    result(name step)))
```

The block returns `step` without invoking it. Its private lexical environment
captures the same outer `f`. The reviewed initial constructor supplies
`R_f`, one dependent complete `F_c`, `beta=(d_f,R_f)`, the immediate
`p_0=(beta,call.effect)`, the complete-invocation elimination origin, and
FullProtection/no annotation grant at that generated position. It does not
supply every original applicable position, every contribution or the actual
dynamic activation of the captured packet.

Use one original scoped `xi=(nu,K,D)` throughout. Let `P` range over genuinely
source-admissible original completions, not every well-formed decorated
signature. This notation describes the universal obligation; it is not a
new generator of admissible completions. The quotient route would have to
establish, for every such P and every original admissible fiber:

1. A source-derived map to the canonical generated representation, with an
   original-scope witness lifting back for **every** original solution.
2. Equality of complete comparison-independent admission and whole
   observations in every independently valid original world, including
   future calls/forces and raw-resumption developments.
3. Preservation of the evidence-rich relation and its principal solution
   information: original positions, profile/contribution witnesses, source
   tags, scopes, owners, receipts, and all coupled `nu,K,D` information.

Equality of an outward row or one terminating execution proves none of
these three items. A representation may rename coordinates coherently; it
may not choose fresh witnesses independently per port. An existential
completion carried as an unexplained semantic parameter is still the open P
input, even if a front-facing record prints only `p_0`.

The governing sources are [inferred call views](../design/2026-10-05-inferred-function-call-views.md)
§§1.1–5, [source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
§§2–3.5, [typed-boundary transport](../design/2026-10-02-typed-boundary-realization-draft.md)
§6 and the [charter](../design/2026-09-29-scc-intrusion-redesign-charter.md)
§§13,21,22,24. Typed-boundary §6 is a conditional realization kernel; its
original profiles and typed owner/flow judgments remain inputs. The
[nested-block addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
§§1–3 fixes the source tree, rather than a full profile producer.

## 3. The exact no-grant difference condition

There is a useful calculation directly in the selected §6 kernel. Fix the
same event, candidate handler, current configuration, executing typed views,
flow/receipt witnesses, actual role/entry and joint assignment on both sides.
Compare a base profile packet `chi` with `chi union Delta`, where Delta adds
only protected positions with no concrete grants. All common original
profiles, including inherited providers and results, are retained. This is
a calculation on a supplied common realization prefix, not an assumption
that different original P constructors admit the same prefixes.

Write

```text
B(q,h,C) = Active(h,C) and Active(owner(h),C) and Covers(h,q.operation)
P(q,h,C) = Protected_chi(q,h,C)
G(q,h,C) = Grant_chi(q,h,C)
J(q,h,C) = exists an Inc_C witness introduced by Delta.
```

Because protection is existential incidence and Delta has no grant:

```text
Protected_chi+Delta = P or J
Grant_chi+Delta     = G

Visible_chi       = B and (not P or G)
Visible_chi+Delta = B and (not (P or J) or G).
```

Therefore the base admits this candidate and the extended packet blocks it
**exactly when**

```text
B and not P and not G and J.
```

An added no-grant profile cannot make an otherwise invisible candidate
visible in this common configuration. It can remove visibility under the
displayed condition. If two full executions have a first changed handler
eligibility with identical prefixes and no earlier typing/admission
difference, this is the condition at that first candidate. The calculation
does not establish identical executions, identical admitted domains or
identical future prefixes by itself.

The expression also identifies the legitimate local discharge cases:

| Case at this candidate | Consequence |
| --- | --- |
| Added original receiver expired, or no matching typed path/receipt/observation | `J=false`; no dynamic difference from Delta here |
| A common applicable profile already protects this event | `P=true`; Delta adds no further visibility difference here |
| A common receiver-local concrete contract grants the event | `G=true`; older no-grant protection cannot veto visibility here |
| No common protection/grant, but a live added incidence | The candidate is blocked only on the extended side |

The grant case follows no-origin-veto and requires the exact local owner and
operation witness. An enclosing receiver's grant cannot be substituted for
the nested candidate owner's grant. The no-path case is a typed-coordinate
statement; equal effect-family heads or equal underlying value identities
cannot prove it.

## 4. Why later entry does not give automatic domination

Charter §24 fixes receiver role before Function ports. Existing Pure callable
values preserve that actual role; viewing or calling one is not itself a
new Handler/callback introduction. Charter §21's Value entry executes one
designated argument Force inside the invocation, but does not recursively
force latent returned values. Typed-boundary §6 explicitly separates
introduction, transport and receipt. Accordingly a later call/force cannot
be assumed to provide a fresh protected callback position covering every
old latent position.

The selected kernel already describes the relevant discriminator: an
independently profiled callback returns a latent value; the original
receiver remains live; a receiving helper obtains that exact returned view,
installs a handler without a concrete local grant, and later explicitly
eliminates the latent value. Result transport carries only the corresponding
result profile, receipt supplies the helper's ownership witness, and the
new latent observation opens that returned view's own effect position. The
old complete CallView is not reused. If no common profile protects this
position, the live old profile supplies J in §3; absence of that profile
would permit ordinary candidate eligibility.

This is the selected typed-value-scope consequence in typed-boundary §§2/6,
not a new language choice or executed raw-source program. The candidate
handler belongs to the helper which **receives** the latent view. A handler
inside a callable's own body does not receive that callable's public callee
view merely by executing it, so that superficially similar setup is not a
valid replacement for the receipt premise.

For this assignment the discriminator has a strict limit: it does not derive
an additional original beta position for `apply`, and it does not assign a
still-live beta receiver to later `step` execution. It refutes the general
domination shortcut. It is **not** a source-certified alternative P for the
exact captured-step component. The previous
[source-origin separation audit](2026-10-06-profile-completion-model-separation.md)
and [applicability falsifier search](2026-10-06-profile-original-applicability-counterexample-search.md)
already establish why result shape, transport and receipt cannot certify
that missing introduction. This route does not repeat their toy-profile test.

## 5. Expiry does not establish the required joint quotient

Even if an independently proved receiving correspondence showed that every
extra beta incidence is expired at every later latent event, that would
establish only the first local case in §3. It would not erase the retained
source profile or all source solution information.

Charter §13 preserves origin, event identity, latent effects and symbolic
`K,D` at expiry. Typed-boundary §6 states that `chi` stores persistent source
profiles and owner references, that transport keeps the shared K ledger and
its matching D incidences, and that current-scope filtering does not
discharge predicates. Source-contracts §2.2 interprets retained membership,
admission and provider-contract clauses jointly at their recorded original
incidences. Section 3.4 requires a locally proved equivalent rewrite or
another listed transformation certificate; it does not provide an arbitrary
equivalence oracle.

Thus the additional static proof would have to show that any original
profile/contribution differences are recoverable by an original-scope,
evidence-preserving map and do not change independently interpreted
membership/admission in any xi. Dynamic `J=false` is not that proof. Keeping
K,D while dropping the profile-to-path association likewise does not prove
that those predicates have the same recorded incidence interpretation.
This does not assert that an extra profile necessarily imposes a new
predicate or changes admission: no such original source predicate was
constructed here. It identifies the preservation obligation which an
expiry-based inference omits.

The same warning applies to a concrete-grant explanation. A grant can
discharge dynamic protection for one current event and receiver while the
old origin, family predicates and dependent incidences remain distinct.
Admission ranges over all initial punctured contexts and future developments,
including contexts with no such local contract. A grant witnessed in one
development therefore cannot justify deleting those other original worlds.

## 6. Exact residual proof cut and recommended next action

The quotient route needs two source-derived facts which this bounded audit
does not establish:

```text
For every genuinely original P and every independently admitted original
history/world, any original beta difference has a typed evidence map to the
canonical packet and cannot meet B and not P_common and not G_common and J.

That same map preserves/reflexively lifts the entire original constrained
relation, its retained typed incidences, and its principal solution evidence
at every original xi and scope.
```

These are targets, not assumptions offered as another conditional main-gate
theorem. Calling the target a bisimulation, or stipulating that admission
depends only on canonical `p_0`, would assume precisely the desired result.
Calling every well-formed latent profile an Authority-admissible original
completion would instead enlarge the source semantics without certification.

The actual first missing source cut is still the original-formal
applicability/introduction rule. A source derivation of that rule might prove
the inventory exactly, or might expose genuine additional positions whose
dynamic and static redundancy can then be tested. Until such a derivation is
available, the quotient route supplies no substitute closure and no
source-certified semantic obstruction requiring a user decision.

Recommended next action: use the source-introduction lane's result before
funding another quotient experiment. If it supplies an extra source-certified
position, use §3's exact difference condition with actual receiving assignments
as the first falsifier. If it supplies exhaustive original introductions,
preserve the inherited packets and original joint predicates and derive the
complete profile directly. No assumption about receiver expiry should decide
either branch in advance.

## 7. Checks, resources, omissions and frozen commit packet

Verification was manual selected-section reading and elementary Boolean
expansion of the existing visibility equations. Commands were bounded `rg`,
`cat`, `sed`, Python standard-library hashing and read-only `git show` for
baseline-byte equality. Some early broad captures were truncated; all
mathematical claims use later narrow reads of the governing sections.
No tests, builds, Oracle execution, executable profile model, runtime timing,
Git mutation, questions, other-file writes or re-delegation were performed.

Budget: initial 20-minute bounded manual proof/search envelope; lightweight
sequential reads and one leased note write only, zero heavyweight processes.
Exact CPU time, peak RSS and elapsed wall time were not instrumented. Coverage
is the exact fixed source plus the four candidate-local cases in §3, not an
enumeration of all programs, worlds or original completions. The Frozen
Oracle was not used as a semantic premise or executed.

Omitted: complete original P/applicability/contribution generation; actual
capture attachment and receiver activation; evidence-rich principal-solution
equivalence; full original admission-world construction; production acceptance
or Option A/2 conformance. No independent review of this note is claimed.

All direct inputs below matched the pinned baseline bytes when checked:

| Input | SHA-256 |
| --- | --- |
| `AGENTS.md` | `c5ab6ebf0d72fda4c025abc3a0ec9d57c9015a0c8e4ba65900ed385fb62fb9b3` |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `.codex/agents/researcher.toml` | `07759f596adecddcd20092592a317181afb0f542e642385a1cd03b41df05f41d` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/progress/2026-10-06-source-call-generation-construction.md` | `6bd7773326ccdd3101eaeb60a7e0f5d98a6c7a80b68467f6bf06a6466ffc4073` |
| `notes/progress/2026-10-06-profile-source-normal-form-construction.md` | `ea32179888d41ceaddda7ba5c3566e1e83bf489da3fba763a28fda37e8876fad` |
| `notes/progress/2026-10-06-profile-completion-model-separation.md` | `12eeb404d0a5a1515740c2484868885c7a55c967bd705dac5b5858dd8ef6d090` |
| `notes/progress/2026-10-06-source-generation-pa-review.md` | `9f51c91fbaa9976022fed10d4b3fd9ab7eb1ae2027192bb9d5823f5a2d0fef2a` |
| `notes/progress/2026-10-06-profile-original-applicability-counterexample-search.md` | `3b4adc3ca1d2cb3621ed65f99c5615992deea8eda70089b32fc7086de1bf25be` |
| `notes/progress/2026-10-06-profile-P-exact-candidate-construction.md` | `ee3a5ed1ba657c2f7828ef409ba3cf052899d709394ce203c9473bcf73ca0358` |

Commit packet:

- Exact changed lease path:
  `notes/progress/2026-10-06-profile-completion-observation-quotient.md`.
- Baseline: `f93fb06cd40c12fed6caf5051e045f206c4b2da6`.
- Dependency hash changes: none observed; revalidate before integration.
- Review status: frozen, unreviewed research-only route audit; no main gate
  closure, exact-source semantic separation or implementation permission.
- Checks: governing-section reads; four-case kernel calculation; baseline
  dependency-byte equality; final local-link/newline/whitespace checks.
- Proposed one-line checkpoint message:
  `research: delimit profile observation quotient for captured-step source`.
- Shared-record deltas intentionally deferred to primary/curator: retain P
  and main source-generation gate open; record that grant/expiry/common
  protection discharge only the candidate-local dynamic difference, and
  that no exact-source completion equivalence or alternative was certified.
