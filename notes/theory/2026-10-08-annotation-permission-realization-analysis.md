# Annotation permission: eager and deferred realization

Date: 2026-10-08
Status: bounded non-authoritative research; conditional derivation; review repair awaiting delta review
Baseline: `aff71453cefff3b8a8f435b931d204c4ef2249da`
Branch: `research/simple-sub-intrusion`; unrelated dirty files are excluded
Lease: this new note only
Implementation authority: none
Checks: dependency hashes and lease/diff checks only; zero tests/builds/probes

## 1. Objective and governing premises

Make precise the proposed alternatives for realizing the permission in
`apply(f: _ -> [io] _, x) = f x`:

- **A:** release at the realized annotation slot when an identified contribution
  actually leaves that slot.
- **B:** realize only at a live eligible handling opportunity; otherwise defer.

The word “defer” needs a retry rule. This note completes B by retaining a
pending permission after the qualifying crossing and checking it before each
later actual handler candidate in the same live, transported target view.
This is a candidate operationalization, not an inference from current Authority.
Under explicit premises below, it is handler-observationally equivalent to A.
A restriction that retries only at another crossing has a two-event separator,
but that restriction is an additional candidate decision.

Exact governing sections and their claim classes:

| Source | Governing section | What it supplies |
| --- | --- | --- |
| [Inferred Function call views](../design/2026-10-05-inferred-function-call-views.md) | §§1.1–2, 4, 5(3) | Authoritative separation of source annotations/internal views; original static slot and jointly scoped evidence; permission for the identified `io` contribution, without guaranteed realization. Exact realization remains open. |
| [Directional protection](../design/2026-10-06-directional-inferred-effect-protection-addendum.md) | §§1–4 | Current user-selected upper-use protection and no reverse protection of lower/provider occurrences; event-to-profile incidence remains a separate premise. |
| [Callback delivery](../design/2026-10-03-callback-context-delivery.md) | §§2.1, 3–4 | Authoritative callback-literal B, actual callable role/entry preservation, static slot versus dynamic receiver, and receipt before force/body. |
| [Source annotation answer](../../questions/2026-10-05-source-annotation-boundaries/approved-answer.md) | exact approved draft clauses 1–4; matching receipt | Each actual boundary directly checks its current endpoint, exports its target plus local realization evidence, and retains earlier evidence. Concrete successes cannot replace a later direct check. |
| [Protection-release answer](../../questions/2026-10-05-handler-protection-release-crossing/approved-answer.md) | exact approved draft clauses 1–7; matching receipt | Selected meaning/lifetime of **`'e?`**: actual outward crossing, same transported target view and live original receiver, no new crossing for each later occurrence, expiry and preservation. This is retained unchanged; it does not select `[io]`'s realization rule. |
| [Handler-hygiene notation](../design/2026-10-05-handler-hygiene-public-provenance-notation.md) | “Intended reading”, “Small-step / relational interpretation candidate” | Distinguishes protection release from attribution, row membership, capture, selection, consumption and subtraction. Broader source realization is open. |
| [Typed-boundary draft](../design/2026-10-02-typed-boundary-realization-draft.md) | §§2, 6, especially “One relational transport operation” and “Receiving ownership and observation” | Selected typed-value transport principle; candidate exact `Path`, `Inc`, `Protected`, `Grant`, `Visible` formulas. These are conditional model inputs, not completed source elaboration. |
| [Ordinary computation package](../design/2026-10-02-ordinary-computation-semantics-package.md) | §§2–5 | Candidate state-threaded requests, current candidate configurations, ordered innermost-first dispatch, raw shallow resume, receiver expiry. |
| [Concrete compatibility](../design/2026-10-03-concrete-compatibility-boundary.md) | §1 | User-selected single endpoint-dependent inequality and non-composition of concrete successes. |
| [Production Call proposal](2026-10-08-production-call-elaboration-proposal.md) | §4 C6 | Candidate `MayRemove` incidence plus an independently lawful realization; the proposal deliberately supplies no complete realization algorithm. |

**Entailed:** permission alone is insufficient; original annotation/contribution
incidence and live evidence must be justified independently; unrelated effects
and prior/provider evidence survive; source boundaries perform direct checks;
neither permission nor realization establishes family-wide subtraction or
handler selection. Source formation cannot come from successful pending `Q`.

**Candidates introduced here:** `[io]` crossing as a trigger; a receiver/view
scoped release or pending state; its transport/retry policy; precisely which
annotation-governed protection witnesses it can disable; the opportunity test
below. Similarity to `'e?` does not make these `[io]` choices selected.

## 2. Small state vocabulary and independent inputs

Fix one jointly well-formed assignment `xi = (nu,K,D)`. Use proof indices:

```text
a      original [io] annotation occurrence, with static slot beta and position p
k      source contribution identity governed by a; not the family name io
V      target-view identity/evidence root exported at that actual boundary
r      original dynamic receiver activation
q      dynamic event, with operation instance, payload, origin, Kq,Dq, continuation
w      protection witness, retaining original slot/path/seed/provider identity
C      live store, source control and ordered active receiver/handler activations
H(C)   the actual remaining candidate sequence, innermost first
```

Different events may be incident to the same source contribution `k`. Two
events with equal family/type arguments need not be incident to `k`. Two views
of the same underlying value need not be the same `V`. `r` is not `beta`.

The following inputs must come from source typing, resolution and evidence,
independently of the release state and the handler image being compared:

```text
BoundaryCheck(a,current,target; e_a)   direct endpoint query and local evidence
MayRemove(a,io,k; beta,p,xi)           permission with original typed incidence
Qual(q,a,k,V,r)                      q's exact typed observation/receipt incidence
Cross(q,a,k,V,r,C)                   actual outward departure through this slot
Owned(w,a,k,V,r)                     w is governed by this precise permission
Transport(V,p,V',p'; M)              certified corresponding typed path image
ApplicableTransport(q,t,C)          current observation is on that certified image
W(q,h,C)                            all current candidate protection witnesses
Grant(q,h,C)                        current receiver-local concrete contract
```

`Cross` is witnessed before the subsequent handler image; it cannot be defined
as “q survives after release”. It may follow intervening computation and handler
processing. `Qual` uses the event's own `Observe` and receipt/path evidence.
`Owned` is not inferred from a matching family or normalized effect endpoint.
In particular a provider/lower witness not governed by `a` stays in `W`.
`ApplicableTransport` requires the current observation's correspondence to the
original view/path through `M`, including a certified identity correspondence
at the original position. It is independent of the permission state.

The successful actual annotation boundary exports
`(target, e_prior + e_a + permission evidence)`. Release records augment this
evidence; they never replace the direct boundary check or erase a prior record.
A failed or missing direct check supplies no activation or export in this
fragment. This is a stop condition, not a new compiler rejection policy.

For this bounded fragment, at most one permission tuple
`t = (a,k,V,r)` is being compared. Other protection witnesses, grants and nested
slots can coexist as fixed independently justified evidence. No compiler field,
new runtime carrier or global protection bit is proposed. The state below is
metatheoretic shorthand for evidence and its effective candidate interpretation.

Define the ordinary candidate test with an effective witness set `S`:

```text
Vis(q,h,C; S) = Active(h,C) and Active(owner(h),C) and Covers(h,q.operation)
               and (S is empty or Grant(q,h,C))
```

The active-receiver filters used to form `W` remain exactly those of the
typed-boundary candidate. A current local grant has the selected no-origin-veto
behavior: extra inherited witnesses do not override it. Neither alternative
changes `Grant`. Actual pattern/guard evaluation and `OpCompat` remain at their
ordinary stages after this visibility test. In this note, “opportunity” means
visibility at an actual candidate, not a promise that its pattern/guard matches.

## 3. Complete alternatives on the bounded fragment

Use logical states `off`, `pending`, `released`, `expired` for `t`. Initially
both alternatives are `off`, with the same successful boundary-check evidence,
permission and protection witnesses. Historical marks always remain recorded.

### A: release at qualifying crossing

At a `Cross` transition with `Qual`, `MayRemove`, the direct boundary evidence,
and `Active(r,C)`, set `t` to `released` and append local crossing/realization
evidence. Missing any premise preserves the current state: `off` stays `off`,
and an existing release is not reset. Repeated qualifying crossings
while released are idempotent and retain their own event evidence.

At each candidate observation, define

```text
ReleaseApplies(q,t,C) = state(t)=released and Qual(q,a,k,V,r)
                       and Active(r,C) and ApplicableTransport(q,t,C)
W_A(q,h,C) = W(q,h,C) minus {w | Owned(w,a,k,V,r)}
            if ReleaseApplies(q,t,C); otherwise W(q,h,C)
```

Thus even a qualifying event at a live receiver retains all current witnesses
before the first qualifying crossing, or at an uncertified observation path.
This is effective protection interpretation,
not deletion of historical witnesses, events, origins, membership or row support.
Release supplies no grant and consumes nothing. Search next applies `Vis` and
the ordinary arm tests to its actual candidate in the actual reached `C`.

### B: pending at crossing; realize at an actual opportunity

The same qualifying crossing sets `off -> pending`, appending crossing and
pending evidence. It preserves an existing `pending` or `released` state;
failed or nonqualifying crossings likewise preserve the current state. A
crossing by itself supplies no release conclusion. Before testing each actual
reached handler candidate `h` for a qualifying event, when `t` is pending,
`r` is live, and `ApplicableTransport(q,t,C)` holds, compute

```text
W_minus(q,h,C) = W(q,h,C) minus {w | Owned(w,a,k,V,r)}
Opportunity(q,h,C,t) = Vis(q,h,C; W_minus(q,h,C))
```

If opportunity holds, set `pending -> released`, append the current exact
candidate/incidence realization evidence, and perform the ordinary visibility
and arm tests using `W_minus`. If it fails, remain pending and perform the
ordinary tests using the unchanged `W`. B does not inspect a hypothetical future
stack, reorder candidates, execute a guard early, or select an arm itself.
Every reached candidate is tested at its actual current configuration.
When B is already released, it uses the same `ReleaseApplies` gate as A;
when neither rule applies, it uses the unchanged `W`.

This test is noncircular: it computes the ordinary candidate predicate from the
preexisting complete witness inventory after discounting only the independently
authorized witnesses. It does not obtain `Qual`, `Owned`, `Grant` or `Cross`
from hypothetical successful consumption. It is a **candidate lawful-realization
rule**, not proof that C6's source premise follows from the existing documents.

The gate is checked even if an existing local grant already makes `Vis` true;
requiring removal to be strictly necessary would be another state-policy
variant with the same proof below for handler observations.

### Shared transport, lifetime, fresh events and order

Both alternatives have these fully specified fragment rules:

1. **Typed transport:** permission and state follow only `M`'s matching indexed
   paths. Bind, capture, store/read, structural adaptation and returned latent
   use do not invent a new tuple. A transported occurrence uses the original
   receiver/view evidence through its certified path. No correspondence means
   no state there. Source witnesses and shared `K,D` remain retained.
2. **Later events:** a fresh event needs its own `Qual` and current observation.
   Released A/B apply without another crossing in that transported view.
   Pending B can realize at a later candidate without a second crossing.
   An unrelated event in family `io` neither uses nor triggers this state.
3. **Nested slots:** a genuinely new boundary/view `a',V',r'` starts with its
   own `off` state and evidence. Transport through a nested call preserves
   applicable original witnesses; it does not copy a release to that new slot.
   Independently present protection on another slot survives both rules.
4. **Resumption:** raw continuation bind keeps the pending source suffix and
   uses the live resumed store. The logical state is retained only if its same
   receiver is still active and the same view is certified to transport to the
   resumed observation. No shallow handler is reinstalled. Repeated resume
   uses the same test, and each new event has a new event identity.
5. **Deep re-entry:** use the actual source expansion and its active frames.
   A surviving original tuple transports; a fresh receiver gets fresh state.
   Neither candidate restores an expired tuple from runtime lineage.
6. **Expiry:** after `r` ends, set the effective state to `expired`; keep its
   historical evidence, but use neither release nor pending state as authority.
   Current candidate incidence rooted at that receiver is already inactive.
   Handler expiry removes that exact candidate's incidence; a later handler
   must establish its own current path and owner receipt.
7. **Dispatch:** ordinary innermost-first search, forwarding, selection and
   raw shallow resume are unchanged. A/B release changes only the effective
   authorized protection witnesses before a reached candidate test. Effects
   of pattern/guard evaluation, selected-arm compatibility and response are
   evaluated by the shared source machinery in the same order.

These are complete rules for the supplied decorated fragment, not complete
source-language semantics or an inference/profile construction judgment.

## 4. Conditional handler-observation equivalence

**Theorem (rule-relative, unreviewed).** For any finite trace in the above
decorated fragment, A and B have equal ordered candidate/arm observations,
selected handlers, event consumption/forwarding, responses, live-store effects,
and external request residuals, under all of these hypotheses:

- The direct boundary, incidence, crossing and transport inputs are identical,
  independently justified, and insensitive to the effective release bit.
- Release is a pure change of effective protection; the candidate does not
  change event membership, `K,D`, payload, store, control, grants or arm behavior.
- B checks every actual later opportunity, including transported latent and
  resumed observations, before the candidate's ordinary visibility test.
- `Vis` is exactly the above predicate; the complete inventory includes all
  other protection witnesses and each current candidate's activity filters.
- No source construct observes the pending/released distinction or the exact
  realization log. Static admission, inference and public interface export do
  not consult that distinction within the trace being compared.

**Derivation.** Relate equal external configurations and evidence except for
the possible state pair `(A=released, B=pending)` and their local release logs.
Before the first crossing, and after expiry, effective predicates coincide.
At the first qualifying crossing, A releases and B becomes pending; all
ordinary state is equal. Failed or nonqualifying crossings preserve the state
pair, and repeated qualifying crossings do not reset either side.
Transport/resume preserves the relation using the same certified path.

At a candidate while that exceptional pair holds, first require the common
`Qual`, live-receiver and `ApplicableTransport` premises. If any fails, both
use `W` unchanged. If all hold, A tests `Vis(W_minus)`. If it is true, B's
opportunity is true, so B realizes first
and tests that same predicate. If it is false, B remains pending and tests
`Vis(W)`, which is also false: removing a subset of protection witnesses cannot
turn a visible candidate into an invisible one when grants and activity are
unchanged. Both forward and reach the same next configuration. Other-slot
marks, nonmatching operations, inactive receivers and local grants are included
in this argument; no family-based cancellation is assumed. Once B releases,
the effective state and all subsequent candidate tests coincide. Induction
over transitions yields the stated finite trace equality. The same argument
covers unrelated events by the frame condition.

Thus there is **no smallest differing handler-consumption trace for these two
completed alternatives under these hypotheses**. The local realization logs
can differ immediately at one crossing with no eligible handler: A records
release, B records pending. That is an evidence-state difference, not an
established source-observable interface or behavior difference.

This does not prove equality of complete Function denotations, principal
schemes, production admission, all infinite observations, or arbitrary source
elaboration. In particular a static exporter that exposes the difference
invalidates the last hypothesis; no pinned source defines such an exporter.

## 5. Smallest retry-policy mutation that distinguishes behavior

Change only B's retry rule: test opportunities at qualifying crossings, and
never test the pending state at a later candidate without another crossing.
Call this candidate mutation `B_cross_only`. It is not the B above.

Explicit two-event decorated trace (not an asserted accepted source program):

| Step | Common independent evidence/control | A | B | B_cross_only |
| --- | --- | --- | --- | --- |
| 0 | Successful direct annotation boundary; `t=(a,k,V,r)` live; no matching active handler | off | off | off |
| 1 | Qualifying event `q1` has its own incidence and actually crosses `a`; `r` remains active | released | pending | pending |
| 2 | With no covering handler, `q1` is an external residual. The test environment resumes its raw continuation without ending `r`. A corresponding result/view path remains certified. | Same residual/response | Same | Same |
| 3 | That continuation installs one handler `h` owned by live `r`, with its own typed receipt. `Covers(h,io)`; no local grant; no other protection witness. | released | pending | pending |
| 4 | Fresh `q2 != q1`, from `k` in the same transported view, has its own `Qual`; it has no new crossing of `a`. The sole ordinary arm matches and is compatible. | `h` consumes | B realizes before `h`; `h` consumes | targeted witness remains; `h` forwards; external residual |

The event `q2` must be at a genuinely corresponding profile position: an
outer `call.effect` annotation cannot be pasted onto an unrelated
`result.latent.effect`. This trace is conditional on the supplied transport
certificate. Raw external resumption without ending `r` is also an explicit
source-machine premise; this note does not construct a closed program that
realizes that environment. If no such transport/live-resume derivation exists
on the intended source envelope, this witness is unavailable there.

Within this displayed trace skeleton, two events are necessary: no matching
handler exists until the environment responds to the first residual, after
which a fresh observation uses the state without a new crossing. One permission,
one live receiver and one later handler suffice. Minimality is relative to that
skeleton; changes of other protection/activity during search might distinguish
the mutation with one event. No global minimum over source programs is proved.
The original A/B pair gives identical consumption in the table.

A second named mutation permits B to realize **before** the first outward
crossing, at an inner candidate that would be visible after discounting the
targeted witness. One pre-crossing event and that handler then suffice: A keeps
protection and forwards until crossing; mutated B releases and consumes. This
requires an independently justified inner incidence and changes the trigger;
it is neither the defined B nor a consequence of `[io]` permission. Applying
this mutation to `'e?` would contradict its selected crossing rule.

## 6. Oracle independence, omissions and next action

No checker, compiler, Oracle, frozen-weight probe, randomized search or build
was used. There are no seeds or enumerated ranges. The proof compares two
supplied transition systems; it cannot prove those transition premises are
source rules. Both sides share the same candidate `Vis`, decoration, transport,
crossing and dispatch assumptions. The conclusion is independent of compiler
output, but it is not an independently grounded validation of source semantics.
The coordinator supplied an independent lane's equivalence/mutation direction;
this note's producer performed the explicit derivation and does not claim that
coordination input independently reviews this artifact.

Unverified scope: construction of `Qual`, `Owned` and `[io]` `Cross`; lawfulness
and completeness of the realization predicate; annotation/callback overlap;
multiple interacting permissions; arbitrary recursive/generalized profiles;
profile principality; an accepted closed source witness for the mutation;
static interface/export observability; whole Function/production conformance.
The full typed-boundary and concrete-compatibility documents contain further
gates outside the cited sections; this was not a whole-document semantic audit.

Precise failure conditions for the equivalence are a release-dependent
decoration/grant, a hidden affected provider mark, irreversible guard work in
the opportunity test, a missed later candidate, a fresh receiver treated as the
old one, or an exporter/source operation that observes release evidence. These
are proof obligations or alternative semantics, not presumed implementation bugs.

**Recommended next action:** retain A versus deferred B as an implementation/
evidence-scheduling candidate pair, and require a source-certified realization
predicate plus confirmation of whether public export can observe their state.
The conditional equivalence does not yet supply a useful non-leading binary
question about handler behavior for this precise pair. For deciding whether
such a handler-behavior question is useful, ask a user only if the
primary establishes a genuine observable policy boundary, such as whether an
already-crossed live transported view must retry at later opportunities.
The two-event mutation supplies exact consequences for that future question;
it does not justify presenting the unsupported retry restriction as current
Authority. The already selected `'e?` timing/lifetime needs no new question.
This recommendation concerns the usefulness of a handler-behavior question
only. Adopting any new durable realization semantics still requires the
independent review and recorded user approval in `rules/design-authority.md`,
even if the candidate handler observations are equivalent.

## 7. Frozen dependencies and commit packet

All assigned dependency hashes matched at initial read and final recheck:

```text
4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1  notes/design/2026-10-05-inferred-function-call-views.md
6b1779933499b360627fa5852c292ce97bda9830d146863b1b7ef440706054a7  notes/design/2026-10-06-directional-inferred-effect-protection-addendum.md
df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5  notes/design/2026-10-03-callback-context-delivery.md
87c2c39bf41a8b652fb96cb3409cf9e2c5735c96e4ccfc8b7c5b7f8380ba6050  notes/design/2026-10-05-handler-hygiene-public-provenance-notation.md
5b0b4321d8644f88a7a946aff31b6b3190d37a9076ac698fa91fdfeef1470f16  notes/design/2026-10-03-concrete-compatibility-boundary.md
1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb  notes/design/2026-10-02-typed-boundary-realization-draft.md
ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917  notes/design/2026-10-02-ordinary-computation-semantics-package.md
e1e2ff77b181fe42edd404ee0d69cfc6d3bb0fbc99ba7e7f092710025d11fb12  questions/2026-10-05-source-annotation-boundaries/approved-answer.md
7cf351cd6abf654f70982c7269d7286b50faaca69461db8d88b1e22da314b4a9  questions/2026-10-05-source-annotation-boundaries/receipt.md
df33959fffeac0003723909de5af11edce2bd233ff70496a0dc5d3864126baff  questions/2026-10-05-handler-protection-release-crossing/approved-answer.md
071a7b0ca95b965c0e2cfc8f20a43baf5d0fe1d545c13bbe004aaf67f50f0ae2  questions/2026-10-05-handler-protection-release-crossing/receipt.md
a6cfbb30ce7ceaaafc0aac70eb326b3b6efaf410e89f5cd3cfe398cd6d0b2d44  notes/theory/2026-10-08-production-call-elaboration-proposal.md
```

- Exact leased/changed path:
  `notes/theory/2026-10-08-annotation-permission-realization-analysis.md`.
- Baseline SHA: `aff71453cefff3b8a8f435b931d204c4ef2249da`.
- Changed dependency hashes: none. Unrelated worktree movement is excluded.
- Review status: two adjudicated findings repaired; producer-frozen, awaiting
  independent delta review; conditional research only.
- Checks already run: assigned dependency SHA-256 equality, current HEAD/branch,
  leased-path new/untracked status, narrow whitespace/diff and link checks.
- Resources: no tests/builds/computational searches; serial lightweight text
  reads/searches, note writes and two original document-integrity Python
  processes plus two repair-integrity Python processes;
  CPU/RAM peak and total wall time were not measured.
- Proposed commit message:
  `research: formalize annotation permission realization alternatives`.
- Shared deltas intentionally left for primary/curator: if accepted, link the
  result from `tasks/current.md` and the theory inventory as a conditional
  equivalence of scheduling candidates plus an unsupported retry mutation.
  Keep C6 realization/source-incidence and static export observability open.
  No design-index status promotion or question-board bundle is proposed.

The producer stops writing before submitting this artifact for frozen review.
