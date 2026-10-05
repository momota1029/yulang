# One-event shallow-handler outward trace

Date: 2026-10-06
Status: frozen, unreviewed research; source-equation derivation and precise blocker
Baseline: `0ca3add326c0683971c8e6af2dc1d8b13e0ab123`
Lease: this file only
Implementation authority: none

## Objective, method and claim class

Instantiate the ordinary source equations with one event and one intervening
shallow handler. Compare consumption with an eligible handler whose single
guard rejects, so actual handler processing finishes before forwarding the
original event. This concretizes the earlier generic cut argument; it does
not assume its proposed marked-delimiter refinement. A third, minimal raw
resume trace discriminates forwarding from resumption.

**Conditional source-equation result:** with the supplied executable typed
view and ordinary eligibility premises below, the consuming image returns
without the original event, whereas the rejecting image yields precisely that
event at the target computation's ordinary outward request boundary. This
boundary result is obtained before evaluating the outer handler image.
**Unproved bridge:** identification of that boundary with the public marked
slot, its independently attributed contribution, and the complete protection
witness; and refinement into the approved protection update before the outer
query. No unrestricted release theorem or production-source program is proved.

## Governing sections and frozen dependencies

All source reads use the baseline revision, rather than live replacements.
Line numbers below refer to that revision.

| Source | Exact governing section / lines | Blob |
|---|---|---|
| `questions/2026-10-05-handler-protection-release-crossing/approved-answer.md` | Exact approved draft, decisions 1–7; q1/d1 | `358438b2a6d7b61408713c5dc48bb84b307c75d7` |
| Same directory, `receipt.md` | Validation; Outcome and reason | `154641f508ea224b5e907639e6c685b207cb3a84` |
| `notes/design/2026-10-02-ordinary-computation-semantics-package.md` | §§2–3: request bind, force/emission and invocation; §4: ordered current search; §5, lines 400–499: shallow image and explicit deep expansion | `640bbfa85630d1dd496a3fd1ccb757536385d720` |
| `notes/design/2026-10-02-typed-source-owner-realization.md` | §6 Selected outside-image equation, lines 399–448; control preservation, lines 457–477 | `d0c6c5e2d10cf1b72da0e8613b74641bd25b2caf` |
| `notes/design/2026-10-02-typed-boundary-realization-draft.md` | §4, lines 249–344: Flow versus observation and superseded outward observation; lines 388–515: current structural pre-dispatch observation; §6, lines 667–700, 732–790, 792–868: views, transport, receipt and live incidence | `5e0499e43b3dbf04de0bcdb6c0fa5994224d8a87` |
| `notes/design/2026-10-05-handler-hygiene-public-provenance-notation.md` | Intended reading; Small-step / relational interpretation candidate, lines 89–149; relation table, lines 159–164 | `0b249e14d1ecb3bea076549b52af121478552491` |
| `notes/design/2026-09-29-scc-intrusion-redesign-charter.md` | §§14–15: outside selection and primitive shallow / explicit deep | `4a6db32d07ae23a18669a62b5ea25d1d19383c14` |
| `notes/progress/2026-10-05-handler-release-crossing-constructive-attempt.md` | Hypotheses and retained witness; Local transition derivation, especially missing cut/annotation/continuity premises | `63cf77a14b0e42330c99f5cadb7cd0c1812fff25` |

The approved decision fixes actual outward crossing after intervening
processing, same target while the original receiver remains active,
no release caused by consumption without crossing, and preservation of
pre-dispatch observations and full protection evidence. Release supplies no
selection, capture, consumption or subtraction. Those meanings are fixed;
the candidate notation's older timing/lifetime questions do not reopen them.

## Smallest supplied source instance

Fix one assignment `nu` and retain its original `K,D`. Choose a single
unparameterized operation `E : Unit -> Unit` and an already constructed
request thunk `t_E`. Its construction was inert. A source-demanded
`Force(t_E)` emits

```text
q = (E, Unit, alpha, epsilon, K, D, k0)
k0(Unit,C) = Return(Unit,C)
```

`alpha` and `epsilon` are fixed origin and dynamic event identities. The
suffix has no further request. There is no store mutation. These are ordinary
source-machine objects, not asserted public parser syntax.

Supply this decorated executing context:

```text
Owner(r, H_o[View_o(T,p, H_i[Force(t_E)])])
T = (value identity, signature position, evidence root)
```

`Owner` names the already active invocation, not a new invocation here.
Both handler occurrences are installed by this same live receiver `r`, with
`h_i` inside `h_o`; `h_o` encloses the complete target computation. Its
value arm is irrelevant before the outer request query. The target's
computation is exactly the inner shallow image; there is no later adaptation
or force that could consume its result. Both handlers cover `E`. Supply typed
receipt and profile evidence making `Visible(q,h_i,C_i)` true, and compatible
`Unit` endpoints for an accepted arm. An explicit receiver-local admitting
contract can satisfy this premise. The argument does not require the outer
query to accept, reject, or be changed by release.

The public annotation occurrence `s:'e?` is intended to designate `(T,p)`.
That designation, attribution to `'e`, and its relation to a protection witness
are **not** consequences of the supplied executing context. They remain the
bridge obligations below. Assume the target is initially unreleased when
discussing its first release; a previously released target needs no new
crossing under q1/d1.

This instance minimizes dynamic ingredients: one fresh event, one intervening
handler, one target view, one live original receiver, and one outer candidate
query. A constant false guard is the smallest visible processing step that
distinguishes forwarding after handler evaluation from immediate ineligibility.
It is not a formal minimality theorem over all source grammars.

## A. Consumed original event; Observe survives

At emission, `o` belongs to `views(EC(C_emit(q)))`. Hence the current §4 rule
records `Observe(q,T,p,o)` before either candidate is searched. Matching uses
the original request's yielding-boundary applicability and exits `h_i`.
Choose one accepting arm whose body is `Return(Unit)` and never invokes `k0`:

```text
H_i[Request(q,C_i,k0)]
 = MatchRequest_i(q,k0) >>= Finish_i(q,k0)
 = Return(Accepted(arm,bindings),C_minus_i) >>= Finish_i(q,k0)
 = Run(Return(Unit),bindings,C_minus_i)
 = Return(Unit,C_minus_i).
```

These are successive equation instances, not a count of primitive VM steps.
`C_minus_i` has left exactly `h_i`; `r` and `h_o` are still active. The arm
runs in the ambient target view outside `h_i`. The original `epsilon` has
no request result from this target computation, so no outer request query
for it occurs. The pre-dispatch `Observe` and underlying profile/Flow/receipt
evidence are retained; `Inc_C` for the expired `h_i` is false. Retaining
full evidence does not mean retaining a live grant for an expired candidate.

For this initially unreleased target, q1/d1 forbids a release caused by this
consumed contribution. The final result can trigger an ordinary value arm;
normal return is not an outward request crossing. Thus an
`Observe => crossing` shortcut fails already on this one-event trace.

## B. Handler processing then same-event forwarding

Keep the identical emission, observation and initial eligibility. Replace
the accepted arm decision by a single matching arm with `guard = false` and
no fallback. The guard executes outside `h_i`, emits nothing, and advances
ordered matching to exhaustion:

```text
H_i[Request(q,C_i,k0)]
 = MatchRequest_i(q,k0) >>= Finish_i(q,k0)
 = Return(NoArm,C_minus_i) >>= Finish_i(q,k0)
 = Forward(q, lambda a,Cnow. H_i[k0(a,Cnow)]).
```

The source equations specify `Forward` as onward propagation of the original
request with this forwarding continuation. Call that continuation `k_f`.
The target computation's ordinary request result is therefore
`Request(q,C_minus_i,k_f)`: same `epsilon`, `alpha`, payload and `K,D`, with
only the source-prescribed future control wrapper added. That wrapper runs
only if an outer computation supplies a response; it installs a fresh
shallow occurrence rather than reviving `h_i`.

The outer image now has a request result from its enclosed target computation,
so ordinary source search proceeds to `h_o` at its actual configuration.
It has not run `MatchRequest_o` yet. This is the shortest derived boundary
witness in this supplied source instance: the complete inner computation
has yielded the original `q` after its guard and finish computation, with
the original receiver still active, before the next outer query.

This does **not** use final whole-program residual support: a later outer
selection may consume `q` without changing this already derived local
request result. Nor does it redefine `Observe` by outward support. The old
outward projection is superseded as an observation rule; an ordinary
computation having a request result remains a distinct source fact.

The equations establish the request result at the ordinary boundary. They
do not display a combined transition
`leave marked (T,p); update its protection; then query h_o`. Claiming that
combined small step from this trace would assume the missing refinement.

## Raw resume is not same-event forwarding; explicit deep stays distinct

Choose an accepting arm `Resume(k0,Unit)` instead of the rejecting guard:

```text
H_i[Request(q,C_i,k0)]
 = Run(Resume(k0,Unit),bindings,C_minus_i)
 = k0(Unit,C_minus_i)
 = Return(Unit,C_minus_i).
```

The selected original event has been handled. Raw resumption begins its
saved suffix outside the selected shallow handler. It does not re-emit
`epsilon`. If that suffix instead emits another `E`, that request has a
different dynamic event identity and needs its own attribution/observation
facts. An arm's fresh re-performance likewise is not this original event.
Thus this trace supplies no same-event crossing. An arbitrary suffix is not
claimed incapable of exposing other pre-existing events; the claim concerns
the original handled event in this minimal instance.

Explicit deep expansion uses `wrap_i(k) = lambda a. D_i[Resume(k,a)]` and
`D_i[c] = S_i-with-wrapped-continuations[c]` (ordinary §5). With this pure
`k0`, one reapplication still returns without re-emitting `epsilon`. With an
effectful suffix it installs a fresh shallow occurrence and uses its actual
source ownership/contracts. It does not reinstall the old handler or copy
release to a new receiver. No deep wrapper is inserted into traces A or B.

## Exact association and transition blocker

At emission and through B's forwarding, retain the full proof coordinates:

```text
original b, receiver r, original profile position p_b;
tagged typed Flow derivation gamma into T at p;
Observe(q,T,p,o), candidate owner's actual Receive derivation;
q.event=epsilon, q.origin=alpha, original nu,K,D and attachment;
current exact active receivers/handlers.
```

`Path` joins matching profile paths, `Observe` and receipt; `Inc_C` adds
current activity. Their definitions contain neither marker occurrence `s`
nor an attribution judgment `AttributedTo(q,'e)`. They cannot identify which
complete protection evidence belongs to that public output marker merely
from equal effect-family heads. Even choosing identity `Flow` eliminates no
such obligation. In A the full witness exists without an outward request;
in B the outward request exists without a derived annotation association.

The precise missing premise is a source/elaboration rule associating the
original annotation occurrence `s` with target `(T,p)`, independent `'e`
attribution, and the intended full protection witness, together with a
refinement theorem placing that target's ordinary outward request result as
the actual marked-slot exit before the next outside eligibility query.
No marked-delimiter transition or persistent compiler carrier is invented
here. If this premise is independently supplied, B meets the approved first
crossing condition and A does not; the protection-only frame condition and
post-release visibility filter still need their own proof. General typed
transport is not a proof of same-target release continuity for every later
latent or resumed view.

## Checks, coverage, resources and next action

Commands were bounded read-only `git show <baseline>:<path>`,
`git cat-file blob <approved-answer-blob>`, `git ls-tree`, `git rev-parse`,
and `rg`/`nl`/`sed` for the exact source locators. `test ! -e <leased-path>`
succeeded before creation. At dependency inspection, `HEAD` equaled the
baseline and the eight dependency blobs above matched their pinned versions.
Only this leased note was written, using `apply_patch`.

No executable checker, test, build, random seed, enumerated input range or
oracle comparison was used. Three text derivations cover consumption,
post-guard exhaustion forwarding, and pure raw resume; one explicit deep
unfolding is discussed. The independent grounding is the retained ordinary
source equations, not another checker using guessed release rules. This is
source-rule consequence under shared supplied view/eligibility assumptions,
not independent validation of those candidate rules or self-review.

Mutations discriminated: release on pre-dispatch observation; treat raw
resume or fresh same-family re-performance as forwarding the original event;
test the outer handler before inner guard/finish completes; infer crossing
from final residual support. Failure conditions: missing executable view
decoration, initially ineligible inner handler (the guard-processing trace
changes), additional target-side computation before its output, expired
original receiver, or a wrong annotation/attribution association. A divergent
guard gives no completed crossing in a finite prefix.

Budget: text/source derivation only, zero compiler/build/test processes, no
heavy computation, no Git mutation and no delegation; completed within the
15-minute lease. Peak RSS/CPU and exact wall time were not instrumented.
Omitted: raw-source grammar/elaboration, all adapters and latent paths,
multi-shot histories, general deep recursion, overlapping protections,
unrestricted release adequacy, inferred production shapes and compiler code.

Recommended next action: derive or reject the annotation-to-full-witness
association and the explicit boundary/query refinement from a typed source
rule for this exact false-guard instance. Another profile/filter toy probe
would leave the identified premise untouched.

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-handler-marked-slot-outward-trace.md`.
- Baseline SHA: `0ca3add326c0683971c8e6af2dc1d8b13e0ab123`.
- Dependency hashes changed: none at inspection; direct blob hashes listed
  above. Primary should recheck before checkpointing.
- Claim/review status: frozen unreviewed research; conditional ordinary source
  derivation, minimal distinguishing instance, explicit unresolved bridge.
  No independent review, theorem closure or implementation authority claimed.
- Checks already run: pinned source/locator reads, dependency SHA inspection,
  and absent-path lease check; no tests/builds/experiments.
- Proposed one-line commit message: `research: derive one-event handler forwarding boundary trace`.
- Shared-record deltas intentionally left for primary/curator: link this
  concrete false-guard witness and raw-resume distinction from the handler
  release gate; retain annotation association and marked-boundary/query
  refinement as open. Do not close the gate or change authority/index/task
  files from this artifact alone.
