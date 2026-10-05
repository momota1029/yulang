# Constructive attempt: an event-preserving outward cut for protection release

Date: 2026-10-05
Status: independently reviewed research; conditional source-transition refinement and exact remaining premises
Assigned gate/method: derive the approved crossing predicate from the pinned source machine, rather than enumerate another supplied path/filter model
Implementation authority: none
Lease: this file only
Task baseline: `e4df3c09643babd2e3ced824bf560d8f7c61440a`
Source snapshot: `659eb05646bb95f10a991bbb9cefdee55721eea1`
User constraint: `questions/2026-10-05-handler-protection-release-crossing/approved-answer.md` at `28dddc75f`

## Result and exact claim class

The source rules support a **conditional, noncircular transition refinement**:
follow the original pending request through intervening handler processing;
record release when its event-preserving outward unwind crosses the marked
executing view delimiter, before searching an outside candidate. This uses
the local control cut, not emission-time `Observe`, typed-value `Flow`, final
row support, or a handler image computed after the proposed release.

The approved decision fixes timing and lifetime. It does not supply two
source derivations still needed to instantiate this refinement: (A) the
marked annotation's association with the exact attributed contribution and
full protective witness; (B) proof that a later result/latent transport
continues the same released target, rather than creates an independently
protected fresh view. The pinned source equations also lack an explicit
marked-delimiter crossing rule. The construction below shows how to state
that rule without circular search; it does not claim the rule already exists
in the source typing or production compiler.

Established within the inspected source candidates are the distinction
between observation and outward propagation, preservation of the original
event on forwarding, raw shallow resumption, exact-activation filtering,
and typed transport of tagged profiles and symbolic dependencies. Those
facts are not a proof of arbitrary source elaboration or of the new release
judgment. No finite characterization or executable experiment was run.

## Governing sections and dependencies

- Typed-boundary realization §4, **Operational interpretation and proof**:
  state-threaded adapters; **Superseded outward projection and its control
  counterexample**: request-bind propagation and consumption versus forwarding;
  **Structural observation before dispatch**: `View(v,p,c)`, emission-context
  observation, capture/re-entry and completion. The discarded outward
  projection is not reused as the definition of `Observe`.
- Typed-boundary §6, **Views, signature positions and introductions**,
  **One relational transport operation**, **Receiving ownership and
  observation**, and **Transport and lifetime theorem package**: full tagged
  views, persistent evidence, `Flow`/`Observe`/`Receive`, and live incidence.
- Ordinary computation §§3–5: complete invocation/force, current ordered
  search at post-unwind configurations, outside shallow selection, and
  explicit deep expansion.
- Callback context §§1–4: original static slot/profile, dynamic boundary at
  receiver activation, independent endpoint synthesis, and preservation of an
  existing Pure value's role/entry through its invocation view.
- Pinned hygiene notation, **Intended reading** and **Small-step / relational
  interpretation candidate**: attribution and emission are independent
  premises; only protection changes. Its then-open timing/lifetime discussion
  is narrowed by the later approved answer, clauses 1–7.

The prior bridge note and conditional-filter note at the source snapshot
were read to avoid repeating their consumption and alias-bit attacks. This
attempt's new work is the local outward control cut and the shortest unresolved
same-target transport chain. It adds no new language choice.

| Direct semantic dependency | Pinned Git blob |
| --- | --- |
| Typed-boundary realization | `5e0499e43b3dbf04de0bcdb6c0fa5994224d8a87` |
| Ordinary computation | `640bbfa85630d1dd496a3fd1ccb757536385d720` |
| Callback context | `eeed5c2b5dd38404a4c774cda486864a63992fad` |
| Hygiene notation | `0b249e14d1ecb3bea076549b52af121478552491` |
| Approved crossing/lifetime answer | `358438b2a6d7b61408713c5dc48bb84b307c75d7` |

At the dependency check, HEAD was
`f50c8a88882a10f109a71e2842f4d1b02982de53`. The four source blobs matched
the pinned snapshot exactly; the approved-answer blob matched its integrated
version. A later exact-byte check found that the live notation path differs
from its pinned/HEAD bytes: pinned SHA-256
`331943d5efb352ce29ee8d76d1d0238485f7d66d69a937e647db601cceab54db`,
live SHA-256 `87c2c39bf41a8b652fb96cb3409cf9e2c5735c96e4ccfc8b7c5b7f8380ba6050`.
The index-to-worktree diff was empty, whereas `git diff HEAD -- <notation>`
showed a staged deletion with a replacement present on disk. The initial
index-relative diff therefore did not establish HEAD/worktree equality.
The other three source files matched pinned/HEAD/worktree bytes. Uncommitted
replacement content was not used as authority; the primary was notified of
the discrepancy. Unrelated HEAD movement does not supply missing source rules.

## Hypotheses and retained witness

Fix a finite decorated execution prefix under one joint `nu,K,D`. Assume:

1. The executable view decorations and typed computation positions are
   supplied as in the reviewed decorated-kernel theorem. Original owner and
   boundary identities are supplied by the source ownership derivation.
2. The ordinary request/search computation can be refined into its actual
   successive context cuts, without changing selection order, state/effects,
   or the source-prescribed raw continuation wrappers. An outside candidate
   is tested only after the actual unwind to its configuration.
3. Independent source evidence associates marker occurrence `s:'e?` with an
   original protection witness, attributes the qualifying contribution to
   `'e`, and identifies its target typed view and executing effect position.
   This is missing premise A, not family equality or a new provenance rule.
4. A source proof decides which later typed result/latent transports preserve
   that same target and its original receiver. This is missing premise B;
   general relational-image transport alone is not stipulated to decide it.
5. Until a first qualifying crossing, dispatch uses the prior protection
   state. After that crossing, the approved protection-only filter is used
   for qualifying witnesses of that same target while its original receiver
   is active. This is the approved sequencing constraint, not a theorem
   recovered from the old unfiltered `Protected` equation.

Keep the full witness, schematically:

```text
w = (static annotation occurrence s, original profile position p_b,
     boundary b and exact original receiver r,
     source tag and typed Flow derivation gamma,
     target view T=(value, signature-position, evidence-root),
     executing observer occurrence o and current effect position p_T,
     event q.event, independent contribution attribution/attachment,
     actual Receive derivation for the candidate owner,
     joint nu,K,D and the current exact activation configuration)
```

The tuple names existing proof coordinates; it is not a proposed compiler
record. A projected `Inc_C(q,h,b,p)` tuple, an underlying value pointer, and
an observer occurrence alone cannot replace it. Observer occurrences are
fresh on each raw re-entry; release lifetime is tied to the identified target
and receiver, rather than to one executing occurrence or one dynamic event.

## Local transition derivation

At fresh emission, the executing context has the decomposition

```text
E_out[View_o(T,p_T,E_in[Request(q,C,k)])].
```

The structural theorem records all enclosing executing view observations
before search. Retain these observations unchanged. Then evaluate the
intervening computation/search in source order. For the pending original
event there are three outcomes:

```text
interior selection consumes q, does not forward q  -> no outward cut for q
interior processing still runs or diverges         -> no completed cut yet
original q continues outward past View_o           -> an outward cut for q
```

The last case means that the actual forwarding/unwind derivation moves the
pending original request from the inside to the outside of this exact
delimiter. It can be witnessed by the request result at that local boundary,
or by the source context cut toward the next outside candidate. These are
boundary-local presentations of the same event-preserving transition, not
membership in the final whole-program handler image. The first such crossing
is recorded before testing that outside candidate. If there is no outside
handler, yielding the request at this local outward boundary supplies the
same cut. Normal `Return`/view completion without a request is insufficient.

Define the candidate metatheoretic certificate `kappa` as that cut together
with `q.event`, `o`, the supplied marked position, the full source witness,
the before/after source configurations and its chronological prefix index.
This definition does not run an outside handler to discover whether crossing
occurred. Later outside selection can consume the now-eligible event; that
does not invalidate the earlier cut or its preserved pre-dispatch evidence.

**Conditional ordering lemma.** Under hypotheses 1–5, constructing this
certificate does not depend on an image computed using the protection change
it certifies. Proof: induct on the chronological source prefix. Before a
first qualifying cut, every interior candidate sees only the already-known
release history. Each ordinary bind preserves the pending event and appends
the remaining suffix. Each intervening shallow image either consumes the
original event or forwards it under its actual previous query state. Outside
selector/arm events get fresh event identities and their own context/cut
derivations; none is silently identified with the pending original request.
At the event-preserving delimiter cut, append the certificate and only then
evaluate the next outside query. Earlier certificates are fixed by shorter
prefixes, including when the same target was already released. Therefore no
query used to obtain the new certificate reads that certificate's own
consequence. Divergence simply has no later completed cut in the finite
prefix. This proves the ordering property of this refinement, conditional
on the supplied cut/annotation/continuity premises.

The original ordinary package gives ordered post-unwind queries and the
request-bind/forwarding behavior needed by the induction. The typed-boundary
package gives view context decomposition. Neither displays the combined
marked-delimiter transition, so a complete refinement correspondence still
needs that explicit source rule and its capture/unwind proof. Calling a final
handler-image oracle here would discard the ordering argument.

## Lifetime consequence and shortest unresolved chain

Given missing premise B, the source history yields a conditional selector:

```text
Release_s(q_now,w_now,C) iff
  there is an earlier qualifying cut certificate kappa for s and target T,
  source-proved same-target transport connects it to w_now,
  w_now has the independently required attribution to 'e,
  and the exact original receiver of kappa is active in C.
```

There is no requirement that `q_now.event = kappa.event`: the approved
lifetime explicitly permits later qualifying observations of the released
same target. There is also no license to use equal family, lineage or value
pointer as the same-target proof. A fresh receiver or independently fresh
protection slot requires its own applicable crossing. Fresh execution
occurrences from shallow raw resumption do not by themselves end or restart
the same-target release; an expired selected shallow handler stays absent.
Deep re-entry follows its actual shallow source expansion and owner identities.

The shortest remaining transport chain is:

```text
one qualifying q crosses marked target T while original receiver r is live
  -> source continuation returns latent value d
  -> result transport constructs a result view T' with matching profile/path
  -> later Force/application emits fresh q' under T', while r is still live.
```

Typed-boundary §6 derives profile/path transport and the later event's own
observation/receipt. It explicitly allows a **fresh result view** with both
actual-value and callee-result evidence. What it does not derive is whether
this particular `T'` continues the released target for the approved lifetime,
or is an independently fresh protected view. The user requires that
distinction, including no automatic copy to a fresh view. No second handler,
recursive type, duplicate event, or large graph is needed to expose this
unfinished premise. This is a shortest unresolved derivation chain, not a
claimed accepted surface-program counterexample or a proof that existing
tagged evidence cannot express the distinction.

Once the selector is supplied, the existing filter theorem applies unchanged:

```text
Protected?(q,h,C) iff exists w in raw Inc_C(q,h). not Release_s(q,w,C)
Grant?(q,h,C) = raw Grant(q,h,C)
```

All other protections remain. This keeps raw `Flow`, `Observe`, `Receive`,
`Path`, incidence and grants; origin/event/operation arguments; attachment;
the joint `nu,K,D`; and row support. Ordinary typed transport can relocate
dependent paths as before. The frame applies to the release step, not to
the later complete execution after a newly eligible handler consumes an
event. Release still performs no handler selection, capture grant or
subtraction.

## Independence, coverage, checks and stop condition

This is a source-text derivation attempt. There is no second executable
oracle, random seed, enumeration range or mutation run. The proof shares the
pinned source transition/decoration hypotheses with the proposed refinement;
it does not independently validate those source hypotheses. Chronological
cut construction rejects the named shortcuts of emission-time release,
release from final post-release image membership, and copying release from
event/family identity, but those are logical failure conditions, not reported
mutation-test results.

Covered conditionally: ordinary bind/force/adaptation propagation; consumption
versus forwarding; outside selector/arm fresh events; later latent observation;
raw repeated resumption and explicit deep re-entry with supplied owner and
same-target derivations. Omitted: a total transition-table proof for every
source fault/control form, raw-source marker elaboration, arbitrary inferred
shapes/imported clients, construction of the same-target judgment, principal
scheme ordering, finite abstraction/correlation, compiler behavior and
runtime resource bounds. The sources themselves retain raw-source elaboration
and re-entry-owner premises.

Read/check commands: `git show <pinned-revision>:<named-path>`; bounded
`sed`/`rg` section reads; `git ls-tree` for direct dependency blob IDs;
`git diff <source-snapshot> HEAD -- <four-source-paths>` and worktree
dependency diff (empty); exact-byte dependency comparison (first assertion
failed on live notation, identifying the discrepancy recorded above);
output-only newline/trailing-whitespace and new-note whitespace checks.
One requested receipt read at `28dddc75f` failed
because that commit had no receipt; the later HEAD receipt confirmed validated
integration. No incomplete search was hidden; no search was launched.

Resource budget used: zero Cargo/build/test processes, zero executable
semantic probes, zero performance samples; bounded text and Git reads only.
Initial independent read batches were concurrent, with no heavyweight
processes. Numeric CPU/RAM/wall budget was not provided in the packet; peak
memory, CPU time and total wall time were not instrumented. This finite note
is the sole output; no scratch/cache output or production writes were made.

Recommended next action: derive the explicit marked-view request-unwind rule
and same-target result/latent continuity from the source transition relation,
using the displayed four-step latent chain as the first obligation. Another
toy path/filter enumeration would leave premises A/B untouched.

## Commit packet

- Exact leased path: `notes/progress/2026-10-05-handler-release-crossing-constructive-attempt.md`.
- Baseline SHA: `e4df3c09643babd2e3ced824bf560d8f7c61440a`;
  semantic source snapshot: `659eb05646bb95f10a991bbb9cefdee55721eea1`.
- Changed dependency hashes: pinned-to-HEAD blobs unchanged for the five
  semantic dependencies; live notation differs, with both SHA-256 values
  recorded above. The artifact uses the pinned content. Recheck before integration.
- Review status: frozen conditional research; independently reviewed by
  `spec_auditor` with no conformance defect found. Source/production gate
  closure is not claimed.
- Checks already run: pinned section/dependency correspondence and blob/diff
  checks; note-only final-newline/trailing-whitespace and whitespace-diff checks.
  No compiler tests/builds or executable probe.
- Proposed commit message: `research: derive conditional outward cut for handler release`.
- Shared-record deltas left for primary/curator: update `tasks/current.md`,
  `tasks/research-lab.md`, the inference theory map and `notes/design/INDEX.md`
  with the conditional cut construction and exact remaining marker/continuity
  premises after adjudication. Do not promote the crossing gate to proved,
  reinterpret the approved lifetime, or infer production implementation
  authority from this checkpoint. No shared record or question bundle was edited.
