# Source bridge for protection release: exact local obstruction

Date: 2026-10-05
Status: unreviewed source-artifact audit and conditional derivation; no semantic selection or implementation authority
Baseline: `dfd49d1b14a9aba922bb0278ca7c1bfac8061058`
Scope: one supplied typed callback boundary and one marked output slot; independent of API and production Function-inlet work
Method: constructive correspondence with the existing profile, transport, observation, and visibility judgments

## Result and authority

The corrected local meaning of `'e?` is fixed: stop the slot's handler
protection for qualifying, already `'e`-attributed contributions leaving that
slot, while retaining their provenance. The frozen
[notation draft](../design/2026-10-05-handler-hygiene-public-provenance-notation.md#small-step--relational-interpretation-candidate)
records this decision; its broader elaboration and lifetime rules are open.
The working-tree edits to that draft were not used in this audit.

The existing source artifacts derive the incidence and concrete grant at a
supplied input profile, and the existing conditional filter derives subsequent
eligibility once a source release witness is supplied. They do **not** derive
that witness from the marked output annotation. The missing bridge is narrower
than a new effect carrier: a source judgment must associate the original
annotation occurrence with the qualifying contribution's protective witness,
and identify the source transition and downstream lifetime at which that
witness stops protecting it. Existing `Observe` or a typed `Flow` crossing
alone does not supply this judgment.

This audit adds two reductions to the previous conditional-filter result:
release cannot be an instance of unchanged persistent transport at a live,
grant-free incidence; and observing an event at an enclosing output port does
not prove that an event left that slot. These are obstructions to proposed
derivations from the displayed rules, not source-program counterexamples or
proof that existing evidence cannot support a computed release query.

## Exact source correspondence

| Needed object or judgment | Frozen source | Derivable fact and remaining limit |
|---|---|---|
| Static callback slot `β`, `Slots(β)`, complete instantiated `F_cb` | [Callback-context §2](../design/2026-10-03-callback-context-delivery.md#2-bounded-source-judgment), §3 | The original slot/profile precedes literal-body generation; this does not define output-marker attribution. |
| Dynamic boundary `b=(r,a,Γ,endpoints)` and positions | [Typed-boundary §6 introduction](../design/2026-10-02-typed-boundary-realization-draft.md#views-signature-positions-and-introductions) | `Γ` marks protection and concrete contracts at declared positions. Source elaboration supplies it; no displayed rule elaborates `?`. |
| Tagged profile and dependency transport | [Typed-boundary §6 transport](../design/2026-10-02-typed-boundary-realization-draft.md#one-relational-transport-operation) | `χ'=M_*χ`, `D'=M_*D`, shared `K` and inherited `L` under one `ν`; original source witnesses remain. |
| Request-to-view exposure | [Typed-boundary §4 observation](../design/2026-10-02-typed-boundary-realization-draft.md#structural-observation-before-dispatch-theorem-candidate) | `Observe(q,o.view,o.port,o)` comes from the emission context before dispatch and outward filtering. |
| Candidate incidence and protection | [Typed-boundary §6 receiving/observation](../design/2026-10-02-typed-boundary-realization-draft.md#receiving-ownership-and-observation) | `Path` joins profile, typed `Flow`, event `Observe`, and matching `Receive`; `Inc_C` adds exact current activity. Every displayed incidence is protective. |
| Input concrete grant | [Concrete-profile derivation](2026-10-05-concrete-capture-profile-derivation.md#conditional-concrete-item-corollary), [ordinary semantics §4](../design/2026-10-02-ordinary-computation-semantics-package.md#4-callback-boundaries-and-candidate-visibility) | Given the supplied explicit `Γ_b(p)` contract, compatibility, incidence and activity derive receiver-local eligibility. This neither releases protection nor subtracts support. |
| Protection-only output query | [Existing conditional filter](2026-10-05-handler-protection-filter-derivation.md#conditional-derivation) | A supplied release selector over full derivation witnesses changes only `Protected`; raw incidence and grants remain. Its source premise is not proved. |
| Mixed-row invariants | [Approved answer](../../questions/2026-10-05-function-effect-row-denotation/approved-answer.md#決定案と範囲), clause 6 | Role and typed ports precede interpretation at the same `(ν,K,D)`, retaining occurrence, path and attachment. The targeted deep-handler subtraction clause is separate from release. |

The reviewed Draft source packages remain conditional source candidates.
The Authoritative expected-context contract supplies order and original slot
identity, not the missing suffix semantics. No legacy `pop` count follows.

## Reduction 1: persistent transport cannot discharge a live witness

Choose the smallest supplied instance of typed-boundary §6:

```text
χ(p,b)
Flow along identity to p of the received executing view v
Receive(u,slot,v,identity)
Observe(q,v,p)
owner(h)=u; h, u and b.receiver are active in C
Covers(h,q.operation)
no Γ-profile in this instance explicitly admits q.operation
```

There is one boundary profile, one view, one event, one candidate and one
protective route. The source boundary is omitted/wildcard for capture, so
its protection is present without a concrete grant. All endpoints, predicates
and dependencies are interpreted under one fixed `ν,K,D`.

Unfolding the displayed definitions gives:

```text
Path(q,u,b,p) = true
Inc_C(q,h,b,p) = true
Protected(q,h,C) = true
Grant(q,h,C) = false
Visible(q,h,C) = false
```

Now additionally supply the corrected notation's premises: this contribution
is attributed to `'e`, it leaves marked slot `s`, and the sole protective
witness is exactly the protection associated with `s`. These are conditional
inputs, not consequences established by the above instance. A faithful
protection-only release must make the protective query false for that witness,
making this covering active candidate eligible under ordinary search.

Applying only §6's identity transport cannot do that: `Id_*χ=χ`, `Path`
still has the same witness, and all activity premises remain true. Thus the
displayed `Protected` equation remains true. Merely recording the marker as
an annotation occurrence adds no protective discharge to any displayed rule.
The same argument applies to any typed composite retaining this route and
the same receiving/observing witnesses.

This is a non-derivability result **for unchanged transport and visibility
equations**, not a contradiction in the corrected meaning. It does not assert
that a particular release annotation erases to the same actual production
descriptor: no such elaboration is defined in the inspected sources.

Receiver/handler expiry already clears the incidence, but expiry is not a
general implementation of the marker while those exact activations live.
Adding a concrete grant makes the candidate eligible even without release;
that case cannot distinguish a working release bridge from sticky protection.
Consequently, the existing `['e, foo]` concrete-contract corollary provides no
proof of `'e?`: its successful grant can mask the missing discharge.

## Reduction 2: output observation is not a leaving transition

Typed-boundary §4 deliberately computes `Observe` before handler filtering.
Consider the supplied decorated context:

```text
View(v,s, Handle(h_internal, Request(q)))
```

At emission, the enclosing output computation position `s` contributes an
`Observe(q,v,s)` witness. If ordinary selection by `h_internal` consumes the
event and its arm returns without re-emitting it, the complete outward handler
image need not contain `q`. The draft explicitly permits this difference
between emission-context observation and outward support. The example is a
decorated-kernel shape; it claims no accepted surface program or annotation.

It follows that the implication

```text
Observe(q,v,s) => q has left output slot s
```

is not supplied by that theorem. A `Flow` path to the observed position cannot
repair this: `Flow` is value/dependency correspondence, whereas leaving a
computation slot requires a source computation/control judgment. In particular,
the same request may be observed by several enclosing views before the first
candidate is tested. An algorithm that uses those observations must not
silently identify all enclosing outputs with already completed release steps.

This does not select release before or after internal selection. Nor does it
define "leaving" as outward support membership: doing so would inherit the
handler-image dependency and could be circular if release affects eligibility.
The source rule must fix the transition order. The current observation theorem
cannot determine it for the suffix.

## Exact conditional bridge, without semantic selection

Let `w` be the **full existing** profile/typed-flow/observation/receipt
derivation witness for an active incidence. The narrow bridge obligation is:

```text
original marked annotation occurrence (s,'e)
  + qualifying existing contribution attribution
  + source computation/control step at this typed slot
  + exact protective witness w and its continuation/result scope
    => protection of w has ended at the actual candidate query
```

This is an obligation schema, not a new judgment approved for the language.
Its source proof must establish which witness belongs to this slot and when
the consequence holds; it cannot use family equality, event lineage alone,
or the mere existence of an `Observe`/route-crossing witness as that proof.
It must distinguish sibling aliases and independent protections retained in
the existing tagged evidence graph. It selects neither one-pop nor
all-protections behavior.

**Conditional consequence.** If that source obligation supplies the existing
filter note's selector `Release_s(q,w,C)`, then its theorem applies unchanged:

```text
Protected?(q,h,C) iff exists w in Inc_C(q,h). not Release_s(q,w,C)
Grant?(q,h,C) = Grant(q,h,C)
Visible? uses the ordinary Visible equation with Protected? and raw Grant
```

The derivation changes no raw `χ`, `Flow`, `Observe`, `Receive`, `Path`,
`Inc_C`, event identity, family/type arguments, source component, attachment,
or inherited lineage. `ν`, predicate identity in `K`, and every `D` incidence
remain in the same joint relation; ordinary path relocation still uses `M_*D`
where the source step actually transports a value. Release adds no equation
identifying separate endpoint variables and removes no predicate.

Unreleased witnesses continue to protect. A raw receiver-local concrete grant
can still discharge independent inherited protection, as before. If no
protective witness remains, ordinary ordered search tests active covering
handlers. Actual selection, `OpCompat`, raw continuation behavior, and support
subtraction remain governed by their separate source rules. The frame is a
local release frame, not equality of complete program behavior after a handler
subsequently consumes a newly eligible event.

For a returned latent view, existing result-path transport and the later
view's own observation establish raw incidence. They do not decide whether
the earlier marker has already ended its protection for that later event.
The bridge obligation therefore must cover that scope explicitly. Repeated
resumption similarly preserves the stored typed packet but creates fresh
execution occurrences/events; shared lineage is not evidence that release
has already occurred for them. No new ledger or carrier is justified here.

## Freeze, checks, and next action

Frozen semantic inputs were read with `git show dfd49d1b1:<path>`. Their Git
blob IDs are:

| Dependency | Blob |
|---|---|
| Notation draft | `92923b4dbb0993c3dbed0093c4df3b020d982562` |
| Concrete-profile derivation | `8b23a4f3349d4048748b16ecdc7beb11c84551db` |
| Typed-boundary Draft | `5e0499e43b3dbf04de0bcdb6c0fa5994224d8a87` |
| Ordinary-computation package | `640bbfa85630d1dd496a3fd1ccb757536385d720` |
| Existing conditional filter | `9663da0c8928a0a567bd8c2a7dbd6e450ebe2853` |
| Callback-context contract | `eeed5c2b5dd38404a4c774cda486864a63992fad` |
| Approved mixed-row answer | `77e28d7826634421a98e556a0023b29c762420ad` |

Verification budget: output-only whitespace check. No builds, tests, executable
probes or performance measurements; no independent review claimed.
No production/source/design/test file was changed. No pending question or
uncommitted handler artifact was consumed as authority.

Checks: the new-file `git diff --no-index --check /dev/null <this-note>`
reported no whitespace diagnostics (exit 1 for the added-file difference);
an output-only Python assertion of final newline and absence of trailing
whitespace passed. These checks inspect the note, not compiler behavior.

Next action: independently audit the two reductions, then derive or select the
single source crossing/lifetime judgment with retained annotation occurrences
and full protective witnesses. A larger path-query enumeration would not
resolve this premise. General elaboration, syntax, principal scheme ordering,
and complete source safety remain open.

Commit packet: only this note; proposed message `research: isolate source judgment for handler protection release`.
Shared `tasks/current.md`, theory maps and design index synchronization is
deferred to the primary; this note does not declare their gate complete.
