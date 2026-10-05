# Returned `step`: static registration and later source-call activation

Date: 2026-10-06
Status: Frozen, independently reviewed conditional research derivation; no implementation authority
Independent review: compiler_referee found no BLOCKING, major, or minor findings; source registration and production generation remain open.
Baseline: `81ceae2804d66142245384db298b8dfb3d0813a8`
Branch supplied by primary: `research/simple-sub-intrusion`
Exclusive lease: this file only
Method: forward/backward proof-obligation derivation; static inspection only

## Objective and bounded result

Derive the registration obligations for the single `f x` occurrence in:

```text
my apply f = { my step x = f x; step }
```

The approved interpretation fixes lexical resolution and retention of outer
`f`. It therefore supplies an origin chain that did not exist as an approved
premise in the earlier encoding/legacy audits. It supplies neither the
position-to-contract registration nor its typed profile. The useful reduced
obligation is preservation of a registered **captured provider relationship**
from that static origin through return and later invocation, before the
separate source-boundary/receipt premises can be used.

Claim class: bounded characterization of the inspected rule interfaces and
conditional derivation. Selected source identity/capture requirements are
established requirements of the addendum. The transport implications below
are conditional on complete typed source certificates. No source registration
rule, complete admission theorem, accepted-program counterexample,
principality result or production acceptance is established.

This lane does not prove block-to-core correspondence. It uses the addendum's
specified structure as its input and isolates the registration seam. It does
not repeat the earlier seed-eligibility/use-aggregation or information-loss
mutation attacks.

## Authority and exact dependencies

- [Nested-block addendum](../design/2026-10-06-nested-block-function-source-realization-addendum.md)
  §§1–2: exact candidate, sequential local binding, final-expression function
  result, `f`/`x` resolution and retained outer capture. §§3–4 preserve the
  independent call-view, evidence and production gates.
- Its integrated [q1/a1 approved answer](../../questions/2026-10-05-nested-block-function-source-realization/approved-answer.md)
  items 1–4 and [receipt](../../questions/2026-10-05-nested-block-function-source-realization/receipt.md).
- [Inferred Function call views](../design/2026-10-05-inferred-function-call-views.md)
  §1.1 separates internal views, written annotations and public schemes;
  §§2–5 require source position plus contract, original profile/scope, typed
  name/capture/receipt/call relations and joint `nu,K,D`, all independent of
  pending comparison `Q`. Concrete generators remain open.
- Its integrated [q1/a2 approved answer](../../questions/2026-10-05-function-call-view-formation/approved-answer.md)
  items 1–6 and [receipt](../../questions/2026-10-05-function-call-view-formation/receipt.md).
  The packet's reference to “q2 a2” was corrected by the primary to q1/a2;
  no additional decision is assumed.
- [Typed core](../design/2026-10-02-typed-computation-core-elaboration.md)
  §§2–3 supply derivation-indexed lexical descriptors and calls; §6 supplies
  conditional parameter/name/result rules, complete call obligations and
  preservation under admissible substitution; §9 distinguishes carrier,
  body and complete invocation. The document remains Draft with reviewed
  conditional constructions, not complete source inference authority.
- [Callback delivery](../design/2026-10-03-callback-context-delivery.md)
  §§2–4: supplied instantiated static profile, normative literal B,
  dynamic receiver distinct from static slot, actual supplied roles/entries.
- [Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
  §§2.1–2.2,3.1–3.4: jointly interpreted constrained roots; decorated source
  input; captured provider roots; separate initial/future-use admission;
  certified whole-tuple transport. These are conditional premises.
- The prior [source-rule inversion](2026-10-06-call-view-source-rule-derivation-attempt.md),
  registration [construction](2026-10-06-source-registration-constructive-derivation.md),
  [invariant audit](2026-10-06-source-registration-falsification.md),
  [HIR bridge](2026-10-06-source-registration-source-bridge.md),
  [encoding](2026-10-06-source-registration-existing-encoding-audit.md) and
  [legacy audit](2026-10-06-source-registration-block-value-legacy-audit.md)
  locate the missing source producer. Their historical unresolved block
  meaning is superseded for this candidate by the approved addendum.
- The [boundary-activation audit](2026-10-06-erow-hinst-boundary-activation.md)
  separates a receiving slot's activation from a later callable invocation;
  receipt consumes an established source boundary rather than creating it.

`tasks/current.md`'s source-call/registration paragraphs and the design index
were locator/status context. No live shared-record edit or another lane's
unfinished block-to-core artifact is a proof premise. Option A, production
membership Option 2, actual callable roles, annotation permission and B remain
fixed. No annotated variant is analyzed here.

## 1. What the approved source identity establishes

Use proof labels, without proposing compiler records:

```text
b_f         outer apply formal
b_step      local step binding / its closure origin l_step
b_x         step formal
u_f,u_x     names in the inner body
c           that body's application occurrence f x
u_step      final expression naming the local function
s_outer     source lexical scope containing b_f
s_inner     source lexical scope containing b_x and the captured use u_f
```

The addendum establishes, for this candidate:

```text
resolve(u_f) = b_f       resolve(u_x) = b_x
resolve(u_step) = b_step
c belongs to l_step's body
l_step retains its enclosing capture of b_f across later calls
```

These identities and scope nesting exist before any Function comparison.
They can anchor a source-registration input consisting of the original
position, its absence of annotation, relevant contract/use component and
resolved capture path. They cannot alone define `beta` or `Slots(beta)`.
Call-view §2 says **position and contract** form the slot. Choosing
`beta := b_f`, `beta := c`, or `beta := a source range` without that contract
would skip the missing producer; this note makes none of those assignments.
The exact registered typed position and profile inventory remain outputs to
derive. Their source origin must be recoverably linked to these identities.

Likewise the known lexical nesting does not determine the logical binder tree
of original `nu,K,D`. The typed generator must relate those scopes to the
source component and retain captured dependencies at their original scopes.
No local generalization or quantifier-placement policy follows merely from
the existence of a local `step` binding.

## 2. Forward source evidence at the inner occurrence

Explicit hypotheses:

H_core: the addendum's resolved structure is represented by an admitted finite
derivation with typed-core §6's ordinary parameter/name rules; actual raw
production lowering is not assumed.

H_call: application generation retains its callable, whole-argument,
typed-path and complete-invocation obligations as obligations. Generating one
does not certify a profile, owner or receiver.

H_scope: the inner environment uses the same captured source relationship for
`b_f` as the outer binding; ordinary symbolic endpoints are shared through
that relationship, rather than invented at the name occurrence. General
scheme instantiation is not proved by this hypothesis.

Under these hypotheses:

```text
outer formal:   P_apply,f = Value(A_f)
inner formal:   P_step,x  = Value(A_x)
inner lookup:   Gamma_inner(b_f) = Value(A_f)
                Gamma_inner(b_x) = Value(A_x)
n_f = result(name b_f)   n_x = result(name b_x)
Result(I_x) = Comp(empty,A_x)
c generates call(n_f,n_x) with symbolic complete result E_c,A_c
```

Here `A_f` names the captured endpoint relationship conditionally retained by
H_scope; a certified whole-interface freshening can rename it uniformly. This
is not a proof that arbitrary generalization leaves one literal variable
unchanged at every use. The call row relates the whole `Result(I_x)` to the
unknown callable interface and preserves complete invocation obligations.

The two Value entries belong to different source callable parameters:
`apply` receives `f`; `step` receives `x`. Neither determines the actual
entry of the callable denoted by captured `f`. The ordinary-value tag of
the inner `x` is available statically, including before a later activation.
`Comp(empty,A_x)` describes that rebound name's normalization, not the whole
incoming carrier to `step` or the complete invocation effect of `f`.

This exposes where approved a2's formal/use evidence must be connected to the
shared inferred interface. It does not derive a new seed-discharge rule for
nested scopes. The addendum preserves a2; the exact inference connection is
still a separate open premise.

## 3. The extra return-and-activation obligation

Distinguish source origins from dynamic events. Let `s` denote a returned
closure instance corresponding to `l_step`; `r_outer` an activation that
produced it; `r_step` a later activation of it; and `u_call` the activation
of the callable denoted by `f` at `c`, if that body point is reached. These
labels assert no representation, allocation policy or boundary placement.

The approved capture means that later evaluation of `u_f` refers to this
closure's retained outer `b_f`. Typed-core §§2–3 additionally demand typed
evidence in the descriptor relation. To use their conditional transport
result, the missing evidence must satisfy the following implication:

```text
registered original formal/provider relationship at b_f
  + closure s related to l_step and its retained outer capture
  + certified return/use transport T of that whole relationship
  + actual later invocation of this returned s
  ------------------------------------------------------------
  later body occurrence retains source origin c;
  its callee lookup corresponds to T of s's captured b_f provider;
  its argument lookup corresponds to this r_step's rebound b_x;
  original beta/profile and every dependent nu,K,D incidence
    accompany that same transported relationship.
```

This is an open proof-obligation diagram, not a selected rule. Source capture
alone supplies the lexical-reference conclusion. The typed provider,
profile/path and constraint conclusions require registration and transport
certificates. The prefix must not secretly assume those conclusions by
calling the closure “fully source-certified.”

In particular the source binder `b_f` is common static identity; it does not
by itself select the captured provider of a particular returned `s`. The
closure/environment correspondence must preserve that pairing. Nor is the
static origin of `c` a dynamic receipt. Reaching `c` under the right closure
only locates the call for which typed activation/receipt must be established.

The final expression returns `s` and does not execute `c`. A later use can
therefore be an admission case at an actually returned provider, as named by
source-contract §3.3. That case takes an original typed port and jointly
typed future context as premises. Retaining the closure does not prove that
all future arguments are admitted.

Capture retention is also insufficient to retain dynamic authority. A later
invocation may occur after `r_outer` has ended. The captured provider link
does not establish that any boundary attached to `r_outer` remains active,
or revive its owner/receiver/grant. No equality of `r_outer`, `r_step`,
`u_call` or the relevant callback-receiving owner is inferred. Establishing
the correct receiver-to-original-profile association is the boundary-activation
audit's separate producer; merely entering `u_call` does not discharge it.
This note leaves the corresponding boundary timing and owner mapping open.

## 4. Backward inversion: premises versus conclusions

For a complete view at later `c`, inversion gives the following ownership of
proof obligations. “Output” means required output of a missing source producer,
not something produced by this note.

| Fact | Available or required status | Consuming rule/limit |
| --- | --- | --- |
| Resolved `b_f,b_x,c,l_step` and lexical nesting | Approved source requirements; finite derivation representation conditional | Name and closure clauses can preserve them; no profile follows. |
| Shared role-indexed formal interface at captured `A_f` | Output of missing source registration | Callable constraints and a Name's Value tag do not construct it. |
| `beta`, `Slots(beta)`, annotation-absence protection and logical profile scope | Outputs of registration/profile generation | Callback delivery starts with these already instantiated; this candidate supplies no known contract automatically. |
| Typed capture/provider/path correspondence | Output of typed registration/elaboration; premise of closure transport | Lexical retention fixes the reference, not its typed incidence or complete provider relation. |
| Transported original joint `nu,K,D` | Generated from the source component, then premise of every admitted transport | Source contracts interpret/transport the tuple jointly; they do not generate its initial binder links. |
| Static call/argument and receipt-path schema | Output of typed call elaboration | §6 keeps complete obligations; typed Flow cannot be inferred from a lexical edge or solved Function shape. |
| Actual owner/receiver and original-profile binding | Separate source-certified activation premise | Static `beta` is not the active boundary; an unrelated active invocation is insufficient. |
| Dynamic receipt and entry/rebind facts | Outputs of invocation under established source boundaries; inputs to subsequent typed Flow/owner observations | Receipt is ownership evidence, not a slot/profile/boundary constructor. |
| Event-specific Flow/Observe/activity and grant | Later operational premises/conclusions at an actual event | Call-shape normalization supplies neither a request nor current grant. |
| Complete Q-independent admission | Independent admission producer and its preservation theorem | Known returned closure and local Value evidence supply only parts of its inputs. |

There is no conflict between saying that typed Flow is a source-generator
output and that typed-core's simulation takes Flow as input: the producer and
consumer are different proof layers. Using the consumer to construct its own
source certificate is circular. The same applies to dynamic receipt and
joint `nu,K,D`.

## 5. Exact comparison-independence obligation

The approved direction permits registration and admission to be independent
of `Q` here. Capture adds a transport requirement rather than a reason to
inspect pending comparison success. The decisive construction must begin
with this resolved component and original source constraints, construct its
formal/provider/profile relations, and relate their closure-carried evidence
to later typed invocation using independent source rules.

Conditionally, if each primitive formation, capture/return/use transport and
admission clause depends only on that source component, original jointly
scoped assignment and independently typed context, then replacing pending
`Q` while holding those inputs fixed leaves the family of formed views and
admission predicate unchanged, up to certified renaming. This is dependency
noninterference for a supplied relation; it does not require choosing one
principal view or one deterministic generator. It proves no source producer.

Omitting `Q` from a judgment's written signature is insufficient if a hidden
input was formed from `Q` success. In particular, no later comparison can
retroactively register the captured provider, choose the original profile,
authorize a receiver, invent receipt/Flow or repair joint scope. Source-local
typing obligations may still fail; Q independence is not unconditional
source acceptance.

The compared families must retain one joint relation under original scopes.
Different permitted uses can uniformly freshen that relationship; the claim
does not force all distinct closure instances or polymorphic uses to share
one literal `nu`. It forbids assembling one view from independently chosen
port or capture/receipt witnesses without their joint correspondence.

## Evidence limits, resources and precise blocker

There is no executable oracle. Governing approval texts independently fix
source meaning; typed-core and source-contract constructions share the
displayed registration/transport/admission hypotheses. The prior audits are
dependency context, not independent review of this derivation. A checker
assuming those transition rules would test consequences rather than prove
their source legitimacy.

No seed/range, enumeration, semantic mutation, runtime experiment, build,
test or formatting command was run. The only source instance analyzed is
the exact approved candidate; labels for later activations describe required
future-use premises, not an accepted executable calling harness. This is not
a repository-wide absence search. Some initial combined captures were
truncated; the decisive addendum, approvals, §6/§9 core, callback and contract
sections were subsequently read in bounded captures.

The packet permits static work only and gives no numeric CPU/RAM/wall-time
limit. Local work used lightweight reads, pinned `git show`/`rev-parse`,
hash/byte inspection and creation of this unique note. At most four
lightweight read commands overlapped; no heavyweight local process ran.
CPU time, peak RSS and elapsed wall time were not measured. No Git mutation,
compiler edit, test edit, question-board write, shared-record write or child
agent was performed. Only this leased path was written.

The earlier derivation and registration constructor both stopped at the
position/endpoint-to-contract premise. This attempt does not present another
toy probe as a solution. It isolates the additional seam made available by
the approved nested capture: the registration must export a provider-linked
typed certificate that survives return and is associated with the same
captured `b_f` at later `c`. Without that producer, the full diagram remains
conditional, and repeating the core name/application table cannot close it.

Failure conditions for a proposed proof: assuming a complete contract in
`Gamma`; declaring a lexical source label to be the whole profile; replacing
closure-instance capture/provider pairing by the common binder alone;
mistaking a retained capture for live receiver authority; using entry of
the invoked callable as proof of receipt through the receiving slot;
independently freshening dependent segments; or sourcing any of these facts
from pending `Q` success.

Unverified: raw block-to-core and production acceptance; registration/profile
sufficiency; exact typed capture/return/use transport; role seed discharge;
logical scope generation and permitted local generalization; receiver mapping
and activation timing; complete admission including production Option 2
extras; uniqueness/principality, source adequacy and implementation.

Recommended next action: formulate and independently review the narrow
Q-independent registration producer for this resolved captured formal/use
component, with an explicit conclusion linking the original contract/profile
to the closure-carried provider root. Its first proof must derive that link
from source inputs; transport and later boundary admission consume it.

## Frozen dependency snapshot

Pinned whole-file SHA-256 values follow. All live bytes matched these pinned
bytes before writing and were rechecked at freeze. No lane dependency write
occurred. Primary integration must recheck any subsequent movement.

| Dependency | SHA-256 |
| --- | --- |
| `rules/research-lab.md` | `ff641f0f929fa914a4c4297311e700824f1a4fb4a6f6e3698820f6ea3a5bbbdd` |
| `rules/design-authority.md` | `9ba8aa857587cfc392b815455dbd961d82c535444b0196f70af5ff02c3187f29` |
| `rules/git-concurrency.md` | `e148f50560d181974ab23d656af89476eb66e563194704f12d32a410f361636e` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-03-callback-context-delivery.md` | `df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5` |
| `notes/design/2026-10-05-source-contracts-and-common-allowance.md` | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `questions/2026-10-05-function-call-view-formation/receipt.md` | `6dcf408143c7eb48260d8c4df9ef73834da8d28a7f4ec9744ab381e67414cee0` |
| `questions/2026-10-05-nested-block-function-source-realization/approved-answer.md` | `04ee0dc089dc6ad19a184d31775a146c08b07f2f287099d2e5b54d7d1d5a643e` |
| `questions/2026-10-05-nested-block-function-source-realization/receipt.md` | `e5e59e176eb865a588b2843b18137571fe9c5b6f43bf1ca349bc60c9ad90f0ec` |
| `notes/progress/2026-10-06-call-view-source-rule-derivation-attempt.md` | `0009795b060e3bac47d17437f7350f0e45f0bc1eee4131706e04bd4d44624c4d` |
| `notes/progress/2026-10-06-source-registration-constructive-derivation.md` | `b4d15fd017085f0b58836be544c576d1ce94b1f869482496d1c0507eecd24bd9` |
| `notes/progress/2026-10-06-source-registration-falsification.md` | `1efe0a779c5708a7eedf047c03cdc2764c07d75328bc055cc362d6cc8f58e292` |
| `notes/progress/2026-10-06-source-registration-source-bridge.md` | `363dea86f77f7513276a6314dcf19aeba779d370f8ed28c2f94135bf483afd1c` |
| `notes/progress/2026-10-06-source-registration-existing-encoding-audit.md` | `5ea1957b97e18eb3640fb39039f1af44c2fa2730ff2db79db19cd78158f230e1` |
| `notes/progress/2026-10-06-source-registration-block-value-legacy-audit.md` | `bef24bf81b5d561538974db75c950a2df9cc2ed0b49248f2440fb0781941e436` |
| `notes/progress/2026-10-06-erow-hinst-boundary-activation.md` | `0835095409d132e86becb2ad7c8bb9e34a5ae751ffaff00688ef6f7dfbd034d6` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-nested-block-callview-registration-attempt.md`.
- Baseline SHA: `81ceae2804d66142245384db298b8dfb3d0813a8`.
- Changed dependency hashes: none during this lane; snapshot above. The
  addendum/receipt now supersede the older audits' unresolved source-meaning
  premise only for this exact candidate.
- Review status: frozen unreviewed conditional research; no independent review,
  source-gate closure, production conformance or implementation authority.
  Writing stopped before submission.
- Checks already run: pinned governing-section and prior-attempt audit;
  whole-file dependency hash/live-byte equality; exclusive-path absence check
  before creation; final leased artifact/dependency inspection. No tests,
  builds, probes or formatters.
- Proposed one-line research-checkpoint commit message:
  `research: isolate captured call-view registration obligations`.
- Shared-record deltas intentionally left for primary/curator: distinguish the
  approved source origin/capture from the missing contract/profile producer;
  record closure-carried provider/evidence preservation as its required
  conclusion; retain separate activation/receipt and complete admission gates.
  Link this note without closing registration or inference replacement. No
  task/index/theory/authority/question-board file was changed by this worker.
