# R181 — ordered scoped composition and actual contextual consumers

Revision 1. Author `/root/r177_source_consumer_proof`; assignment
`R181-CONTEXTUAL-CUT-CONSUMER`. Outcome: **candidate scoped algebra and actual
nonidentity-filter obligation conservation; same-source/use semantic consumer
bridge still OPEN**. No source-qualified counterexample or self-certification.
All original parent, A/B, source/native, implementation and production gates
remain OPEN. Luna activated the exact packet after CLEAN prospective review.

Contract SHA-256 `b61d1cc8b0efbd480dd964e52f4fd7e083d1ab9a973d7b1ed91af4956ecf3577`;
issued proof packet SHA-256
`ccfd7cc53109138eaa5beac203de897ebc55f88d28c895477eb63493fc529b9e`.
Initial observed current.json SHA-256
`a75f5a8ba62b829da0c185352c4ef41b26e145acd2c5ef1814ce94d632361e4a`.
Its exact active contract/packet and RUNNING identity matched activation.
Central runtime records belong to Luna; this writer did not change them.

## 1. Parent claim, application and full-scope boundary

Unchanged parent: `notes/theory/2026-10-15-computation-forwarding-preservation.md`,
SHA-256 `d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79`.
Preserve shared xi, original source/formal/provider identities, open incoming E,
arbitrary finite forwarding chains and prefixes, repeated/simultaneous entries,
independent ancestor protections, pending computations, raw repeated resumption,
guards/value arms, alternatives, residual/scoped payloads, canonical/current/
reused pairs and valid rollback. F1/FK1 remain independent. The original domain
is unchanged; the local cases below do not redefine the parent theorem.

R180 supplied physical materialization for identity/default row cuts, conditional
on authentic input incidence and Capture/consumer joins. R181 removes one
specific algebraic uncertainty: the pinned ScopeTransformer really composes
lower then upper on every finite tag/protection state, with release tombstones
and independent protections handled exactly (§2). The actual Replay constructor
uses that very composition (§3). The nonidentity ContextExpr executor really
installs the corresponding allowance-check obligations and preserves its exact
remaining residual and scoped payload (§4). It does not simply drop a nonidentity
context at memoization.

Immediate application to R180: a successful, stable-representation row cut may
carry a nondefault scoped transformer and a supported zero-word filter context.
Its actual row insertion carries the post-check context, same source set and
same scoped flow, alongside the filter obligations it installed. This extends
the operational representation result; it is not semantic satisfaction merely
because the relation is discharged. At an actually quiescent all-local Capture
boundary, with the independent authentic same-instance input/consumer premises,
this physical representation can be used in R180's application of finite cut
compression. It preserves the underlying real row path and its decorations.
Thus it supports the parent's instance-relative native implication only when
those mapped admissions and exact provider/Apply links are separately proved.
No transformer may be erased to claim a stronger source theorem.

For the original parent's §6, separate authentic maps mu_i and forwarding
Apply joins are still required for every actual provider. For §3/§7, static
scope/input IDs are not runtime receiver identities or execution receipts.
No source entry/read/Force/Observe, request eligibility, grant or dynamic
protection correspondence follows from the algebra alone.

**First remaining full-scope premise:** BOTH ordered fibers must originate
from the required original source cut and reach its same provider/use consumer.
Even granting that input premise for a local construction, the new consumer
boundary is exact: the carried ScopedFlow has a correct algebra, but no admitted
correspondence makes its tag/protection state plus pending/check/conflict state
into semantic satisfaction at that original source/use. The actual checker and
read-only observer consume different objects (§5). This is an unproved bridge,
not evidence of an inference bug or a request to change checker semantics.

## 2. Source-derived transformer law

All lines in this section refer to the exact pinned candidate_scope.rs under
`/tmp/r181-inputs/candidate-a8f7c4d74/`. Its header explicitly calls this a
private candidate without adopted source semantics. ScopeTransformer changes
route tags/protection scopes, not effect members or capture grants (:1–4).

Represent a transformer T by its canonical stamped set S_T and, for each scope
s, a keep bit k_T(s) and finite missing-tag set A_T(s). An omitted entry means
k=true, A=empty. For initial finite input/protection sets (I,P), evaluation is

```text
I_T = I union S_T
s in P_T  iff  (k_T(s) and s in P) or (exists a in A_T(s): a notin I).
```

This follows directly from Missing::holds (:85–94), sorted_copy/union (:53–83)
and evaluate (:180–209); duplicate/unsorted arguments are normalized. Private
constructors and merges preserve sorted, distinct finite supports. Consider T
then U. Substituting T's output into U gives

```text
S = S_T union S_U
k(s) = k_U(s) and k_T(s)
A(s) = (if k_U(s) then A_T(s) else empty) union (A_U(s) minus S_T).
```

Indeed a second missing predicate is true at I union S_T precisely when one
of its tags lies outside BOTH I and S_T. A second release kills the first
inherited bit and all first additions. Those equations are exactly
ScopeTransformer::then (:131–175): first_add is filtered by keep_second,
second_tags are filtered against self.stamped, and the canonical unions are
retained. Tombstones with keep=false survive even if A is empty (:169–170).
Therefore, whenever the fallible constructions succeed,

```text
evaluate(T.then(U), I, P) = evaluate(U, evaluate(T, I, P))
```

for EVERY finite I,P. This is an extensional law, not a test of invented
transitions. It yields identity and associativity of evaluated behavior for
arbitrary finite compositions; no fixed chain or initial-empty-state bound.

Concrete consequences from the actual constructors (:102–128): stamp_i adds
only i; protect_(s,i) preserves all existing P and adds s iff i was absent;
release_s removes only s and preserves every other protection. Thus
stamp_i then protect_(s,i) adds no new s, while protect_(s,i) then stamp_i may
add s. An independently retained protection on s is preserved by protect even
when i is present; any other protection survives release_s. These facts must
not be restated as permissions, handlers, receiver expiration or F1/FK1 closure.

Remap (:212–265) calls each closure once per distinct supported ID, preserves
keep bits, renames stamps/predicates, and rejects support collisions. Evaluation
commutes with an injective renaming on the UNION of transformer and state
supports, provided that same renaming is used on the state. This condition is
necessary: injection only among transform IDs does not rule out collision with
a foreign state ID. FreshUse calls these actual remaps (scheme:1851–1875), but
fresh regional allocation is delegated to candidate_source::ScopeInventory::fresh
(:1633–1639), outside the eight source pairs and not read. Therefore universal
freshness against foreign states is not inferred from remap's local check.

## 3. Actual ordered Replay, transport and uses

candidate_context::compose_scopes (:2780–2788) calls the exact then function,
with identity ID 0 handled on either side. Actual candidate_context_begin_replay
(:3854–3939) selects BOTH attached fiber lists at the exact lower_input and
upper_input BoundKeys. It enumerates the disjoint new-lower/all-upper plus
old-lower/new-upper product; incoming_use resets the old heads and enumerates
the full product. Each child retains BOTH ordered relations and BOTH keys.
At :3899–3911 it constructs ContextExpr::Replay(lower_context,upper_context),
unions source sets, rejects a lower deferred demand, and calls

```text
compose_scopes(lower_scoped.transformer, upper_scoped.transformer)
```

while preserving upper_scoped.demand. Hence the actual stored child's scoped
meaning is the lower-then-upper law above. Scope order is not reversed because
a Function field is contravariant: FunctionPortOperation::Swap separately
transforms the ContextExpr inheritance (:3481–3491). Conflating that swap with
reversal of then would be wrong.

The owned ReplayOperation, exact child/current/queue transfers and return/ack
barriers are the real constructors covered by R180, not a harness callback.
Its result is reused within valid successful-history premises. Ordinary recipe
dedup conserves a prior actual operation/materialization history; incoming-use
replay retains its own operation. A recipe alone remains insufficient. Scope
IDs and shared relation interning do not independently allocate a new use.

Canonical task transport (:3629–3646) checks actual canonical task pairs,
retains scoped flow/source set and uses post_check_context. Canonical bound
transport (:4092–4113) creates exact witness transport and attaches the canonical
fiber before Replay. transported_scoped (:2826–2837) changes a deferred demand
root only when the actual witness rewrites it; its transformer is preserved.
FreshUse (:4140–4153) requires the caller's remapped scoped flow when enabled,
retains the explicit use_origin and both witness keys, and attaches that child.
These are actual retention laws. None proves that equal endpoints authenticate
original source ownership or that any scope/input ID is a runtime receiver.

A nonzero scoped self-relation is explicitly rejected at relation construction
(:3021–3030) and execution (:3670–3672), rather than silently treated as a
reflexive constraint. This is an exact bounded-experiment deferral. No original
source instance requiring that case was established, so it is not a source
counterexample.

## 4. Actual nonidentity filters and retained residual obligations

There are TWO distinct channels: ContextExpr's executable receiver filters and
ScopedFlow's scope/input transformer. Both are retained by relation keys. The
following supported nonidentity route is an actual constructor proof, conditional
on its actual fiber inputs and valid successful history, not a claim that every
original source cut supplies them.

Take exact attached lower/upper fibers whose nonidentity contexts are valid
zero-word PrefixLeft weights or their accepted Replay filter fragments. The
actual Replay child has those ordered contexts. Transport/Context stages run
BEFORE Dispatch/current-pair memoization (lib:12427–12445,12507–12521).
candidate_zero_word_filters (:3531–3627) validates owner, position, closed_weight,
empty words and acyclic child IDs for the complete fragment before publishing
any checks. It retains every distinct filter weight. Duplicate weight IDs are
deduplicated, not unrelated equal-looking source occurrences.

A pure Replay of such filters produces residual IDENTITY. Supported outer
prefixes with payload-free Swap/WithoutLeftFilter spines preserve their exact
directed residual. Buried filters inside directed spines and a mix of Replay
filters with directed residuals are rejected (:3562–3612). No law for those
rejected contexts is invented; no actual source reachability is established.

The consumer callback (:3688–3748) temporarily retains checking_filters=(r,W)
through synchronous callbacks and restores its previous scope on success/error
(:3614–3619). For EACH filter, using the actual task's lower operand:

- An existing exact row->Allowance(view) upper is reattached with this occurrence's
  bound origin and Replay is driven (:3708–3731).
- Otherwise candidate_apply_effect installs that exact row bound or checks the
  actual operand (:3732–3733; extrusion:946–969).
- checked_boundary in candidate_context_bound_for (:3766–3797) matches this exact
  processing parent, lower owner and weight's view. Only that allowance bound
  gets identity context; the Derived edge still points to the complete parent.
  Its scoped payload remains the actual Effect flow (:3002–3018).

Only after all these constructor calls return does the executor publish
r in discharged and its exact nonidentity residual, if any (:3736–3746).
post_check_context (:3255–3259) returns that residual thereafter. If the original
upper is one of those same allowance views, consumed_endpoint is true;
otherwise ordinary Dispatch continues. For a nonreflexive row-to-row child,
physical insertion then retains its post-check context, unchanged scoped flow
and same source set through bound_scoped_payload_for/attach. The physical append
is the actual candidate insertion, not lib.rs's legacy mirrored rows.

This yields a local conservation fact: each processed nonidentity filter child
is represented by its installed exact allowance obligations AND any remaining
row/residual relation; current-pair reuse cannot skip the initial Context stage.
A repeated discharged relation reuses those exact installed obligations, under
the same valid-history/unchanged-representation conditions. Generation changes
and canonical transport still require their actual witness/history, not a
marker-based semantic argument. R180's physical row argument extends to this
post-check decorated row because same-kind bound payload retains the exact
ScopedFlow; its fiber may be r_post rather than r. No equality of those relation
IDs or original-source meanings is inferred.

### Discharged and Ok are not semantic satisfaction

candidate_check_effect_operand (:1183–1250) makes this distinction concrete:
Support(view) enqueues AnnotationMember checks and possibly a tail task, then
returns Ok. A Contribution/AnnotationMember at an Allowance tests its actual
member against allowed or forwards to its tail; mismatch records Conflict and
returns Ok if recording succeeds (:722–775). Therefore a successful filter
constructor may mean a physical future check is installed, pending member work
is owned, or a diagnostic conflict is retained. A discharged relation does not
prove that those checks all passed or all descendants returned.

The operation/current/FunctionDispatch pending/worklist/settle/return owners
must retain this future work until real completion. R180's ownership argument
supplies the local transport discipline, not a general Capture-compatible
continuation. Scope observation is recorded BEFORE those checks (:3674–3685),
so even an exposed observation is not a completion receipt. Neither an empty
filter list nor a current memo marker supplies a missing semantic proof.

Rollback of a VALID checkpoint removes newly discharged/residual entries,
restores contexts, relations, fibers, frontier heads, current frames and actual
Replay owners (context:2049–2147), together with physical row/queue undo under
R180's stated journal premises. Rolled-back checks cannot justify a surviving
use. Scope transformers/flows are immutable interned objects; retention of
unused intern IDs is not a surviving source/check obligation and does not prove
full state/resource rollback. Failed private attempts must be discarded or
validly recovered; no general retry/unwind theorem is claimed.

## 5. Exact Apply/AE/RE/allowance seam and remaining constructor

shadow_apply::admit_candidate_fact (:2631–2752) checks the registered recipe's
actual source-input index, occurrence and endpoints. Scoped source authenticity
is delegated to candidate_call::authenticate_scoped_apply (:2640–2643), outside
this lease and not read. It constructs the actual negative Function demand with
argument effect and fresh invocation RE, retains NativeInterface, and constrains
callee<=demand. Slot 2 then admits invocationRE<=applicationEffect
(:2774–2820). DirectionalIntroduction is explicitly retained before admission
and has no semantic consumer (:2705–2722).

When that actual Function comparison is freshly dispatched, lib:12680–12729
constructs the four actual fields. FunctionDispatch retains each pending item,
admits its relation, then enqueues it (:12835–12858). The AE/RE field pairs
are the actual contravariant/covariant endpoints (:12688–12700). The exact parent
relation owns them. candidate_function_port_admit (:3462–3526) validates a deferred
demand's negative Function root, consumes that demand, and generates AE stamp_i
or RE protect_(s,i), retaining a FunctionPort edge. Thus these fields are real
producer records, not merely hypothetical transformer values. Current Function
reuse still needs the inherited field obligation; four retained edges alone
are not four executed/discharged fields.

The pinned map-backed authenticator (scheme:475–635; context:2875–2982) checks
one exact retained FreshUse snapshot/emission/readback, both Replay inputs,
mapped four ports, use and scope/input maps. It supports the explicit zero-step
p1=h and q=C cases and rejects rewritten consumer spines without a separate
producer edge. It requires the Value Replay parent's transformers to be zero;
its generated AE/RE transformers are checked by constructor equality. It does
not authenticate arbitrary nonidentity Effect cuts or their later check return.
It is called by read-only shadow observations (:858–918), not by a replacement
semantic discharge algorithm.

The actual scoped evaluator is context:evaluate_observation (:2820–2824), which
calls evaluate with EMPTY initial sets; shadow:scoped_observations (:822–829)
exposes that result read-only. The actual operand/allowance checker consumes
allowed members and tails, not this evaluated ScopeState. Therefore the first
new missing law, even after local source/use authentication, is:

```text
actual source-qualified ordered fibers / same use
 + retained ContextExpr checks/residual / ScopedFlow transformer
 + actual matching FunctionPort or allowance continuation and its outcome
 -> the source-required transformed obligation at that SAME provider/use.
```

An observer state, a checked root/map, installed allowance, discharged flag or
Ok cannot replace the last premise. A semantic correspondence proof might use
the existing checker; this note neither prescribes adding transformer gating
nor claims that its absence is an inference error. Native bound admission and
the dynamic received-view bridge remain distinct. ScopeInventory regional
freshness, candidate_call source authentication and general source caller
Capture timing are exact outside-owner dependencies if needed next, and were
not read. No lease expansion is requested or made here.

Minimal return to Luna: **R181-SAME-USE-CONSUMER-LAW**, with falsifier a foreign
or sibling source/use accepted as the obligation's consumer; **R181-CHECK-RETURN**,
with falsifier a Support enqueue/discharged/Conflict/Ok record substituted for
actual retained pending ownership or compatible return; **R181-RENAME-DOMAIN**,
with falsifier local support injection silently colliding with an independent
foreign state. These are proof prerequisites, not an approved production TODO.
For Capture, a mapped retained row alone cannot transport a live check/drain;
prove actual quiescence or its exact compatible continuation as already OPEN
in R180. No source-qualified violating instance was constructed.

## 6. Evidence, omissions, resources and stop

Reused only R180's CLEAN unfinished-research proof/mapping within its premises,
and the unchanged parent's source theorem/native conditional implication.
Rejected: reversing then because of Function variance, dropping tombstones,
turning scope IDs into permissions/receiver IDs, recipe-only completion,
endpoint-only consumer identity, discharged/Ok as semantic satisfaction,
ordinary source narrowing and inherited FunctionPorts as automatically executed.
New evidence is constructor algebra plus actual executor/consumer mapping;
it is not independently reviewed theorem or production authority.

Resource hypotheses remain separately OPEN: successful checked arithmetic and
allocation/capacity, shared allocator accounting, Arc/refcount behavior, and
rollback/publication/error/unwind. Fallible algebra equality is conditional on
both constructions succeeding. No resource erasure or complete rollback follows
from extensional equality or immutable intern retention.

Requested gpt-6.1-sol/high; exact observed model/effort UNKNOWN. Actual identity
/root/r177_source_consumer_proof; session current-conversation-2026-10-21-r181.
First observed clock 2026-10-20 19:12:32 UTC; pre-freeze observation
2026-10-20 19:16:17 UTC. Trusted launch/full elapsed UNKNOWN. Charge full grant
1380s; returned 0, remaining 0, no carryover; Astra/probes/descendants 0.
Final clock and both artifact hashes appear in the frozen handoff/external STOP
receipt. Luna owns runtime reconciliation and fresh independent review.

Entry and exit checks: all sixteen exact source hashes, files 0444, four roots
0555, exact contract/original packet and five dependency hashes. Targeted
semantic reads used only these eight candidate owners and pinned proof evidence;
no mutable compiler source substituted. Baselines supplied hash/mode evidence.
No tests/builds/probes, compiler/evaluator/Yulang2 execution, network, nested CLI,
Git, code edits, scratch outputs or descendants. Only new/changed paths are
this note and tasks/agent-loop/inbox/20261021-r181-proof.md.

Authors: this worker for R180/R181 proof note/handoff; Luna for contracts,
snapshot allocation and frozen R180 mapping. Earlier authors remain as recorded
in those exact dependencies; compiler authors UNKNOWN. This author appoints no
reviewer and does not independently certify the combined result.

The scoped result and exact missing same-source/use consumer law are the stop
condition. No further in-envelope source owner or semantic change is authorized.
After final hashing: **FROZEN; writer STOPPED**. No background work, descendant,
pending child lease or RUNNING claim while awaiting Luna's next assignment.

### Frozen source manifest

Six pairs plus shadow_apply.rs use baseline root
`/tmp/r178-inputs/baseline-7ec64a378/` and candidate root
`/tmp/r178-inputs/candidate-e9a7a4f/`. candidate_scope.rs alone uses
`/tmp/r181-inputs/baseline-a8f7c4d74/` and
`/tmp/r181-inputs/candidate-a8f7c4d74/`. All roots/files 0555/0444.

| Owner | Baseline SHA-256 | Candidate SHA-256 |
| --- | --- | --- |
| candidate_context.rs | d884c20a98140da2a737d65f61faa97491bd9a2af7870bf3f0ea7dd428e9ffeb | a08ff10637f1ff9a67005f96c5e1bc26a44778f911944054a25cf28bec5ce733 |
| candidate_effect.rs | c1d7ce19ef5192a46d605faabae34e4437b1f1a15819b5657ec1d70eda7900d1 | c1d7ce19ef5192a46d605faabae34e4437b1f1a15819b5657ec1d70eda7900d1 |
| candidate_extrusion.rs | 7c9a46d327a5e2e3f9e6f8d79f36f11fe21b4a3f68426526e85424a39e2c6332 | 7c9a46d327a5e2e3f9e6f8d79f36f11fe21b4a3f68426526e85424a39e2c6332 |
| candidate_intrusion.rs | 475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97 | 475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97 |
| candidate_scheme.rs | 9569e7cc2ba7152cafe1273fba279a8511fe56aa39358798f3e4586c10ede225 | 48094aff85175ef7b30d1ef8be0e8fc42d6e5282d0c4d562c4a730c13d401b25 |
| lib.rs | c75bf47b3d0d87e99d4365a587e6b90d5d05d05c335db16880cb2943b8b25985 | 24f480355979ee5d96305a08abf6aab67025ede32c2a1575b779e46f5e23b436 |
| candidate_scope.rs | 9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a | 9fdb36b4bbd66d702fbd3fcfaf593bfbc5dce0c52ff3252442aeb998bbb52c2a |
| shadow_apply.rs | 13ae8de60293b91e24659090649ff84002f5632a8909451d3f7bd8492b61bea5 | 2b0e46f28c328172477ac263360f4f3d01d27714dc62cd93235b8e3b1fe4e9ff |

Frozen other direct dependencies:

```text
d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79  notes/theory/2026-10-15-computation-forwarding-preservation.md
cb2fff33a1ab983a932064cc1699d9f4f4a8d5e00d52986525884d42bc58234f  tools/inference-playground/examples/r171-formal-name-forwarding.yu
90e942502581473459db8e23f3b469b01fc536b1919dde09c03a233e190a42d0  notes/theory/2026-10-21-r180-ordered-cut-preservation.md
9580572fb95ef81dfc6ef61b632a5920187e9fed3f459fa9c91b12db9cf7ef56  tasks/agent-loop/inbox/20261021-r180-proof.md
7c4b10b16084fc800270e1ebef12b90a6b877c169edcadf1ccdd095661bf483e  tasks/agent-loop/inbox/20261021-r180-implementation.md
```
