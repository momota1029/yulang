# Receiver-relative forwarding and protection exit

Date: 2026-10-15
Status: research-only application of reviewed decorated-source theorems;
bounded native source correspondence and remaining constructor obstruction.
Independent compiler-referee review found no BLOCKING or major findings;
original source/runtime hygiene parent OPEN.
Baseline N: `af3ed318b4c022e6baa211134ef89d0f3810eecb`.
Exclusive lease: this new note only; no compiler or shared-record changes.

## 1. Frozen claim, decisions and hypotheses

The latest direct user statement is:

> 保護の解除というのも全部解除するんじゃなくて引数として取り入れた場合関数内のハンドラ的関数から保護し，そこから出たら保護しなくなるみたいな話なんですよね．ここらへんの健全性って結構大変だと思います．質問があればどうぞ

The primary's bounded interpretation is: when an effect passes outward beyond
a receiving boundary, that receiver's protection must not prevent outside
handling. This need not destroy stored witnesses or wait for normal return or
receiver inactivity. Existing ordinary forwarding, concrete annotation
permission and compose e-release decisions remain binding. Release preserves
effect membership and independent protections; permission does not handle.

Original quantifiers: every supported accepted source computation, all original
argument/formal/handler binders, actual providers and complete Call witnesses,
normal and abrupt paths, latent results and admissible resumptions, under one
shared scoped assignment `xi=(nu,K,D)`. Preserve source effects, provider and
attachment correlation, residual lineage, soundness and natural inference.
No bounded fragment below replaces this parent or proves its full conclusion.

For the local steps fix at least two distinct receiver occurrences r,s and
their authentic boundary instances b_r,b_s, original slots and typed profiles.
Fix a full existing contribution witness w and event q, not independently
selected endpoint marginals. The decorated-source hypotheses are precisely
those of [typed boundary](../design/2026-10-02-typed-boundary-realization-draft.md)
§§4,6 and [source owner](../design/2026-10-02-typed-source-owner-realization.md)
§§1–4: supplied original profile positions, typed correspondences, executable
view decorations, receipts and actual owner/control derivations. The results
below apply those reviewed theorems; they do not derive those inputs from N.

Authority also includes [charter](../design/2026-09-29-scc-intrusion-redesign-charter.md)
§§13–18; [Call contributions](../design/2026-10-07-complete-call-contribution-definition.md)
§2; [source scheduling](../design/2026-10-02-source-call-scheduling-choice.md)
§§1–2; [ordinary forwarding](../design/2026-10-15-callback-identity-forwarding.md);
and [compose release](../design/2026-10-15-compose-scoped-effect-release.md).
Reuse the [protection-filter derivation](../progress/2026-10-05-handler-protection-filter-derivation.md)
and [capture theorem](2026-10-15-effect-scope-ownership-capture.md), retaining
their exact source-attribution/inventory hypotheses. No new U-minus-S theorem
or all-source receiver representation is introduced.

## 2. Receiving boundary and callee-use introduction are different owners

The selected complete Call is callee computation followed by execution of the
actual returned provider in its actual current world. Its `C-Inv` includes
entry, body, designated consumers and invocation return; the preceding callee
computation is outside that receiver operation. The whole argument is reified
inertly and received before the statically known interface demand is executed.

Therefore the source owner of a boundary for an argument accepted by r is
that actual receiving Call's entry/slot/profile, independently of whether its
callee was obtained through a Name or a Block. A callback use inside r can
reveal an omitted formal's effect demand, but is not the earlier receiving
invocation or its lifetime. Nor does invoking a callback make its own body
receive its public callee view: it receives its actual arguments and original
private captured views (typed-boundary §6, “Receiving ownership”).

For `f x` versus `({ my unused = 0; f }) x`, the latter first evaluates the
callee Block. If that finite literal/binding prefix returns the same typed
f view under its ordinary identity value correspondence, dispatch uses the
same provider interface and argument-receiving rule. Block itself introduces
no callback boundary and ordinary value transport preserves inherited views.
This is a local source-constructor consequence, not general Block equivalence:
other prefixes may emit effects, diverge or introduce genuine contracts.

The reviewed [named-frame obstruction](2026-10-15-callback-named-frame-source-bridge.md)
C3 still stands: Oracle's omitted-local-callee producer requires actual
`Expr::Var`; native authentication accepts Block-final formal routes. Its
source-shape test cannot decide whether an actual Call receives an argument.
No protection can be erased or source rejected merely to recover that test.
Conversely this source consequence does not prove N supplies the required
entry profile, typed receipt or actual receiver mapping for either route.

**Small explicit source cut.** Fix the actual ordinary definition
`my id x = x`, an original received callback h and an admissible typed source
execution of `id (h i)`. Selected C-Call first obtains id, then invokes
`ExecuteCallable(id, Delay(h i), C1)`. C-Inv enters a fresh id occurrence,
receives the whole carrier and applies its value-entry Force in that same
occurrence. If h i exposes q, the receiver-pending suffix retains the entry
rebind of x, body lookup of x and id's exact return delimiter. q has not
completed that delimiter. The received h packet remains the original captured
packet used inside the delayed argument; id's entry cannot rename its
receiver. This derives the exact entry/Force/source-suffix ordering from the
selected source operators, without claiming native C0 or Gen-Call-0 formation.
Replacing h's callee with the finite unused-0 Block above adds only the
preceding callee Bind returning that same typed view before the h invocation.

There is a concrete native producer obstruction to identifying that source
entry with existing omitted-callee introduction: G2's two renamed ordinary-id
controls at `candidate_receiver_boundary_release.rs:370–395` authenticate
their module Calls while asserting `formal_registration()==None` and
`directional_introduction()==None`. `shadow_apply.rs:1585–1603` constructs
that introduction only through `source_call.formal_name`. Both identity Calls
still have the source receiving entry just derived. Hence those introductions
cannot enumerate receiving invocations; this is a real constructor mismatch,
not evidence that identity lacks effects or requires a special rule.

## 3. Local preservation steps from the existing theorem package

### Ordinary forwarding, including ordinary id

For a non-handling bind/call/view boundary, ordinary request-bind forwards
the **same** q and retains its ordered continuation suffix. It does not
consume q, create a concrete grant, change w's provider/origin or act on K,D.
Typed value movement uses the existing indexed relational image; composition
preserves original boundary references and dependent paths. Recorded event
observations persist. New observations arise only from the actual executing
view context, never family equality or a completed latent CallView.

Thus inserting a non-handler forwards the effect contribution. It cannot
erase/reown an external b_r merely by forwarding q or returning the same
value. Its own actual receiving boundary, if licensed at a corresponding
profile position, is a different original entry/slot instance. Distinctness
comes from actual source boundary entries, not an invented second shield.
Derivation of both entries/profiles from the exact native example is still
required; this statement alone does not license two native scopes.

For fixed candidate h the existing definitions require, in addition to
activity, a matching `Path(q,owner(h),b,p)` made from Flow/Observe/Receive.
Forwarding an event creates no value-receipt edge. In particular, if outside
owner u never received a view carrying fresh b_r at the applicable path,
ordinary forwarding across r cannot manufacture such a receipt. Consequently
there is no b_r Path witness for a handler owned by u, **even if r is live**.
The internal owner with the actual matching receipt can still have its b_r
witness. This is candidate-relative territory, not a global event mask.

The no-outside-receipt condition is essential. Returning/storing/capturing an
evidence-bearing value can provide a genuine later receipt at a corresponding
typed path; request forwarding alone cannot. Raw observation witnesses are
not deleted on outward passage, and boundary/profile reachability alone does
not imply a receipt for every outer handler. Hence the current Path theorem
does not prove every possible live-r boundary-crossing release by itself.

### Receiver expiry and independence

Suppose the exact r occurrence ends while s and a fixed candidate h and its
owner remain active. The source-owner theorem ends only r and any exact
occurrences actually unwound; it never changes s by sharing a static name.
For unchanged full Path witnesses, `Inc(q,h,b_r,p)` becomes false and
`Inc(q,h,b_s,p)` is unchanged. This is the existing live-filter theorem,
not deletion of b_r profiles, q, latent code or K,D. If unwind also ends h
or s, their incidence changes for that separately justified reason.

Grant is computed from the full original incidence plus explicit local
annotation; protection-only release does not filter grants out of existence.
An independently protective b_s remains. A compatible local explicit grant
can still discharge transported protection by the selected no-origin-veto
rule. Thus “another protection remains” is not a claim that a valid local
annotation becomes ineffective. Outside handling is permitted when the
candidate covers q and its remaining protection/grant query permits it;
ordinary ordered search, patterns and selected-arm typing still decide capture.

### Outward boundary crossing while r remains live

This is a distinct case from expiry. The reviewed protection-filter result
already proves preservation if an actual source exit identifies the complete
existing witness whose r protection ends on that outgoing route: filter only
that protection, preserving raw incidence, explicit grants and w's other
coordinates. Independent b_s witnesses and sibling alias routes remain.
The new user statement supplies the behavioral requirement for the actual
receiving boundary; it does not supply the native route/exit constructor.

Absence of the candidate's matching receipt gives no b_r incidence; exact
expiry disables incidence. The separately conditional marked-exit filter
can end protection on an outgoing witness without either condition. None
licenses “a boundary was crossed, therefore delete every profile for r.”
Historical observations and still-live explicit permission remain meaningful.

## 4. Two-receiver paper walk and control cases

This is an instantiation of the preceding rules, not executed source evidence.

| Local step, with actual source evidence supplied | Consequence |
| --- | --- |
| r receives an external view; nested s receives its corresponding view | Original b_r is transported; s's actual licensed introduction, if any, has its own b_s. Neither entry reowns b_r. |
| id/non-handler forwards q while r,s live | Membership, same event and suffix survive; existing applicable b_r/b_s witnesses and grants are not globally erased. |
| q passes beyond s to an h_r with no b_s receipt | b_s cannot block h_r by mere activity of s; a matching b_r witness can still protect against h_r absent its local grant. |
| s's own protection ends on an authenticated outgoing route | The marked protection ends on that same witness; b_r and unrelated alias routes remain. |
| s returns normally; r remains live | Exact s occurrence ends; no expiry of r follows. Returned latent views retain their original profiles. |
| search abruptly unwinds s and r | End the exact crossed occurrences; preserve q and saved suffix/typed packets, and query each later candidate in its actual configuration. |

The original g direct-return control has no h-view observation path at the
direct return source. The received h profile therefore supplies no Path for
that request merely because both operations share return's family. Its local
handler uses its ordinary body-request eligibility, subject to other actual
received boundaries. The callback return instead has its actual h-view and
g receipt; non-handler forwarding cannot erase that evidence at g's internal
candidate. This reuses the reviewed finite derivation, not native execution.

Normal completion removes its exact owner delimiter and continues the parent
suffix. Abrupt forwarding need not be normal completion: no body-result edge
alone establishes it. Shallow selection removes the selected handler before
selectors/arms and does not reinstall it on raw resume. Saved owner re-entry
borrows a still-live occurrence or allocates a fresh execution occurrence;
neither action renames historical b.receiver or replays boundary entry.

Escaped/returned callables retain raw profiles along matching result paths;
while r lives, future receipt/observation can still make them applicable.
After r expires those original references do not become live during another
entry of the same source. Multi-shot resumptions retain exact current owners,
saved view nesting, live store and correlated symbolic data. N's source IDs,
FreshUse IDs or group IDs do not yet prove this activation/re-entry mapping.
The capture theorem preserves supplied nominal ownership/inventories; it does
not equate generic inference copies with executions or manufacture receipts.

## 5. Native owner/consumer bridge and earliest missing construction

N G1 retains actual named-header groups, original formals/Lambdas, enclosing
group and terminal body at `local_source.rs:27–58,445–520,630–635`.
G2's `candidate_receiver_boundary_release.rs:143–395` joins authentic calls
to those facts and their actual callee wrapper routes. It does not select a
receiver, and its direct/Block observations establish no dynamic boundary.

The actual reusable native prefix is more precise than another group table:

| Actual source/native owner | Established prefix; required next owned fact |
| --- | --- |
| `candidate_source.rs:990–1019` | Apply and original callee/whole argument, checking cause and authentic formal attachment; needs the original argument-receiving boundary template/profile, not a reinterpretation of callback-use attachment as entry. |
| `shadow_apply.rs:1518–1620` | Same recipe/Call and jointly constructed Function4 fields; needs complete source provider/role/entry/output interpretation under the same assignment. |
| `lib.rs:11271::admit_lambda_fact`; `candidate_context.rs:300–350,3000–3065` | Original FormalConstruction and actual Function Argument child/dependencies; the authentic receiving formal/domain is available here, but explicitly is not a runtime receipt or contract. This is the seam to join receiving Call to original slot/profile and typed boundary, for both direct and Block callees. |
| Actual receiver entry / complete Call output and abrupt unwind | Must instantiate that original boundary and preserve exact receiving/view identity, then authenticate which same-boundary witness crosses which actual output/control boundary. No current recipe-completion or slot-2 effect inclusion supplies this event. |
| `yu-core/src/shadow_typed_evidence.rs:93–146` | Computes candidate-relative Path/activity from supplied profiles/flows/receipts/observations; no production users or native source supplier. It has no source-authenticated marked-exit filter. |

The [prior receiving-entry derivation](2026-10-15-receiver-entry-source-derived-map.md)
§§2–3 already establishes the structural Argument prefix and identifies its
missing complete-source interpretation; it is not reproved here. The explicit
cut above shows which source operation the prefix must mean even when the
receiving Call has no omitted-callee RE introduction. Its first absent map is
the actual source receiving invocation/slot/profile to the authentic native
upper-demand RE and received typed view, along the real helper/FreshUse and
Function-port transport to that same receiver's output/abrupt exit. G1/G2
identify source operands but supply none of that operational interpretation.
This is independent of Oracle Var recognition. No new semantic vote is needed.

Current `candidate_context.rs:2895–2911` instead takes slot-0 omitted-callee
demand and slot-2 argument computation scope; the latter installs a scope
release from the argument expression's scope. `:3041–3053` transforms Function
fields. These are real scoped-algebra constructors, but do not authenticate
the receiving boundary/territory/exit identified above. They cannot substitute
for the missing join merely because a finite output row looks released.
Catch still conservatively forwards; classifier inputs and normal/abrupt
lifetime are not native consumers of G1/G2 facts.

Next exact action: consume G2's direct/Block pair at the existing receiving
Function Argument dependency and original FormalConstruction, construct or
expose the first missing source slot/profile/complete-Call interpretation
without changing availability, and retain its corresponding output witness.
An effect observation must correlate the same received boundary through id
and both routes; an existence-only good route is insufficient. Keep native
release/handler cutover OPEN until that join and both exit modes are reviewed.

## 6. Snapshot, checks and handoff

SHA-256 of frozen N dependency bytes (read-only `git show N:path`):

```text
typed-boundary-realization-draft.md 1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb
typed-source-owner-realization.md   5cbd8110736ee4d43e0c65460fa9ecf700228bfdbe9fbaa7642ea0302d86f1aa
complete-call-contribution-definition.md 4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e
source-call-scheduling-choice.md    181e95a9d87d90c265f28ad87e0176f10dd11c3c84bd308e1b802c571ae8d568
callback-identity-forwarding.md     1613a8c91ae1dd9b0d600265dcf1728aac4bf7533a9e58077551b8dba0cf3d8e
handler-protection-filter-derivation.md 82402427727102e9afdf3065da4f6b6e2e836b4571b1355ece088dbda36f1cc1
effect-scope-ownership-capture.md   44d69d6506f14c1658d7670ef68c46348d1315ce98ff1d2677f68993c5e00ea6
callback-named-frame-source-bridge.md ed5d8407fb20324578dc649aeec4547977d9c83299bdf0992a15e92f13da82c3
receiver-entry-source-derived-map.md 82fbf7019eb37f8c4506f39953f902530f28a1a7141db1c2501afd40388353df
scc-intrusion-redesign-charter.md   547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed
compose-scoped-effect-release.md   fd56f819f9b33adc5d75cbfdae378c90903e4aa3a266fc053c05dda315d40679
yu-hir/module/local_source.rs      96a77474b9e63eecaf3b5be926e82af9a88d531b40fd758f6009b33ba87c4f44
yu-solver/lib.rs                   b0f7778934a37ec9c642f7e6232cb61e37a1b0768f6af92556cf873f6b2a69f7
yu-solver/candidate_source.rs      90db34173d366ed826b34492da0fb2f1c5422b1b41e43fcda14892ec8415e7ab
yu-solver/candidate_call.rs        359566bccaa150cbe001c060475cce3d0a3e35a37a9e45d118c0f485df2e88cf
yu-solver/candidate_context.rs     9f71c8c40d6850bffccb27d7393bf6219f0ceca5cf1fe1e738073ea943706083
yu-solver/shadow_apply.rs          28112e3a8b04bff3abbed0bf7496a4e49300384e7e943ee8a71f4eff3a100294
yu-core/shadow_typed_evidence.rs   dabcbd07b2d1baace0227cb94164db871fdadc1089b1854b396dfb464d26ce95
candidate_receiver_boundary_release.rs 7fbaef0fe590a24f399d46a355f25b6987c5d81995205bc48355eb0970fa064c
```

Checks: source/constructor reads, exact dependency hashes and paper derivation;
no tests, builds, source executions, network, delegation or Git mutations.
One <=20-minute Sol/high leaf requested; actual model/effort metadata unknown.
Independent compiler-referee review checked the frozen body at SHA-256
`53d8dca90457b102fb443cd1500f9626cc99fe2278f753e4606431dcbd4e168a`
and found no BLOCKING or major findings. It confirmed the candidate-relative
receipt/expiry/marked-exit distinction and the source entry-before-Force cut.
The native entry/exit, latent/reentry and full soundness obligations remain OPEN.
This review-status update does not alter the reviewed mathematical body.

Primary integration checks matched all 19 listed baseline hashes (including
unchanged working compiler bytes) and all 11 local references. Complementary
read-only falsification checked two distinct receivers and later observation of
a retained view with both live and expired original receivers. It found no
counterexample to the stated conditional claims; unchanged unrelated incidence
requires the exact Path and candidate-activity hypotheses, and does not imply
unchanged Visible. The paper-control report is retained at
`/tmp/yulang-receiver-relative-falsifier-20261015/REPORT.md`, SHA-256
`c09c6725648c3d448cb08d09fea77be2b1f053fb83dc2033a86c00726625928a`.
These controls are not executed source evidence or additional certification.

M2 bounded source/proof application: one prover, one independent compiler
referee, and complementary read-only falsification. The behavioral transcription
has its separate spec-auditor review. Runtime measurement budget consumed: zero
processes, zero samples; no Cargo, Oracle or native execution rerun. The primary
synchronized `tasks/current.md`, `tasks/research-lab.md` and the design index;
the original parent remains OPEN with the primary owning the missing source
entry/profile/exit correspondence.

## 7. Concrete annotated instance at its actual producer

A further bounded construction attempt uses the existing successful branch of
`crates/yu-solver/tests/candidate_formal_effect_polarity.rs:72–91`:

```yu
act io:
    our tick: int -> ()
act other:
    our tick: int -> ()
my bridge (thunk:[io] int) = thunk
my answer:[io, other] int = bridge {
    my first = io::tick 1;
    my second = other::tick 1;
    1
}
```

The checked-in acceptance assertion was inspected, not rerun. The paired
`[other]` annotation below is a source-substitution argument, not a newly
parsed/executed fixture. This concrete computation-formal control does not
replace the omitted callback h case or establish its no-grant behavior.

The outer annotation determines Computation role and the root argument
computation position. Annotation integration §1.1 determines local permission
for io, accepting additional other effects without granting their removal.
There is no nested function-position choice in this instance. Entry binds the
whole carrier without Value-entry Force; the later body/result consumer uses it.
An ordinary Value id need not introduce a nonempty protection profile merely
because it has a receiving invocation.

At frozen compiler N the actual producer branches are:

1. `candidate_source.rs:575,699–715` selects Computation role and schedules
   FormalEntry and FormalAnnotation with the original annotation/formal scope.
2. `:1192–1198,1304–1307` allocates entry row e_t and generates equality between
   the body Name effect and that same entry row.
3. `candidate_effect.rs:1170–1182::candidate_formal_entry_annotation` sees no
   variable tail in `[io]`; its variable-equality branch emits nothing. Concrete
   io produces no permission, profile or receipt output here. The handling
   integration is explicitly deferred in the source comment.
4. `candidate_formal_annotation` and `candidate_formal_value_pair` produce the
   Int positive/negative pair and constrain the formal Value at slots 43/44;
   this branch does not traverse the outer concrete effects.
5. `lib.rs:11271–11335::admit_lambda_fact` uses e_t, omits the Value-entry
   slot-3 inclusion, and sends the body Name effect to the returned row at slot 4.

The authentic Function-port comparison therefore gives Argument to Int,
ArgumentEffect to e_t, and returned effect to the Call result-effect row. The
Lambda's Value result remains the original parameter row v_t, constrained by
`Int+ <= v_t` and `v_t <= Int-`; the result child is `v_t+ <= v_result-`, not
a replacement of that row by the Int leaf. The body Name equality connects e_t
to the returned effect. These scalar channels
can carry both io and other. They are not a complete original scoped assignment,
FrameCall, receipt, operation Observe or actual receiver completion witness.

**Finite information loss at this output.** Replacing only `[io]` with `[other]`
retains Computation role, an empty variable list and Int Value. The inspected
Value/AE/RE constraint outputs are isomorphic up to fresh/provenance address
renaming, while the required local permissions differ. No renaming-invariant
consumer of only those erased scalar channels can recover both permissions;
source/provenance lookup is excluded from this statement. The original HIR,
source annotations and scheduled actions remain distinct and retain the needed
fact; this is not a claim that the entire source/native state is identical.
It instantiates the acknowledged permission implementation gap, without a
runtime counterexample or a new semantic decision.

The first missing formation rule must take that original annotation, formal,
root position and actual receiving carrier under one assignment, preserve its
old evidence, and produce local io permission plus the corresponding typed
receipt tied to that receiver. It must precede the carrier's body/result
consumer. The current scalar Function incidence does not produce that output;
the conditional evidence consumer assumes it. The same source identity must
then reach operation exposure and normal completion. Those latter steps remain
unproved for this finite instance as well as for the original parent.

This gives the next owner at FormalEntry/annotation formation, without selecting
a new record representation or an interpreter. A proposed test-only interpreter
was held because choosing its own profiles would assume this absent constructor.
The inferred h position/profile remains an additional obligation. The primary
owns the concrete constructor and its matching receiving/output consumer.

The frozen detailed derivation is
`/tmp/yulang-receiver-entry-instance-20261015/REPORT.md`, SHA-256
`4d4aa4a6b3f0422909c15b47809b3272681ce7b01b0d91b83f5720dbd90e59d5`.
Independent compiler-referee delta review found an original Value endpoint
collapsed to an Int leaf and an overbroad nonrecoverability quantifier. One
batched repair retained v_t and its annotation constraints and restricted the
claim to renaming-invariant erased-channel consumers. The reviewer checked the
repaired frozen report and this archival summary, closed both findings and
reported no new findings. Primary integration matched the repaired report hash
and its nine additional baseline dependency hashes, including unchanged working
compiler/test bytes. No new tests, builds or executions ran.

Commit packet: this leased path only; baseline N above; dependency bytes
unchanged. Suggested checkpoint: `research: bridge receiver-relative forwarding and isolate entry/exit source owners`.
Primary/curator delta: preserve original parent OPEN; reuse decorated lifetime,
Path and filter results at their exact scope; assign actual receiving Argument
join and its same-instance normal/abrupt output witness. Shared records deferred
to their primary owner.
