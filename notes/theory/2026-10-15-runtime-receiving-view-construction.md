# Runtime receiving views: constructive RootComp certificates

Status: independently reviewed local source theorem. Source-derived
positive eligibility certificate and exact constructor handoff; current runtime
implementation, general negative-decision completeness and the original parent
remain OPEN.
Dispatch source HEAD: `2dc90eaeb78dd9b13277bb3f41b6d10dbf60759a`.
Read-start HEAD after primary integration: `0a9af0da5080469f930da0032aa96d7d89d358c5`.
Frozen runtime: machine `6004e345…`, program `6563dc9b…` (§7).
Exclusive lease: this new note only. No production change or executable probe.

Independent review: `runtime_semantic_review` accepted the original positive
Grant lemma and exact constructor obligations without findings at SHA-256
`b668eaa5c95d7a0c3c284394b10b77951eb776a5dcbbba78062973424546d9bc`.
An architect independently confirmed the local-Grant disjunction and separate
negative-completeness requirement. This closes the local source lemma only;
the actual view/receipt/Observe consumers still require implementation and review.

## 1. Frozen claim, scope and exclusions

Fix original resolved source declarations, formal/Lambda identities, annotation
occurrences and row positions, original symbolic endpoints, and one shared
assignment xi=(nu,K,D). Consider authentic, successfully formed current
LocalSource programs and finite current-runtime execution prefixes. The source
entry considered here is an actual invocation of a formal whose original outer
annotation is `[S] int`, selecting Comp(E,Int), with its compatible original
ground source typing derivation retained under xi; S denotes its resolved written
concrete family IDs. This is not a claim that `from_hir` alone checks that typing.
E remains open. Annotation variables are retained as
dependencies and do not themselves become concrete permissions.

The required local conclusion is a source-derived certificate for a candidate
Catch handling an event exposed by actual execution of that received root.
Construction must distinguish underlying value, typed view, fresh receiving
boundary, original receiver, actual Name-read receipt, new event and Catch
occurrence. A complete **positive eligibility certificate** means enough
authentic evidence to decide the selected disjunction `!Protected || Grant`
for this event and candidate. It does not mean an exhaustive incoming profile.
No hypothesis that the incoming profile is empty or exhaustively known is used
for the positive result in §3.

For transported inherited root profiles, apply the already reviewed source
theorem only at its actual constructors: finite chains of explicit ground
Computation formals forwarded as their resolved whole formal Names. This theorem
has no fixed chain-length bound. Its primitive typing/operation-response
contracts remain those of the reviewed source theorem. It is a proved subcase
of the original parent, not a new restriction on accepted source. Arbitrary
argument code is allowed by §3's fresh local certificate; its **inherited**
profile completeness is not thereby supplied by the direct-Name theorem.

There is no current raw-resumption execution API. Saved continuation templates
are retained; this note does not implement resume or claim its general theorem.
Full Function/B profile construction, unknown nested/symbolic positions, general
source-to-profile completeness, whole-language soundness/principality, native
Simple-sub residual suppression and production cutover remain separate OPEN
gates. This note neither weakens their original quantifiers nor certifies its
own proof or the current absent receiving-view implementation.

## 2. Authentic constructors, before the proposed runtime representation

The reviewed [root construction](2026-10-15-root-computation-profile-source-construction.md)
§§2–4 derives the following from original formal syntax, rather than assuming a
profile supplied by runtime shape:

```text
original formal t of L; annotation a at row position p is outer [S]Int
registered source role Comp(E,Int), original entry endpoint e_t
  => RootCompSchema(L,t,a,p,e_t): Protect(RootComp), Admit(RootComp)=S
```

The receiving default protects that one exposed position, including effects
outside S. The explicit contravariant annotation supplies local permission for
S. It supplies no effect occurrence, closed row cap or automatic handling.
This is the selected receiver-relative policy plus annotation policy, not an
automatic traversal of a whole result or a new inferred directional seed.

At a genuine retained entry u, source whole-argument reification has produced
an inert carrier T for the actual argument computation. Instantiate:

```text
b_u = fresh(original receiver u, original formal t, RootCompSchema, endpoints)
V_u = received view of T
chi(V_u) = inherited root image of T union {(RootComp,b_u)}
Receive(u,t,V_u,Id)
```

The fresh local singleton is known independently of whether the inherited image
has a complete native certificate. Its source coordinates are exact; unknown
inherited dependencies are retained, not replaced by an empty image. The view
is distinct from T's unreceived provider alias. Entry executes no argument code.

These static source operands are accessible in the actual program: `program.rs`
retains `_hir`, `Instruction::Lambda.parameter`, and the original LocalSource
Lambda. `SourceAnnotation` retains owner/position; `SourceAnnotationType` has
outer effects and `SourceAnnotationValue::Int`; `SourceEffectRow` retains its
position, resolved concrete `SourceEffectId`s and variables. The existing
`ParameterRole::Computation` stores only `effects.is_some()`: it does **not**
by itself certify ground Int, the written family set or a complete schema.
The source annotation owner must supply that exact descriptor at lowering or
entry. The source root can be referenced by original formal/annotation/path;
this does not claim `_hir` already stores solver registration endpoint integers.
Any required solver-endpoint join remains at its actual registration owner,
not a fabricated runtime ID. The descriptor can reference the retained HIR;
no inverse row matching,
identifier spelling or duplicate whole-source semantic reconstruction is needed.

The actual `Frame::Callee` closure branch allocates a fresh activation before
Computation binding, stores the whole Delay without execution, and preserves
the original parameter ID. It is therefore the concrete boundary constructor.
The accepted [owner result](2026-10-15-runtime-execution-owner-correspondence.md)
derives its executable owner and the required ModuleRun/Invocation decoder;
that repair remains a required actual implementation, not a supplied fact
about an already repaired machine.

## 3. A complete positive certificate without exhaustive incoming profiles

Consider an actual formal Name read under current executable owner w. Source
resolution selects the original binding carrying V_u. Typed identity transport
produces its read view V_n and the actual read receipt:

```text
Flow(V_u.RootComp,V_n.RootComp)
Receive(w,actual read slot,V_n,Id)
Execute_RootComp(V_n)
```

This is the reviewed root source theorem's actual Name/designated-consumer
case. A receipt is created by the executed read, not by Delay allocation or
inspecting an environment. The execution opens the whole root computation
view; it does not paste a callee's public profile onto its private bindings.
For each fresh event q exposed during that execution, before dispatch/unwind,
the source View projection gives:

```text
Observe(q,V_n,RootComp,actual observer occurrence)
chi(V_n)(RootComp,b_u)
```

This includes events in actual delayed argument code and its dependent source
suffixes while this root is executing. It does not include a request emitted
after that execution view has completed. Nested execution retains all still
executing applicable view observations. No event is invented for unused code.
The event and original predicates/providers remain the same in every witness.

Let the actual candidate h have installer u, cover q's exact resolved operation,
and still be live at its current search configuration C. Require u still live;
the exact original receiver of b_u is u. Suppose w=u for the read above, or an
actual additional receipt/typed route supplies **that same** V_n to u. For the
usual `catch t` in the receiver body, the owner theorem derives w=u and the
actual Name read supplies the receipt directly. The same-view join gives:

```text
Path(q,u,b_u,RootComp)
Inc_C(q,h,b_u,RootComp)
q.operation.family in S
  => Grant(q,h,C)
  => (!Protected(q,h,C) || Grant(q,h,C))
  => Visible(q,h,C).
```

Every witness is constructed above from entry, the actual source binding read,
execution and the actual Catch installation. The activity tests are at this
candidate's configuration, not cached at view construction. This proves the
local conclusion for every such source execution and event; it is not a proof
for a list of examples. No assumption about absence of other profiles appears
in the derivation. Typed-boundary §6 explicitly states that an inherited older
protection cannot veto this receiver-local Grant. Consequently even an unknown
inherited image cannot change this **positive** decision. It must still survive
for other candidates/events, dependency transport and future source execution.

The conclusion is eligibility only. Actual operation identity, ordered payload
matching, guards where supported, arm selection, shallow exit and arm effects
remain their ordinary source consumers. Permission does not itself consume q
or suppress a complete native effect support. Unrelated events emitted by body
code outside the executing received root cannot reuse this certificate.

If a nested helper installs h with owner w != u, b_u alone gives no local Grant.
An outer explicit contract is not local authority for that helper. If the old
receiver has expired, the old b_u contributes no Inc even if its raw profile
and a later observation remain. These are exact identity/activity consequences,
not arbitrary rejections of captured code or delayed code.

## 4. Inherited direct-Name views and the first completeness obstruction

For an actual argument which is exactly a resolved formal Name t, root source
construction §4 derives, before executing that Name:

```text
original binding t -> V
  -> designated eliminate_RootComp(Name t)
  -> whole Delay(code=that consumer, captured original binding)
  -> next retained argument RootComp
```

All four ports are the original same source root. Their generated map is
identity at that root. Delay construction may therefore retain the exact
dependency on the bound view's root without executing the Name or making a
future read receipt. This is a source-owned latent dependency, not all profiles
of all cells reachable from the environment. In the machine the Name label,
resolved original parameter ID and the original initialized binding cell are
available at Callee Delay construction. Formal cells are initialized by entry;
this requires no evaluation of a recursive initializer.

Apply [forwarding preservation](2026-10-15-computation-forwarding-preservation.md)
§§1–3 and its source-constructor induction: each new entry contributes its fresh
singleton and composes the preceding actual root map. For every finite retained
chain, all originally generated boundaries are retained with their own receiver
identities; equal family sets/endpoints do not merge them. If the incoming source
packet has exhaustive root coverage, this exact identity dependency and the new
singleton preserve exhaustive root coverage. If it has unresolved coverage,
these constructors preserve that unresolved dependency instead. Neither branch
requires trying candidate typings or dropping complete future information.

This supplies an actual source construction for the forwarded image, rather
than merely assuming a map exists. It also supplies the precise native repair:
the Delay constructor retains this dependency; the later executed Name creates
its own read view/receipt and opens its own execution delimiter. The outer and
inner event observations remain separately identifiable.

**First obstruction to a generic completeness claim.** Current Callee allocates
`Delay {code: argument, environment}` for *every* argument expression. Fresh
allocation says nothing about which inherited source paths its whole latent
computation exposes. The reviewed direct-Name theorem does not generate maps
for an arbitrary non-Name argument, and `ParameterRole` supplies no such maps.
Thus `fresh Delay -> Complete(empty inherited profile)` has no source derivation.
The exact owning output missing is that argument computation's source-derived
root evidence/correspondence and coverage, before binding it as an apparently
exhaustive received view. Looking at all captured cells is not a repair: a
delay may ignore one cell or consume a different typed position.

For example the original source distinction is between inert `Delay(Name t)`
and inert `Delay(1)` in an environment containing protected t. The first has
the root dependency proved above; the second does not execute t. Their equal
allocation form and shared environment do not imply equal root profiles. This
is a static constructor distinction, not a claimed run or a newly discovered
runtime bug. More complex source constructors require their actual typed maps.

The obstruction affects an exhaustive **negative** decision: absence from a
partial list cannot prove `!Protected`, nor can it prove absence of every local
Grant. It does not obstruct §3's fresh positive local Grant. A handler consumer
may use that certificate generically for any actually certified event/view,
without a whitelist of argument spellings. At a query lacking a proof of the
selected disjunction, unknown evidence remains `HandlerEvidence` unavailable;
it must not be treated as false eligibility and silently forwarded. An actually
proved ineligible candidate follows ordinary forwarding. Whole-parent natural
execution completeness remains OPEN where source evidence is unavailable.

## 5. Concrete runtime construction and consumer obligations

The following are proposed representation repairs justified by §§2–4. They are
not assertions that the frozen code already implements them or a grant of code
authority. Immutable handles must separate ValueHandle, typed received view,
boundary and request event; identity of a shared closure/Delay never unions all
its alias views. A view may retain unresolved source dependencies; no empty
collection carries an implicit completeness assertion.

| Existing owner | Source-required retained output or consumer |
| --- | --- |
| `program::from_hir` Lambda/Name lowering | Resolve the original explicit ground schema through the actual parameter ID/annotation; retain its source coordinates, concrete family IDs and endpoint references. Preserve source-selected Name consumption. |
| `Frame::Callee`, Comp closure entry | After fresh actual activation, create b and the received view with inherited root dependency plus fresh local singleton; create entry receipt; bind it without force. |
| Callee whole Delay allocation | Retain the argument computation's authentic latent root evidence. For the reviewed direct formal Name constructor retain the exact original cell/view dependency without executing Name. Otherwise preserve unresolved evidence until its source constructor supplies a map; never fabricate complete emptiness. |
| Name evaluation/`consume` | Read the bound typed view, transport by the actual read map, create a receipt for the current decoded executable owner and read slot, and execute that same view when source role selects Execute. |
| `execute` and a root-return delimiter | Execute one layer under Cnow with a RootComp observation delimiter for the exact view. Ordinary return removes it and source-projects the result; request exposure records applicable observations before unwind. |
| `execute` Request allocation / `PendingRequest` | Associate the fresh q with its declaration, actual exposure observations and original evidence dependencies. Preserve them through every propagation/saved suffix step, after observer delimiters have popped. |
| Catch evaluation / candidate query | Allocate a fresh Catch occurrence, snapshot its actual installing executable owner using the reviewed owner decoder, and test exact current handler/owner/original receiver liveness. A popped local candidate remains logically active until its source selection/forwarding transition commits. |
| Matching operation arm | Require exact event/view/typed path/receipt plus proved selected eligibility disjunction. Then run ordinary ordered matching/selection; retain unrelated request/continuation and arm effects. |

The actual `ReceivedValue` record currently contains only value/interface.
Every reconstruction must preserve or source-map its future view handle:
Catch value binder, Comp entry, ReceiverReturn, ValueEntry, local binding,
Root cache, GlobalRead cache/read, and `data`. Existing bind/extend/cells can
store the whole received record. Every role change needs its actual typed
correspondence; blindly copying all root profiles or blindly clearing them
at each reconstruction is unsound evidence handling.

For the proved ground computation, Force's eventual Int result has no effect
observation position corresponding to the consumed RootComp. Result transport
therefore drops that RootComp image, while preserving K,D and lineage on their
actually matching surviving paths and in the pending source evidence graph.
It does not paste computation-root protection onto a scalar; it does not erase
unrelated continuation/residual dependencies. Other return shapes need their
own actual result correspondence. `RuntimeValueKind` cannot choose it.

The owner proof already covers module materialization, Value entry, operation
native-return/result-consumer and delayed/captured execution. These paths must
preserve this evidence invariant through their actual reconstructions. A global
definition label or captured environment never changes b.receiver. Base literal
ground views have their source ground type, not a universal empty-profile rule
for everything `data` allocates (which also includes closures/request carriers).

## 6. Result and finite next implementation seam

Established source result submitted for review: an explicit ground RootComp
entry produces a fresh **sufficient local positive eligibility certificate**
when the actual same-view root executes and the same live receiving owner
installs the matching permitted handler. Incoming profile exhaustiveness is
unnecessary for that conclusion. Exact inherited direct-Name transport is
provided by the reviewed source theorem and preserves whatever coverage its
actual input has. This is progress beyond an assumed supplied-profile equation.

Current-source finding: no existing receiving-view/delimiter/event consumer
implements this invariant. General incoming completeness cannot be inferred
from Delay freshness or absence of stored profiles. The earliest missing owner
for exhaustive inherited evidence is the actual argument computation's latent
root construction. That is reconstruction debt with an A/B consequence; retain
its authentic output, rather than add another theorem assuming complete empty
metadata. No equivalent generic completeness attempt is recommended.

One next action: implement the original-schema -> actual Comp-entry view and
receipt -> executed Name root delimiter -> per-event observation -> exact
Catch-installer local-Grant consumer slice, preserving unknown inherited
dependencies and every ReceivedValue transport. Review that frozen actual delta
against §§2–5 before enabling handler selection. A failure to produce its exact
witness stays unavailable; no arbitrary source-name whitelist, no unproved
negative case, no blanket source restrictions and no native residual deletion
follow from this packet.

## 7. Dependency freeze, checks and commit packet

Runtime files are under `tools/inference-playground/src/runtime/`; HIR source
annotation is `crates/yu-hir/src/module/source_annotation.rs`. Full dependencies:

| File | SHA-256 |
| --- | --- |
| machine.rs | `6004e3453114a831882181f5f39bcdd30dc0eddeeb9d4616db0818b4a8f917cc` |
| program.rs | `6563dc9b4951a18832e2d31d70d88dddf244a4a85df0b91fb5ae35ebef2c2e39` |
| source_annotation.rs | `f8f8a1934d9961d443b2a0b55a79aa3272ec7cd820f7a40d9bd6217f3456ae38` |
| root-computation-profile-source-construction.md | `d98e1a4e5d93f807d77c88dcf6138924e7a2b0bd2f9af031caa58bd7c79047c0` |
| computation-forwarding-preservation.md | `d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79` |
| computation-formal-permission-construction.md | `7766aff08cedde1ebc796b8927cd1d44f459df72a632e0c0d35d4bfcd28d335e` |
| runtime-execution-owner-correspondence.md | `f550a824a33e130fd143bf8097fd951d417ccf8e1bcb24721e37ca27c9ee8975` |
| typed-boundary-realization-draft.md | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| typed-computation-core-elaboration.md | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| typed-source-owner-realization.md | `5cbd8110736ee4d43e0c65460fa9ecf700228bfdbe9fbaa7642ea0302d86f1aa` |
| source-call-scheduling-choice.md | `7b2d2556f4b6a93d7beb73a78f476bfea7d0f94de0c5f77649f6cd15ff69a530` |
| ordinary-computation-semantics-package.md | `ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917` |
| callback-identity-forwarding.md | `c544ed3c7b83686a740aa43b1db92d901de31a3b197f81f90a4c9dbdae561134` |
| annotation-effect-hygiene-integration.md | `4a98b5136a9d0d1bdddf135727c5e8779b579bf3c0b76d0524d01c951df34fd4` |
| yulang-inference-top-level-principles.md | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |

Checks: bounded static cat/sed/rg, read-only HEAD and SHA-256; write this exact
lease; final whitespace/dependency recheck in handoff. No test, build, runtime
probe, network, Git mutation, other write or delegation. One <=25-minute leaf;
zero heavy processes or measurement samples, RSS/exact elapsed unmeasured.
Requested normal Sol/high; observed runtime model/effort unknown. Configuration
registration and role contract were read; no reload/model-override claim.

Final rehash detected a concurrent machine delta to
`bcfe34546789b646aed53dda9519a05af14bbb52157187e0e9341871335ebad7`;
program/HIR annotation/owner-note hashes above remained unchanged. This note's
actual-code inventory and missing-operation claims concern the frozen
`6004e345…` machine read earlier, not that unfinished delta. No bridge or review
of the concurrent implementation is claimed. HEAD remained `0a9af0da…`.

Commit packet: exact leased path
`notes/theory/2026-10-15-runtime-receiving-view-construction.md`; frozen runtime
baseline and dependencies above; only this lease changed by producer. Independent
review pending; no source theorem/production gate self-certified. Suggested
checkpoint: `research: construct explicit RootComp runtime eligibility certificates`.
Shared-record delta for primary: retain original parent OPEN; consume the local
Grant certificate for the finite implementation seam in §6; track arbitrary
argument inherited-root completeness separately at its actual source constructor.
