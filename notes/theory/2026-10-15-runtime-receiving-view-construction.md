# Runtime receiving views: constructive RootComp certificates

Status: independently reviewed local source theorem. Source-derived
positive eligibility certificate and exact constructor handoff. Sections 8–10
record actual runtime bridges and their repair history. Section 8's Unit gap
is repaired in §9; an accepted major against §9's receiving/observing-receipt
join is repaired by the independently reviewed different-receipt construction
in §10. General negative-decision completeness and the
original parent remain OPEN.

Final independent proof delta: `runtime_semantic_review` accepted §10 and carried
forward unaffected primitive-selection/cache claims at SHA-256
`e6a5befabc70b1f502fb81bba21f7be8dff6c6a47a4db9bbfc14c8e6031e9c45`.
The observing-receipt major is closed without narrowing the original §3 claim.
Independent contract and resource delta reviews are clean. The primary verified
72 playground tests, including 15 receiving controls, on the final code.
Cache preservation remains limited to the no-Resume runtime.
Dispatch source HEAD: `2dc90eaeb78dd9b13277bb3f41b6d10dbf60759a`.
Read-start HEAD after primary integration: `0a9af0da5080469f930da0032aa96d7d89d358c5`.
Frozen runtime: machine `6004e345…`, program `6563dc9b…` (§7).
Exclusive lease: this new note only. No production change or executable probe.

Independent review: `runtime_semantic_review` accepted the original positive
Grant lemma and exact constructor obligations without findings at SHA-256
`b668eaa5c95d7a0c3c284394b10b77951eb776a5dcbbba78062973424546d9bc`.
An architect independently confirmed the local-Grant disjunction and separate
negative-completeness requirement. This closes the local source lemma only.
Sections 2–7 retain the original source packet and its then-frozen runtime;
the actual later implementation is evaluated separately in §8. Its new bridge
and obstruction have not been independently reviewed by this producer.

Accepted major at producer SHA-256 `f0665186…`: §8.4's completeness converse
and §9.6's local source-correspondence conclusion were not established. The
query incorrectly required the **observing** receipt's owner to be the Catch
owner, whereas source §3 permits any genuine candidate-owner receipt of that
same observed view. §9's optimization equivalence to its previous native search
does not fix that incomplete search. Those completeness claims are withdrawn
for the old code, without changing the independently reviewed source theorem.
Section 10 gives the exact counterexample, retained constructor repair and
corrected proof. Other payload/cache/ordering derivations remain distinct.

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

## 8. Actual receiving implementation: Grant bridge and selection obstruction

### 8.1 New frozen statement and operational premises

Dispatch implementation baseline: `e6fdb660f` plus explicitly pending HIR;
observed read-start HEAD `c7e56d0f0ef85064411a35ff7ad1c0cc21f2d105`.
The four runtime byte hashes in §8.7 match the primary's frozen packet. This
section consumes the independently reviewed source lemma at producer hash
`b668eaa5…`; it does not replace that lemma's quantifiers or narrow the parent.

For every finite current machine prefix under §1's original source typing and
one xi, prove (a) every successful native `local_grant` is an authentic source
Grant, (b) the actual original explicit-ground entry, executed Name and live
same-owner permitted Catch witnesses of §3 make that query succeed, and (c)
an actual selected arm follows the source shallow selection transition. The
separate question whether **all** source-required such selections execute is
answered negatively in §8.6. No future Resume transitions are assumed.

For (c), original declaration/payload/arm typing is explicit: the emitted
payload has the declared source argument type under xi, operation responses
have the declared result type, and each actually selected arm satisfies original
`OpCompat_nu`, including its binders, answer type and retained dependencies.
These are the existing ordinary-operation typing contracts, not new runtime
selection criteria. `from_hir` alone does not check them. The signature-shape
checks inspected below do not independently prove OpCompat or payload typing.
Nothing about the source **shape of the arm body** is assumed: any originally
well-typed body may run, emit requests, bind values or call functions, subject
to the existing runtime unavailable boundaries.

### 8.2 Schema, boundary and image constructors

`program.rs` Lambda lowering calls
`RootCompSchema::from_parameter(actual Lambda SourceSite, original parameter)`.
That constructor requires matching annotation.owner/definition, an explicit
outer effect row and the actual `SourceAnnotationValue::Int`. It stores the
whole original `LocalSourceParameter` and Lambda site. Hence the row position,
annotation position, original formal ID and resolved concrete family IDs used
by §2 survive. No schema is inferred from the closure tag, solved effect row,
Function equality or a missing field. Unsupported shapes yield no schema.

The actual closure's `Frame::Callee` branch allocates its unique checked
activation, pushes the receiver delimiter, and only then calls `Receiving::enter`
for a present schema. `enter` allocates one fresh Boundary(receiver,schema),
one Image node with that boundary and the inherited image as parent, and one
distinct received View for the whole Delay. The actual entry receipt stores
that invocation, the received view and original formal ID. Original boundaries
are never renamed or modified. Nothing executes the argument at this entry.

The finite linked Image spine implements exactly the source-tagged root image
plus new singleton of §2. For the actual direct formal-Name argument,
`direct_formal_root` requires that exact original Name instruction, Parameter
resolution and source Execute mode, looks up its initialized original binding
and retains its Comp view. `Receiving::delay` copies that image/dependency onto
the **new** Delay view without doing a Name read or creating its receipt.
Thus the reviewed direct-Name map of §4 has an actual producer, not an assumed
transport input. The spine retains individual boundaries, even when their
schemas/families coincide. A fresh invocation adds a distinct boundary.

Other argument expressions receive `unknown=true` with no inferred inherited
image. This is incomplete profile representation, explicitly carried as such.
There is no native consumer of `unknown` that infers false protection or empty
source evidence. The fresh local singleton remains usable by the positive
lemma despite that unknown input. This does not certify complete inherited
profiles for arbitrary code, wrappers or aliases.

### 8.3 Executed Name, receipt and observation correspondence

Actual Name evaluation resolves its original binding cell and calls `consume`
with the whole ReceivedValue. `consume` first checks that the immutable view's
underlying value matches this ReceivedValue, then creates a receipt with the
current decoded executable owner, same ViewHandle and actual Name SourceSite.
The receipt's `formal=None` here is not a fabricated match: its source origin
is the actual cell read and exact retained view. It does not require the read
to reidentify the boundary's original formal through an inverse shape test.

If source mode is Execute and the view has a represented root image, `consume`
pushes the exact (view,receipt) pair both onto `executing_views` and in a
`Frame::RootCompReturn`, then executes the Delay in Cnow. This is the actual
RootComp execution delimiter required by §3. Views with no represented root
do not get a fabricated observation witness; they remain uncertified for this
positive consumer. Observe-only reads preserve the view and receipt without
forcing it. Neither path changes the old boundary's original receiver.

`execute(Request)` creates the new checked event ID and calls
`Receiving::observe(event,executing_views)` **before** Request propagation.
It allocates a fresh observer for each actual executing (view,receipt), storing
that exact pair and event. The pair was created only by the Name execution
constructor above. Nested executing root views all get their own observation;
an unrelated view outside this execution gains none. This applies the source
projection to actual root delimiters, without deriving an event from family
equality or a saved source label.

On ordinary return or request crossing, the matching RootCompReturn pops
exactly its execution pair, checked against the last pair. PendingRequest
retains the already recorded observations, and every forwarding step retains
the same request/event/payload/observations. At root escape SavedContinuation
also retains them. Thus observer exit does not erase a legitimate event witness
before the later handler query. Source `Inc` requires current handler/owner/
original-receiver activity, not continued activity of this historical observer.
There is still no claim about executing saved root templates through Resume.

### 8.4 Actual Grant and candidate correspondence

Catch evaluation allocates a checked unique HandlerInstallation and snapshots
its current executable owner. `propagate_request` examines a Catch at
`frames.last()` before removing it. `validate_handler_installation` checks its
original occurrence and equality with the current owner. Reuse the independently
reviewed owner correspondence: nested invocation delimiters have returned or
unwound before this reached Catch, so its installing owner is still current;
ModuleRun is distinct from every Invocation and supplies no receiving Grant.
This is an actual frame/owner invariant, not the assumption that any arbitrary
handler owns the last receiver.

`Receiving::local_grant` examines only the actual request's stored observations.
It checks the exact event, authentic allocated observer, matching receipt.owner
and receipt.view, then traverses that view's immutable Image spine. A successful
node has boundary.receiver equal to the candidate owner, still the last live
invocation, and its original schema's resolved written row contains the event's
family. Entry receipts, if used, additionally retain their formal identity;
executed-read receipts are justified by §8.3's constructor. Every reachable
boundary was made by §8.2's actual source entry and forwarded only through the
derived root map. These operands therefore construct the same-view Path, then
Inc and receiver-local Grant of §3 under the same original assignment.

The reached Catch is still installed, the installer invocation is live, and
the successful boundary has that exact original invocation as receiver: all
three source activity premises hold at this query. Old expired boundary nodes
may remain in the spine but cannot pass the receiver check, since invocation
IDs are never reused. Candidate `Covers` is checked separately using exact
resolved operation identity before the grant query. The query does not cache
eligibility or treat an enclosing owner's permission as a nested helper grant.

Conversely, the actual local witnesses of §3 are represented here: entry makes
b_u's Image node, actual Name consumption supplies the same-view receipt,
execute records its observation, and a live same-owner Catch query finds that
node and its original family permission. `unknown=true` never rejects this
positive witness. Thus both directions (a)/(b) hold for the local represented
source certificate. This is not completeness of every possible source Path.

If no positive Grant is found at an otherwise matching operation candidate,
the machine returns HandlerEvidence unavailable. It does not infer
`!Protected`, infer a negative eligibility result or silently forward past that
candidate. A different exact operation arm is skipped normally; with no matching
operation arm the Catch forwards structurally. These cases preserve the original
distinction between missing evidence and proved source absence of a match.

### 8.5 All actual received-value and selected-arm routes

For every constructor below, view/value identity is preserved or projected at
its actual source boundary; no field is dropped accidentally:

| Actual route | Inspected preservation/projection |
| --- | --- |
| Unit/Int/Bool/Str literal; implicit Unit | `ground_data` creates the original ground value and its ground view. |
| Lambda and operation public value; request carrier | `data` creates an opaque unknown public view. A closure separately retains its lexical environment and original entry schema; the public view is not pasted onto private bindings. |
| Whole Callee argument | A new Delay value and corresponding `delay` view; inherited direct-Name image is the source-derived map in §8.2. |
| Comp closure entry | Fresh local boundary/view and receipt, then bind the whole Comp ReceivedValue inertly. No force or premature Name receipt. |
| Value entry | Force whole Delay under the new receiver; ValueEntry binds the actual returned value with the same view and changes only its source interface role. |
| Operation Value payload | OperationPayload passes the complete actual ReceivedValue into the inert Request carrier. The native ReceiverReturn and separate declared-result consumer keep their source ordering. |
| Operation Comp payload | Its retained Delay includes the actual delay view; it is not forced at entry. General operation-payload boundary profiles are not invented here. This initial handler consumer does not select this payload shape. |
| ReceiverReturn | Ends exactly the invocation, passes the same value/view with the returned Value interface. It never reowns boundaries or unions callee public evidence with private captures. |
| Local/recursive cell publication | Stores value and exact view together; recursive cell references remain shared. `extend`/`bind` stores the whole ReceivedValue. |
| GlobalRead and Root cache | Stores the exact returned value/view; later GlobalRead calls ordinary consume with that same view. Source materialization does not create a receiving boundary. |
| Catch normal binder or no value arm | Binds the actual returned view unchanged, or passes it through. Its exact handler has exited before the value arm runs. Wildcard creates no binding. |
| If/Block/Forward/condition suffix | Executes the actual chosen child with unchanged enclosing views/frames. A source Unit-discard suffix creates a new ground Unit; no unrelated branch's evidence is imported. |
| RootCompReturn normal completion | Ends only its own root execution, constructs a ground result view for the actual result and preserves the value. Every represented root image originates in a schema selecting Comp(E,Int); by original source typing the normal result is Int. Its consumed RootComp has no corresponding result effect path, justifying this projection. Arbitrary ill-typed HIR alone would not justify it. |
| Selected payload binder | Binds the exact request payload ReceivedValue, preserving value/view. Wildcard adds no binding. No continuation binder is constructed by this initial discard-only consumer. |

Actual selection first checks exact operation equality, positive Grant, the
declared operation signature shape, payload syntax/Value role/view identity
and discarded continuation. It then pops the Catch once, binds the original
payload if required, and evaluates the actual arm body. The old raw suffix is
discarded by source control. Already crossed root/receiver delimiters have
already updated execution/activity; outer still-executing root delimiters stay
active. Thus the body executes outside this exact shallow handler, with other
source enclosing views still present. The body is not reduced to a literal,
forced to be pure, or selected by its spelling. Its new events obtain fresh
event IDs and their own current observation/candidate tests.

Given §8.1's original payload typing and selected-arm OpCompat, every such
actual successful selection simulates the corresponding source transition.
The runtime's coarse signature checks alone do not establish these static
typing premises, and unavailable is not forwarding for a statically incompatible
arm. This is the exact safety/correspondence claim, with no invented ordinary
typing rule. Complete symbolic K,D transport is not represented by this local
runtime certificate; those original source obligations remain fixed premises
and their general native correspondence remains OPEN.

### 8.6 Exact original-scope counterexample to selection completeness

The original selected annotation policy §1.1 already specifies this source:

```yu
act signal:
    our ping: () -> int
my relay(thunk: [signal] int) = catch thunk {
    signal::ping(), _ -> 1,
    v -> v
}
my answer = relay signal::ping()
```

Its intended source result `1` is explicit authority, not a new inferred
semantic choice. Its RootComp entry schema and query satisfy exactly §§8.2–8.4:
the receiver's t has fresh local signal permission, executing t observes the
same q, and the installed relay Catch has the same live owner. Declared Unit
payload creation and native-return/result-consumer are already established by
the reviewed request-control source bridge. Payload and arm types satisfy the
ordinary original contracts and discarded continuation requires no Resume.

Nevertheless frozen `propagate_request` requires
`matches!(argument.value, SourceAnnotationValue::Int)` at machine.rs:884. The
authentic declaration has argument Unit, so this exact source route returns
`HandlerEvidence` **after its Grant succeeds**. In addition, the next check
requires the payload syntax to be `[LocalSourceCatchPayloadPattern::Value(_)]`;
the actual `ping()` pattern is retained as `Unit { source, range }` (the HIR
constructor explicitly calls it empty-call syntax, not a semantic Unit test).
This is a static source-to-branch derivation, not an executed test or a claim
that an unavailable result was silently wrong acceptance.

Therefore the actual view/receipt/Observe/local-Grant bridge succeeds, while
the stronger claim that this implementation executes every original explicit
ground permitted selection is refuted. Restricting the proof or supported
parent to `int -> int` operations would hide the original case. The new
implementation gate remains OPEN for its original scope.

The first repair owner is the selected operation/payload consumer in
`propagate_request`, not `RootCompSchema`, `Receiving::local_grant` or the effect
row. It must consume the original declaration's Value payload/result contracts
and the actual ordered payload syntax. For this falsifier, accepting the
declared Unit payload and interpreting its retained empty-call pattern according
to the original source matching contract removes both exact failed checks;
do not reinterpret that syntax as a newly required Unit match for other
declarations. Keep original selected-arm OpCompat/payload typing explicit.
General payload forms and raw continuation binding still need their genuine
source consumers. No body-shape whitelist or family-specific patch follows.

### 8.7 New freeze, checks and commit packet

| Actual-bridge dependency | SHA-256 |
| --- | --- |
| runtime/machine.rs | `c1156fad29f3c215253240ce7afecd3eb53b92a7a5c1f88d12f85b117d3aeae6` |
| runtime/program.rs | `984efecac3257976b87c24c851f2f3d1e5a5a762bfcaaa92b572ac75000591ea` |
| runtime/mod.rs | `72b8963d42e6bb6c92914f13f5b96d2e33ecfd865a17836b2f046534303c053c` |
| runtime/receiving.rs | `1fd06e3d3392e3db0ba110b40a22567efe4435a4c94f2f2fcd9570cdd1f6f6ba` |
| HIR module/local_source.rs (pending carrier work) | `13c134afb7f85996c2f12fd27fbb78ab640878611287ca4952c10fd48cfd4c81` |
| HIR module/source_annotation.rs | `eea39d10383bd76e6307f059f6f502633aaadcb9adea3aba33f9f385f0a39acc` |
| runtime-execution-owner-correspondence.md | `8a7bbd5cd69f6a8c5ae87b2cf737a8e5fc45028ab416bfeea913c5cb490eb9a3` |
| playground-request-control-simulation.md | `740fde158d76cd89a6348b7a2f7406af21446ffbb1904e65a09be258cbab263f` |
| playground-ordinary-runtime-simulation.md | `16dcc7252c966a6d0f317ed9625cf9f5c101e4bada5f9f00d0788fe4ebe28a8b` |

The original source-authority/root/forwarding hashes remain listed in §7; this
section changes no authority or source theorem. The owner note's updated
metadata/actual owner bridge is a separately reviewed parent input.

Checks: static constructor/consumer reads, first/final runtime hashes, complete
ReceivedValue-constructor inventory, static source falsifier and whitespace
check. Zero tests/builds/probes/network/Git mutations/children. Only this leased
note changed. Requested normal Sol/high; actual runtime model/effort unknown;
zero heavy processes/measurement samples. Independent review of §8 pending;
the producer has not certified the implementation or promoted a parent gate.

Commit packet: exact lease remains this file; actual runtime baseline/hash set
above; inherited §7 dependencies retain their historical baseline. Suggested
checkpoint: `research: bridge runtime RootComp grants and expose Unit selection gap`.
Shared-record delta for primary: apply the positive actual Grant bridge after
review; keep original handler-execution completeness OPEN at the concrete Unit/
payload selection consumer; keep full B, inherited/negative profiles, symbolic
transport, Resume and production parents OPEN. Next action: repair that owning
consumer against the existing selected source behavior, then review/prove only
the changed operation-selection delta; do not repeat the already constructed
view/receipt/Observe chain.

## 9. Repaired actual selection, abandonment and Grant search

### 9.1 Delta freeze and unchanged statement

This constructive delta uses the primary's final repaired implementation:

```text
machine.rs   d1d0380bf6b2e70996777829c6e4b8643921d7656fa4cb093b962e26bb5e6a92
receiving.rs 4c8d23733ec6b8aac3a73875051f79fce6914fcc0e4d56fc90c239bad86bc22b
program.rs   984efecac3257976b87c24c851f2f3d1e5a5a762bfcaaa92b572ac75000591ea
mod.rs       72b8963d42e6bb6c92914f13f5b96d2e33ecfd865a17836b2f046534303c053c
read HEAD    d40452204ff4e5b8547287a46f6f27af29781e16
```

All other source/operational inputs and original xi, binders and theorem scopes
remain those of §§1/8.1. Reuse §8.2–8.5's actual source schema, immutable view,
receipt and pre-unwind observation bridge: the changed methods do not replace
those constructors. This section proves the changed methods at their actual
owners, including the newly affected abrupt cache path. It does not assume
ordinary module behavior stayed unchanged because ordinary tests once passed.

Claims submitted for independent review: optimized positive Grant is equivalent
to §8's direct positive search; actual primitive payload compatibility and source
shallow selection are preserved; original Unit example's two selection checks
are repaired; pending definition-cache ownership survives both completion and
discard of a captured suffix. Full B, arbitrary inherited/negative coverage,
symbolic transport, nonprimitive payload consumers, bound raw continuations and
Resume remain OPEN. The producer does not promote these claims or close the
whole parent.

### 9.2 Establish ordering and unique ownership at actual entry

The following are constructional invariants, not consequences of debug_assert:

1. `next_receiver` is checked-incremented exactly on genuine closure/operation
   Invoke. No receiver ID is reused. Force/Name/global materialization do not
   mint or reactivate an old receiver.
2. A closure's one selected Comp entry calls `Receiving::enter` at most once
   for that fresh activation; there is one original formal in this actual
   Lambda constructor. An operation does not call this boundary constructor.
   Hence each receiver has at most one Boundary in this implementation.
3. Every retained input view and inherited Image exists before that entry.
   `enter` appends a fresh Boundary and Image with the existing image as parent.
   Fields are immutable afterward. `delay` may share an existing image but
   cannot add an ancestor or alter a parent. Ground/opaque views add no image.

By induction on actual entries, the Boundary vector is strictly ordered by
receiver ID, possibly with gaps from operations or schema-less Invokes. Each
Image parent has an older image index and a strictly smaller boundary.receiver.
Captured old views do not violate this: they existed before the fresh Invoke.
Normal return and unwind do not mutate either vector. This establishes both
binary-search's sorted unique-key premise and the strictly decreasing receiver
order down every actual image chain. No Resume restoration case is assumed.

### 9.3 Optimized Grant is exactly the previous positive query

Fix one event q, candidate h, configuration C, family f and its stored
observations. ModuleRun or a noncurrent invocation cannot pass either native
query's required owner/activity check. Otherwise let r=owner(h). By §9.2 there
is at most one boundary b_r with original receiver r. The previous positive
relation is therefore exactly:

```text
b_r exists and its original schema admits f
and some authentic observation of q has a receipt whose owner is r,
 whose view is that observation's view, whose optional formal matches b_r,
 and whose immutable image chain reaches b_r.
```

This is §8.4's source Grant witness; no other receiver's boundary can grant
locally. `binary_search_by_key` finds precisely b_r or proves its absence from
the represented positive inventory. Checking its family permission once is
equivalent to checking it independently at every visit to that same boundary.
Neither absence from this inventory nor the final false query result is used
to prove negative source eligibility.

For each observation, the optimized code authenticates event/observer, receipt
owner, exact view, and the optional formal **before** inserting any image into
`visited`. The target boundary is already fixed. The image predicate now tested
is only reachability of that immutable target, independent of which authenticated
receipt led to the node. Thus a mismatching formal cannot cache a negative
verdict about a node which a later valid receipt could use. This is the concrete
reason moving authentication ahead of memoization is necessary.

If a traversed boundary.receiver equals r, both queries succeed. If it is less
than r, §9.2 proves every remaining ancestor is smaller still; stopping cannot
miss b_r. If it is greater, continue to its actual parent. If a node was visited
earlier, its tail has already been explored without finding b_r or stopped at
a proven-absent smaller receiver/shared tail. Had the earlier walk found b_r,
the whole query would already have returned true. By induction on completed
walks, stopping at a visited node preserves the answer. These cases prove both
directions of equivalence for every constructor-generated query, including
shared ancestry, repeated observations and wrong-formal observations preceding
a valid one. They do not rely on the new tests constructing the right answers.

For B retained boundaries, P concrete entries in the target permission row,
V supplied observations and U distinct visited image nodes, work is
`O(log B + P + V + U)` in source-ID comparison units, with expected amortized
constant-time HashSet operations; temporary space is O(U). Repeated failed
insertions contribute at most one per observation walk. Source-ID hashing/
comparison costs are additional if those IDs are not fixed-cost operands.
No timing measurement or worst-case hash guarantee is claimed. This optimization
does not memoize a current activity result across queries.

### 9.4 Actual payload compatibility, EmptyCall and selected-arm transition

The repaired operation consumer still requires exact operation identity,
authentic positive Grant, a declared Function operation with no outer signature
effects, Value payload role, one retained payload pattern and discarded raw
continuation. It now checks the actual declaration argument against the actual
payload kind for each primitive pair:

```text
Unit <-> Unit; Int <-> Integer; Bool <-> Boolean; Str <-> String
```

For these authentic source literal/base values, these tags are the original
primitive semantic constructors, not guesses at a higher-order source role.
Together with `matches_value`, this independently supplies actual primitive
payload compatibility with the selected original declaration: the view belongs
to that payload, and its primitive value has the declared type. The old
`matches_value` check alone proved only identity, not this typing claim.

A Value Binder pattern receives that exact compatible ReceivedValue. A Value
Wildcard and retained EmptyCall (`LocalSourceCatchPayloadPattern::Unit`) both
bind nothing. EmptyCall is interpreted as the original wildcard source match
for **any** otherwise compatible declared primitive payload; it is not an extra
Unit test. These are total patterns, so this first reached exact-operation arm
is the actual source-selected arm. No source body-shape check is added.

There is no longer a declared response-Int gate. The continuation is discarded,
so selection supplies no operation response and resumes no response consumer;
any declared response type remains the original latent contract of that
abandoned suffix. Its type need not equal the handler's answer type. The actual
arm body still has its original static `OpCompat_nu`/answer typing under xi,
with the original payload binding now supplied. Dynamic payload checking is
not a proof of arbitrary body typing. This static premise is explicit in §8.1
and remains a requirement of the original typed source theorem, not a new
runtime body predicate or a claim that `from_hir` is a type checker.

Only after these premises succeed does the machine remove h, abandon the
captured raw suffix as proved in §9.5, install any original payload binder and
evaluate the actual body. The handler occurrence is absent during that body;
still-enclosing root/receiver frames remain. Already crossed invocation/root
delimiters were ended during propagation and are not ended twice. New arm
requests have new event IDs/current observations. Hence successful selection
is the ordinary compatible shallow source transition, including effectful
arm bodies, rather than an unconditional suppression of all family effects.

The exact §8.6 authoritative Unit->Int source now passes its declared Unit/
actual Unit check and its EmptyCall wildcard, with the original discarded
continuation. It has the already-derived local Grant and evaluates body `1`.
Thus its previously identified two-check obstruction is removed by actual
constructors. This is a source-to-code derivation, not a reported execution.
Other primitive payloads use the same contract; nonprimitive payload consumers
and bound continuation execution remain separate missing source consumers,
not new permanent restrictions on the parent source language.

### 9.5 Pending cache-write ownership under abrupt suffix abandonment

Let W(c) be the unique pending cache-write owner for a global cell c: the
actual `Frame::GlobalRead {cell:c,...}` or `Frame::Root {cell:c,...}` introduced
when its original definition materialization starts. In a nonterminal running
prefix, this owner is either on the live frame stack or in the currently
propagating request's saved suffix. It may move between them only by the
actual propagation step. The current code has no Resume/concurrent-evaluation
operation that duplicates such an owner. At unhandled termination the saved
continuation retains that suffix; no subsequent source execution is claimed.

Invariant: a pending marker c in `initializing_globals` corresponds to exactly
one such W(c), its cell is not yet published, and no distinct live/pending
initializer owns c. A successful cache publication removes W(c) and its marker
together. A captured W(c) that is discarded without completion releases its
marker and publishes nothing. This is an ownership invariant over unfinished
source work, not a claim that all initialization must terminate or be cached.

Derive it from actual constructors/transitions:

- Start has empty markers/owners. Source-root scheduling starts one root at a
  time; roots are unique, completed roots have populated cells, and begin_root
  is reentered only after that root's write completed. It introduces its Root
  owner and marker together. No still-pending earlier root is restarted here.
- Demanded global Name first reads a populated cell without starting work. For
  an empty cell, `initializing_globals.insert` must succeed before GlobalRead
  is pushed. A second demand of an owned empty cell fails explicitly as true
  recursive initialization; it cannot create a duplicate W(c).
- Normal GlobalRead/Root return stores the actual initializer ReceivedValue,
  removes the marker, and consumes/proceeds. It does not cache a hypothetical
  future arm result or a different source's value.
- Request propagation moves its popped ordinary frame into the same request's
  suffix, retaining its original c and write continuation. It neither clears
  its marker nor publishes a value. Ordinary frames elsewhere are unaffected.
- On compatible discard-only selection, `abandon_suffix` scans only this
  request's actual saved frames. It removes markers exactly for its captured
  GlobalRead/Root owners. By uniqueness, no live outer W(c) can own that same
  cell. It leaves all live-stack owners and their markers intact, does not
  touch other cells, and never writes the selected arm's result into the
  abandoned cell. Those captured continuations will not execute afterward.
- If matching is unavailable, no successful next source transition is claimed.
  A resource pause retains the private machine state unchanged. At an unhandled
  outcome the suffix is retained in its opaque continuation rather than
  discarded; `abandon_suffix` is not applied. No future Resume invariant is
  smuggled into either case.

These exhaustive changed and owner-changing cases establish the invariant
including abrupt abort. The old implementation's failure to release markers
for abandoned owners was not justified by ordinary completion preservation.
The repair clears only their source-owned pending work, not every marker.

A concrete source route illustrates the disjoint-owner case (not executed):

```yu
act signal:
    our ping: () -> int
my relay(thunk: [signal] int) = catch thunk {
    signal::ping(), _ -> 1,
    v -> v
}
my main = { my ignored = relay pending; pending }
my pending = signal::ping()
```

Source-order execution starts main before pending's later scheduled root. Its
first demand starts pending under a GlobalRead write owner while main's Root
write owner stays outside relay. The request's suffix captures the pending
GlobalRead; relay's compatible selection discards it. `abandon_suffix` clears
pending's marker, leaves pending's cell empty, and preserves main's outer
marker. The subsequent Name pending can therefore start its original initializer
again and expose a fresh request; it cannot fail merely because of the abandoned
read's stale marker, and it cannot read `1` cached as pending's value. No claim
that this later request has a handler or that main completes follows.

### 9.6 Closure status, checks and final commit packet

The positive local Grant source-to-runtime correspondence retains its original
source/event/view/assignment quantifiers, and the repaired query is equivalent
to its direct native witness search. Actual primitive discard-arm selection
has the payload/identity/typing and shallow-control bridge above; the original
authoritative Unit example and abrupt cache-owner case are discharged at their
real consumers. This establishes the assigned local runtime correspondence
submitted for review, not full handler-execution completeness for the original
whole source language. Full B, nonprimitive/continuation consumers, inherited
and negative profile completeness, symbolic transport, Resume and production
gates remain OPEN with their original domains.

Checks for this delta: static constructor/consumer derivation, original-source
falsifier rederivation, all changed methods and marker ownership transitions,
first/final dependency hashes and whitespace check. No test/build/probe/code
edit/Git mutation/network/delegation. Existing cfg(test) routines were not run
and are not premises of the proofs. Requested Sol/high; observed runtime
model/effort unknown; zero heavy processes/measurement samples. Fresh independent
proof review and parent adjudication remain required; production code reviews
are separate primary-owned evidence.

Commit packet: exact lease remains
`notes/theory/2026-10-15-runtime-receiving-view-construction.md`; repaired runtime
hashes/read HEAD in §9.1, stable source dependencies in §§7/8.7. Suggested
checkpoint: `research: prove repaired receiving selection and cache ownership`.
Shared-record delta: after independent review, consume this local actual bridge
and mark §8's Unit obstruction repaired; retain the explicitly named parent
gates OPEN. Next action: fresh independent proof review of §§8–9 against this
final runtime hash set, then primary integrates the coherent implementation/
proof checkpoint without another reconstruction of the same Grant witnesses.

## 10. Independent observing and receiving receipts: final major repair

### 10.1 Counterexample and unchanged source relation

The accepted independent major gives an authentic source route:

```yu
act io:
    our tick: int -> int
my helper(item: [] int) = item
my relay(thunk: [io] int) = catch helper thunk {
    io::tick(p), _ -> p
}
my main = relay(io::tick 7)
```

At relay entry u, the original `Receive(u,V_u)` receipt is genuine and its
fresh boundary b_u permits io. Helper entry h creates a distinct received
view V_h and its own boundary. Executing helper's formal forces its delayed
argument, which actually reads relay's original thunk under h and executes
V_u. Thus q has an authentic `Observe(q,V_u)` whose **executing-read** receipt
belongs to h. At the later outer Catch query helper h has unwound, while relay
u, its Catch and original b_u remain live. Source §3/typed-boundary §6 joins
the recorded observation with relay's original **entry** receipt of V_u.
Hence Grant holds. The old native query rejected h's observing receipt because
h != u and missed that distinct valid receiving witness.

The corrected source relation retains two witnesses, with no required equality
of their receipts or owners:

```text
authentic actual Observe(q,V,RootComp) from executing V
and genuine Receive(u,slot,V,identity-RootComp-map)
and V's image reaches candidate-owned b_u
and h/u/b_u.receiver are currently live; original b_u permits q.family
  => source Grant(q,h,C).
```

The observer-owner need not still be active. Original receiver and current
candidate-owner activity remain mandatory. Equality is on the exact typed
ViewHandle/RootComp path, not underlying value, family or a different alias.
This is the original source Path relation, not a new semantic rule or weakened
profile default. The helper example demonstrates its necessity; the corrected
claim below applies to every actual constructor-generated instance.

### 10.2 Final source freeze and constructor-owned receipt index

Frozen byte dependencies for this correction:

```text
machine.rs   bac47d83a5f928bb30cb73df830048f9f57d9041fbc2cac2bc965dde10a7cdc8
receiving.rs dcd40e9ff0eae587339825d5e434d627269b6f56e2aa61990230fd5dd7af0fe1
program.rs   984efecac3257976b87c24c851f2f3d1e5a5a762bfcaaa92b572ac75000591ea
mod.rs       72b8963d42e6bb6c92914f13f5b96d2e33ecfd865a17836b2f046534303c053c
read HEAD    f75299ea4b81dcae4a2807abf33a8ea25d36bf58
```

Machine owner/view identity types now derive Hash for exact index keys. Actual
entry/read receipt calls, execution/observation construction, primitive payload
checks and `abandon_suffix` retain the constructors inspected in §§8–9.
The repaired new output is produced **inside** `Receiving::receipt`:

```text
receipt_index[(owner, exact ViewHandle, optional original formal)]
  = an authentic retained ReceiptHandle with precisely that key.
```

Proof of index adequacy is induction on actual receipt insertion. Initially
both ledger and index are empty. Insertion adds the new authentic ledger entry
and its exact key. A new key preserves every old representative. Replacing a
handle at an existing key preserves existential receipt validity, since both
records have the same owner/view/formal and identity RootComp correspondence.
The original ledger entry and source slot remain retained, including any old
entry referenced by an observation. No receipt or index key is created by a
query, and neither store is changed at unwind or observer expiry.

Therefore an exact key is present iff an actual constructor inserted at least
one genuine receipt with that key. Distinct views remain separate even when
they share an underlying value or image; wrong-formal and unqualified receipts
have separate keys and cannot overwrite one another's valid route.

For a candidate u with its unique boundary b_u and original formal t_u, the
actual machine has exactly two relevant receipt constructor forms: its own
entry receipt uses `Some(t_u)`; any later executed read uses `None`. There is
one formal/entry per original runtime Lambda invocation. Thus for **actual**
receipts of this candidate, looking up `(u,V,None)` and `(u,V,Some(t_u))` is
exhaustive. The optional-formal check is a constructional authenticity check,
not an extra semantic restriction on source Receive. A same-owner entry with
some different formal cannot arise from these constructors. Future receipt
constructors must supply their actual typed maps; they are not presumed covered
merely by adding a key.

### 10.3 Exact repaired query and source correspondence

The repaired query keeps §9.2's unique sorted owner-boundary construction,
binary search and once-per-target family check. It then performs these steps:

1. Authenticate the stored event and observer allocation; authenticate that the
   observing receipt references the exact observation view. The execution pair
   comes from actual Name Execute/View construction, so this proves the recorded
   execution/observation. It imposes no equality with the candidate owner.
2. For that same exact view, look up a candidate-owner receipt under the two
   keys in §10.2. The selected representative is rechecked for exact owner,
   view and admissible original formal. Either valid key is sufficient. Neither
   receipt can substitute a different view or typed port.
3. Only after both independent authentications, inspect the immutable image
   chain using the query-local visited set and smaller-receiver cutoff. A
   reached target is the candidate's original boundary, with its explicit
   permission and exact current activity already checked.

Soundness: index adequacy supplies a genuine candidate-owner Receive distinct
from the genuine executing observation. Together with the represented root
image they are exactly the source Path witnesses of §10.1. Current candidate,
owner and original receiver liveness supply Inc; the original schema supplies
Grant. No observer-owner liveness is required or fabricated.

Completeness for the assigned actual local certificate: §8's actual entry/read
constructors retain the original receiving witness even if another owner later
executes the same view. Index adequacy and the exhaustive actual key forms find
that witness. Actual execution retains its event observation before unwinding.
Unique owner-boundary identity locates the same b_u, and the ordered-image
search reaches it. Thus every such authentic local source witness succeeds,
including the helper counterexample, without adding the rejected requirement
that the observation and receiving receipt be identical. This proves the
original local positive bridge, not complete arbitrary source-profile inference.

Memoization remains sound: it starts only after **both** observation and
candidate-receipt authentication. For a fixed query all accepted views now ask
only whether their immutable image chain reaches the one fixed target. §9.3's
decreasing-receiver/shared-tail proof applies unchanged to that reachability
question. Wrong-formal receipts cannot insert visited nodes, cannot overwrite
the two valid index keys, and cannot poison a later valid observation. A failed
candidate lookup likewise cannot cache an image result. Historical observers
and a fresh owner with a different key never become authority by association.

For B boundaries, P target permission entries, V observations and U distinct
visited image nodes, query work remains expected `O(log B + P + V + U)` in
source-ID comparison/hash units: at most two expected-constant index lookups
per authenticated observation, plus the existing distinct-node traversal.
Each receipt insertion adds one expected-constant hash-table operation. Added
index storage is O(distinct owner/view/formal keys); the full original receipt
ledger is still retained separately. No worst-case hashing or measurements are
claimed. The index caches existence of persistent Receive, not candidate
eligibility or activity across configurations.

In a byte-cost model, add the aggregate source-ID hash/equality cost of those
receipt-key operations (and the already counted permission comparisons).
HirParameterId hashing includes its source-definition identity/spelling, so
fixed-cost bounds require bounded source identity size. The primary's fresh
cost review also establishes that the formal-key clones share existing
references and introduce no per-probe heap allocation. The structural test
counter counts image visits only; observation-loop/two-probe bounds come from
the inspected code, and no counter is treated as a measurement of hashing.
Index keys refer to immutable ledger/view identities, so there is no eligibility
cache invalidation operation hidden in this cost bound.

### 10.4 Surviving obligations and final freeze packet

No payload, selection-order, RootComp result projection or cache-abandonment
semantic changes accompany this receipt repair. Actual primitive compatibility,
discarded-response independence, outside-handler arm execution, and original
static payload/body/selected-arm OpCompat obligations remain explicit in §9.4.
The global cache-write uniqueness/abrupt-abandonment proof in §9.5 expressly
uses the absence of a Resume API or duplicated pending write owners; it is
**not** promoted to a multi-shot/raw-resumption theorem. Such a future consumer
must establish its own ownership rule before reusing that invariant.

Submitted result: corrected actual local source Grant correspondence, original
Unit/primitive discard selection, and no-Resume abrupt cache preservation. The
accepted major against the old source completeness argument is repaired by a
constructor-retained existential receipt join, not by narrowing §3 or changing
the original source theorem. The independent reviewer/primary decides closure.
Full B, inherited/negative profile completeness, nonprimitive/bound-continuation
consumers, symbolic K,D transport, Resume and production parents remain OPEN.

Checks: final static constructor/query/unchanged selection-and-abandonment
reads; first/final runtime hashes; whitespace check. The supplied runtime test
file hash is `d2b2172154598a4e76ca6777f2042c19e4e85be4ced00eea63c1801b75da5732`;
it was hashed only, not run and not used as a proof premise. Zero tests/builds/
probes/network/Git mutations/children or production writes. Only this leased
note changed; requested Sol/high, observed runtime model/effort unknown.
Fresh independent proof review is pending; previous clean payload/cache/code
reviews do not certify this repaired source join.

Commit packet: sole lease remains this note; final runtime baseline/hashes in
§10.2 and stable HIR/authority dependencies in §§7–8.7. Suggested checkpoint:
`research: prove receiving history joins independently of execution receipts`.
Shared-record delta for primary: mark the observing-receipt major repaired only
after fresh review of §10; retain original source theorem, original parent
domains and the named OPEN gates. Next action: independently review this final
constructor/index/query bridge against the frozen hash set, then integrate
the coherent corrected implementation/proof checkpoint.
