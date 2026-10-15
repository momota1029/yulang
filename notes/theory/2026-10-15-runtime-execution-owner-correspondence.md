# Playground execution owners: current configuration and the missing root case

Status: independently reviewed source-to-machine owner-stack derivation and
source-qualified counterexample to the unqualified last-receiver shortcut;
owner-decoder repair contract established; handler/profile implementation OPEN
Dispatch HEAD: `2dc90eaeb78dd9b13277bb3f41b6d10dbf60759a`
Frozen runtime: machine `6004e345…`, program `6563dc9b…` (full hashes in §7)
Lease: this file only; constructive leaf; no production edits or delegation
Method: derive executable-owner transitions from source Invoke/Force/Bind and
GetDefinition, then inspect every actual machine owner-changing constructor

Independent review: `runtime_semantic_review` accepted the original owner theorem
and all actual stack-mutation/Force/global/native-result cases without findings,
at artifact SHA-256
`1549cc41bc951735538c2e88ed50bc638866e29612b2c78446ad8d6bcf04512b`.
The tagged decoder and per-install Catch snapshot are implementation handoffs;
this review does not claim that those proposed constructors already exist.

## 1. Frozen original claim and scope

Quantify over authentic successfully formed current LocalSource programs S,
successful `RuntimeProgram::from_hir`, selected definition d and the program's
source-derived `execution_roots()` passed to `start`. For every actual finite
successful machine prefix, ordinary Completed result or Request propagation
prefix before its explicit terminal outcome, identify the executable source
owner of every evaluated span and every installed Catch. Include module roots,
delayed arguments, Value entry, retained Computation consumption, closure bodies,
operation payload/native-return/result-consumer, demanded global materialization
and captured computation views after a maker has expired. Source labels,
lexical binders, original receiver identities and one original assignment remain
fixed; no row or family equality supplies an owner.

The proposed shortcut to assess is

```text
owner of installed source Catch = active_receivers.last().
```

The raw shortcut is **not total** on the admitted source runtime. Its root case
is refuted in §4. The actual invocation stack otherwise admits a constructive
source correspondence below: current execution inherits the current source
configuration unless a genuine Invoke creates a fresh owner. A lexical author,
stored closure maker or source definition identity is not that current owner.

This packet covers the existing runtime only. No raw continuation execution API
exists; saved continuations are returned as opaque handles. Future resume,
fresh/borrowed owner resolution, dynamic profile introduction/transport and full
Receive/Observe/eligibility are not claimed. Missing handler evidence currently
stops execution; a control-owner derivation alone does not discharge it. Resource
pause is a preserved prefix, not source completion or source divergence.

## 2. Governing source rules and their owner consequences

`notes/design/2026-10-02-typed-source-owner-realization.md` §§2–4 specifies
fresh dynamic invocation occurrences, matching return/unwind delimiters,
current handler owners, and separation of executable owner resolution from
old boundary/receipt identity. §3 prohibits rebinding `b.receiver` when execution
later enters another owner. Typed-boundary §6 distinguishes receiving ownership,
executing-view observation, original receiver activity and a handler's exact
current owner. A source/event label is not a receipt or an active owner.

The ordinary-computation package §3 and typed-core §§3,6,9 give these specific
source transitions, rather than a hypothesis that the implementation's top
receiver is correct:

| Source operation | Executable-owner consequence |
| --- | --- |
| Invoke a closure | Fresh current invocation r encloses entry and body; normal return removes exactly r. Closure lexical references are preserved, not activated as old maker owners. |
| Value entry | Force the whole received Delay *inside* that same r; bind/rebind its result and execute the body before returning r. |
| Retained Computation entry | Bind the whole carrier without executing it; later designated Name/consumer runs it under the then-current configuration. |
| Force an ordinary Delay | Execute its code and lexical environment under **C_now**. Force itself is not Invoke, and construction stored no active-configuration snapshot. A handler in that code is installed by the current executable span, not automatically by its lexical author. |
| Invoke an operation | Fresh native invocation o owns its entry/payload/native carrier production. Its normal delimiter ends o before the separate declared-result consumer. That consumer runs in the surrounding current source configuration; its source provenance still names the operation. |
| Bind/local/conditional/handler arm | Ordinary state-threaded continuation composition preserves the current execution owner; nested Invokes have their own delimiters. Leaving a shallow handler is not leaving its surrounding invocation. |

The selected scheduling authority
`2026-10-02-source-call-scheduling-choice.md` §§1–2 explicitly requires inert
whole-argument reification and Force in the current receiver context. The
ordinary-computation package also states that an escaped closure runs under
the caller's current configuration, with no persistent maker activation mask.

Module source initialization/GetDefinition uses the separately reviewed ordinary
runtime proof's actual source-root and materialization bridge (§5, “Module
initialization” and final constructed-program theorem). Materialization runs the
original defining computation under a cache-write suffix; it is not source
Invoke or Force by value shape. Changing its lexical environment to the global
environment therefore does not itself create a fresh executable invocation.
Top-level root evaluation uses the initial module execution span. This span is
not a callback receiving boundary and has no parameter contract or local grant.

No new source owner is introduced solely because `SourceSite.definition`
changes. The owner of global **code provenance** and the invocation currently
executing a GetDefinition can differ, just as Delay code provenance and the
current forcer can differ.

## 3. Actual source constructors establish the maximal stack invariant

All runtime paths below are under `tools/inference-playground/src/runtime/`.
The inspected hashes match the primary's frozen machine/program snapshot.

Let μ denote this standalone program run's ambient module execution span.
It is a proof name for the initial source evaluation context, not an invocation
or a profile-granting receiver. Let A be the actual `active_receivers` vector.
Relate its entries bijectively to the active source Invoke occurrences in their
current nesting order. The candidate execution-owner decoding is

```text
ExecOwner(A) = Invocation(last(A))    if A is nonempty;
               ModuleRun(μ)         otherwise, while module execution is live.
```

For current source **evaluation/continuation execution**, this decoding follows
the source transitions. During Request search it follows the source configuration
after each actual frame unwind; it is not the historical owner of every saved
frame. Every Catch occurrence's owner is ExecOwner at **its own installation**.
Repeated installations of the same Code/owner are distinct handler occurrences.

### 3.1 Base and ordinary source continuation cases

`RuntimeProgram::start` (machine:195–244) initializes A empty and calls
`begin_root`. `begin_root` (:782–813) evaluates the original root body with
environment 0 under a Root cache-write suffix; it does not call Invoke.
Source module Bind/materialization likewise starts in μ. Thus A=[] correctly
represents no active source **invocation**, while its execution-owner base
is μ rather than an absent/invalid owner.

Literal/data return, Forward, lexical Name observation, Apply callee evaluation,
local initializer sequencing, conditional selection, discarded no-else result,
and normal Catch/value-arm code create no receiver entry. Inspecting their
evaluate/return branches shows no A mutation. The corresponding ordinary
source constructors introduce no Invoke, so the decoding is preserved. Local
recursive cells preserve lexical identities but create no executable owner.

`Instruction::Catch` (:420–429) installs its CatchReturn before evaluating the
scrutinee. The source constructor installs h under this current owner. Its
normal return branch (:440–475) pops h before binding/evaluating a value arm;
it does not pop a ReceiverReturn, so the arm remains in the same current owner
outside h, as the source rule requires. No old handler frame is reused.

### 3.2 Actual closure Invoke, Value entry and retained entry

On actual callee return (:482–538), the machine first creates a Delay containing
the **argument's original code and lexical environment**, without executing it.
When that callee is a Closure, it allocates fresh activation r with checked
`next_receiver`, pushes r on A and pushes its ReceiverReturn. This is precisely
the source closure Invoke. The closure's saved environment is lexical data;
it contains no restored A or maker-activation pointer.

For Value entry the machine then pushes ValueEntry and executes D. The source
entry's Force is within r, so Delay code begins with the current owner r.
Nested source calls push/pop their own entries. When that Force returns,
ValueEntry (:598–615) binds the actual result in the closure environment and
evaluates its original body. Its outer ReceiverReturn remains pending, so
r still owns the body. The body is not owned by the argument-code author.

For Computation entry, the machine binds the Delay with the Computation tag and
immediately evaluates the closure body under r. It does not execute the Delay
or create another owner. Later `consume(Execute)` checks that source tag and
calls execute. Name role selection is from the original parameter in
program.rs::from_hir, not from the actual value's runtime shape.

The actual normal ReceiverReturn (:589–597) requires the matching last r and
pops it. The source normal delimiter removes precisely r and restores its
surrounding executable context. That runtime check is not used as a premise:
the push placement and pending-frame induction above establish matching nesting
on successful paths. A checked identity failure stops the private machine
before a fabricated completed source value is exposed.

### 3.3 Delay execution and captured Comp after maker expiry

`execute(Delay)` (:870–876) evaluates its saved code/environment **without**
altering A. This agrees with Force under C_now. ReceivedValue stores the value
and source interface tag, not an active maker owner. Source profile evidence,
when implemented, must still retain its own original receiver identities;
the new execution owner cannot rebind those boundaries.

An authentic current source path separates all three identities:

```yu
my make (t:[] int) = \ignored -> t
my saved = make (catch 7 { value -> value })
my main = saved()
```

At saved's actual call, make receives the inert computation and returns a
Closure capturing its original t cell. make's invocation r_make then ends.
Calling saved creates new r_saved. Its Value parameter forces Unit before
the body; the captured original t has Computation consumption, so its actual
Name read executes the original delayed Catch under r_saved's current
configuration. That Catch's lexical SourceSite belongs to saved's definition;
its closure maker r_make is expired; its installer/executable owner is r_saved.
These are source constructor paths, not claimed test executions. The admitted
forms are precisely the current original Lambda/Comp/Apply/Catch constructors.

Substituting the already supported value-only-Catch scrutinee
`signal::ping()` yields the same owner result up to its actual Request. It
does not restore r_make or invent a grant on that captured carrier. No source
handler/profile conclusion follows merely because r_saved is the executor.

### 3.4 Operation native return and declared consumer

Operation dispatch (:539–586) derives payload role from the original declaration,
allocates/pushes fresh o, and pushes OperationResultConsumer **below**
ReceiverReturn(o). Value payload execution is above that delimiter and is owned
by o; retained payload construction does not force its carrier.

OperationPayload constructs a Request carrier without emitting the request.
Returning that carrier first pops ReceiverReturn(o), removing o. Only then
OperationResultConsumer (:480) executes the carrier. `execute(Request)`
(:877–893) emits the event without changing A. Therefore the request consumer
is owned by the surrounding current source span, not expired native o, even
though PendingRequest.source retains the operation call's source origin.
This is exactly the typed-core native-return/result-consumer distinction.

### 3.5 Global definition materialization and module roots

An initialized global read obtains the cached value and performs its original
consumption. An uninitialized module Name (:346–365) pushes GlobalRead and
evaluates that definition's body with environment 0, without changing A.
GlobalRead (:692–705) caches its completed result and returns to the original
read. The source GetDefinition/cache-write constructor has no fresh Invoke;
therefore it inherits the current source execution owner. Its global lexical
environment and SourceSite identify provenance, not a new invocation.

For example, source-ordered evaluation may demand a later computed definition
while a Value-entry receiver is forcing a global Name:

```yu
my force value = value
my first = force later
my later = catch 7 { value -> value }
my main = first
```

At this demand, later's Catch is executed within the current force receiver;
source materialization does not install a new receiving boundary merely
because the defining source label changes. A cached later read then executes
no defining code and installs no second Catch. At direct module-root execution
with A empty, the same constructors are instead owned by μ. Invalid recursive
initialization stops Unavailable and is not a source completion.

### 3.6 Actual request propagation

`propagate_request` (:709–765) transfers one actual frame into the saved suffix.
A ReceiverReturn pops exactly its activation from A and saves its historical
lineage ID; it never reactivates it. Ordinary frames preserve A. A Catch frame
is reached before the enclosing receiver's lower delimiter is crossed, so that
handler's installing invocation is still active at its own candidate boundary.
If it was installed at module scope, the ambient module span is the base.

This proves the current source-owner mapping while search reaches each handler;
it does not make the request's innermost yielding owner the owner of all outer
handlers. Matching operation candidates currently stop HandlerEvidence. Value-only
or different-operation handlers forward with saved original frames. No resume
case is present, so saved historical IDs are not evidence of future activity.

These cases exhaust actual A mutations and all current executable span creators.
Induction on actual machine steps, paired with the corresponding source rule,
proves the maximal current invariant. An unavailable or completed terminal state
is not queried for new handler eligibility. A fuel pause preserves the live
state and A; it does not end any source owner.

## 4. Concrete counterexample to raw last() and owning repair

The existing admitted runtime control is enough:

```yu
my main = catch 7 { value -> value }
```

The actual source root classifier selects main. start initializes A=[];
begin_root evaluates Catch without any closure/operation Invoke. CatchReturn
is installed with A still empty. The source handler is installed by the initial
module execution span μ, while `active_receivers.last()` is None. Normal return
still completes through the value arm. This is a real source-qualified failed
total owner mapping, not a speculative resumed trace or a new semantics choice.
The existing matching-operation root control likewise reaches its handler
evidence stop after the operation's native receiver has returned, with A empty.

Current runtime does **not** mistakenly handle that operation: it stops at its
missing consumer. The defect is in the proposed prerequisite “last receiver
always supplies a source handler owner.” Refine that prerequisite before
handler implementation, rather than forbidding root handlers or fabricating
a receiving contract at module entry.

Minimal representation handoff:

1. Represent an executable owner as the disjoint sum ModuleRun/Invocation.
   ModuleRun names this private machine's live ambient source span. It is
   not a receiver activation, creates no profile or grant and must not alias
   receiver ordinal 0 (the existing first receiver value).
2. Give current executable-owner decoding one authority:
   last Invocation when nonempty, otherwise this live ModuleRun. Preserve the
   existing checked Invoke pushes/pops; do not add an Invoke to Force,
   GetDefinition, Name, cache lookup or ordinary control frames.
3. At actual Catch installation, retain that decoded **installing owner** on
   the particular handler occurrence. A logical handler occurrence is fresh
   per installation even for the same Code and owner; a future implementation
   must not key its activity solely by Code/SourceSite or source owner.
4. At dispatch, query the handler's retained owner and its actual activity,
   independently of the request's source author/current innermost receiver.
   Normal return/forwarding removes the exact handler occurrence before arm
   code, preserving its enclosing source owner. An invocation's removal is
   still owned by its own ReceiverReturn.

Current request propagation physically pops a CatchReturn into its local
candidate branch before stopping for missing evidence. A future eligibility
consumer must retain that exact h as an active **candidate under inspection**
until the source forwarding/selection transition commits; vector membership
after the pop is not an Active(h) oracle. This does not claim a current wrong
selection: the current branch stops without selecting. It fixes the owning
lifetime of the candidate snapshot needed by the next implementation.

The snapshot is construction-retained evidence of the proven install-time
mapping. Reconstructing it later from SourceSite.definition or a closure's
captured environment would discard the distinction shown in §3.3. The existing
stack nesting also permits a consistency check that a reached current handler
has its original installer active; it is not a substitute for future resume
mapping or for profile/receipt identities.

## 5. What this enables and what remains separate

The proposed repair supplies a concrete total **execution-owner** prerequisite
for current no-resume handler installation/dispatch. A RootComp receiving
boundary still belongs only to an actual source receiving entry and must keep
that original Invocation identity. ModuleRun cannot pass a local receiver-grant
equality test just because it is an executing handler owner.

On a later captured computation use, the actual current Name load may give a
new receipt to its new executor, but it does not rename an expired original
boundary receiver. Conversely a live receiver's permission is not lost merely
because the delayed code's lexical source label is elsewhere. Eligibility must
still join the same actual received view, source event/Observe/path and active
original boundary under the existing typed-boundary rule.

No ordinary source owner field can replace those profile witnesses. No owner
proof here justifies a Catch family filter, suppressing a residual, restoring
an old source owner, or equating endpoint/source identities. The separately
reviewed request-control proof and RootComp source schema remain reused inputs;
full dynamic profile and raw-resumption gates remain OPEN.

One next action: primary assigns the minimal ModuleRun/Invocation owner decoding
and Catch installation snapshot repair to the runtime owner, then obtains focused
source-correspondence review of that actual delta before enabling eligibility.
The active receiver stack can be reused; no separate historical-maker stack or
new universal Call reconstruction is needed.

## 6. Actual producer/consumer inventory for implementation handoff

| Owner | Required delta or preserved invariant |
| --- | --- |
| Machine start/begin_root | Supply the live ambient ModuleRun execution span; no receiving boundary. |
| Closure and operation Callee branches | Preserve current fresh checked Invocation allocation before entry, and exact ReceiverReturn delimiter. |
| ValueEntry/Delay/consume | Preserve current Cnow execution; lexical captures never restore a maker owner. |
| OperationResultConsumer | Remain after native ReceiverReturn; use restored enclosing executable owner. |
| GlobalRead/Root | Materialize/cache under current source execution span; source definition labels remain provenance. |
| Catch evaluation/frame | Retain fresh handler occurrence and exact installing executable owner. |
| Catch normal/forwarding/request handling | Remove/test that exact occurrence; owner query uses retained installer, not request origin or blanket last(). |
| ReceivedValue future profile extension | Preserve original receiver identities independently of current executable owner. |

No code was changed by this packet. The proposed repair is an implementation
handoff grounded in the current source rules, not authorization to expand into
raw resume, another source ownership policy or a full runtime rewrite.

## 7. Frozen dependencies, checks and commit packet

| Dependency | SHA-256 |
| --- | --- |
| runtime/machine.rs | `6004e3453114a831882181f5f39bcdd30dc0eddeeb9d4616db0818b4a8f917cc` |
| runtime/program.rs | `6563dc9b4951a18832e2d31d70d88dddf244a4a85df0b91fb5ae35ebef2c2e39` |
| runtime_control.rs | `8fae651ed7d14f4ed25c2aaa7d1d5fd3ba40940414a1995a42ddfcb5fe6d4815` |
| Typed source owner | `5cbd8110736ee4d43e0c65460fa9ecf700228bfdbe9fbaa7642ea0302d86f1aa` |
| Typed boundary | `1a5172366a1cb0d6b6cd84beac8994d6162793c217e11aef85872e642e2748bb` |
| Source scheduling | `7b2d2556f4b6a93d7beb73a78f476bfea7d0f94de0c5f77649f6cd15ff69a530` |
| Ordinary computation | `ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917` |
| Typed core | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| Ordinary runtime proof | `16dcc7252c966a6d0f317ed9625cf9f5c101e4bada5f9f00d0788fe4ebe28a8b` |

Runtime paths are under `tools/inference-playground/src/`; the fixture is under
its tests directory. Named authority files and the previous runtime proof are
linked by their full locators above. Dependency changes by this leaf: none.

Checks: bounded static cat/sed/rg/SHA-256 and read-only Git HEAD/status; apply_patch
on this lease; final static whitespace/hash recheck reported in handoff. No test,
probe, build, network, Git mutation, source/shared-record write or child. One
bounded constructive leaf pass, zero heavy processes/measurement samples; RSS
and exact elapsed time unmeasured. Requested normal Sol/high; observed runtime
model/effort unknown. No Astra/reload claim. Review/implementation/integration
remain primary-owned; the producer does not certify its derivation.

Commit packet: exact lease
`notes/theory/2026-10-15-runtime-execution-owner-correspondence.md`; frozen runtime
hashes above and dispatch HEAD `2dc90eaeb78dd9b13277bb3f41b6d10dbf60759a`;
research-only derivation/repair contract, independently reviewed as above. Proposed
checkpoint: `research: derive runtime execution owners and expose the module-root gap`.
Shared-record delta for primary/curator: raw last-receiver prerequisite refuted
at module roots; maximal current-stack-plus-ambient correspondence supplied;
assign concrete Catch installer snapshot, leaving profiles/eligibility/resume
distinct and OPEN. No shared record was edited by this leaf.
