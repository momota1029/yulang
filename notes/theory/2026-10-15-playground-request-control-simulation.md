# Playground requests and normal Catch: control simulation

Date: 2026-10-15
Status: independently reviewed constructive request/control simulation and exact
repaired frozen-runtime bridge; original suspension/normal-return invariant
discharged locally; selection, raw Resume and full hygiene remain OPEN
Claim class: source-qualified request-prefix and normal-return control simulation
Baseline: `943342ec9b816165a415cdbabd4133ffd9e7d202`
Branch: `research/simple-sub-intrusion`
Exclusive write lease: this file only
Dependencies: independently reviewed ordinary constructed-program simulation;
selected source scheduling and operation/result/shallow-control rules below

## 1. Frozen statement and original scope

Extend the reviewed ordinary machine argument with operation application up to
request suspension, structural request forwarding through nonmatching Catch,
and Catch normal-return value handling. Construct the reference invariant
before reading the concurrently changing runtime. Actual source-to-runtime
correspondence will use only the primary's frozen later hashes.

Fix any authentic immutable source S on the baseline's successfully formed
LocalSource route and the ordinary theorem's original constructor/binder
environment. Operation declarations retain their actual SourceOperationId
(family identity plus declaration SourceNodeKey), whole signature, original
annotation positions and call occurrence. Catch arms retain original ordered
source nodes, scrutinee/body indices and LocalSourceCatchBinderId values.
Quantify over every finite ordinary/control prefix before first unhandled
request, explicit unavailability, exhaustion or completed result, including
requests raised during callee/argument entry, nested local RHSs, conditionals,
closure bodies and value arms. Initial lexical environments and current live
cells are related exactly as in the ordinary theorem; no fresh independent
payload/result/continuation witnesses are selected.

Required conclusion: operation application introduces the whole argument
inertly, follows its declaration's Value/Computation entry, constructs a
request carrier without emitting it, returns across that native invocation's
delimiter, then exposes exactly the designated result computation. The
request has the same operation declaration, source generating occurrence and
payload. Its saved raw control suffix contains every unfinished source step
once in order and shares original live cell references without storing a
store or live receiver/handler snapshot. Normal Catch completes via its first
matching total value arm outside that Catch, or passes through the value if
there is no value arm. A request with no matching operation arm forwards;
mere absence of a generated capture certificate never proves protection
absent or a syntactically matching arm ineligible.

This packet does not implement or prove a runtime Resume API, handler arm
execution, selected-operation compatibility, callback protection/permission,
typed receipt/Flow/Observe, complete symbolic K/D transport, multi-shot
resumption, re-entry, store effects or full effectful Call adequacy. The saved
raw template is a construction for a later consumer, not proof of that future
consumer. All full hygiene, native inference soundness/principality and
production parent gates remain OPEN. A blocked matching operation consumer
is an explicit unavailable observation; it is not a forwarded request or a
source type rejection.

## 2. Governing rules and actual source owners

Source-call-scheduling-choice §§1, 1.1, 2A and 4 fixes inert whole arguments,
same-receiver entry and separate designated result completion. Charter §21
fixes outer source roles. Typed-computation-core-elaboration §3 supplies the
selected operation expansion:

```text
Invoke(entry_decl; Return(MakeRequestThunk(op,payload)), argument)
  >>= request_value. Execute_decl_result(request_value)
```

Ordinary-computation-semantics-package §3 requires current configuration for
Force/calls, separates carrier creation from request emission, and retains
pending entry/rebind/body/return suffixes. Its §§4–5 require actual receiver/
profile evidence for ordered matching and shallow selection outside the
candidate. Those requirements bound the present unavailable branch; they
are not assumed discharged by an operation ID comparison.

The immutable HIR `source_annotation.rs::declarations` constructs each actual
SourceOperationDeclaration from a declaration-only member, including exact
family/operation IDs and a SourceAnnotationType Function signature.
`local_source.rs::resolve_operation` resolves exact family/member identity,
returning explicit Unresolved/Ambiguous/Private otherwise. A request producer
cannot turn those failures into a resolved operation. Runtime call origin is
the actual generating application occurrence; the declaration ID is a
different original source identity and must remain distinct from it.

The actual candidate preflight (`candidate_source.rs:418` and following)
requires signature.effects=None and signature.value=Function for reached
Operation source forms; child argument/result effects remain allowed. This
root-signature shape is a confirmed existing admission fact, not a new
restriction invented for the proof. An unvalidated runtime call path must
validate the same shape or return unavailable; it cannot assume candidate
preflight was run on an arbitrary HirModule supplied directly to its API.

At `candidate_effect.rs::candidate_signature_value`, the Function constructor
reads actual argument/result endpoints and argument.effects. Its root
Operation case supplies the declared family to candidate_signature_effect
for the result port. That effect constructor creates family support even
when result.effects=None. Hence absent result effect annotation is not a
missing native result consumer; it cannot justify returning a carrier as the
completed source response. Nested result values may remain latent. This
source/constraint owner bridge identifies the port; it does not prove native
inference's complete effectful correspondence.

`LocalSource::catch` constructs actual arm order from CatchBlock children and
retains their actual bodies/scopes. Its value pattern owner permits only
Binder or Wildcard, both total. Each Binder ID includes the source owner,
arm source and ordinal; arm lexical work installs those exact IDs under a
Restore bracket. Operation patterns retain actual resolved declaration and
payload/continuation binders; they are not equated merely by family name.

Normal-return fallback has an additional exact frozen Oracle owner:
`a58eefc31e22141574b6f20c6a5748151c6d79f1`,
`crates/evidence-vm/src/runtime.rs::eval_catch` (22558 onward) removes current
active Catch/provider frames before continue_catch_body_result reaches
eval_value_arm. `eval_value_arm` (23654 onward) scans value arms in order and
returns the original value if none matches. The current Binder/Wildcard
fragment therefore takes its first value arm, or identity fallback.
`infer/src/lowering/control.rs:973` separately relates scrutinee/result when
no value arm exists. No match failure or implicit Unit fallback is invented.

## 3. Reference extension and central invariant

Retain the ordinary invariant R relating current source label/environment,
runtime values/cells and `plug(K,current)` to the original pending source
suffix. Add operation carrier values, Catch delimiters, and raw templates:

```text
OperationCarrier(op, payload, origin)
RawSuffix(K, lexical cell references, original source-owner descriptors)

Execute_decl_result(OperationCarrier(op,payload,origin), C_now)
  = Request(op,payload,origin,C_now, RawSuffix(K,...))
```

This line does not store C_now inside RawSuffix. Current C at emission is an
observation of the present search configuration; the future continuation
takes a future current C if and when its actual Resume consumer is built.
Code/environment references retain original lexical cells by identity.
Historical receiver/handler IDs can at most identify source owner spans;
they cannot be treated as a future live activation list or grant snapshot.

For an operation callable, lay out the actual suffix in source order:

```text
receive whole argument t in fresh operation invocation
Value payload: Force(t) >>= p. rebind original payload
Comp payload:  retain that same t as payload p
native body: Return(OperationCarrier(op,p,origin))
ReturnFromNativeInvocation
Execute_decl_result(carrier)
remaining caller suffix
```

The post-native consumer is pending before entry starts. Thus a request from
the argument retains the native carrier creation, native return and the
declared result consumer in its saved suffix. No operation event is emitted
when the operation value is looked up, the whole argument is delayed, the
payload is rebound or the carrier is allocated. No result shape test chooses
the declared consumer. Its one exposure is selected by this operation's
actual source interface even if the declared result effect row was omitted.

For Catch H introduce a delimiter meaning exactly the primitive shallow
image of its still-running scrutinee. Its pending normal return action is:

```text
on Return(v):
  leave this Catch occurrence
  select first value arm in source order (Binder/Wildcard is total)
  Binder: extend H's captured lexical env at the original arm binder with v
  Wildcard: keep H's captured lexical env
  execute arm body outside this Catch
  if no value arm: Return(v) outside this Catch
```

For a Request, value arms do not match. A resolved operation arm for a
different exact SourceOperationId cannot match this request. If every
operation arm is thus ruled out (including no operation arms), forward the
same request across this Catch occurrence. Retain the original Catch
descriptor's source re-entry/normal-return suffix in RawSuffix; it is needed
to describe a future resumed scrutinee but is not an active handler snapshot.
A matching resolved operation arm requires its actual eligibility/capture
certificate and matching/selection rule. Without it, stop unavailable at
that owner. Unresolved/private/ambiguous arm operations cannot be silently
classified as unequal resolved operations.

**Extended invariant Q.** R holds for all ordinary data/control. Additionally:

1. Every pending operation phase denotes its original declaration, source
   origin, payload and exact remaining entry/native/consumer suffix.
2. Every inert request carrier has the same declared payload (Value-entry
   result or retained Computation carrier), with original shared lexical
   references; it is not itself the completed response value.
3. Every current Catch delimiter corresponds to its exact source Catch,
   ordered arms, captured lexical environment and normal-return action.
4. A request observation preserves original operation/payload/origin and the
   complete pending suffix. Structural forwarding removes no future source
   work and adds no callback grant or permanent maker mask.
5. A raw template stores suffix structure and cell references only. There is
   no theorem here that executing it restores or re-enters owners correctly.

## 4. Constructive derivation before implementation inspection

**Operation entry.** Apply the reviewed callee/whole-argument lemma. Case on
the source declaration's actual argument.effects: None gives the same
Value force/rebind rule; Some gives retention. Unknown solved effect support
cannot choose another role. The body receives exactly the prescribed payload.
In the Value case the argument's normal return is required before carrier
creation; a request during that argument leaves the operation phases pending
once. In the Comp case the carrier's code remains inert, including effects or
divergence of a payload not yet consumed.

**Native return and designated exposure.** Carrier construction changes only
private data storage, then the native return delimiter exits the current
operation receiver. The known declaration result consumer remains pending
outside that delimiter. Executing it emits exactly the source operation with
its actual payload/origin; it does not run latent descendants of a response
that has not yet been supplied. This is a constructor-directed two-phase
proof, not the false equation “ApplyValue returned a carrier, therefore it
is already a completed source Comp result.” One-layer result exposure is
independent of whether result.effects is syntactically present.

**Normal Catch.** By Q the body return reaches its unique Catch delimiter.
Leaving it before value-arm execution reproduces the actual source/frozen
outside-handler law. Ordered total patterns give the first value arm. Related
environments plus identity-preserving arm extension give related body input;
the reviewed ordinary theorem applies to its ordinary body, or Q applies
again if it raises a request. A new arm request has the outer current Catch
path: the completed Catch cannot handle it. With no value arm the identity
source rule returns the same related value. No operation-arm profile premise
is required merely to return an ordinary body value.

**Structural forwarding.** Induct over the pending source delimiter order.
Ordinary continuations retain the same request and compose the still-pending
suffix. At a Catch with only value arms or unequal resolved operations no
request arm can select, regardless of missing capture data. Forwarding keeps
the same event identity/payload/origin and the Catch's source re-entry suffix.
At a matching/unknown operation declaration, structural nonmatching is not
proved; the available implementation must stop unavailable rather than
equating missing protection evidence with lack of protection. This leaves
source matching behavior pending without making a false hygiene claim.

**Raw suffix formation.** Interpret the saved suffix as a graph of pending
source actions on the same cell arena. Its data representation shares cell
indices and immutable code/arm descriptors. It must not deep-copy cells or
save an active receiver/store configuration for later replacement. Induction
on each pushed pending frame gives one suffix node per unfinished action,
including ordinary RHS/entry/body/conditional/root consumers and native result
exposure. Saving that graph establishes formation/provenance only. A future
raw-resume implementation additionally needs current-state threading,
borrow-or-fresh owner re-entry, matching native return delimiters and shallow
handler expiry; these cannot be inferred from stored frames alone.

**Finite-prefix composition.** Every pre-existing ordinary step preserves R
by the reviewed theorem. The new source rules above preserve Q by their
constructor cases. Therefore induction on any finite sequence of implemented
ordinary/new control steps yields either the same ordinary completion or
the same first source request with its correct pending suffix, until explicit
missing-evidence/resource exit. The proof includes a request nested during
another operation's Value entry and a request raised by an outside value arm.
It is not a theorem about executing that request's continuation, request
handler selection, future response typing, K/D preservation or row subtraction.

## 5. Exact frozen runtime bridge

The primary froze and authorized inspection of these first-snapshot runtime files;
observed hashes match every supplied hash:

| Runtime file under `tools/inference-playground/src/runtime/` | SHA-256 |
| --- | --- |
| `program.rs` | `6563dc9b4951a18832e2d31d70d88dddf244a4a85df0b91fb5ae35ebef2c2e39` |
| `machine.rs` | `dbdc990cde22de92cb5d4a93fc4e5766ffb6f4130de242de0c29c3e44fda868f` |
| `mod.rs` | `cf0f7762a0086d8dc4fe50399f620700f5e82319b925dd5dabdcd42070329554` |
| `literal.rs` (unchanged) | `8dfd2538070a3854c7a56dd8631bcae94999011bb8134cee7e71fb6a32ae46a1` |

Required owners are:
operation declaration validation and role extraction; whole-delay/call entry;
native carrier constructor; receiver return delimiter; distinct designated
consumer; emitted request source/payload/operation; Catch body delimiter;
outside normal-return arm/fallback; resolved nonmatching forwarding versus
explicit matching-evidence failure; raw-template formation with shared cells
and no store/activation snapshot; and public outcome publication.

Falsifiers include pre-entry payload execution, skipping result exposure when
result.effects=None, emitting before native return, returning the carrier as
the response, running a value arm under its own Catch, Unit/error fallback
when no value arm exists, forwarding a matching arm because its certificate
is missing, losing a pending ordinary suffix or snapshotting live cells.
No such probe has been executed. The actual constructor/consumer proof follows.

### Code construction, original identities and ordinary reuse

program.rs::from_hir retains the reviewed original code-label/Name/role/root/
annotation construction. Its Catch translation now maps each actual arm to
CatchArm(pattern clone, checked body label, original source node and range),
preserving iterator/source order. Body labels still pass the exact source
owner's expression read check; Binder IDs remain the original HIR IDs. The
existing source self-reference walk traverses scrutinee and arm bodies, so
ordinary closure recursion and capture remain available inside a value arm.
No reconstructed selector or family-name matching table is introduced.

The immutable ordinary proof at the pinned baseline is independently reviewed
and its constructor/control cases are reused. Machine::evaluate dispatch for
literals, Name, Lambda, Apply, Bind, Forward, If, local/global materialization
and their ordinary return suffixes preserves the same meanings. Changed
execute clones only an ExecutableValue's small source descriptors; its Delay
case still selects saved code/environment in the current live machine.
Thus the extension composes at actual new State/Frame cases, rather than
reproving the ordinary algorithm with a new assumed model.

### Actual operation phases and emission

evaluate(Operation) returns data containing the exact SourceOperationResolution,
with no request executable and no event. On a later Callee return, the existing
whole-argument Delay allocation occurs first with the application site's
argument label and caller lexical environment. The operation branch accepts
only Resolved(declaration), validates declaration.signature.effects=None and
Function shape itself, then obtains its argument.effects predicate. Therefore
the runtime direct API has the same original declaration-shape validation as
candidate preflight; this fact is not assumed from a prior candidate run.

It allocates a fresh receiver and pushes, bottom to top:

```text
existing caller suffix
OperationResultConsumer(source = actual application site)
ReceiverReturn(actual fresh activation)
OperationPayload(declaration, actual application site)  [Value entry only]
```

Value entry execute(delay) starts only after that receiver and all suffix
phases exist. OperationPayload consumes the returned argument value and
passes that exact value handle to make_request_carrier. Comp entry instead
passes the same inert delay handle directly to make_request_carrier; its
argument code has no intervening evaluation transition. The declaration
signature remains attached to the request executable, so the chosen payload
role is known from the original declaration, not guessed from the payload
value shape. A handler payload consumer is not implemented or proved here.

make_request_carrier calls data with RuntimeValueKind::Computation and an
ExecutableValue::Request containing declaration, payload and actual call
SourceSite. data only allocates and sets Return; it emits no event. The next
return_value consumes ReceiverReturn, checks/pops the matching live receiver,
and returns the same carrier. Only the following return_value consumes
OperationResultConsumer and calls execute on this already source-designated
carrier. execute(Request) then allocates a checked fresh request event and
sets State::Request with the same declaration/payload/origin and an initially
empty saved suffix. Thus actual return delimiter removal strictly precedes
event exposure. result.effects is never tested to skip this consumer; the
candidate family-injection owner above grounds that absence-insensitive rule.

If the Value argument raises an inner request, OperationPayload,
ReceiverReturn and OperationResultConsumer are still pending in that order
above the caller. propagate_request moves them into the saved suffix in
consumption order; it does not run the outer native body or restart argument
entry. This is the exact ordinary bind lifting needed for nested operation
entry, not an omitted corner case. An operation call never reaches Completed
with the newly created carrier: before any ordinary caller suffix can
consume it, its distinct operation result consumer emits the Request.

### Actual normal Catch and request forwarding

evaluate(Catch) pushes CatchReturn(handler code, captured lexical environment)
and evaluates only the actual scrutinee label. On normal return, return_value
has already popped that delimiter before searching arms. It finds the first
source-order Value pattern; Binder binds the actual returned handle as Value
under the exact Binder::Catch ID, while Wildcard reuses the captured
environment. It then sets Evaluate to that exact arm's checked body label.
No current delimiter for this Catch remains. With no Value pattern it sets
Return(received), preserving the original value/interface. This is precisely
the source fallback and outside-arm law, including a new request raised by
the arm: that new Request cannot encounter the already popped CatchReturn.

propagate_request handles one pending frame per step. At CatchReturn it
checks every Operation pattern. A Resolved declaration with a distinct exact
SourceOperationId is skipped. Any equal declaration or unresolved/ambiguous/
private operation exits with HandlerEvidence; none becomes a “no protection”
forwarding fact. Value-only arms never enter that check. If all operation
arms have been positively shown distinct, it stores HandlerBoundary with the
original immutable handler code and lexical environment and forwards the
same PendingRequest. No operation matching/body code executes in this packet.
This suffices to prove structural forwarding for exactly the nonmatching
paths; it does not infer eligibility of a matching operation from equality.

### Actual raw suffix representation and order proof

Write K for the still-live bottom-to-top frame vector and F for the saved
top-first `request.suffix`. Initially F is empty and K is the complete caller
suffix after request emission. After j successful propagation steps, the
invariant is:

```text
the original next-to-consume suffix
  = interpret(F[0]), ..., interpret(F[j-1]), interpret(reverse(K))
```

At each step frames.pop removes exactly the next live frame and suffix.push
appends its interpretation, proving the equation by induction. Ordinary
frames move intact as SavedFrame::Ordinary: no RHS, rebind, body, discarded
conditional, root cache-write or remaining operation phase is executed or
lost during capture. CatchReturn becomes HandlerBoundary(code,environment),
denoting the same still-pending shallow source computation's re-entry and
normal-return obligation. ReceiverReturn checks/pops the live activation and
becomes a unit ReceiverBoundary marker in the same suffix position. These
markers retain the number/order of pending invocation delimiters but do
**not** retain typed source receiver identity, profile paths or a borrow/fresh
re-entry certificate. Q's current local control projection treats them as
delimiter templates, not preserved full owner evidence. Its stronger
source-owner/typed interpretation remains a future explicit premise.

No SavedContinuation field contains Machine.cells, Machine.globals,
active_receivers or a copied store/activation vector. SavedFrame contains
immutable code references and integer environment/cell indices already
pointing into this same Machine. Frames are moved, not recursively cloned;
environments and current initialized/uninitialized cells remain in their
single arena. Caller fuel may pause propagation between frames without
changing this representation. At empty K, propagate_request moves F into
SavedContinuation and publishes an opaque same-Machine ContinuationHandle.
continuation_depth reads only its stored frame count. There is no method
that executes this template or supplies a response. Its existence/count is
formation evidence only, not activation, replay or Resume correctness.

### Actual outcome theorem and limits

UnhandledRequest is constructed only after complete structural propagation
with no remaining live frame: it carries the exact source call site, actual
operation ID, fresh event, payload handle and saved-template handle. Each
intermediate Request step retains those same fields. Completed remains a
normal-return-only outcome. HandlerEvidence/UnresolvedOperation/invalid
signature and other errors become Stopped(Unavailable); caller fuel remains
ResourceExhausted with the current private state intact. No partial value,
fake operation arm or automatic response is published. All handles and
relatedness in this theorem are relative to this owning Machine; cross-
Machine numeric handle reuse authenticates no source record.

**Unreviewed derivation of the control projection.** For every source-qualified constructed
program satisfying the reviewed ordinary initialization premises, each finite
actual execution of the frozen runtime preserves Q's control projection. If
it completes normally, its result is the corresponding source result,
including the actual normal Catch value-arm/fallback rule. If it publishes
UnhandledRequest, the source execution has exposed that same first operation
event after native return, and the raw control template retains exactly its
pending suffix in the displayed order with shared live cell references.
Each structural Catch crossing has actual resolved nonmatching evidence;
matching/unknown cases instead report explicit unavailability. Proof is
induction on the actual State/Frame branches traced above, using the reviewed
ordinary R cases and the new Q clauses. No executable probe or assumed
transition checker is a premise.

The construction intentionally stops before any response or selected handler
arm. The event's complete typed K/D, receiver/profile incidence and later
raw-resumption re-entry are still not supplied by this projection. Unit
ReceiverBoundary markers cannot close those missing original premises. The
theorem is not full effectful operational adequacy, hygiene or native type
soundness/principality. Allocation failure, parser/HIR limits and external
formatting retain the ordinary note's explicit resource exclusions; a caller
step budget controls transition count only.

### First-snapshot construction finding: retain original receiver lineage

The primary's explicit architecture handoff requires retaining original
receiver references in the raw suffix while forbidding restoration of an
old live activation snapshot. The frozen unit ReceiverBoundary does not meet
that requirement. At its actual producer, propagate_request owns
Frame::ReceiverReturn{activation}, validates it against the current live
receiver and then discards activation. The replacement contains no reference
to that original invocation. This is a precise constructor-known fact lost
at the capture owner, rather than missing global metatheory or evidence that
all raw suffixes are ready for execution.

Finding: **major, construction invariant / reconstruction debt (D)**. The
current code establishes the count/order control projection proved above,
but fails Q's required original-owner lineage component. No executed Resume
counterexample is claimed because no Resume consumer exists. This bounded
projection cannot substitute for the original stronger capture invariant.

Minimal proposed owning repair: save ReceiverBoundary{original_activation}
using the exact activation just popped, treated solely as inert historical
lineage. Original call SourceSite may also be retained at Callee invocation
construction where that source-qualified connection is known. Never restore
that saved ID as active or clone the original active receiver vector. A
future Resume must supply its separate original-to-current fresh/borrowed
occurrence mapping and prove the correct return delimiter. Retaining this
existing reference preserves source behavior and removes the avoidable later
reconstruction problem; it does not grant capture permission or prove re-entry.

The original full capture/normal-Catch packet therefore remains OPEN at this
owning repair until revised frozen bytes are inspected. Other actual
operation/native-consumer/value-arm/forwarding branches have the direct
correspondence above. This is one concrete failed constructor-preservation
case, not another equivalent conditional proof attempt.

### Repaired source lineage: original capture invariant discharged

The primary froze the single owning repair; observed machine.rs SHA-256 is
`6004e3453114a831882181f5f39bcdd30dc0eddeeb9d4616db0818b4a8f917cc`,
exactly the supplied hash. program.rs, mod.rs and literal.rs retain the
preceding table's hashes. The actual SavedFrame constructor is now:

```text
Frame::ReceiverReturn { activation }
  -- check active_receivers.pop() == Some(activation) -->
SavedFrame::ReceiverBoundary { original_activation: activation }
```

This is a direct value copy of the exact validated original ID; no inferred
source-name/shape match, independent witness choice or later reconstruction
is involved. Invocation allocation's checked monotonically increasing
next_receiver gives a distinct same-Machine ID to each original invocation.
Q before capture already relates that actual ID to the same original source
invocation. Retaining the exact ID therefore extends that same relation
after capture, including repeated source call sites and recursive invocations.
The suffix order induction is unchanged except that each receiver marker
now retains its original invocation reference as well as its position.

The repair does not push anything to active_receivers, replace cells, copy
an active vector or add a Resume API. The only active pushes remain actual
fresh closure/operation invocation constructors. Thus the newly retained
reference is inert lineage, not restored current authority. A future Resume
must still choose and prove its current fresh/borrowed occurrence mapping
and delimiter consumption; no execution rule follows from a stored ID alone.
Typed receipt/profile certificates are a separate pending construction even
though their avoidable receiver-identity loss is repaired here.

The first-snapshot major construction finding is discharged for these frozen
repaired bytes. The source operation phases, normal-value Catch, exact
nonmatching forwarding, pending-suffix order and shared-cell lemmas above
compose without any additional source assumption. This is a repair of the
original capture invariant, not promotion of the weaker count-only projection.

**Final local theorem (unreviewed constructive derivation).** Under the original
source qualification, declaration validation, source interfaces and ordinary
initialization premises fixed in §1, every finite actual repaired-machine
execution preserves Q's assigned suspension/control invariant. Normal
completion implements the original ordinary and normal Catch return/first
value-arm/fallback rules. An UnhandledRequest implements the same first
source operation event after its own native invocation return, with exact
declaration, original generating call site, event and payload; its saved
suffix preserves every pending source control action once in consumption
order, the same shared live cell/environment references, exact original
receiver references and original Catch descriptors. Value-only and resolved
unequal-operation Catch crossings have structural source forwarding proofs;
matching/unknown candidates stop at explicit HandlerEvidence. No absence of
protection or eligibility fact is inferred from that unavailable path.

Proof: use the actual new State/Frame constructor induction in §5, replace
its unit-marker case by the exact-ID preservation equation above, and reuse
the independently reviewed ordinary theorem for every unchanged case. The
native entry/return/result consumer stack gives the operation ordering;
the popped Catch delimiter plus exact total binder pattern gives normal
outside-arm execution; the top-first suffix equation gives complete local
capture. All premises are grounded at the listed owning constructors rather
than assumed transitions. The no-store/activation-snapshot property follows
from the actual SavedContinuation/SavedFrame fields and the repair's absence
of restoration. This proves the entire assigned suspension/normal-return
invariant at the repaired source, not raw Resume execution.

No code executes a saved response continuation, an operation arm or a
typed-profile handler search. Full raw-resumption/current-owner re-entry,
complete typed K/D and receiver/profile/Observe transport, selected operation
compatibility, full effectful Call, native inference soundness/principality
and production remain OPEN. The final statement neither removes those source
behaviors nor labels the corresponding unimplemented consumer complete.

### Final source delta: literal spellings exclude exterior trivia

The primary's focused runtime verification found four normal-Catch cases
stopping LiteralDecoding while seven other cases passed. These counts are
primary-reported evidence; this proof worker ran no tests. The owning cause
was the HIR carrier's original node.text() extraction, which could include
exterior leading trivia owned by the literal node. That produced explicit
unavailability, not an incorrect Completed value, so it does not refute the
completed-path theorem; it exposed a real ordinary literal-coverage gap.

The primary froze the narrow HIR fix at
`crates/yu-hir/src/module/local_source.rs`, SHA-256
`0255329f6c3261d46f1108ca2fa7b9696441669ab2c70a43a17adac50708abaf`.
The inspected diff adds only integer_spelling/string_spelling and substitutes
their results at the existing IntegerLiteral/StringLiteral form constructors.
The original source node, set call, scope, occurrence allocation, source key
and diagnostic range are unchanged. The StringInterpolation rejection remains
before extraction. Runtime machine/decoder bytes are unchanged.

integer_spelling filters direct whitespace/newline/line-comment/block-comment
elements and requires exactly one direct Integer token. Therefore for every
authentic successfully extracted IntegerLiteral, its retained spelling equals
the original integer token text, with no exterior trivia and no altered digit.
The strict runtime decimal decoder now consumes exactly that source token;
the reviewed arbitrary-decimal normalization lemma applies without assuming
literal node trivia is empty. Invalid/multiple substantive token shapes fail
explicitly rather than creating an approximate spelling.

string_spelling selects the original direct StringStart and StringEnd tokens,
requires exactly those two delimiters in that order, and checks that the
start token ends no later than the end token starts. Both are children of the
same original literal node, so their byte ranges lie within its range. The
owner subtracts that node's origin and takes node.text()[start..end] from
StringStart.start through StringEnd.end. Token boundaries are original UTF-8
boundaries; the guarded get additionally rejects an invalid range. Hence the
result is exactly the original delimiter-to-delimiter source spelling: it
excludes exterior trivia while retaining every interior byte, including
leading/trailing string content, spaces, escapes, newlines and heredoc quote
runs. This is not trim/whitespace normalization. Normal/heredoc delimiter and
escape decoding therefore follow the unchanged reviewed runtime lemma.

This supplies the actual source-to-literal-input bridge for normal Catch and
every other source position using the same constructors. The helper adds no
new source cap, decoding rule, synthetic source occurrence or public syntax
restriction. The final local theorem above composes with this owning delta:
its source identities/control invariants are unchanged, and valid literal
inputs previously hidden behind exterior-trivia unavailability now reach
their actual strict decoder. The original ordinary note remains pinned to its
reviewed baseline; this note explicitly records and proves the dependency delta.

## 6. Dependencies, checks, resources and commit packet

| Direct immutable dependency | SHA-256 |
| --- | --- |
| `notes/theory/2026-10-15-playground-ordinary-runtime-simulation.md` at the baseline | `16dcc7252c966a6d0f317ed9625cf9f5c101e4bada5f9f00d0788fe4ebe28a8b` |
| `crates/yu-hir/src/module/local_source.rs` at the original baseline | `53e3b324cac9364ac7313e44f9cc739d876427c9018df2a22e5a88119c46c1f9` |
| `crates/yu-hir/src/module/local_source.rs` final literal-extraction delta | `0255329f6c3261d46f1108ca2fa7b9696441669ab2c70a43a17adac50708abaf` |
| `crates/yu-hir/src/module/source_annotation.rs` | `f8f8a1934d9961d443b2a0b55a79aa3272ec7cd820f7a40d9bd6217f3456ae38` |
| `crates/yu-solver/src/candidate_source.rs` | `26abb65f09f2dcf7b3f798329d7f9cf867d3e6196b4cd79c03b3b558d90566e5` |
| `crates/yu-solver/src/candidate_effect.rs` | `deee5a0892b02bc9ee23a1f2a35c76175094c558ed7dfb2cf55a7e115ac54225` |
| `notes/design/2026-10-02-typed-computation-core-elaboration.md` | `0dbd943a1254dd58c435ff295a8ac0a9d025af70ba37a17154d624da8a86ab2e` |
| `notes/design/2026-10-02-ordinary-computation-semantics-package.md` | `ee3f5cf8185d516775b8915b0fda6dbb07390c3ecad7ac028eb5995581dff917` |
| `notes/design/2026-10-02-source-call-scheduling-choice.md` | `7b2d2556f4b6a93d7beb73a78f476bfea7d0f94de0c5f77649f6cd15ff69a530` |
| Oracle `crates/evidence-vm/src/runtime.rs` at `a58eefc31e22141574b6f20c6a5748151c6d79f1` | `eb3f2d42752ff112b621d35471ebab79e767523f4597c7d6bd57329d02231ee7` |

Checks so far: read-only pinned baseline/source/authority inspection,
authorized first/repaired frozen runtime inspection/hash matching, narrow HIR
literal-extraction diff/owner inspection and dependency hashing, plus note
whitespace/fence checks (no trailing whitespace; balanced
fenced blocks).
No moving runtime read, tests, builds, probes, network,
Git mutations or delegation. One static proof lane; primary owns runtime
verification. Requested normal Sol/high; effective runtime model/effort metadata
unavailable and recorded unknown. No escalation claimed. No repeated unchanged
proof-obstruction attempts occurred.

Independent review: `runtime_semantic_review` accepted the final local theorem,
repaired original-activation capture and literal-extraction bridge without
findings at artifact SHA-256
`7a6159410ed97095dc4c863c7da273afb36d6e39c47fb90ced318fbc5cd84601`.
`runtime_contract_review` separately accepted the declaration/Catch contracts,
lineage repair and literal extraction. Historical unreviewed statements above
describe the producer snapshots; this review closes only the final local claim.
Next action: construct actual receiving-view and handler-owner evidence before
operation-arm selection, then establish raw Resume correspondence separately.

Commit packet: exact lease
`notes/theory/2026-10-15-playground-request-control-simulation.md`; baseline
`943342ec9b816165a415cdbabd4133ffd9e7d202`; direct dependency hashes above;
independently reviewed source/control derivation with the exact original-receiver-lineage
construction defect repaired; checks and review above;
proposed message `research: derive playground request
and normal Catch control simulation`. Shared-record deltas left to primary:
record this packet's original suspension/normal-return derivation and repaired
lineage preservation with the completed independent review. Keep raw-
resume execution, selection, hygiene, inference and production gates OPEN.
