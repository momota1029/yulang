# Native template capture and finite replay correspondence

Status: source argument candidate; pending combined Lean/source independent review.
Author: primary `/root`, with constructive formal author
`/root/native_template_replay_astra_r1`. Baseline
`8c505d5ae5e3b784b172100b25041c8167e74682`, research/simple-sub-intrusion.
Contract LEAN-NATIVE-TEMPLATE-REPLAY-20261025/r1 SHA
`8e60f8c80fbc6ca07fabec90cd2db9455f39192500fd34bbc2674dad28e112f2`.
All55 dependency pins match before use. Requested child Astra/medium;
observed model/effort UNKNOWN. This note gives source equations and their
application; it is not a Lean execution of Rust or full native safety proof.

## Claim and projection

For every successful capture_template publication, observe its immutable node
arena, root, declaration/event and all exact node payloads. Observe a replay's
current metadata/control world, its actual ReceivedValue and outer frame vector.
The model's ordinary-frame, handler, owner and view payload parameters denote
those existing values without identifying them by spelling or throwing away
nested continuation handles. A mathematical list represents the vector's
bottom-to-top order unless the companion model explicitly states the inverse.

A native entry segment consists solely of consecutive State::EnterTemplate
steps for that fixed template, ending in Return or Stopped(Unavailable), or an
unfinished prefix when a step budget is exhausted. It does not execute the
restored ordinary frames. This separation is necessary: callback or resumed
program execution can request again, fail or diverge after the Hole returns.

The finite chain yields valid entry indices, a unique Hole, exact successful
entry count and chronological materialization order. Every successful non-Hole
step appends one actual materialized frame without changing the preexisting
outer frames; the final Hole returns exactly the incoming ReceivedValue. Metadata
can change during materialization, and explicit errors can stop before Hole.
No theorem here identifies Unavailable with a permitted Original.Failure or
proves those errors impossible in well-typed complete programs.

World denotes projected mutable metadata: current owner, invocation descriptors,
active-owner order and counters, handler counter, receiving records/execution log,
executing views and the per-entry control map as applicable to the companion
state. The immutable program/templates and restored frame vector are separate.
Machine.step's saturating instrumentation counter is not erased into a safety
claim: each model step corresponds to one native entry step, while run's external
step budget may expose any finite prefix. The structural theorem does not prove
an exact global runtime cost or whole-machine observation equivalence.

On failure the native machine stores only Unavailable(error), not the previous
ReceivedValue or local control map. Any such fields retained in the formal failed
state are explicit ghost bookkeeping with no native failure observation; only
EnterTemplate and successful Return assert actual response identity. Post-error
metadata is the actual remaining mutable state, not a rolled-back snapshot.

## Capture construction and publication

Machine::start_with_schedule initializes resume_templates empty (machine:460).
The private arena's sole production append is capture_template:1904. All other
production occurrences are lookups. The only TemplateNode constructors used for
publication are in capture_template; test-only hand-built arenas are excluded
from this source producer argument. No existing template node, root, declaration
or original event is mutated. Growing the vector can move allocations, but index
handles keep selecting the same immutable entry, not an address into the vector.

The complete capture branch map (machine:1841–1911) is:

| Saved input frame | Output node / failure |
| --- | --- |
| Ordinary GlobalRead or Root | ContinuationMaterialization error before any arena publication. |
| Ordinary RootCompReturn(execution) | View(previous root, exact execution). |
| Other Ordinary frame | Bind(previous root, cloned frame); ResumeArgument first validates its referenced existing template handle. |
| ReceiverBoundary(original_activation) | Owner(previous root, Invocation(original_activation)). |
| AmbientBoundary | Owner(previous root, ModuleRun). |
| HandlerBoundary(handler,environment,installation) | ForwardHandler(previous root, exact handler/environment, installation.owner). |
| After all saved frames | Owner(previous root, containing owner). |

No branch drops a successfully translated saved frame or inserts an additional
Hole. Clone retains every ordinary frame field, including nested handles and
lexical references; Bind replay may later remap a callback entry owner, as below.
An invalid nested template lookup returns InvalidSourceReference before publishing
the new arena entry. Infallible allocation abort is outside a successfully
returned/published capture; no claim is made that every allocator failure becomes
Result::Err. Failed local node assembly cannot leak a partial ResumeTemplate.

A direct loop invariant after j saved frames have successfully translated is:
nodes.length=j+1, root=j, nodes[0]=Hole, and for each1<=i<=j, nodes[i] is exactly
the translation of saved frame i-1 with inner=i-1. Earlier nodes are unchanged.
Initially j=0 by vec![Hole]/root=0. Each branch constructs its node with the old
root and then pushes once, so len-1 is precisely the new index j+1. It is safe
to subtract one after successful push because the vector is nonempty; successful
Rust vector lengths embed without wraparound into the model's natural numbers.
The final containing Owner applies the same invariant once more. For saved
suffix length L the published root is L+1 and arena size L+2, with exactly one
Hole at0 and every nonzero inner strictly decreasing by one. This is derived
from the actual builder, not assumed from an arbitrary arena's shape.

The descriptor stores request.declaration.clone() and original_event unchanged.
Those fields do not participate in entry indexing and remain immutable through
replay. The previous reviewed declaration correspondence supplies their local
operation meaning; this structural result does not extend that interpretation
to callable/polymorphic/effectful signatures.

## Entry equations and all materialization results

At entry, machine:1919–1926 first checks the template handle and node index and
clones the selected immutable node. Invalid references return explicit
InvalidSourceReference. For a successfully captured template entered at root,
the builder invariant and decreasing indices exclude that lookup failure during
this segment. The table nevertheless does not certify arbitrary hand-built
self-referential or out-of-range arenas.

For each non-Hole node, separate the branch's metadata calculation from its one
frame push. Its observation is a total returned-result operation on the projected
world: either success(new world, exact produced frame) or error(post-error world,
actual RuntimeUnavailable). This is a definition by the following inspected
branches, not an assumed safety/preservation/always-success law.

| Node | Actual materialization equation |
| --- | --- |
| Bind(frame) | Clone frame. If it is ValueEntry with callback_schema Some, map Invocation(entry_receiver) by the current control map and replace only entry_receiver; require Invocation result. Return that frame and unchanged metadata. Other Bind frames are copied exactly. |
| Owner(original) | Save previous=current_owner. Resolve original by one control lookup. If resolved owner is active, set current_owner=resolved and use owned=false. Otherwise require original=Invocation(id), read descriptor at original id, open a fresh invocation with its exact call/provider, and use owned=true. If original and resulting owner are invocations, insert/overwrite original->resulting id in the current control map. Produce OwnerReturn(owner,owned,previous). |
| ForwardHandler(handler,environment,original owner) | Resolve owner; require it active and equal to current_owner. Read next_handler, checked increment; produce CatchReturn(exact handler/environment, fresh occurrence and resolved owner). |
| View(original execution) | Call receiving.execution(original.view, original.receipt). On success append its fresh execution to executing_views and produce RootCompReturn(execution); on None return InvalidSourceReference. |
| Hole | Do not materialize a frame; set Return(response) and finish this entry segment. |

`resolve_control:1830–1839` is exactly one HashMap lookup for Invocation and
identity on ModuleRun. It does not chase a transitive closure. In the Bind
callback branch the input is Invocation, hence this implementation also returns
Invocation; the defensive noninvocation error is retained as source code, not
assumed reachable. The actual frame payload can differ from the captured payload,
so a theorem that claimed byte-identical restoration of every Bind would be false.
Its correct assertion is order/identity of the actual materialization outputs.

`owner_active:2057–2064` treats ModuleRun as active and an Invocation as active
only when its descriptor exists and is active. The Owner fresh path reads the
**original** descriptor even if resolve_control found a different inactive id.
`new_invocation:1780–1798` checks next_receiver+1 before assignment, appends an
active descriptor and active-receiver id, and sets current_owner to the fresh
Invocation. The map insert shadows the nearest binding along this single inward
path; it is a fresh per-use map rather than a shared mutation of the template.
The success frame records previous, owner and whether the activation was created.
No Owner entry executes leave_owner or consumes a saved return frame.

`receiving.execution:429–459` validates receipt.view, the view kind and exact
callback-result receipt/use links; CallbackEntry fails, Ordinary/RootComp proceed.
After validation it appends one (view,receipt) to the execution log and returns
its fresh occurrence. View then appends that exact execution to executing_views.
These are current-world observations, not a restore of an old receiving snapshot.
The helpers are finite lookups/conditionals and bounded appends. No helper used
by entry runs user code or recursively enters another continuation.

In every branch, an explicitly returned Err precedes that branch's self.frames
push; prior successfully materialized frames remain. Metadata is not globally
rolled back. In this inspected code the failure guards precede the mutations
that can successfully finish the branch (checked-add assignment happens only
on success; receiving validates before its append), but the formal result
interface may retain arbitrary post-error metadata so it does not rely on a
rollback property. Allocation aborts are not successful transition results.

Each success appends exactly one frame and assigns State::EnterTemplate with
the same template handle, selected node.inner, the updated local control map and
**the unchanged response** (machine:2020–2026). The response comprises the same
value handle, interface, view and dispatch. Materializers never read/replace it.
Hole assigns that ReceivedValue directly to Return. Machine.step:659–688 turns
any returned error into Stopped(Unavailable(error)); it does not continue entry
or execute the just-restored frames on an error. Its handling of an already
Stopped state is a native no-op; the formal finite entry relation ends there
rather than counting arbitrary repeated calls to step on a stopped machine.

## Root entry, order, shallow handlers, nested handles and reuse

The only initial EnterTemplate producers are accepted ResumeArgument return
(machine:1033–1076) and authenticated host response (:599–655). Both read the
stored root and initialize control=HashMap::new(). The recursive producer is
enter_template itself, which follows inner. ResumeArgument has already been
popped and pushes ResumeReturn before entry; that frame and every other currently
outer frame belong to the untouched starting stack. The host route likewise
has an existing stack which entry only appends to. No other production entry
assignment was found in the runtime search.

Saved suffix order is the order frames were removed while propagating the
request, innermost first (machine:2275–2320). Appending nodes in that order puts
the outermost saved action nearest the final containing Owner. Therefore
materialization order is containing Owner, then the translated saved actions in
reverse order, then Hole. The native vector ends with the innermost restored
frame, which its ordinary pop-based return interpreter will consume first.
For chronological produced frames F, final stack is outer++F, not F++outer.
No existing outer element is popped, overwritten or rearranged during entry.
This does not assert that materialized frame payloads ignore changed metadata.

`propagate_request` selects a handler and calls capture_template before popping
that selected CatchReturn (machine:2179–2189). The saved suffix contains only
already removed frames; selected handler is absent and is not reinstated. A
HandlerBoundary is added only when a handler was passed/forwarded at2310. Those
forwarded handlers legitimately become ForwardHandler nodes. Final containing
Owner supplies control ownership without reintroducing the selected handler.
This is the exact structural shallow-handler boundary, not a proof of every
handler eligibility/dispatch semantic condition.

A Bind containing ResumeArgument carries its other template handle unchanged.
Capture validates that earlier handle and replay pushes the frame; it does not
traverse its referenced arena or count its eventual execution in this chain's
rank. The newly appended outer template cannot be the validated previous handle.
Subsequent callbacks can resume other templates and require separate execution
proofs; the entry termination claim does not assert their termination.

Repeated internal continuation calls take the same template through new active
worlds/responses and fresh control maps. The arena entry is never consumed or
modified, so the constructed structural theorem applies independently each time,
without requiring the two worlds/materialized frames/results to be equal.
The public host-write path separately enforces saved.resumed once; the reusable
structure theorem does not repeal that host capability condition or assert a
second host call is accepted.

## Application boundary to original Call obligations

`Arena.size` and `Arena.at` are the extensional finite-vector projection: size
is the actual vector length and at is indexed lookup, yielding None outside it.
`P` may be the tagged disjoint union of ordinary-frame, control-owner,
view-execution and forwarded-handler/environment/owner payloads. Each source
constructor injects its exact payload into the corresponding summand before
wrapping it in `Payload`; no two distinct payload sorts are conflated. The
source materializer equations above apply on those injections. The abstract
model permits more payloads/worlds than this source projection, and proves its
structural conclusions for every total returned-result materializer.

Apply `capture_built`, `capture_size` and `capture_root` to the successful
translation list from the loop invariant. Apply the inspected entry equations
to every native entry step to obtain `EntryStep`. Its finite closure is
`EntryTrace`: zero steps emit no frames; a step's optional push is prepended to
the rest's chronological list. Induction on a native finite entry sequence,
using one exact vector push or none per source step and list associativity,
therefore gives that EntryTrace and native stack=outer++its emitted frames.
No opaque preservation premise is added: these are the enumerated branch
assignments and the ordinary finite-sequence induction.

`trace_describes` derives Prefix for every still-entering trace, and Replay for
both terminal results, preserving the returned response equality. Thus
`prefix_rank`/`prefix_order` place every unfinished prefix on the actual inward
chain; `capture_trace_bound` bounds every trace by L+2 entries and L+1 frames.
`capture_entry_exists`, through `capture_replay` and `replay_trace`, constructs
an actual EntryTrace to Hole-return or explicit error within that bound.
`completion_exact` and `capture_completion_order`, applied to the returned
Replay obtained from `trace_describes`, give exactly L+2 entries and payload
order containing Owner :: reverse(saved translations). The associated frames
are the actual metadata-dependent materialization outputs in that same order.
`observe_return`/`observe_error` give the exact response/error and outer++frames
observation. `returned_no_step`, `unavailable_no_step` and `terminal_trace`
exclude further entry steps after termination. Reapply these universally
quantified results for each immutable-template use with its new world/response.
This closes the local structural supplier of RESPONSE-TEMPLATE-1, subject to
independent review; it leaves the full typed template parent open as below.

CallCaptureResponse::plugResponse_captureFrames shows substitution cancellation
and innermost-first syntactic plugging for its represented ContextFrame list.
The native order above is structurally compatible after reversing vector storage.
Native ordinary frames, ForwardHandler code/environment, dynamic Owner remapping
and View occurrence recreation do not yet all have a typed semantic interpretation
as those Call frames. No equality with captureFrames/plugFrames or whole
CallControlStep simulation follows merely from the same ordering. POI-TRACE-1,
full callable/environment, metadata safety/freshness, Force and original Call /
inference A/B remain OPEN. No native safety counterexample was asserted.

NO_SAFE_CODE_SLICE: capture_template and enter_template expose no confirmed
implementation defect or new approved behavior change. This is formal/source
work only. No Rust/compiler/diagnostic/expectation/config/test changes and no
native/Cargo/tests were run to support the source equations.
