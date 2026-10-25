# Actual saved graph continuations under immutable extension

Status: research mathematics elaborated by primary; author checks NOT_RUN and
fresh independent review pending. No reviewed-theorem, source/native,
implementation or production closure is inferred before the sprint adjudication.
Author: `/root/graph_continuation_extension_astra_r1`; requested
`gpt-6-astra/medium`, observed model/effort UNKNOWN. No contributing descendants. Primary supplied
pre-freeze reserved-token/comment syntax feedback; this is not independent review.
Frozen authority: HANDLER-GRAPH-EXTENSION-THEORY-20261025/r1, outcome B,
contract SHA256 `b0b9f069dc8f08ed5f87a26b37d98df404e5a9dd4f0628244adc79095634a9e8`.
Baseline supplied by primary: `7ff6e74d4515099bdb13e1cbf20fc38257cb2e36`.

## Original claim and application

The paper at `docs/yulang-operational-type-safety-ja.tex:1139` quantifies over
arbitrary finite internal transitions, typed external responses with fresh
immutable graph nodes, and repeated uses of saved continuations. Its extension
lemma at line980 preserves old node values and types. The candidate supplies this
extension/response component for the **entire accepted HigherOrderGraph grammar**.
It does not claim the paper's omitted grammar, combined handler/graph language,
metadata adequacy, source/native correspondence, or Simple-sub A/B closure.

`GraphExtensionTransport.lean` maps references in arbitrary `Value R S`,
`Comp R S`, and `Adapter R S` to the same syntax with reference sort T and
unchanged recursive-name sort S. It retains recursive names, local indices,
full operation instances, literal contents, receipts, view occurrences, paths,
mode and type annotations. Unary both retains two distinct typing derivations.
Wrap keeps all independently quantified inner/input/output types. Lambda body
and outer consumer, adapter input, bind/union arm, and request response binders
retain their original scopes. Structural identity/composition, arbitrary local
renaming/substitution commutation, and typing are mutual constructor inductions.
The Empty specialization equals the accepted allocation `mapOld` structurally.

`Embedding` consists solely of an injective reference function, old type
equations, and actual old **node syntax** equations. Execution/observation/safety
is not an extension premise. Composition retains exact old nodes under composed
maps. `allocationEmbedding` consumes the actual accepted `allocate` constructor.
`map_step` and `map_steps` transport every raw graph step/event, including actual
lambda/wrap entry plan computations, lookup events, views, and finite traces.
Evaluation contexts and their plugging equations are transported explicitly.
Old-node overwrite and reference collision contradict the relation.

`GraphContinuationExtension.lean` stores the actual full operation instance,
payload, response continuation, and finite outer evaluation context in `Saved`.
`capture_typed` derives the existential continuation result type, payload type,
response binder and outer context typing from `Safety.request_context_typing`.
`capture_reached` first consumes actual internal Steps and preservation;
`capture_decomposition` consumes actual Requested decomposition. No saved typing
oracle is required by the parent application. `Saved.map` preserves complete
record syntax. `saved_map_resume` is a concrete substitution/plugging equation.

The dependent `Chain` allows arbitrary finite sequences of heterogeneous
reference sorts. `Chain.embedding`, `chain_old_nodes` and `chain_injective`
retain the composed injection and exact old content. `chain_resume_safety`
types each independently quantified response in the FINAL graph, then proves
all finite internal prefixes safe. It never requires a fresh reference to type
in the original graph. Final graph WellTyped/Guarded are explicit environmental
premises; typing alone does not imply a transparent-spine guard.
`repeated_responses` keeps two independent responses/traces/results;
`finite_response_family` gives every finite family, including the empty family.
`saved_after_second` identifies the original record after a second extension
syntactically. `chain_resume_four` obtains actual return, context request,
context failure, or next raw step.

`Run` makes the parent application an induction over arbitrary finite
**interleavings**: actual internal Step; actual request publication; immutable
extension of current computation and every stored record; and a matching typed
response to any stored record. Publication stores the original record, and
response does not remove it. The initial arena is empty. `run_invariant` derives
all arena typing from publication and preserves it under extension/reuse;
`run_prefix_safety` derives the original overall result type and four-way
progress after every final internal prefix when the final graph is Guarded.
This is an external research protocol, not a new native scheduler claim or a
replacement for raw Step. It tracks membership rather than native stable handles.
Its response constructor is the environmental typed-response contract; internal
rules contain no typing premises. Full operation equality is explicit in Answer.

## Actual allocations and discriminating applications

`source_allocation_resume` consumes actual source RHS derivations, independently
typed old captures, and `FreshNoCycle`. Existing `sourceCloseValue_typed`,
`allocate_typed` and `allocationGuard` supply new graph typing and guard. The
same derivation is used concretely in Demo's two successive finite allocations:

1. `callbackRhs` is a source value-entry lambda with real body `ret (var 0)`
   and a distinct result consumer `bind (ret unit) (ret (var 1))`. The fresh
   graph node is obtained through `sourceFresh`, with its exact syntax equation.
   The old saved request has an old reference in its delayed argument and an
   independent scope/bind outer context. `fresh_response_entry` constructs the
   actual lookup and lambda-entry prefix carrying this code and consumer.
2. `responseOne` is the fresh callable reference; `responseTwo` wraps that
   reference in typed input/output adapters. They are syntactically distinct.
   `two_responses_safe` applies the quantified theorem to both independent
   response executions of the same saved record.
3. A second source allocation creates delayed code that captures the first
   graph's callable. `secondResponse` is a computation-entry lambda whose body
   forces the newest reference and calls the resulting callback; its parameter
   remains a thunk and its consumer remains explicit. `old_after_second_safe`
   reuses the ORIGINAL saved request with this response. `first_interaction`
   and `second_interaction` exhibit actual publication/first answer/second
   extension/second answer in Run, retaining the original stored record.
4. `delayedSaved` is another original request with response type thunk(callable).
   Its old continuation forces that response and calls the callback.
   `delayed_old_after_second_safe` responds with the second allocation's actual
   delayed reference. Both graph typing and guards are derived from source RHS
   and finite allocation suppliers, not passed as example-specific oracles.
5. `wrongInstance` keeps operation ID and endpoint types but changes ordered
   type arguments. Full-instance Answer rejects it. `overwrite_unit_rejected`
   contradicts replacing an old unit node with the allocated lambda. The general
   collision theorem retains reference distinctness under arbitrary embeddings.

These are source-to-accepted-research-grammar constructions. They are not evidence
that native Rust constructors emit these logical graphs. The finite examples
supplement universal statements; they do not replace any quantifier.

## Native source audit and NO_SAFE_CODE_SLICE

Read actual frozen owners, without running or modifying native code:

| Owner | Actual behavior | Exact unresolved bridge |
| --- | --- | --- |
| `machine.rs:2500` `begin_local`, `machine.rs:1498` `Frame::Local` | A local starts as a new `None` cell, recursive environment exposes its address, initializer completion assigns a `ReceivedValue`. | Define the logical graph domain and publication boundary. Show committed captured graph nodes retain their meaning; an initializing None-to-Some cell is not automatically an immutable logical graph extension. Sequential source initialization is not the simultaneous accepted source allocation theorem. |
| `machine.rs:2318` `stop_unhandled_request`, `machine.rs:350` `SavedContinuation` | Stores actual suffix, optional template, resumed flag and observations; a template is generated only on the selected host-write route. | Connect actual payload/full declaration/suffix to Saved's whole context and response binder, plus typing and graph/environment interpretation. |
| `continuation.rs:13` `ResumeTemplate`, `TemplateNode`; `machine.rs:1913` `enter_template` | Immutable template nodes contain frames/environment handles. Replay resolves active owners, may freshen invocations, reinstalls forwarded handlers and reobserves views. | Preserve full operation instance and graph references through current environment/cell reads, control remapping, receipt/view replay and error paths. These are not supplied by structural mapContext. |
| `machine.rs:600` `resume_host_write` | Checks stopped state/handle/operation/declaration/payload and rejects a saved record already marked resumed. | This host endpoint has an explicit one-use restriction. It is not an implementation of the general repeated-resume protocol proved here. No bug verdict or removal of the restriction follows. |
| `machine.rs:2081` `propagate_request` | Examines the live installed handler delimiter and actual source operation information before forwarding. | The accepted graph machine suspends under contexts. Native forwarding and current handler eligibility require their own correspondence and live metadata proofs. |

**NO_SAFE_CODE_SLICE**: graph projection/publication, complete request capture,
current native value/code/consumer readback, and live owner/view replay remain
unproved. No dependent compiler/runtime edit is authorized or inferred from this
candidate. Minimal provisional TODO requests are below; they request evidence,
not permissions or changes to the native contract.

## Reuse, exclusions, and remaining premises

Reused only within actual accepted premises: HigherOrderGraph's complete syntax
and local substitution; source split/closure and finite fresh-cycle allocation;
canonical observation/progress, actual request-context inversion, and finite
internal trace preservation. The new generic reference map has its own
constructor proofs; allocation's old map is connected by explicit equations.
The accepted HandlerInteraction protocol is conceptual prior work only, not an
import or a source of graph correspondence. No new lane-A module is imported.
Historical literal readback does not cover callable/delayed responses; native
host-write success does not certify repeated callback resume. No historical
excluded failed module or conditional premise is used as an unconditional fact.

Full-paper recursive/nominal/type-changing roll, polymorphism, records/constructors,
mapop/primitive forms and native authenticity remain outside the accepted grammar
and OPEN at their existing owners. Combined handler/graph integration requires
explicit transport of lane A's final grammar, handlers, trial/wait binders and
its different request propagation machine. Neither lane automatically supplies
that future dependency. Live metadata/owner freshening and independent F1/FK1
remain OPEN; an outer context typing theorem is not a native foreign-continuation
law. Simple-sub generation, accumulation, propagation, levels, extrusion,
qualifying intrusion and generalization are unchanged.

## Mutual evidence TODOs

- `GCE-CHECK-1`, primary checker then fresh nonauthor reviewer: elaborate the two
  frozen files and inspect every explicit public declaration and transitive
  axiom set. Falsifier: any elaboration failure, unproved constructor branch,
  extra axiom, old-graph response requirement, or assumed source transition.
- `GCE-NATIVE-GRAPH-1`, Luna source/proof intake, parent GRAPH-CONTINUATION-EXTENSION-1:
  begin_local/Frame::Local plus current value/environment lookup must provide
  an explicit committed-cell-to-Graph mapping and publication equations. Minimum
  provisional evidence is a read-only source trace or later authorized bounded
  instrument showing one captured old callback before/after allocation. Falsifier:
  a represented committed old node changes meaning or any captured read uses an
  unresolved cell not covered by the representation. No instrument is authorized
  by this TODO.
- `GCE-NATIVE-SAVED-1`, Luna source/proof intake, RESPONSE-TEMPLATE-1 and original
  safety: stop_unhandled_request/capture_template/enter_template must map the
  full declaration, payload, K and outer suffix, retain old graph content, and
  justify live owner/view restoration. Falsifier: repeated supported template
  replay changes an old captured value or accepts a mismatched full instance.
  The host_write single-use endpoint is explicitly not the repeated-use supplier.
- `GCE-COMBINED-1`, Luna theory intake after lane A acceptance: generalize this
  actual reference/substitution transport and saved protocol to the combined
  handler/graph grammar using the frozen combined raw execution correspondence.
  Falsifier: references under handler/attempt/wait code or propagated request K
  fail composition, typing, or full-instance matching. This requires a new lease
  and dependency authorization; no cross-lane import is made here.

## Dependency and verification receipt

All 121 dependency bytes in the frozen contract were SHA256-inspected with no
mismatches. No Lean, build, tests, checker, Git, nested CLI, external contact or
subagent execution was performed by this author. Python was used only for direct
leased file generation/editing and read-only SHA256 inspection. No scratch files,
background processes or additional paths were created. Source/manual inspection
is not kernel verification or independent review.

| Direct accepted dependency/source | SHA256 |
| --- | --- |
| HigherOrderGraphSyntax.lean | `2dca03ee408f7f35545c02847d03fae47ab1887c2761c82e8b59cc9ad6001886` |
| HigherOrderRecAllocation.lean | `30a6e1855fb8bb4950ad2bdfad238e000554563cb0d1d4b1ec311e3c0cf4f0dd` |
| HigherOrderGraphObservation.lean | `8817db7bc5181481745f49696d7b7d2e4dc927a715353ab83bc36f4ed53420cc` |
| HigherOrderGraphSafety.lean | `de67122c098579b5ba088ff832ef8ca36e233537faf064ab8e36520cf2532533` |
| machine.rs | `b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e` |
| continuation.rs | `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3` |
| Operational paper | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |

Exact source/note hashes, runtime/STOP timestamp and consumed finite budget are
recorded in the sole assignment handoff
`tasks/agent-loop/inbox/20261025-graph-continuation-extension.md`. Next step is
primary-owned kernel checking and fresh independent review of those exact bytes.
Any repair after author STOP creates coauthorship and needs a new reviewed hash.

## Primary elaboration before independent review

Author STOP07:53:04.230399UTC preceded primary source/note takeover07:53:14.962148UTC.
Primary is a contributing coauthor; fresh nonauthor review remains mandatory.
Recorded candidate failures are retained in the sprint verification JSONL.
Mechanical repairs explicitly unfold identity maps, annotate implicit injection
binders, derive the captured-request cast via its actual syntactic equation,
perform constructor inversion without surplus case names, and make the Saved,
heterogeneous Chain indices and Run constructor binders explicit to Lean.
The composed-map equation for the second interaction unfolds the actual chain
and identity constructors. Unused simplifier arguments are removed. These
repairs preserve the declared domains, raw steps, environmental premises,
full operation matching, old-node equations and arbitrary response quantifiers.

Both modules and the joint598-pair public signature/axiom query passed before
this record update. Explicit constructors and structure fields are queried too.
All transitive axioms lie within {propext, Quot.sound}; no Classical.choice,
sorryAx, new axiom or native_decide is used. Final coherent source/note checks
are recorded before fresh independent review. The immutable author handoff
retains original submitted hashes; exact final hashes/review/adjudication are
owned by the sprint outcome receipt.
