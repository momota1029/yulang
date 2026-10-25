# Combined higher-order handlers and guarded value graphs

Status: research construction elaborated by primary; fresh independent review
pending. Exact final acceptance belongs to the sprint outcome receipt. Production authority: none. Parent:
`HO-HANDLER-GRAPH-COMPOSITION-1`, paper guarded values 180–196, recursive
allocation 980–993, shallow handlers 399–456, local preservation 1069–1088,
and safety 1139–1159. The original paper theorem and Simple-sub A/B, F1/FK1
quantifiers remain OPEN.

Contract: `HANDLER-GRAPH-EXTENSION-THEORY-20261025/r1`, SHA-256
`b0b9f069dc8f08ed5f87a26b37d98df404e5a9dd4f0628244adc79095634a9e8`.
Author: `/root/handler_graph_composition_astra_r1`; primary `/root` supplied the
wait-result reference coverage reminder and cancellation-hypothesis shadowing
repair observation. Neither is eligible to independently certify this packet.
Requested model/effort: `gpt-6-astra/medium`; observed model/effort: UNKNOWN.
No descendants, additional dependencies, scratch paths, compiler changes or
production semantic decisions.

## Original claim and candidate application

The parent needs one actual syntax and execution relation supporting both
accepted languages simultaneously. Separate safety theorems were insufficient:
the old graph machine suspends requests/failures inside finite evaluation
contexts, while the old handler machine propagates them to the root. The new
candidate constructs the shared grammar, derives finite observations from the
actual graph typing and guard, and proves preservation and root-only progress
for every finite raw internal prefix. It then connects both old machines and
consumes the actual old recursive allocation supplier under an independently
typed combined handler.

`HandlerGraphSyntax` has six mutually recursive sorts: Value, Comp, Adapter,
Handler, ValueArms and OperationArms. Every accepted Graph and Handler
constructor is represented structurally. References, recursive names and local
indices remain distinct. Lambda bodies, outer result consumers, adapter input
bodies, request response binders, value-arm binders and both operation-arm
binders contain the full combined language. The existing Ty, modes, operation
instances, literal payloads and all metadata fields are reused unchanged.
Extrinsic typing and structural renaming/substitution cover every constructor.
The six cancellation lemmas justify substitution after binder insertion; they
are applied to the actual context resumption equation.

`HandlerGraphEmbedding` recursively embeds both old languages in arbitrary
typing contexts. Its renaming/substitution commutation lemmas are consumed by
actual old-step simulation. `liftGraph_typed` derives new node typing from old
node derivations. `liftGraph_projection` proves exact equality of the guard
projections, so `liftGraph_guard` transports the existing guard. Projected unit
is only a stopping token; it supplies neither typing nor a canonical value.

`HandlerGraphSafety` derives `ObservedTyped` from actual node typing and the
transparent successor rank. Intersection has two separate premises, top retains
its underlying type witness, and wrap retains different inner and outer callable
types and both adapters. No typing premise occurs in `Step`. Lookup is explicit
for force, union/intersection elimination, absurd and dynamic call, and also for
references returned as No/Yes carriers inside both kinds of wait. The machine
retains all shallow-handler trial, ordering, skipping, nesting, propagation and
restoration rules. The selected arm receives the original K:Q→A; only exhaustion
constructs the shifted handler around K, yielding H K:Q→B. Eligibility remains
raw Bool data, with no native permission adequacy claim. `preservation` assumes
actual closed graph typing; `closed_progress` additionally consumes the guard.
`finite_prefix_safety` quantifies over every raw finite internal trace.

`HandlerGraphCorrespondence.graph_step` and `handler_step` map every old raw
step, actual event and complete lambda/wrap entry plan. Their finite trace
versions preserve event order. `propagate_graph_request` and
`propagate_graph_failure` construct finite sequences through every old context;
`graph_suspended_root` consumes the old full suspension decomposition.
`graph_request_correspondence` retains the identical full operation instance and
payload and derives the resulting continuation typing from the old contextual
computation typing plus actual propagation. `graph_resume_equation` states that
substituting any combined response into the propagated continuation equals the
same outer context around the original response-substituted K.
`old_graph_resume_equation` further identifies this with the embedding of the
old resumed contextual computation. `graph_resumption_safety` applies the
supplier to arbitrary independently typed responses and every subsequent
internal prefix, without consuming the saved code or imposing linear use.

`source_rec_under_handler` calls the exact accepted `source_rec_allocation`,
lifts its actual allocated graph and closed body, derives combined typing and
guard, and establishes every finite prefix under an independently typed combined
handler. Its only fresh guard premise is the old actual `FreshNoCycle`; no new
fresh-node typing or rank supplier is introduced. `SourceExample` starts with
an empty old graph, closes a genuinely recursive source lambda with a request
and self-call in the response continuation, gives the exact allocated-node
equation, and executes its request through handler selection. `Examples` also
executes a recursive graph lambda through a graph-backed attempt/wait result,
and a nested request followed by restoration, reference lookup and Yes return.
The examples supplement the quantified statements.

## Reused evidence and exact open boundaries

The accepted Handler syntax/substitution/trial construction and Graph
syntax/allocation/observation construction are reused within their actual finite
constructor domains. Their independent safety conclusions were not assumed to
compose. The previous contextual graph terminal convention is not reused as
combined root progress. Literal readback, template replay, closure environments
and historical Call proofs are not treated as universal higher-order native
readback or metadata suppliers. No failed or withdrawn Simple-sub bypass is
restored. No residual, provider, witness or foreign-continuation lineage is
identified by this construction.

The original paper remains OPEN for omitted μ/type-changing roll,
polymorphism, mapop, primitive and other forms. This packet does not allocate
arbitrary new combined handler-valued RHS simultaneously: it embeds the actual
accepted old RHS allocation and permits independently typed combined handlers
around its body. Combined external responses carrying fresh graph extensions
remain a future integration with the independent extension lane; no cross-lane
import is assumed. Live metadata, grants, activation/owner freshening and full
source/native correspondence remain OPEN. The internal safety candidate does
not imply F1, FK1, inference soundness/principality or production adoption.

## Source/native audit and mutual TODOs

`tools/inference-playground/src/runtime/machine.rs` was inspected at these
actual owners:

- `begin_local` (2500) allocates an empty cell, extends recursive environments
  before evaluating the initializer, and pushes `Frame::Local`. The return
  branch (1498) installs the received value into that cell. The proof's immutable
  finite graph allocation is not an established readback of every such native
  execution or arbitrary initializer.
- `propagate_request` (2081) examines the installed CatchReturn delimiter,
  validates its installation, resolves declarations and demands a local Grant
  unless the closed primitive certificate applies. A Bool arm flag is not a
  proof that these live checks succeed.
- `TemplateNode::ForwardHandler` replay (1989) resolves and validates the owner,
  allocates a fresh handler occurrence, and installs CatchReturn. The finite
  syntax retains identity/metadata but proves no activation freshness or owner
  adequacy theorem.
- `Frame::CatchReturn` (1097) returns the incoming value when no value arm exists.
  The accepted paper empty value trial fails with MatchFailure. Existing
  `HO-HANDLER-VALUE-EMPTY-1` remains OPEN; no identity-arm normalization or runtime
  defect verdict is inferred.

`NO_SAFE_CODE_SLICE`: these owners need the missing source/readback and semantic
premises before any dependent production patch. No compiler edit is proposed.
The following requests specify evidence, not permission to write or run:

| Request | Owner / first missing evidence | Exact falsifier |
| --- | --- | --- |
| HG-ALLOC-READBACK-1 | Luna/native source intake; map actual begin_local/Frame::Local cells, captured environments and accepted recursive RHS code to the immutable allocation and prove all reachable supplier premises | An accepted recursive initializer/capture path has no typed graph readback, or exposes an unfilled cell along a claimed represented path |
| HG-HANDLER-METADATA-1 | Luna/metadata source intake; supply full operation-instance, Grant, installation and owner-freshening correspondence for propagate_request and ForwardHandler | A claimed represented typed execution returns HandlerEvidence or violates restored owner/activation identity despite the proposed supplier premises |
| HG-EMPTY-VALUES-1 | Existing HO-HANDLER-VALUE-EMPTY-1 owner; resolve native no-arm return versus paper MatchFailure under approved semantics | Direct mapping of an empty value-arm CatchReturn yields Ret natively and Fail formally |
| HG-EXTENSION-INTEGRATION-1 | Luna future proof intake; transport the independent extension construction through the complete six-sort grammar and saved combined waits | An old saved handler-bearing continuation loses typing or changes its old node/operation identity after an admitted fresh extension |

These requests preserve original owners and quantifiers. No local frame action
is offered as a replacement for the independently quantified foreign continuation
obligation. Primary elaboration and fresh independent review are the immediate
next steps for this candidate, before any finite-domain theorem acceptance.

## Frozen dependencies and checking boundary

Baseline: `7ff6e74d4515099bdb13e1cbf20fc38257cb2e36`. All 121 exact contract
pins were rehashed read-only at 07:50:53 UTC; no mismatch. Governing source pins:

| Dependency | SHA-256 |
| --- | --- |
| HigherOrderHandlerSyntax.lean | 4578e2d3c8b06a57937dd652e06eabb8c9271113a7eb3388dc718856d64b249d |
| HigherOrderHandlerSafety.lean | f74c35666d8f4f5ab1af52009c005d5cb0be9958f7f8d64185c31750b2dd38ef |
| HigherOrderGraphSyntax.lean | 2dca03ee408f7f35545c02847d03fae47ab1887c2761c82e8b59cc9ad6001886 |
| HigherOrderRecAllocation.lean | 30a6e1855fb8bb4950ad2bdfad238e000554563cb0d1d4b1ec311e3c0cf4f0dd |
| HigherOrderGraphObservation.lean | 8817db7bc5181481745f49696d7b7d2e4dc927a715353ab83bc36f4ed53420cc |
| HigherOrderGraphSafety.lean | de67122c098579b5ba088ff832ef8ca36e233537faf064ab8e36520cf2532533 |
| docs/yulang-operational-type-safety-ja.tex | a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b |
| tools/inference-playground/src/runtime/machine.rs | b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e |

All other direct/transitive frozen dependencies retain their exact contract table
hashes. The final inbox freezes the four module hashes and this note hash.
Author checks: Lean/build/tests/checkers/Git NOT_RUN. Read-only source inspection
and byte hashes only. Primary owns complete elaboration/signature/axiom receipts,
strict axiom closure within {propext, Quot.sound}, and independent review.

## Primary elaboration before independent review

Author STOP07:52:21.474671UTC preceded primary source/note takeover07:52:41.503862UTC.
Primary is a contributing coauthor and cannot supply independent certification.
Recorded Lean calls1–16 include the original candidates and every failed attempt.
The accepted statements and raw transition premises are retained. Mechanical repairs:
`liftGraph_projection` closes its final reflexive equality explicitly; two
`up_typed` calls use the actual `env` named parameter; request correspondence
unfolds both extensionally identical empty-name environments; the concrete
example graph constant is renamed `exampleGraph` to avoid a section-variable
name collision; two concrete traces are supplied as complete constructor terms;
one case layout is corrected. Unused simplifier arguments are removed rather
than disabling warnings. No constructor, typing rule, response quantifier,
source allocation premise, native boundary or theorem domain is weakened.

All four modules and the joint598-pair public signature/axiom query passed before
this record update. The query also includes explicit constructors and structure
fields. Its axiom closure is within {propext, Quot.sound}, with no Classical.choice,
sorryAx, new axiom or native_decide. A final coherent source/note re-elaboration
is recorded in the sprint verification JSONL before fresh nonauthor review.
The immutable author handoff preserves the original submitted hashes; the final
review snapshot and adjudication are in the sprint outcome, not inferred here.
