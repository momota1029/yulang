# Higher-order graph observation and finite execution

Status: candidate research construction, awaiting primary elaboration, axiom
inspection and fresh independent review. Author: /root/higher_order_graph_safety_astra_r1.
No production or native correspondence authority follows from this note.

## Original parent and exact application

The packet is outcome A of GRAPH-HANDLER-INTERACTION-THEORY-20261025/r1,
contract SHA-256 7f9dd634a1a70b082033518d8d46a936fb4e78b1780c4cb373166d72f5a65467,
baseline d94c36b61dc140ba9fa1441c9cab9e0577280392. Its immediate parent is
B-OBSERVE-1: actual typed observation of the full accepted HigherOrderGraph
syntax after source recursive allocation. The original paper locators are
180–196 (guarded graph observation), 258–267 (immutable graph typing), 980–993
(rec allocation), and 1139–1159 (all finite execution prefixes).

The candidate proves the following within the already accepted graph grammar:
for every actual graph, graph typing and accepted transparent-edge guard, every
closed typed graph value has a finite typed observation; every raw internal
step preserves closed computation typing; and every finite raw internal prefix
of a closed typed computation ends typed and has a concrete return, request,
failure or next-step alternative. These quantifiers cover every accepted
Value/Comp/Adapter constructor, including higher-order bodies, consumers,
independent wrapper adapters, and recursive references in code.

`source_rec_execution` applies the result immediately to the actual
`source_rec_allocation` theorem. Inputs are the old graph's typing/guard, common
source recursive RHS derivations, separately typed old captures, the actual
fresh transparent-cycle criterion, and the actual source body derivation.
Outputs include typed observation of every allocated reference and safety of
EVERY finite raw prefix from the actual `sourceCloseComp` body. There is no
per-fresh-node typing premise, fresh numeric rank oracle, or dynamic rec rule.
`finite_source_rec_execution` supplies the old guard from its finite NoCycle
criterion. `named_rec_execution` covers explicit old references in source RHS
code under the accepted explicit-name syntax.

The original full-paper theorem remains OPEN. This packet does not combine
handler and graph syntax, implement recursive μ types or type-changing roll,
cover every omitted paper form, or prove native readback/lifecycle semantics.
It proves internal prefix safety after actual immutable allocation. The local
response/context substitution theorem retains arbitrary independently typed
responses and arbitrary typed outer evaluation contexts, but does not pretend
to prove graph extension plus externally scheduled repeated interaction.

## Constructive observation

`ObservedTyped` is a finite derivation over the actual graph values. Reference
observation reads `graph r`; a view retains its occurrence; both/intersection
retains TWO observations of the same underlying value; top retains its actual
introduction; and wrap retains the original input/output adapters and their
inner/outer callable types. A wrapper from callable A B to callable C D never
claims that its inner callable has type callable C D. Lambda/delay/data stop
transparent observation and retain the real typed code or payload.

`observe_from_references` performs finite structural descent through actual
wrapper syntax. `typed_observation` supplies the reference case by induction
on the accepted guard rank bound. Its only edge conversion is the accepted
`projection_edge` equation; projection's Node.unit is ONLY a rank token, never
a canonical higher-order unit or a value-typing supplier. Both premises descend
independently; no intersection witness is discarded or merged.

`Head` is independent raw reference/view lookup. The typed thunk, callable,
union, intersection and top suppliers derive concrete introduction witnesses
through that lookup. Callable terminals keep lambda mode/body/consumer or the
complete wrapper and distinct adapter typings. `ObservedTyped.bottom_empty`
and `bottom_empty` exclude closed bottom inhabitants under exactly the graph
premises. Ref-type equalities are explicit in canonical inversions so that an
arbitrary Xi(r) is not treated as an injective syntax constructor.

The chain example follows a view/reference chain to `.both (.inLeft .unit)`
and retains its two different union typings. A separate wrapper example uses
unit→unit internally and bool→bool externally, and observes that callable
under top. The delayed self-reference example observes a genuine recursive
computation without claiming its body terminates. The previously accepted
actual source alias self-cycle rejection remains applicable unchanged.

## Independent raw execution and preservation

`Safety.Step` contains no typing, guard, canonical-form or safe-body premise.
Reference eliminators actually replace `.ref r` with `graph r` and record the
reference. Views have explicit steps. Lambda entry reconstructs the original
value/computation-mode conventions: value entry forces the delayed carrier,
computation entry substitutes the carrier itself, and the designated result
consumer belongs to its independent outer scope. Wrap input adaptation occurs
inside the delayed carrier and output adaptation runs after the inner result.
Raw entry events retain the complete lambda/adapter plans as data.

All accepted computation forms are covered. Return is terminal; request and
failure are explicit suspensions through finite bind/scope/expose contexts;
force, union and intersection eliminators execute their actual introductions;
absurd cannot be reached typed under the graph guard. Its raw reference/view
rules nevertheless have no typing premise. Bind evaluates only its first
computation; code bodies and response binders execute only on actual entry.

The candidate `preservation` theorem requires WellTyped but no Guarded premise.
The graph is immutable, and each actual lookup uses the declared reference type
and its original node typing. Closed progress additionally consumes Guarded
through typed observations and bottom exclusion. `trace_preservation` and
`finite_prefix_safety` quantify over every raw Steps derivation, without a
termination hypothesis. `progress_four`, `returned_no_step`,
`requested_no_step` and `failed_no_step` distinguish terminal alternatives from
actual transitions. Request decomposition and `request_context_typing` retain
the actual operation instance, payload, original response binder, and outer
context; `resume_in_context_typed` keeps the response independently quantified.

`force_observation_execution` additionally realizes a supplied thunk lookup as
an actual finite raw sequence of reference/view steps followed by force.

## Actual source constructions

`Examples.mutual_two_entries` uses the accepted `mutualRhs` allocation, not a
pretyped fresh-node oracle. Five raw steps enter one source lambda, consume its
shared old capture, look up the other allocated lambda, and enter that lambda
while retaining the first result consumer. Recursive consumer accumulation is
visible. `mutual_all_prefixes` applies `source_rec_execution` to the actual
source dynamic call and proves its arbitrary finite prefixes safe, not merely
the five displayed transitions.

`request_two_steps` forces the accepted allocated `responseRhs`. The resulting
request has the original operation instance, the shared old payload reference,
the recursive reference under the response continuation, and the unchanged
response index under its local bind. `request_all_prefixes` derives safety from
the actual source RHS/body/capture/guard premises. These are theorem instances;
the author did not run them as tests or claim native traces.

## Source/native boundary and implementation TODO

Read-only source inspection found two concrete incompatible lifecycle owners:

- `Machine::begin_local`, runtime/machine.rs 2500–2545, allocates a mutable None
  cell, extends the environment early for a recursive binding, schedules its
  initializer and applies initializer environment state.
- `Frame::Local`, runtime/machine.rs 1498–1560, publishes the received current
  value/dispatch/view into that cell and proceeds to the next binding.

These are actual producers/consumers, not the immutable simultaneous allocation
constructor proved here. Native execution also needs a relation for closure
captures, uninitialized reads and shared cell identity. Neither the raw graph
Step nor the source prefix-splitting equations establish that relation.
NO_SAFE_CODE_SLICE: the present packet is implementation-independent theory;
these owners have neither a proved complete realization relation nor a
production write lease in this packet.

A-NATIVE-1 / ENV-GRAPH-1, owner Luna/source intake: the minimal proposed
provisional instrument records allocated cell/binder identity, publication,
captured environment identity and actual lookup value while preserving explicit
uninitialized reads. Inputs are these exact owner paths and existing native
closure/environment evidence; proposed output is a source-qualified lifecycle
trace and a realization invariant. Falsifier: a captured read is uninitialized,
a current cell differs from its immutable readback, sharing yields inconsistent
types, or sequential initialization is asserted simultaneous without proof.
This is a TODO for later authorized work, not permission to edit production.

A-COMPOSE-1, owner Luna/theory intake: supply a single combined handler+graph
syntax and actual operations, preserving both accepted standalone embeddings,
before using this internal graph theorem for handler arena interaction.
Falsifier: a handler payload, response, saved continuation or adapter can contain
a graph reference that the proposed combined syntax/typing fails to represent.
HO-HANDLER-GRAPH-COMPOSITION-1 remains OPEN.

A-PAPER-1, owner full-paper theory intake: preserve the original paper's omitted
μ/roll, polymorphism and other forms; provide their actual source/operational
typing cases. Falsifier: an accepted paper term lacks a faithful translation or
a type-changing evidence wrapper is transported as type identity. OPEN.

A-CHECK-1, owner primary: serialize elaboration of the frozen bytes, query every
public declaration and full transitive axiom closure, then assign an eligible
fresh reviewer. Falsifier: failure to elaborate, omitted accepted constructor,
incorrect binder scope, forbidden axiom, hidden typing/canonical premise in raw
Step, changed guard/domain, or invalid reuse of a premise outside its source.
The author is not eligible to independently certify this result.

## Prior work, dependencies and resources

Reused within their exact premises: HigherOrderGraphSyntax structural substitution;
HigherOrderRecAllocation actual source construction, captures and allocation;
FiniteGuardDecision only for the projected transparent-edge criterion/rank;
and HigherOrderEntry/HigherOrderSafety as proof patterns reconstructed for graph
syntax with explicit new lookup cases. Restricted GuardedValueGraph NodeTyped,
transparent_type and canonical theorems are NOT reused as full higher-order
value-typing evidence. The old projection-only canonical shortcut remains
invalid for both/top/wrap and was not reinstated.

The entire 109-entry frozen dependency table was compared by read-only SHA-256
and matched. The exact table is preserved in the assignment inbox. Principal
inputs include:

- HigherOrderGraphSyntax.lean: 2dca03ee408f7f35545c02847d03fae47ab1887c2761c82e8b59cc9ad6001886
- HigherOrderRecAllocation.lean: 30a6e1855fb8bb4950ad2bdfad238e000554563cb0d1d4b1ec311e3c0cf4f0dd
- FiniteGuardDecision.lean: a9924ab2c8d96a173c886ddfbb2580a7719fbf08064d9f85d0644784778de9fa
- HigherOrderSyntax.lean: ea727d33692bdcbe6b40245b960d01225b556b5334ffab649eea2699930d5972
- paper: a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b
- runtime/machine.rs: b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e

Author Lean/build/tests/checkers/axiom inspection: NOT_RUN. A first attempt to
invoke the file-writing interpreter `python` found no executable; the leased
file write subsequently used python3. This was not a checker or model launch.
Manual reasoning/source reads and SHA comparisons are not independent review.
No sorry, new axiom, Classical.choice or native_decide is intended. Actual
transitive axiom evidence belongs to primary verification.

Requested route: gpt-6-astra / medium; observed model/effort: UNKNOWN. The fixed
author resource grant is 1200 seconds from acknowledgement, with conservative
predispatch bound 2026-10-25 07:26:52.675914 UTC. No descendants, nested CLI,
external contact, production/config/semantic edits, or Git operation occurred.
Only the two leased Lean files, this note and the assigned inbox are written;
there are no scratch paths. The final inbox supplies byte hashes, elapsed/STOP
receipt and all dependency pins. No background process remains after author STOP.

Simple-sub generation, accumulation, propagation, levels, extrusion, qualifying
intrusion and generalization remain unchanged. F1/FK1 and foreign-continuation,
residual/provider/witness lineages are not collapsed by this graph result.

## Primary coauthorship and verification freeze

Primary acknowledged the author's final STOP and source/note takeover at
07:34:33.656964 UTC. Primary coauthorship: the six observation inversion proofs
now use explicit induction on their finite ObservedTyped derivations after
reverting the target-type equality. The raw force-observation realization proof
uses explicit induction with a generalized head target and equality. This makes
the existing structural argument visible to Lean; no syntax, raw transition,
theorem premise, conclusion or source domain was changed.

The original author inbox and its original candidate hashes remain byte-frozen.
The three modules have passed serialized Lean elaboration; the combined query
covers223 explicit named module declarations plus8 named query constructions,
and8 additional anonymous applications. All231 emitted transitive axiom closures
are contained in {propext,Quot.sound}. Earlier failed attempts remain recorded.
The additional graph examples execute both projections through the same actual
view/reference chain, retain distinct union results, execute a guarded delayed
self-loop, and type an actual wrapper step with distinct inner/outer callable
types. Handler examples complete both response values, reject direct publication
under a handler and reject an uninhabited bottom response.

Final source/note-bound rebuild and fresh nonauthor review remain required before
acceptance; exact receipts/adjudication are owned by the sprint outcome. Primary
is a coauthor and is not an independent certifier. Current module SHA-256:

- `HigherOrderGraphObservation.lean`: `8817db7bc5181481745f49696d7b7d2e4dc927a715353ab83bc36f4ed53420cc`
- `HigherOrderGraphSafety.lean`: `de67122c098579b5ba088ff832ef8ca36e233537faf064ab8e36520cf2532533`

Graph Step deliberately represents request/failure suspension under a finite
bind/scope/expose evaluation context, as the accepted pre-handler graph value
projection does. Its four alternatives explicitly expose that context; they
are not root-only handler propagation rules or a full-paper machine simulation.
The independently proved handler arena uses its own actual root propagation.
Their combined language/operational correspondence remains an explicit OPEN
composition obligation; these two theorems cannot be silently interchanged.
