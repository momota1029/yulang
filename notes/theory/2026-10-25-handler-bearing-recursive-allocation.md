# Handler-bearing simultaneous recursive allocation

Status: candidate constructive mathematics; author Lean/build/checker/tests NOT_RUN.
Fresh independent review and primary kernel verification are required. This note
confers no native correspondence, semantic adoption, or production authority.
Assignment: COMBINED-RECURSIVE-INTERACTION-THEORY-20261025/r1, lane B.
Author: `/root/handler_bearing_recursive_allocation_astra_r1`; requested
`gpt-6-astra/medium`, observed model/effort UNKNOWN. No descendants or coauthors
of this new module at author freeze; primary supplied integration requirements.
Baseline: `d8af06a7e6a9a6d0ba22b887c2dc28ceec9d31d2`.
Contract SHA-256: `16364e08bf9352ecf3d81ff20f672b5c1b0c1a15026511c63253f4111b2b8687`.

## Parent and actual application

The original recursive-allocation obligation is the immutable graph extension
lemma in `docs/yulang-operational-type-safety-ja.tex:980`, with guarded source
values at line180, shallow handlers at399 and arbitrary finite interaction
safety at1139. Its fresh nodes must be typed by simultaneous substitution of
actual RHS derivations, and the body must use the same closure. The full paper
and original inference A/B, F1/FK1 remain OPEN. This packet supplies the
allocation side in the already accepted combined six-sort grammar; the primary
owns its composition with arbitrary saved-entry interaction and independent
responses. One selected arm action is not a proof about foreign continuations.

`source_rec_allocation` quantifies over arbitrary old reference type R, finite
n (including zero), old graph and types, every RHS family, every outer context,
all independently typed old captures, and every source body/type. Its hypotheses
are old graph typing and guard, actual source RHS typing in sourceContext,
old-capture typing, absence of fresh transparent cycles for the ACTUAL closed
RHS family, and source body typing. It derives every fresh typing, allocated
graph typing/guard and closed body typing. No fresh typing or numeric fresh
rank is supplied. `source_allocation_typed` exposes the guard-independent typing
supplier needed for the primary immutable-extension composition.

`source_rec_finite_prefix_safety` immediately consumes those suppliers in the
accepted combined raw `finite_prefix_safety` theorem. For every raw Prefix from
the actual closed source body in its allocated graph, its endpoint has the
original result type and CanProgress. `source_rec_closed_progress` supplies the
zero-step case. No Step is filtered by typing, bounded to a selected trace, or
assumed to have been emitted by a native constructor. The explicit attempt
example also applies this quantified theorem to a real three-step prefix.

## Exact source representation and binder laws

The source is `HandlerGraph.Value/Comp R Empty` and the corresponding Handler,
ValueArms, OperationArms and Adapter sorts. Ordinary source recursive names are
local variables in the nearest n-slot `sourceContext nu env` prefix; ordinary
outer variable i occupies n+i. Existing `.ref r` values retain xi typing.
This is the exact research source domain, not an assertion that HIR already
uses these de Bruijn indices or that all full-paper constructors are represented.

`inject*` embeds the impossible Empty recursive-name sort while preserving old
references. `split*` uses the accepted local substitution to move precisely the
recursive prefix into `.recvar (Fin n)`; ordinary binder lifting remains the
existing six-sort lifting. `closeNames*` changes old refs to inl and recursive
names to inr simultaneously. `close*` then substitutes separately old-typed
captures. Each stage has typing derivations for all six sorts, and every sort
has a `sourceClose*_typed` law.

The six `closeNames*_rename` and six `closeNames*_subst` laws commute closure
with local renaming/substitution. Lambda parameters, adapter input, bind/union
arms, value-arm payloads, and request responses lift once. Operation-arm
payload0/originalK1 lift twice. waitOperation's original K lifts once under its
own response binder; the attempt and remaining arms retain their proper outer
scopes. Constructor equations `close_operation_arm`, `close_waitOperation`,
`close_waitValue`, `close_lambda`, `close_adapter`, and `close_request` expose
these cases. `split_arm_payload`, `split_arm_originalK` and
`split_arm_recursive` fix the two local slots and recursive offset explicitly.
`closeNames_continuation` maps original K without installing a handler;
`closeNames_forwarded` separately maps HK with its reinstated shifted handler.

`sourceClose_old_ref`, `sourceClose_recursive` and `sourceClose_outer` distinguish
all three source cases. Shared capture equality remains shared after closure;
old node values and types are exactly mapped, old nodes gain no fresh edge,
and Sum constructors prove old/fresh disjointness and fresh-name injectivity.
No residual/provider/witness lineage is collapsed.

## Constructive guard and examples

The accepted HandlerGraph frontier/projectGraph are used unchanged. Inspection
traverses both/top/view/wrap; actual data introductions, lambda and delay stop
it. `frontier_closeNames`, `next_mapOld`, `projectNode_map` and
`project_allocation` establish exact equations from the actual syntax to the
accepted guard projection. The projection's unit token is only a termination
marker; actual lambda/delay/handler code is retained in the allocated graph.

`FreshNoCycle` is finite absence of a transparent cycle in the projected actual
fresh family. `freshNoCycleDecidable` invokes the constructive finite decision
procedure without requiring equality on old references. `allocationGuard`
computes the required fresh ranks through the accepted finite construction;
`allocation_guard_iff` establishes necessity as well as sufficiency given the
old guard. Fresh-to-old edges and shared aliases are admitted.

The Examples namespace includes:

- two mutually recursive computation lambdas with real request-bearing handlers,
  opposite recursive calls and one old capture shared by body/result consumers;
  `mutualFresh_equation` gives their actual allocated syntax;
- `attempt_prefix`, an actual handleReturn/valueCons/valueRequest trace from a
  source-closed body, and `attempt_prefix_safe` applying the parent result;
- an operation arm using originalK1 after capture bind and response bind,
  with an exact closure equation retaining payload/K order;
- an actual handler-bearing delayed RHS retaining its recursive ref beneath a
  response and bind, its typing, no-cycle proof and actual allocation theorem;
- two fresh aliases that share the same old reference, with actual allocation;
- typed direct, top-evidence and callable-wrapper self aliases whose actual
  transparent cycles are rejected. Typed syntax alone never implies a guard.

These declarations are candidate formal evidence pending primary elaboration,
not executed tests or independently reviewed proofs.

## Native owners, missing evidence and NO_SAFE_CODE_SLICE

Read-only inspection covered at least two real owners, with immutable hashes
below. `program.rs`'s source ownership walk at600–650 marks a parameterized local
initializer recursive when an active local Name is encountered; LocalBinding
construction at748–764 installs that flag. `machine.rs::Machine::begin_local`
at2500 reserves one None cell and conditionally extends its initializer
environment. `Frame::Local` at1500–1560 sequentially installs Some and continues
the block. `Instruction::Lambda` at864 captures its current environment;
`Machine::lookup` at2585 and `extend` at2626 preserve native binder/cell lookup.
These facts do NOT establish the simultaneous finite-family equations above.

`receiving.rs::Receiving::delay` at208 retains inherited image/unknown metadata;
`Receiving::enter` at224 mints an invocation boundary and links the older image.
The formal closure retains supplied view/receipt data but supplies no theorem
that these native fields instantiate the formal annotations or fresh owner
bindings. Native grant/eligibility, handler empty-arm directmapping and one-use
host resume remain the accepted explicit gaps.

NO_SAFE_CODE_SLICE: this research packet authorizes no production change.
The first missing native equation is simultaneous source recursive-name/capture
readback versus the actual sequential cell/environment construction. A minimal
future provisional instrumentation TODO would expose the resolved binder IDs,
reserved cell identities, initializer capture environment and installed values
at `program.rs` LocalBinding plus `begin_local`/`Frame::Local`/Lambda/lookup.
Its exact falsifier is a research simultaneous family whose required sibling
reference lacks a native cell/environment entry, changes an old node, or maps
two reads of the same captured binder to different cell identities. Any such
instrumentation needs Luna's separate exact lease; none is implemented here.
A separate metadata correspondence TODO has the falsifier that delay/entry
image, receiver or receipt identity differs from the formal retained annotation.

No constraint-generation/accumulation, propagation, levels, extrusion,
qualifying intrusion or generalization behavior changed. No withdrawn bypass
or ordinary-inference restriction was reintroduced. Full-paper records,
constructor families, polymorphism, type-changing roll/effect transforms and
native source typing remain open at their existing owners.

## Reuse, handoff and validation

The prior HigherOrderRecAllocation construction supplies the prefix/old-capture/
Sum-allocation/projection proof pattern within its original three-sort premises
(author `/root/higher_order_rec_rhs_astra_r1`). Its old theorem is not applied to
handler syntax. All handler-bearing cases are newly constructed over accepted
HandlerGraph syntax (prior author `/root/handler_graph_composition_astra_r1`,
primary `/root` repairs recorded in the prior outcome). FiniteGuardDecision's
constructive no-cycle/rank theorem is reused only on the exact projected graph
(prior author `/root/finite_guard_completeness_astra_r1`). Existing combined
safety is reused only with the graph typing, guard and closed typing derived
here. Separate old-graph extension or handler simulations are not treated as
full combined allocation or native adequacy.

Primary TODO B-JOIN-1: establish equality of A's full six-sort transport with
Recursive.closeNames on Empty names, derive the actual immutable allocation
embedding and apply it to old saved entries and independently typed responses.
The planned repeated-response/second-extension trace remains the primary's
leased output. Falsifier: old node mutation, changed binder order, loss of an old
saved handle, or a sourceFresh response replaced by an arbitrary pretyped node.
Primary TODO B-VERIFY-1: elaborate every public declaration, inspect allowed
axiom closures, repair within explicit takeover after author STOP, and obtain a
fresh nonauthor review. Author/coauthors cannot certify this candidate.

Checks: Lean/build/tests/checkers/Git NOT_RUN by author. Read-only text and
SHA-256 inspection only. All writes are the three exact leases; no scratch,
background processes or descendants. Requested/observed settings remain
separate; no model switch or resource extension is asserted. The exact runtime
and freeze receipt is the one leased inbox file. Once frozen the author stops
writing; further repairs belong to primary takeover or a new explicit grant.

## Frozen module and direct dependency hashes

Module SHA-256: `5563163a5fe2741dc4cb1968329e5ec417a170099448978b653dc487cd136dfd`.
The contract pins all136 dependencies; primary reported its136/59chains/12receipt
preflight. The author directly inspected and hashed the following subset:

| Path | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/HandlerGraphSyntax.lean` | `2a6b3f455e408336290bbe28616d7db8ee928f1b342b4c80f975bbacb419c24c` |
| `notes/theory/lean/YulangClosure/HandlerGraphEmbedding.lean` | `36b616d809554feb585f32203fa72c1a084c7136beb4141a46d3a27a5145f656` |
| `notes/theory/lean/YulangClosure/HandlerGraphSafety.lean` | `554c5a1a003f27c3b8657d77455aa4f5eda7852338254034e3dd63a6db42a558` |
| `notes/theory/lean/YulangClosure/HandlerGraphCorrespondence.lean` | `94a6c2d24045bf9959121f4b31efea2f0630abc53c5bb776ab356d3ff108f964` |
| `notes/theory/lean/YulangClosure/HigherOrderRecAllocation.lean` | `30a6e1855fb8bb4950ad2bdfad238e000554563cb0d1d4b1ec311e3c0cf4f0dd` |
| `notes/theory/lean/YulangClosure/FiniteGuardDecision.lean` | `a9924ab2c8d96a173c886ddfbb2580a7719fbf08064d9f85d0644784778de9fa` |
| `tools/inference-playground/src/runtime/machine.rs` | `b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e` |
| `tools/inference-playground/src/runtime/program.rs` | `6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907` |
| `tools/inference-playground/src/runtime/receiving.rs` | `57b1664e26f137e6425731dde2bb1f1559170d9914f5be7a0f17fae3a8555e26` |
