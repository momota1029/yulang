# Combined handler graph extension and root interaction

Status: candidate research derivation; author checking and independent review
NOT_RUN. Production authority: none. Contract
`COMBINED-RECURSIVE-INTERACTION-THEORY-20261025/r1`, SHA-256
`16364e08bf9352ecf3d81ff20f672b5c1b0c1a15026511c63253f4111b2b8687`.
Baseline: `d8af06a7e6a9a6d0ba22b887c2dc28ceec9d31d2`.
Author: `/root/handler_graph_extension_interaction_astra_r1`; requested
`gpt-6-astra/medium`, observed model/effort UNKNOWN. Primary `/root` supplied a
simplifier-warning prevention observation; neither producer can independently
certify this result. No descendants.

## Parent claim and application

The original full goal is Yulang Lean proof completion. This packet applies the
accepted combined six-sort raw safety theorem and immutable graph extension
method to the paper's finite external interaction claim (paper lines1139–1159),
retaining shallow-handler K/HK distinctions (399–456) and repeated resumption
(1069–1088). The exact local target is the contract's lane A. The full paper,
source/native correspondence, original Simple-sub A/B and independent F1/FK1
quantifiers remain OPEN.

For arbitrary old/new reference sorts and arbitrary recursive-name sort,
`HandlerGraphTransport` maps every Value, Comp, Handler, ValueArms,
OperationArms and Adapter constructor. Local indices and recursive names remain
distinct from references. The operation instance, receipt, path/view metadata,
mode, all type annotations, arm order and eligibility Bool remain unchanged.
The six typing, identity, composition, local-renaming and substitution laws
handle both operation-arm binders, response binders, lambda mode binders and
outer consumers. They are applied to actual raw execution, not merely retained
as algebraic facts.

`Embedding` requires injective references, exact old types and exact structural
old node equations. Its composition retains these conditions. `map_step` covers
every accepted raw combined transition, including valueRef and operationRef,
all handler and wait propagation, actual lambda/wrap plans, original shallow
continuation arguments and separately forwarded H K. No step gains a typing
premise. `map_prefix` preserves the complete mapped event sequence. Collision
and overwrite rejection follow from the actual embedding fields.

`HandlerGraphInteraction.Saved` contains only operation, payload and continuation.
Its suspended computation is exactly a ROOT request. There is no context field
permitting early capture beneath a handler or wait; three explicit rejection
lemmas distinguish these forms. `capture_typed` inverts actual request typing;
`capture_reached` first consumes accepted finite-prefix preservation.
`Answer.matched` requires full OperationInstance equality. `map_answer` commutes
raw matching/resumption with reference mapping. Response typing remains an
independent hypothesis of the external protocol and is never baked into the
raw answer relation.

`Chain` contains an actual finite sequence of heterogeneous embeddings.
`chain_resume_safety`, `repeated_responses` and `finite_response_family` quantify
over arbitrary final graphs, independently typed responses in those graphs and
all subsequent raw prefixes. A response can mention fresh references absent
from every earlier graph. `saved_after_second` identifies the exact old saved
syntax after another extension. No old-reference response restriction or
single-use hypothesis occurs.

`Run` begins with an empty saved arena. Its only stages are actual internal
Step, publication at a root request, immutable extension and a full-matching
typed answer to any arena entry. Answering retains the entire arena; extension
maps every entry. `run_invariant` derives current and ALL saved typing from the
initial term/graph typing. `run_saved_provenance` reconstructs an actually
reachable origin request and a concrete embedding chain for every entry.
`run_saved_origin_typed` applies that provenance back to the parent invariant,
constructs its publication and derives origin typing from reachability.
`run_all_saved_responses` then proves safety for each old entry and every finite
family of independent responses. `run_answer_twice` constructs sequential reuse.
`run_prefix_safety` and `run_prefix_four` consume the explicit final graph guard
and establish the four actual outer alternatives. WellTyped extension alone is
not asserted to supply that guard.

## Concrete application

Demo starts with a unit node and a root request whose response continuation
calls its callable response. The first actual immutable extension adds a
callable node containing a handler with a value arm that itself requests an
external response. `fresh_response_reaches_request` is a six-step raw trace:
fresh lookup, computation-mode lambda entry, handler return dispatch, value-arm
attempt, wait-request propagation and bind-request propagation. The resulting
`laterSaved` typing is derived from this trace, not assumed.

`later_publication` retains the original entry while publishing the later root
request. A second extension adds a delayed node containing the first callback
reference. `secondResponse` is independently typed callback code that forces
this newest node and invokes the obtained callback. `second_interaction` answers
the ORIGINAL entry, now second in the arena, with this response.
`concrete_run_safe` applies the quantified invariant and final guarded safety
to the full concrete interaction, preserving both saved entries. Distinct
fresh-ref/wrapped responses apply `repeated_responses`. Equal operation IDs and
endpoints with different type arguments are explicitly rejected.

These demo nodes are direct immutable combined graphs, not a source recursive
allocation supplier. The independent B lane and primary joint module own the
arbitrary handler-bearing recursive source RHS construction and its application
as this packet's extension. No new B module was imported or inspected.

## Source/native evidence and remaining premises

Read-only inspection covered these actual owners:

- `runtime/machine.rs::resume_host_write` (599–656) compares the currently
  exposed continuation/operation and host declaration, rejects `saved.resumed`,
  sets it true, allocates a unit response and enters a saved template. This is
  a one-use host-write interface, not the multishot `Run.answer` supplier. Its
  restricted literal response does not establish arbitrary graph-valued response
  typing or an operation-instance readback.
- `runtime/machine.rs::capture_template` (1841–1908) builds immutable template
  nodes from the actual pending suffix and retains declaration/original event.
  `TemplateNode::ForwardHandler` replay (1989–2009) resolves the owner, checks
  activity/current ownership, allocates a fresh occurrence and reinstalls
  CatchReturn. The theory's unchanged handler identity and raw Bool eligibility
  do not prove these native ownership, Grant or activation premises.
- `runtime/continuation.rs::ResumeTemplate` and `TemplateNode` (13–43) retain
  concrete frame, environment, owner and view handles; original_event is kept as
  lineage, not replayed as a new event. No theorem here identifies equal types
  or projected observations with these distinct native lineages.
- `runtime/machine.rs::begin_local` (2500–2546) reserves None and evaluates one
  initializer; the `Frame::Local` return branch (1543–1559) writes Some and moves
  sequentially to the next binding. This does not establish immutable
  simultaneous allocation readback or exclusion of exposed unfilled cells.
- `Frame::CatchReturn` (1097–1135) directly returns an incoming value when there
  is no value arm. Formal valueEmpty produces MatchFailure. Existing
  `HO-HANDLER-VALUE-EMPTY-1` remains OPEN under its original owner.

`NO_SAFE_CODE_SLICE`: the missing native/source suppliers above block dependent
production promotion. No production patch, runtime change, test change or new
semantic decision is proposed. Minimal evidence TODOs, not write authorization:

| ID | Owner and first missing evidence | Exact falsifier |
| --- | --- | --- |
| HG-COMBINED-ALLOC-JOIN-1 | Primary; prove this mapValue agrees with B's simultaneous closure and use B's source-derived typing/guard to build Embedding and Run.extension | A handler arm or captured response binder changes under map/closure, or an old node loses its exact equation |
| HG-ROOT-PUBLICATION-NATIVE-1 | Luna source intake; connect pending suffix capture and root publication to actual propagate_request/capture_template, with full instance and owner data | A published native handle corresponds to a request still under an unprocessed handler, or its operation/owner lineage differs |
| HG-MULTISHOT-NATIVE-1 | Luna native/semantic intake; establish an approved native interface implementing the claimed reusable arena or keep the native theorem separate | The proposed repeated-answer mapping calls resume_host_write twice and its resumed flag rejects the second use |
| HG-ALLOC-READBACK-1 | Existing allocation source owner; relate begin_local/Frame::Local/captured environments to immutable constructed nodes | A claimed represented native path observes None or changes an old represented node |
| HG-HANDLER-METADATA-1 | Existing metadata source owner; provide Grant, full instance and ForwardHandler owner/freshening correspondence | A claimed represented typed execution returns HandlerEvidence or restores a different owner/activation |
| HG-EMPTY-VALUES-1 | Existing HO-HANDLER-VALUE-EMPTY-1 owner; adjudicate the direct native/paper mismatch | Empty value-arm CatchReturn maps native Ret to formal Fail |

Original inference generation, accumulation, propagation, levels, extrusion,
qualifying intrusion and generalization are unchanged. This operational theorem
is no substitute for their source or A/B premises. No withdrawn bypass, foreign
continuation identification or reduced source domain was used.

## Reuse, hashes and validation boundary

Accepted HandlerGraphSyntax/Embedding/Safety supply exactly their combined
finite grammar, typing, actual transitions and guarded finite-prefix theorem.
GraphExtensionTransport/GraphContinuationExtension supply the immutable
embedding and finite-run proof method; their contextual request capture is NOT
reused because combined handlers require root propagation. Historical native
literal/template/cell results are not widened to arbitrary callback readback.
The older independent graph/handler safety theorems are not assumed to compose
without the accepted combined machine.

All136 frozen contract pins were rehashed read-only at08:12:05UTC with zero
mismatches. Relevant direct/source hashes:

| Dependency | SHA-256 |
| --- | --- |
| HandlerGraphSyntax.lean | 2a6b3f455e408336290bbe28616d7db8ee928f1b342b4c80f975bbacb419c24c |
| HandlerGraphEmbedding.lean | 36b616d809554feb585f32203fa72c1a084c7136beb4141a46d3a27a5145f656 |
| HandlerGraphSafety.lean | 554c5a1a003f27c3b8657d77455aa4f5eda7852338254034e3dd63a6db42a558 |
| GraphExtensionTransport.lean | a41bbdb417d3a5f9c1784b690520d5a973d1178c5a1ab47b6b5b80cdd629dac1 |
| GraphContinuationExtension.lean | cae749a64bb641131aa6fdc19a71fe0c635dbe007433556f3dc9efe4388105ec |
| docs/yulang-operational-type-safety-ja.tex | a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b |
| tools/inference-playground/src/runtime/machine.rs | b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e |
| tools/inference-playground/src/runtime/continuation.rs | 194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3 |

Lean/build/tests/checkers/Git: NOT_RUN by the author. Only source reading,
leased file generation and read-only hashes were performed. An initial `python`
invocation failed because that executable was unavailable; it wrote no files,
and file generation then used python3. This was not a failed proof check.
Primary owns elaboration, warning cleanup, public signature/axiom inspection,
strict closure within {propext, Quot.sound}, the B join and fresh independent
review. No candidate is self-certified. Exact final artifact hashes, actual
STOP and finite budget evidence are in the single leased assignment inbox.

Only the four leased paths were created; no scratch paths, descendants,
background processes, compiler files, shared records or configurations changed.
