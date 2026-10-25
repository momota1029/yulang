# Independent review: HG-COMPOSITION-20261025 / revision 1

Verdict: **CLEAN for fixed outcome A and its explicitly bounded research domain**.
No blocking or nonblocking defect found in the frozen artifact. This recommends
finite-domain acceptance by the primary; it does not close the original full
paper, source/native, Simple-sub A/B, F1/FK1 or production gates.

## Identity, authority and independence

Reviewer: `/root/handler_graph_composition_review_astra_r1`, fresh NONAUTHOR.
Session: `HANDLER-GRAPH-EXTENSION-THEORY-20261025/root-r1`.
Requested model/effort: `gpt-6-astra/medium`; observed model/effort: UNKNOWN.
First own clock and ACK: 2026-10-25 07:59:48 UTC; actual spawn acknowledgement
exact timestamp is not exposed to this reviewer. Conservative absolute STOP:
08:09:30 UTC; grant 600 seconds, no renewal.

Contract: `tasks/agent-loop/sprints/handler-graph-extension-theory-20261025-r1.md`,
SHA-256 `b0b9f069dc8f08ed5f87a26b37d98df404e5a9dd4f0628244adc79095634a9e8`.
Baseline: `7ff6e74d4515099bdb13e1cbf20fc38257cb2e36`.
Parent: HO-HANDLER-GRAPH-COMPOSITION-1; paper guarded values 180–196,
recursive allocation 980–993, handlers 399–456 and safety 1139–1159.
Read root AGENTS.md, preserved base, current state/README, sprint/proof skill
contracts, design authority, selected contract and relevant original sources.
Authors remain author agent plus contributing primary. Neither supplies this
independent verdict. Only write lease: this report. No descendants or other contacts.

## Semantic review and attempted falsifiers

1. **Grammar and binders.** HandlerGraphSyntax.lean:14–137 defines actual six-sort
   syntax and extrinsic typing. References, recursive names and local indices
   are separate constructors. All Graph and Handler constructors are retained,
   with full combined code beneath lambda, adapter, request, arm and wait nodes.
   Lambda body and consumer use different binder treatment; operation-arm
   payload/continuation use two lifts; saved operation K uses one response lift.
   Renaming/substitution and their mutual typing proofs at 146–414 preserve
   these distinctions, including references beneath handler bodies. The six
   cancellation proofs support genuine insertion/removal, not a typing oracle.
   No missing accepted constructor or binder capture counterexample found.

2. **Actual embeddings and guard.** HandlerGraphEmbedding.lean:7–210 embeds both
   complete previous grammars structurally and preserves arbitrary-context typing.
   The embeddings recurse into actual code, including consumers and attempts.
   Their local renaming/substitution equations are consumed by simulation.
   At 213–294, graph typing comes from each actual old node derivation, while
   projection equality supplies only the transparent-successor guard. Projected
   unit never supplies a value typing fact. Wrapper, top and intersection remain
   transparent for alias-cycle inspection; lambda/delay/data introductions stop it.

3. **Observation and raw safety.** HandlerGraphSafety.lean:7–357 derives finite
   observation from actual graph typing and the accepted rank guard. Both
   intersection premises survive; top carries its existential underlying type;
   wrap keeps c→a, a→b and b→d distinct. Bottom exclusion follows by observation.
   Step at 542–622 contains no typing, safety, canonical-form or preservation
   premise. It performs actual reference lookup, including both returned wait
   result carriers, rather than assuming every No/Yes carrier is syntactically
   exposed. Preservation at 629 and progress at 835 cover every raw rule and
   typed computation constructor. Terminal at 817 has only root Ret/Req/Fail.
   The universally quantified finite-prefix theorem at 962 allows arbitrary
   typed attempts and arbitrary raw internal prefixes; it does not promise
   termination or fresh external extensions.

4. **Shallow control.** At Safety:475–533 selected arms receive original K:Q→A
   through continuationValue and actual pair substitution. Only exhaustion
   builds shifted H K:Q→B. Exact full operation equality and Bool eligibility
   govern selection; No preserves ordered remaining arms. valueRequest and
   operationRequest restore waits under the new response binder, shifting old
   saved K with up succ, not binding its response twice. Nested requests remain
   real arbitrary Comp code. A deep-handler substitution or discarded pending
   wait would falsify this contract; neither occurs in these definitions.

5. **Previous-machine correspondence.** Correspondence:7–338 maps full entry
   plans/events and every old Graph.Step and Handler.Step, with no typing
   precondition hidden in raw simulation. Prefix mappings preserve event order.
   At 364–480, graphContextPlug and graphContinuation traverse hole/bind/scope/
   expose. Each layer supplies an actual finite propagation trace to root Req
   or Fail. graph_request_correspondence derives payload/K typing from the old
   contextual computation via preservation, retaining identical instance/payload.
   graph_resume_equation quantifies over arbitrary combined responses; under bind
   it cancels lift(single v) against up succ. old_graph_resume_equation identifies
   the result with embedding the actual old resumed context. Thus this is more
   than calling old contextual suspension a new root terminal. The suspension
   decomposition at 532 covers all old suspended cases. Resumption safety uses
   the derived K typing and permits repeated independent uses.

6. **Original allocation application and examples.** Correspondence:497 calls
   HigherOrderRecAllocation.source_rec_allocation:313 directly. It obtains
   allocated node typing, constructed guard and closed body, lifts all three,
   and places the body under an independently typed combined handler before
   invoking finite-prefix safety. No fresh-node typing or rank premise is added.
   Actual FreshNoCycle remains the accepted allocation requirement. The source
   example at 650–717 uses an empty old graph, a recursive source lambda with a
   self-reference beneath lambda and response binders, exact allocated equation,
   sourceCloseComp program and actual request selection trace. Examples:593 and
   623–645 exercise graph-backed wait-result lookup and genuine nested request /
   restored wait / arbitrary response execution. Concrete examples supplement,
   rather than replace, the quantified proofs.

## Source/native boundaries and remaining owners

Read actual machine.rs CatchReturn:1097–1135, Frame::Local:1498–1560,
ForwardHandler:1989–2008, propagate_request:2081ff and begin_local:2500–2545.
These support the note's boundaries. Native cells are initially None and later
published; no general readback from that lifecycle to immutable simultaneous
allocation has been established. Native selection validates installation,
declaration/signature and Grant evidence, whereas formal eligibility is raw Bool.
ForwardHandler checks the owner and allocates a fresh installation occurrence;
retaining formal identity metadata is not an adequacy/freshening theorem.
Native empty value arms return the value; formal empty trial yields MatchFailure.
The existing HO-HANDLER-VALUE-EMPTY-1 discrepancy is honestly OPEN, not silently
normalized or classified as a runtime defect.

HG-ALLOC-READBACK-1, HG-HANDLER-METADATA-1 and HG-EMPTY-VALUES-1 remain with
primary/source/semantic intake under their original quantifiers. Their falsifiers
are respectively an accepted allocation/capture lacking the claimed typed
readback, native HandlerEvidence/owner failure despite proposed suppliers, and
the direct empty-arm Ret versus Fail mismatch. HG-EXTENSION-INTEGRATION-1 remains
OPEN: the independent old-Graph extension lane does not transport the full six
sorts or saved combined waits. Arbitrary combined handler RHS allocation,
mu/type-changing roll, polymorphism, mapop, primitives and other omitted full
paper forms remain OPEN. NO_SAFE_CODE_SLICE is supported; no compiler patch or
production authority follows from this review.

## Primary repairs and evidence audit

Compared the actual initial source_text snapshots against final source bytes.
Syntax is identical. Embedding adds final rfl. Safety corrects two named env
arguments without changing a statement or rule. Correspondence removes unused
simp arguments, unfolds extensionally identical empty-name environments, fixes
case layout, supplies complete trace constructor terms, and disambiguates the
concrete example graph from the section variable. That last repair restores the
intended concrete example and does not restrict the general safety/simulation
quantifiers. No accepted grammar, theorem hypothesis, response quantifier or
source allocation domain is weakened. The primary is correctly a coauthor.

Parsed the frozen existing JSONL; no Lean execution by this reviewer. All 23
calls remain present, totaling 78.12093299600019 seconds. Final calls 17–23 have
exit 0, no timeout, empty stderr and no warnings; input hashes before/after agree.
Four final A source_texts, output objects and note text match current frozen bytes.
Final query has 598 check/axiom pairs (439 A declarations), including explicit
constructors/fields; all 598 axiom outputs accounted for, 430 axiom-free and the
remaining sets only propext, Quot.sound or both. No Classical.choice, sorryAx,
new axiom or native_decide is admitted by that evidence. Source/statement review
above is independent of the green kernel result.

Rehashed all 121 contract pins: no mismatch. Read-only parsing and hashing also
checked all 53 reused accepted module source/object chains across 11 prior
receipts: no mismatch. Five historical failed modules remain excluded by the
receipt provenance. No earlier failed call or warning output was removed.

## Frozen manifest

| Artifact | SHA-256 |
| --- | --- |
| HandlerGraphSyntax.lean | 2a6b3f455e408336290bbe28616d7db8ee928f1b342b4c80f975bbacb419c24c |
| HandlerGraphEmbedding.lean | 36b616d809554feb585f32203fa72c1a084c7136beb4141a46d3a27a5145f656 |
| HandlerGraphSafety.lean | 554c5a1a003f27c3b8657d77455aa4f5eda7852338254034e3dd63a6db42a558 |
| HandlerGraphCorrespondence.lean | 94a6c2d24045bf9959121f4b31efea2f0630abc53c5bb776ab356d3ff108f964 |
| notes/theory/2026-10-25-handler-graph-composition.md | 63412985bc5a6df27cc168591b9c14138a86f349f7d628298b7cf0fc9515418a |
| tasks/agent-loop/inbox/20261025-handler-graph-composition.md | a7781647f896ae20a77b8d62e39f534ac9923c29ea2c44d07945312b72aa535a |
| tasks/agent-loop/inbox/20261025-handler-graph-extension-theory-r1-verification.jsonl | e7d2853d3eeafeca9af1caa77e24226a9047cf52f39ee5cc1bf471c2ff580464 |

The four Lean paths are beneath notes/theory/lean/YulangClosure/.
This report hash is returned separately to avoid self-reference.

## Reviewer checks, resources and cessation

Lean/build/tests/checkers/Git: **NOT_RUN by reviewer**. Permitted source reads,
receipt parsing/diff inspection and byte hashing only; one unavailable `python`
invocation was retried with python3 for read-only receipt parsing. No scratch,
source/note edit, descendant, background process or additional output.

Actual STOP / report freeze: 2026-10-25T08:01:32.782917+00:00.
Conservative charge: 240 of 600 seconds; 360 seconds unused, not renewed.
Worker STOPPED after this sole report write. No unresolved descendants or
processes. Primary alone adjudicates, synchronizes state and performs Git.
