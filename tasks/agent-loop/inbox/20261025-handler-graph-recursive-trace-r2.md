# HANDLER-GRAPH-RECURSIVE-TRACE-20261025 — frozen handoff revision 1

Outcome: CANDIDATE; primary Lean verification and fresh independent review pending.
Sprint: COMBINED-RECURSIVE-INTERACTION-THEORY-20261025/r2.
Contract: `tasks/agent-loop/sprints/combined-recursive-interaction-theory-20261025-r2.md` SHA-256 `b6fbc0648dcaf9fbbc0750fef390f793460331f2a6576b0e181d7a2ef8df6f92`.
Baseline: `d8af06a7e6a9a6d0ba22b887c2dc28ceec9d31d2` (issued baseline; no Git run).
Author/actual assignment: `/root/handler_graph_recursive_trace_astra_r2`.
Session: parent `COMBINED-RECURSIVE-INTERACTION-THEORY-20261025/root-r2`;
supported NEW_TASK receipt supplied this exact assignment and two output leases.
Requested model/effort: `gpt-6-astra` / `medium`; observed model/effort: UNKNOWN / UNKNOWN.
No descendant or coauthor in this delta. Imported authors: `/root` (composition),
`/root/handler_graph_extension_interaction_astra_r1` (transport/interaction),
`/root/handler_bearing_recursive_allocation_astra_r1` (source allocation).

## Parent application and actual result

The parent is the r1 arbitrary-source-allocation/finite-interaction composition,
with its missing concrete self-recursive handler-bearing callback trace; paper
`docs/yulang-operational-type-safety-ja.tex:978` and `:1140` retain the original
immutable-extension and arbitrary finite interaction quantifiers. This delta
instantiates that construction with the SAME `ConcreteSourceRun.recursiveCallback`
and operation 75. It does not replace either generic parent by the example.

`whole_source_closure` states and proves by definitional equality:
`sourceCloseValue captures 1 recursiveCallback = closedCallback`.
The lambda's body is `handle closedHandler (ret unit)`. The literal handler's
value arm requests `recursiveOperation` with `.ref (.inr 0)` and continuation
`ret (inRight (var 0))`. Closure starts outside the whole lambda, retaining BOTH
the lambda binder lift and value-arm binder lift. `actual_fresh_node` and
`actual_graph_node` derive the exact allocated node; none is a theorem premise.

`recursive_callback_reaches_own_request` constructs six actual raw steps:
`callRef`, `callLambda`, `bind handleReturn`, `bind valueCons`,
`bind valueRequest`, `bindRequest`. Its endpoint is `recursiveSaved.suspended`,
with operation 75 and the callback's own newly allocated reference payload.
The continuation is the actual propagated waitValue/bind continuation.
`reached_saved_typed` derives capture typing from reachability and the run invariant.
`recursive_request_published` publishes that reached ROOT request.

`second_source_extension` applies a second actual `sourceFresh`/`allocate` of a
unit source RHS. Both entries survive. `original_entry_reused` answers the
transported ORIGINAL operation-73 entry with `.ref (.inl (.inr 0))`.
`reused_entry_reaches_own_request` transports the established six-step prefix
through the actual source embedding, proving operation 75 appears again with
the transported self-reference. It makes no unbounded recurrence claim.
`first_answer_every_prefix_safe` and `reused_entry_every_prefix_safe` quantify
over every finite internal prefix, applying the actual first/second constructed
graph guards; the latter also preserves typing of every saved arena entry.

This supplies a candidate for the missing r2 finite trace, including the
pre-authorized stronger transported reappearance. No endpoint/node assumption,
new semantic rule, new external dependency or source-domain restriction was added.
Full-paper omitted forms, native correspondence, metadata adequacy,
HO-HANDLER-VALUE-EMPTY-1 and original Simple-sub A/B remain OPEN under their
existing owners. No independent F1/FK1/foreign-continuation obligation is closed.

## Source/native evidence and prior work

Actual research source path: `recursiveCallback` -> whole-lambda `splitValue`
(using lifted `splitNames`) -> `closeNamesValue` -> capture substitution ->
`sourceFresh` -> `allocate` -> raw lookup/lambda/handler/wait/bind steps ->
root publication -> source embedding -> transported saved-entry answer.
There is no new Simple-sub generation/propagation/generalization claim here.

Reused the frozen generic source embedding, source typing, finite-cycle guard,
run invariant, raw prefix transport and source callback typing exactly within
their established premises. The r1 nonrecursive operation-74 trace is NOT
reused as evidence for the recursive endpoint. The former standalone closure
`sourceCloseHandler captures 1 recursiveRequestHandler` is rejected as the
nested handler: it omits the enclosing lambda's binder context.

Read native owners directly: `machine.rs` `begin_local` reserves a None cell
and evaluates initializers sequentially; `resume_host_write` rejects
`saved.resumed`; `continuation.rs` `ResumeTemplate`/`TemplateNode` retain original
event plus owner/view/handler/frame structure. These do not establish the
abstract simultaneous graph or repeated-answer correspondence. NO_SAFE_CODE_SLICE
for this theory-only packet; no production implementation TODO is authorized.

## Frozen artifact and dependencies

Artifact: `notes/theory/lean/YulangClosure/HandlerGraphRecursiveTrace.lean` SHA-256 `9e3c7604f4a32919a5482278e3ebce9ead8b8b58496a64544c9533cc76430956`.
Only new/write paths: that artifact and `tasks/agent-loop/inbox/20261025-handler-graph-recursive-trace-r2.md`. No scratch paths.
Handoff byte hash is sent externally after this final write (no self-hash).
The full r1 pinned dependency closure remains the primary's acceptance obligation.
Directly read/hash-recorded dependencies:

- `notes/theory/lean/YulangClosure/HandlerGraphRecInteraction.lean`: `dc1f89a1e1b8b0b4a9e2e95fdcc47334b1b7578a8fef3f947574678ce8dfdba7`
- `notes/theory/lean/YulangClosure/HandlerGraphInteraction.lean`: `a5094f70dc2ec2843a431cfb24f0111166fbc9172b7e6df08d0d8c800a8ce018`
- `notes/theory/lean/YulangClosure/HandlerGraphTransport.lean`: `a869e61005910dba00cf9cfa57065a45afeac08413974e343d9bcc16821f629d`
- `notes/theory/lean/YulangClosure/HandlerGraphRecAllocation.lean`: `5563163a5fe2741dc4cb1968329e5ec417a170099448978b653dc487cd136dfd`
- `notes/theory/lean/YulangClosure/HandlerGraphSyntax.lean`: `2a6b3f455e408336290bbe28616d7db8ee928f1b342b4c80f975bbacb419c24c`
- `notes/theory/lean/YulangClosure/HandlerGraphSafety.lean`: `554c5a1a003f27c3b8657d77455aa4f5eda7852338254034e3dd63a6db42a558`
- `notes/theory/2026-10-25-handler-recursive-interaction-composition.md`: `7d00bc092d001e1f3e5e9a185bf51ad388999ff950191af147b03be4eb0588cd`
- `tasks/agent-loop/sprints/combined-recursive-interaction-theory-20261025-r1-outcome.md`: `df968bb8f64bbb7f04547437816730ab3e63d55fefa93db6794b70c42d54d09b`
- `tasks/agent-loop/inbox/20261025-combined-recursive-interaction-theory-r1-verification.jsonl`: `a5430a82bfd77a77a15a04c03b6aee3fc5029da1367d05b28dc8ce808a05b531`
- `tools/inference-playground/src/runtime/machine.rs`: `b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e`
- `tools/inference-playground/src/runtime/continuation.rs`: `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3`
- `docs/yulang-operational-type-safety-ja.tex`: `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`

## Checks, resources, next step and writer stop

Author checks: read-only source inspection and SHA-256 only. NO Lean, tests,
builds, checker, Git, nested CLI, external contact or runtime execution probes.
No claim of elaboration success or independent certification. Primary owns
serial compilation and paired #check/#print axioms for every public declaration.

Three substantive stages: (1) exact whole-lambda closure/raw endpoint,
(2) actual publication/second allocation/reuse/transported prefix,
(3) graph-guard prefix applications and source/native premise audit.
Grant: 600 active seconds, max 3 stages; no renewal. First recorded clock:
2026-10-25T08:49:49Z. STOP: 2026-10-25T08:51:54+00:00.
Observed interval after first clock: 125.240 seconds; conservative charged
elapsed from the earlier contract grant 08:49:17Z: 157.240 seconds
(includes pre-dispatch slack; exact pre-first-clock active time UNKNOWN).
Remaining of conservative 600-second ceiling: 442.760 seconds, unspent;
this assignment ends at coherent candidate delivery rather than waiting alive.
Processes: none left running. Descendants: none. Unresolved descendant leases: none.
Writer state: STOPPED; source and this revision frozen; no further writes planned.

Next in-scope owner step is primary verification, then primary-appointed fresh
nonauthor review of these exact bytes. Producer cannot certify this result.
TODO R2-VERIFY-1 (primary): check closure equation and six raw steps with pinned
imports; falsifier is any elaboration failure, assumed endpoint/node, wrong
binder, payload or operation, lost entry, or an axiom beyond allowed propext/
Quot.sound. Output belongs in the primary verification lease.
TODO R2-REVIEW-1 (primary-assigned fresh reviewer): audit actual source derivation,
publication, second allocation, original-entry selection, transported trace and
guard quantifiers; report only in the primary-issued review lease.
TODO R2-NATIVE-1 (existing Luna/source intake, beyond this packet): relate actual
`begin_local`, resume/template producers and consumers to the represented graph
and repeated resume without changing native semantics. First missing evidence
is a state relation preserving sequential cells and owner/view/handler lineage;
any mismatch on those owners falsifies the bridge. No implementation writes granted.
Commit/integration status: pending primary verification, fresh review and adjudication.
