# Operation-v1: runtime response identity and completion correspondence

Status: frozen candidate source/native audit and conditional correspondence; independent review NOT RUN. No observed runtime completion or theorem/production promotion.
Author: `/root/r18_runtime_correspondence_proof`, sole author; no descendants.
Assignment/handoff: `r18-runtime-resume-proof`, revision 1.
Contract: `operation-v1-runtime-evidence-and-callback-resume-20261018-r18`, SHA-256 `472ea2f65946bf815834decf599fd105f20dc0c97fde9711746b8d87c0fea1c4`.
Supplied baseline: `2a3f2a47d5013761f0e0717b0c6073c54c62d36c`, including the contract's frozen r17 workspace bytes. No Git inspection.
Requested model/effort: Sol/high; observed effective model/effort UNKNOWN/UNKNOWN. Current-session assignment is the parent collaboration message; configuration and role names do not establish execution metadata.

## 1. Original parent and application

Parent remains **CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017**, OPEN, original quantified conditions closed here: **0**. The receive obligation is authentic negative-formal pair formation followed by `f () -> install(g) -> fresh use(g) -> g ()`, with its original source/provider/context/world/occurrence/guard/continuation/interaction quantifiers. Choose retains complete original Sigma, joint world/initial admission, whole incoming carriers, private profiles, dependent futures and the original joint witness. F1 and FK1 are independent. FIRST-RESULT, H1/H2/JOINT_DEC, Call/effect, N-Transport, source-Generalize, soundness, principality, termination, F5 and production do not follow from this audit.

r17 supplies one reviewed research-only static vertical: exact `u_ping -> h_arg -> response_definition -> u_outer`, stored q/m0/FieldBoundV1, actual `AnnotationMember <: q-Allowance` and ordinary typed drain, with successful receipt publication gated on final absence of candidate conflicts. r18 asks for one corresponding execution returning 42. This audit localizes the actual runtime premises and two rejecting consumers, and supplies an identity-preservation derivation usable by the implementation lane. It does not supply missing general negative-formal formation or a foreign-continuation theorem.

## 2. Static producer and identity boundary

At pinned `candidate_source.rs`, `operation_v1_catch_source` constructs `HandlerContinuationArgumentV1` only after resolving one same-source path: direct catch scrutinee Apply of the matching operation; matching declaration and continuation binder; unique `k response` Apply in that arm; its exact argument resolves to the local response definition; that definition has the matching annotation and a Lambda initializer whose body is the actual outer-operation Apply. q and m0 retain the same h_arg. `candidate_field_bound_v1_inner` checks actual callback operation/view provenance, exact prepared handler argument, native endpoint kinds and dedicated slot, then constrains and drains before setting consumed.

`CandidateInference::operation_v1_field_bounds` publishes only consumed records when final errors are empty. Its public receipt exposes request, callback Apply, callback operation ID/use, response local-definition ID, family and record ID. It does **not** expose h_arg's catch occurrence, arm source, continuation binder, `k response` Apply or response-argument occurrence. A consumer must recover and validate those exact edges from this same HIR or obtain an equally strong approved projection; absence of those public fields cannot be filled by spelling/type/family equality. The current exact leases keep solver files read-only.

`CandidateInference::observes_hir` uses pointer equality against the retained HIR. Require it for the actual candidate passed to execution, together with exactly one successful consumed receipt and zero conflicts. A numeric record ID is candidate-local. Same-looking IDs, source text or independently lowered HIR do not authenticate this join. A checked immutable projection must originate from this retained candidate, rather than accept freely supplied receipt-shaped fields.

Keep these namespaces distinct throughout:

| Static fact | Dynamic witness required |
| --- | --- |
| h_arg request/catch/arm/binder/Apply | actual request event, installed handler occurrence and bound continuation template |
| response HirLocalId and initializer Lambda | exact local cell read, actual ValueHandle and its executable closure/environment |
| callback body Apply and operation-use occurrence | actual callable invocation and emitted request event at those SourceSites |
| expected outer catch/arm | actual active HandlerInstallation and selected arm code |
| FieldBoundV1 ID/endpoints | evidence origin in the retained successful candidate; no runtime handle cast |

No equality identifies `c`, `c_outer`, native member/view, static HIR occurrence or dynamic event. Native allowance membership licenses no request and constructs no callback.

## 3. Actual baseline constructor/consumer derivation

All runtime claims in this section concern the baseline hashes in §8, before the concurrent r18 implementation. SourceSite includes source root and occurrence; runtime arena indices are interpreted only inside the same program/machine.

**HIR/code.** `RuntimeProgram::from_hir` retains `Arc<HirModule>`, uses source-local child indices to form labels, retains resolved Name binders, Lambda parameter/body, Apply callee/argument, Catch patterns/arm body/source, and each expression's original SourceSite. It checks each child against that LocalSource. Consequently a checked root/occurrence-to-label relation can connect static h_arg to runtime code. This is structural lowering, not runtime execution or typing proof. `RuntimeEvidence` currently contains only name-consumption data, not the r17 receipt.

**Definition/closure.** `Machine::evaluate(Lambda)` allocates one ValueHandle and inserts `ExecutableValue::Closure { parameter, role, root_schema, body, environment }` under that handle. `Frame::Local` publishes the returned handle into the actual local cell. `evaluate(Name(Local(id)))` uses exact Binder identity through linked environments and reads that cell. Thus, if this particular response initializer is evaluated and subsequently read through h_arg's resolved argument, the actual argument is that allocated closure, with its original body and lexical environment. No closure is rebuilt from its signature. Arena environments retain links to cells, rather than snapshots of mutable cell contents.

**Actual response application.** `evaluate(Apply)` saves its original argument label, caller environment and Apply site in `Frame::Callee`, then evaluates its callee. On an executable continuation, `return_value(Callee)` allocates a delay of precisely that argument/environment, enters an invocation and installs `Frame::ResumeArgument { template, source }`, then executes the delay. Therefore the argument expression is evaluated at the actual `k response` application, inside its selected invocation. `ResumeArgument` receives the resulting ReceivedValue. Conditional on the response check succeeding, it places that same ReceivedValue in `State::EnterTemplate`; `TemplateNode::Hole` returns it unchanged. This gives an induction invariant: until a source consumer deliberately consumes/returns it, the response handle is the original handle, not a type-selected replacement. Views/interface checks and control ownership are separate obligations.

**Capture/control.** `propagate_request` appends each actually popped frame in next-return-first order; matching handler selection occurs while its delimiter is still installed and after eligibility/payload checks. `capture_template` folds exactly that suffix into Bind/Owner/ForwardHandler/View nodes, retains declaration and original event, adds the containing owner, and rejects pending GlobalRead/Root cache-write frames. Entry resolves owned/borrowed executable owners with the existing live checks and fresh invocation descriptors. It creates no callback. The chosen handler is shallow: its delimiter is removed before its arm executes; unselected outer frames remain available. These are existing source-control facts, not proof that every source context is supported.

**Calling the response closure.** When a subsequent source Apply actually uses that response handle as callee, `return_value(Callee)` selects its executable record by the exact handle. The Closure branch uses its retained body/environment; ValueEntry binds the actual argument into an extension of that environment. The callback body thus uses the original lexical links. This step still needs an actual source Apply reaching that handle. Returning a Closure value does not execute it.

**Outer request and selection.** Executing the exact callback operation creates a request carrier retaining declaration, payload and source Apply site; `execute(Request)` allocates a fresh event and its actual observations. The static operation-use occurrence and its enclosing Apply occurrence are distinct: runtime request.source names the Apply; the exact Operation child/declaration relation must be checked, including for the original ping request. `propagate_request` validates live installation/owner, compares the exact operation declaration ID, checks the existing visibility/Grant premise and payload, and selects actual arm.body outside that shallow handler. A checked event-to-callback-Apply relation and an event-to-selected-installation/arm relation are needed. Neither matching family nor static existence of the catch proves those events occurred.

**42/completion.** Evaluating the selected Integer literal produces its decoded integer value. Other suffixes can still discard, transform, fail or diverge. The eventual value of `Machine::run` must be `Completed(h)` and `machine.value(h)` must be Integer("42"); proof that an arm was merely selected or scheduled is insufficient. Arm-entry and arm-return evidence must precede the completed receipt. `run` distinguishes exhaustion, unavailable, unhandled, running and completion. Depletion pauses private state; it must publish no completed receipt for that call.

Together these local facts prove a conditional identity/completion implication: if same-candidate/HIR provenance, exact code joins, successful function-response validation, actual callback Apply, existing handler eligibility, selected-arm evaluation and final completion are all established, then the joined response and event witnesses concern the exact source response and its execution. This implication is useful as the runtime review invariant; its antecedents are not reported as observed baseline execution.

## 4. Exact baseline obstructions and coverage

1. **Function response rejected twice.** `Machine::propagate_request` only captures a bound continuation for Unit/Int/Bool/Str operation results. Here `ping` returns a Function, so that consumer rejects with HandlerEvidence if reached. Independently `return_value(Frame::ResumeArgument)` calls `primitive_matches` on the operation result, which also rejects Function. Removing only the first guard cannot admit the response. The missing evidence belongs to these two consumers and the same-HIR research RuntimeProgram constructor: a bounded source-derived witness for this exact function response and actual closure, not generic acceptance by `RuntimeValueKind::Closure`.
2. **Existing eligibility remains required.** `primitive::closed_primitive` returns false for any Lambda and for bound continuation patterns. `Receiving::local_grant` requires an actual live invocation owner and authentic executing view/receipt; ModuleRun cannot satisfy it. A bare module-level outer/inner catch is not made eligible by the r17 receipt. An appropriate existing computation-formal path may supply authentic Grant evidence; this audit did not execute one. No visibility rule, new bypass or closed-primitive certificate is granted here.
3. **The r17 test fixture returns a closure.** `v1_callback_source` supplies no outer handler or later callback Apply. Static receipt success therefore establishes neither the outer request nor integer 42. The exact frozen matcher requires a direct operation Apply as catch scrutinee; inserting `{ my g = ping(); g 0 }` there is rejected by that matcher. A possible same-contract source shape applies the result of `(catch ping() { ... k response ... })` outside the catch. Such execution could reach the returned closure, but it must not be described as callback application *inside the captured raw suffix*. No new source was parsed, accepted or executed here. The stronger inside-suffix claim remains unestablished and may require a different accepted construction or a Luna boundary decision if impossible under the frozen matcher.
4. **No joined completion evidence.** Baseline `execute` binds `_candidate`, calls ordinary preparation, and constructs RuntimeProgram with default RuntimeEvidence. There is no v1 research execution entry, candidate-owned join or actual closure/request/arm trace linked to FieldBoundV1. Existing values retain SourceSite, but neither final Integer(42) nor those stored sites prove the full causal history. This is a producer/consumer gap, not a claim that r18 implementation cannot supply it within its leases.

Omitted cases: arbitrary function responses, aliases/multiple matching continuation applications, unsupported source forms, arbitrary higher-order views, imported/foreign continuation histories and every parent quantified case. These remain original open cases, not exclusions added to parent semantics. Ordinary Simple-sub generation, propagation, levels, extrusion, qualifying intrusion, generalization and separate residual/provider/witness lineages are untouched.

## 5. False-join attacks and falsifiers

These are static adversarial obligations, not executed tests or source-qualified counterexamples.

| Attack | Required rejection/evidence |
| --- | --- |
| Swap `response` for same-family `other_response` | Its local-definition ID differs; local-cell/initializer/actual handle join must follow the receipt's chosen definition. Type/family equality cannot repair the mismatch. |
| Replay receipt from separately lowered HIR or different candidate | `observes_hir`, retained candidate origin and immutable receipt selection must fail. Same raw record ID or textual source is insufficient. |
| Use unrelated same-family operation/request | Require exact callback Apply, exact Operation use and declaration ID, fresh event and causal closure invocation; family alone fails. |
| Missing or already popped outer handler | Require actual live installed delimiter with valid owner and existing Grant, followed by its actual selected arm. Static arm presence fails. |
| Select arm but fail/diverge/exhaust before returning | No final Completed/42, so no completed receipt; arm scheduling is insufficient. |
| Return 42 on unrelated path or have expected arm return another value | Require callback/request/selected-arm lineage plus actual arm evaluation and final 42. Final value alone fails; arm returning 41 fails. |
| Accept closure tag after removing primitive guards | Must reject absent exact source-derived response/initializer/environment witness. This is not a valid correspondence repair. |
| Move callback Apply across a capture boundary and claim same suffix | Compare actual saved frames and source Apply owner. Outside application may be an actual execution, but cannot prove inside-suffix execution. |

## 6. Prior results reused and rejected

Reuse r17 r6 and its closeout only for the exact static producer/typed native consumer and final conflict gate. Its focused 16-test pass is inherited historical evidence, not a run by this worker or execution evidence. Reuse `2026-10-16-runtime-resume-template-correspondence.md` for its actual constructor order, raw suffix preservation, owner resolution and shared-cell hypotheses. Its historical accepted bridge still leaves typing/transport/full source-domain premises explicit; current code was traced directly rather than assuming old line numbers/hashes remain current.

The original receive note is reused to retain the exact missing negative-formal construction and its two distinct invocation rows; the choose initial-installation note retains complete Sigma/Initial/world premises. None supplies this new runtime function-response witness. Reject using an assumed transition checker, an inert evidence object, old primitive-response tests, family equality, allowance membership, a returned closure or one local frame action as parent/FK1 closure. No historical failure proves semantic impossibility here.

## 7. Owner-bound handoff and stop

- **R18-FUNCTION-RESPONSE-IDENTITY**, parent as §1; implementation owner: `RuntimeProgram` research construction and `Machine::{propagate_request,return_value}`. Inputs: retained same-HIR candidate and unique successful r17 receipt, exact LocalSource h_arg recovery, original closure initializer/body/environment. Output: narrowly scoped research function-response witness consumed at both guards, preserving ordinary behavior and existing visibility. Falsifier: alternate closure/HIR/candidate succeeds or primitive-check removal admits arbitrary closures. This is an evidence request within the issued r18 implementation lease, not production authority.
- **R18-ACTUAL-CALLBACK-AND-ARM**, implementation owner: playground research entry and Machine Apply/request/handler/return/completion consumers. Inputs: accepted source with an actual response invocation and eligible live outer handler. Output: causal join of actual argument handle, continuation template, callback invocation, callback request event, selected live handler/arm evaluation and final Completed Integer(42). Falsifier: unhandled/exhausted/non-42 or unrelated 42 path yields success. Identify whether callback application is inside captured suffix or outside after its return; do not conflate them.
- **R18-FROZEN-IMPLEMENTATION-INTAKE**, Luna owner: receive the implementation's frozen bytes and exact source/check evidence, reconcile changed runtime hashes, appoint fresh independent reviewer and adjudicate these premises. This producer/coauthor cannot certify the combined result. The present audit stops at baseline obstruction/conditional bridge; further proof against changed code requires Luna intake of that frozen dependency component.

Bound: 600 seconds, no Astra, no descendants; read/search/hash and two artifact writes only. Exact elapsed active work, CPU/RAM and token usage are UNKNOWN; conservatively reserve/charge the full grant, zero additional authority claimed. No code, tests, builds, Cargo, executable semantic probes, Git, network, nested CLI or other worker edits. Two exploratory reads named nonexistent value.rs/environment.rs; actual data/environment structures were then read in machine.rs. Some combined output was truncated; decisive constructors/guards were reread in bounded excerpts. No scratch/new paths except this artifact and its exact inbox. Parent and implementation were informed of the actual seams through Luna.

Writer state at freeze: **STOPPED**, no descendants or unresolved descendant leases. Result is pending fresh review/integration, not parent DONE. Next step belongs to Luna/implementation owner as the TODOs above; this worker claims no background waiting work.

## 8. Frozen direct dependency hashes

Authors: r18 contract/design and r17 r6/closeout are Luna-owned; r17 solver/test bytes are the prior implementation lane's frozen work, reviewed as recorded in the closeout. Historical notes retain their stated authors/review scope; baseline runtime authorship beyond repository provenance is UNKNOWN. This worker authored only the two leased outputs. Hashes identify bytes, not authority or acceptance. Baseline runtime is a frozen logical input; concurrent implementation replacements are not proof inputs to this revision.

```text
472ea2f65946bf815834decf599fd105f20dc0c97fde9711746b8d87c0fea1c4  tasks/agent-loop/sprints/operation-v1-runtime-evidence-and-callback-resume-20261018-r18.md
0569f9b373123d93fd1ff9e55739bf3cbc0f221bdb0cdce7a625171ba041d37c  notes/design/2026-10-18-operation-v1-runtime-evidence-and-resume.md
276979eccec49396c6799b96ca1e0277c6108dc2fd1fe487a52e4565cff6ed54  notes/design/2026-10-18-operation-v1-source-completion-and-consumer-r6.md
646eae284e176854afd2db89fb4a352e1af009f3b44c43af9f92ee601c5c6ef9  tasks/agent-loop/sprints/operation-v1-source-completion-and-consumer-20261018-r17-closeout.md
66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c  crates/yu-solver/src/candidate_source.rs
6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0  crates/yu-solver/src/candidate_effect.rs
5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb  crates/yu-solver/src/shadow_apply.rs
2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee  crates/yu-solver/src/lib.rs
7c3e163c5ad710f1eb7f44ab21018fe2788f7334390f1afe6f432d8212f3f34a  crates/yu-solver/tests/candidate_operation_catch.rs
b65cfd7200e459c9448438ec979ffeb9eddb35c282600349cebe7ddf3b759bbb  tools/inference-playground/src/lib.rs
b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748  tools/inference-playground/src/runtime/program.rs
b8f15e4617a9d66940183c7327499ff8a2beb1e9cae2abb997137fc1ca464b82  tools/inference-playground/src/runtime/machine.rs
194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3  tools/inference-playground/src/runtime/continuation.rs
97485b9439357497aaf3f19555b1d87eef4aabc955b3a2815f23cf49a65c0153  tools/inference-playground/src/runtime/primitive.rs
8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9  tools/inference-playground/src/runtime/receiving.rs
1c1a4f402c87088454bf31eee2c1eee8d5ff9ec716fe2282ed4fe421b6469859  tools/inference-playground/tests/runtime_resume.rs
f3a4c925a197e63e5b7faf1ce1e1caf5736d76f1b86ba162c6acc85bfff8e7dd  notes/theory/2026-10-16-runtime-resume-template-correspondence.md
2b526b92ef78b8514a81592b303e4db2310dedd13483c74bcfb4bd53798f0a8f  notes/theory/2026-10-17-receive-negative-pair-construction.md
b27eed06d5a3eae63b2dfacb62a1f76d01b71f92a478402b452cd8a3b3346471  notes/theory/2026-10-16-choose-source-declaration-initial-installation.md
```
