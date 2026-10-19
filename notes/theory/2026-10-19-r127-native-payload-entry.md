# R127: operation declaration argument entry and request publication

Status: conditional finite source/runtime evidence, revision 1; fresh independent review pending. Producer: `/root/r118_proof_lane`, no descendants. Authority/review/integration owner: Luna. Requested model/effort: configured Sol/high; observed model/version/effort: UNKNOWN.

Contract: `tasks/agent-loop/sprints/native-payload-entry-cli-20261019-r127-rev3.md`, SHA-256 `04b707e493f53e1fe35747c11ec1fadb57238a560e9f37d6b57d4865fb04fa7f`; baseline `234d2b6d579f12e01448042a8d79d1cf145afb73`. Luna's explicit grant after CLEAN rev3 delta review activates the packet; the contract's preserved candidate header is not a new grant. Semantic authority is charter §21 with the §24 distinction retained. This is the experimental playground's native operation consumer, not a production backend theorem.

## 1. Exact finite claim and open premises

For these two declarations and their exact calls, the source argument annotation is retained to the operation consumer: absence of the argument's outer row selects Value entry; an explicit empty row selects Computation entry. Every call first constructs an inert argument delay. Value entry executes that delay before constructing the operation request carrier. Computation entry puts that same unexecuted delay into the carrier payload. In both cases actual request publication is a subsequent `OperationResultConsumer` execution after the operation invocation returns. Carrier construction and request publication are distinct transitions.

Keep the following premises separate:

- **H:** the exact source produces an authentic ParsedFile with the intended original declaration/expression tree and no diagnostics, and lowering returns the HIR-owned LocalSource, identities, resolutions, annotations and ordered bodies described below. Actual returned parse artifacts are not observed here; shape/diagnostics remain explicit premises.
- **A:** ordinary preflight, candidate generation/solving, conflict checks, RuntimeProgram construction and authentic source scheduling succeed on the same HIR. Constructor inspection does not establish successful source admission or a complete source/native bridge.
- **E:** the concrete runtime follows the retained labels and original binder/value/view identities, with successful owner, lookup, receiving and invocation consumers. The local postcondition is conditional on those actual transitions; it supplies no missing type/effect/permission certificate.
- **B:** the selected bounded execution has no earlier identity/resource/unavailable failure, and public I/O completes as specified. Value is checked at 1000 steps; Computation at 10000. No executable observation, exact prepublication step count or divergence theorem is supplied.

H is the first missing concrete source premise. A, actual E and the bounded observations B remain independently open. A conditional finite trace is neither their observation nor semantic parent closure.

## 2. Exact source bytes and CallTail provenance

Value V: 92 UTF-8 bytes, no final LF; SHA-256 `a620b984fea7f339da2adcf4acfd053725fcf10e63861efc20a0f8e769b5189e`.

```yu
act signal:
    our ping: int -> int
my main = { my loop x = loop x; signal::ping(loop ()) }
```

Computation C: 95 UTF-8 bytes, no final LF; SHA-256 `7041a3314180f4438ca717794bbaaf7b5dc2e904096211f0682df2d14969bbbc`.

```yu
act signal:
    our ping: [] int -> int
my main = { my loop x = loop x; signal::ping(loop ()) }
```

Manual byte arithmetic on these ASCII sources: the first two lines occupy 37 bytes in V and 40 in C. In their common third line, the outer opening parenthesis is at relative offset 44; its CallTail spelling `(loop ())` occupies 9 bytes. Therefore the expected original outer CallTail ranges are **81..90** and **84..93**, respectively. `expression/tails/delimited_tail.rs::call_tail_normalized` starts CallTail before emitting the opening token, emits its delimited items and finishes after the tail. `local_source.rs` forms Apply from that actual tail and retains its `range_of(tail)`. Thus under H's authentic shape these are the Apply ranges; the manual count is not a claim to have executed the parser. The whole written operation call includes the preceding `signal::ping` and must not replace the retained tail range.

Let D_V/D_C be each independently parsed program's original operation declaration, R_V/R_C its main root, A_V/A_C its outer original operation Apply, L its local `loop` binder, P its own original formal `x`, and B_loop its original `loop x` body. These names are per-HIR abbreviations. Equal spellings/common suffix bytes across parses do not equate parse brands, operation IDs, binders or occurrences.

## 3. Fact → constructor → consumer refinement

| Original fact under H | Owning producer and retained data | Consumer/application to V/C |
|---|---|---|
| Authentic source node | `full_parse.rs::parse_file` mints a parse brand; root/descent mints SourceNodeKeys retaining brand, green allocation and start. `source_identity.rs` walks original ancestry into the source-key index. | LocalSource `key`/`set` records original keys and fresh HIR occurrences. Equal range/text cannot replace that identity. |
| Own `signal` family and `ping` member | `module.rs` invokes `source_annotation.rs::declarations` before expression formation; family identity retains module+Act key, operation identity family+original member key; declaration retains name/signature positions and signature. | Namespace resolution for the actual operation use returns the HIR's own D. Runtime and candidate constructors clone that retained declaration, not a text-reconstructed signature. |
| Absent versus explicit-empty argument row | `parse_type_source` removes an initial BracketRow into `Some(parse_row(...))`; `parse_row` retains its own position and initially empty concrete/variable lists. For an arrow, `parse_type_source` moves that effects option onto the argument; the outer Function's own effects are None. | V has Function(argument Int/effects None, result Int/effects None). C has Function(argument Int/effects Some(empty original row), result Int/effects None). Empty contents do not collapse presence. |
| Local recursive definition and formal | Work::Initializer temporarily installs L, pushes P, emits the named Lambda, forms its body and then Work::Publish restores/publishes the local. Thus body `loop` resolves to Local(L), `x` to Parameter(P), and later call `loop` to the same L. | RuntimeProgram's ownership walk marks an actual self reference while L's initializer is active as recursive. Runtime local construction creates a cell before the Lambda so the closure captures its own lexical knot. |
| Original outer call and argument subtree | LocalSource expression lowering emits Apply from CallTail with child indices for callee and argument, then the resolved Operation from its original operation path. The argument is the original `loop ()` subtree, not the body `loop x`. | A's SourceSite carries original root/occurrence/range; runtime delay retains that argument label and current lexical environment. A's site is retained through carrier and request; no new parse is involved. |
| Ordinary candidate operation recipe | `candidate_source.rs::Work::Finish(Operation)` prepares signature primitives, emits pure operation-value evaluation effects and schedules Action::Operation with retained D, source owner/occurrence, target endpoint and level. Its action consumer invokes `candidate_effect.rs::candidate_operation`. | That method builds the signature in `SignatureContext::Operation` at the retained level and admits its value link at slot 42. It does not evaluate the argument or infer the native entry role from a solved empty row. |
| Candidate Function and application facts | `candidate_signature_value(Function)` builds argument/result value ports with their actual variance and calls `candidate_signature_effect` using each original effects option; the root operation result effect context retains its declaration family. `Finish(Apply)` retains callee/argument endpoints and effects, result/effect, original source/cause, level and ApplySourceInput, then schedules its ordinary Candidate recipe. | These are ordinary inference inputs and existing consumers. Registration of P with absent own annotation gives Value role. Recursive source links preserve initializer endpoints. Whole candidate success, generalization/extrusion/propagation/intrusion correctness and complete static/native role equivalence remain outside this finite packet. |
| Runtime code identity | `RuntimeProgram::from_hir` requires the HIR-owned LocalSource, labels child indices, clones Operation resolution, emits Apply labels, and stores original root/occurrence/range in Code.site. It derives P's runtime Value role from its absent own annotation. | `Frame::Callee` receives A.site; evaluating its operation child supplies the original D. Runtime operation role is read directly from D.argument.effects, independently of any solved graph heuristic. |

`CandidateInference::solve` is the ordinary `solve_mode(hir,false,false)` route: preflight retained source, admit only declared placeholder errors, collect ordinary candidate constraints and run its session. `lib.rs::prepare` makes one HIR Arc, solves its clone, rejects conflicts, and returns that same Arc; `execute` passes it to RuntimeProgram with default RuntimeEvidence. Typed evidence must use that same HIR for declaration/Apply assertions. This wiring does not prove H/A or bypass inference. No OperationV1 plan/evidence is needed or used.

§21 fixes the **argument-entry** role from the source boundary and requires inert argument construction followed by Value force/rebind inside the same activation. §24's prior receiver-role selection remains distinct: runtime `ParameterRole` is not a complete §24 receiver elaboration certificate, and an explicit row does not prove handler receiver role or permission. No universal-handler reading of §16 is used.

## 4. Conditional native operation postcondition

Suppose the actual original Apply A has evaluated its resolved Operation(D) and returned that value to `Frame::Callee { argument: a, environment: e, site: s=A.site }`, with outer frame prefix F. Under E, `return_value(Callee)`:

1. Allocates inert value d of RuntimeValueKind::Computation with `ExecutableValue::Delay { code: a, environment: e }`, before any argument prefix executes. It retains `receiving.delay(d,inherited)` as v_d. Here a is an Apply subtree, so `direct_formal_root` does not recognize a direct executable formal Name; no root grant is manufactured by delay construction.
2. Reads the actual resolved D from the returned Operation value; requires D.signature's own effects absent and value Function. The role is **Computation iff argument.effects.is_some()**, otherwise Value. It does not compare row contents, solved support, argument usage, or operation-family equality to select this branch.
3. Enters one new operation invocation u using A.site and the existing operation provider site. It pushes OperationResultConsumer(s), then ReceiverReturn(u,previous) above F. Thus forcing, when selected, occurs inside u.
4. **Value branch:** pushes OperationPayload(D,s), then `execute(d,s)` enters the retained argument a in e. Until that argument returns to this exact OperationPayload, no carrier for this outer D/A has been constructed. If it returns r, that frame constructs carrier q containing exactly D, r and s. This is an ordering postcondition, not a guarantee that forcing completes. An effectful argument in another source might itself publish different requests; the no-request application below depends on this exact argument.
5. **Computation branch:** calls `make_request_carrier` immediately with payload `(value=d, interface=Computation, view=v_d)` and D/s. It does **not** call `execute(d)`, enter B_loop, force P or cache the argument result. The carrier q is also RuntimeValueKind::Computation but is a distinct handle/executable: q is Request(D,d,s), while d is Delay(a,e).
6. `make_request_carrier` uses `data` to return q as a Value-interface received record with its own opaque view. It has not yet minted a request event. ReceiverReturn retires u and restores the previous owner. The subsequent OperationResultConsumer executes q; only `execute(Request)` mints the fresh event, observes current execution views and installs PendingRequest(D,payload,s,event,empty suffix). The payload keeps the interface/view stored at carrier construction; the carrier's return interface does not overwrite it.

The OperationPayload path does not itself perform a general primitive Int compatibility check. This finite native branch depends on successful static source admission; its ordering and identity constructors are not an independent payload typing/effect preservation theorem. No handler applicability, local_grant result or permission equivalence follows from this postcondition.

## 5. Apply to V: Value entry remains pending through the finite bound

Under H/A, the declaration placeholder contributes no executable computation root and main's block is scheduled. `begin_local` allocates the recursive cell c_L, extends environment 0 with Local(L)→c_L, then evaluates the named Lambda in this environment e_L. The Lambda returns its closure with parameter P, Value role, body B_loop and saved e_L. `Frame::Local` fills c_L with that same closure/view and keeps the recursive environment. Creating this closure does not execute B_loop. The final operation Apply A_V then reaches the postcondition above with argument `loop ()` in e_L.

D_V.argument.effects is None, so the operation invocation u_op is live and its exact OperationPayload(D_V,A_V.site) is pending while the argument is evaluated. The first `loop ()` reads c_L, creates a separate loop invocation and an inert Unit argument delay, then ValueEntry forces Unit and binds P before entering B_loop.

For the bounded recursive suffix, the concrete repeating shape is:

1. B_loop is Apply(Name Local(L), Name Parameter(P)), with no base branch or literal-return body. The current P cell contains received Unit.
2. Local(L) lookup follows the saved closure environment e_L to c_L and retrieves that existing closure. A fresh delay for Name(P) retains the *caller* environment e_n.
3. A new loop invocation enters with ValueEntry(P,B_loop,e_L), forces that Name delay in e_n and receives the same Unit value/view. This Name is Observe because P is Value; it neither publishes a request nor executes a computation payload.
4. ValueEntry binds a new P cell in e_(n+1) whose parent is e_L, then evaluates B_loop again. The pending older loop ReceiverReturn remains below the new call; the original operation's OperationPayload is still below those loop frames. Caller e_n for the argument delay and saved e_L for the new closure body are distinct roles.

This invariant can be checked over the finite prefix of at most 1000 transitions under E/B: bootstrap states either advance through closure/operation/first argument entry or reach this repeating shape; recursive microsteps either progress within these four stages or enter the next one. The only immediate returned data are closure/Unit/Name records consumed by their pending Callee or ValueEntry frames. No loop body returns to its own ReceiverReturn, no base case exposes the lower OperationPayload, and neither bootstrap nor the recursive suffix contains an executed operation Apply other than the still-pending outer A_V. Therefore no request for A_V, or any other request, is published in that successful finite prefix.

`Machine::step` begins at steps=0 and increments once for each of these non-stopped transitions. Under E/B's no-earlier-failure condition, `run(1000)` finds no stopped outcome and reports `ResourceExhausted { steps: 1000 }`. The private machine is paused, not completed. This is a finite invariant/application to the fixed bound, not an assertion of mathematical divergence, infinite resource availability, or behavior after arbitrary future resumptions. A fuel-exhaustion assertion alone would not prove this ordering or absence of an earlier request.

Under the public I/O portion of B, `lib.rs::execute` returns the exhaustion error before value formatting and `main.rs::main` adds one LF and failure status: stdout empty; exact stderr `runtime step budget exhausted after 1000 steps; no completed result\n`.

## 6. Apply to C: Computation payload is published without execution

The local closure knot is constructed exactly as above, so e_L/c_L and the original argument code exist. Only the operation declaration changes: D_C.argument.effects is Some(original empty row). A_C selects Computation entry despite that row having no concrete/variable members. The native postcondition allocates d=Delay(original `loop ()`,e_L), constructs distinct q=Request(D_C,payload d,A_C.site), returns q through u_op, then executes q through OperationResultConsumer.

No loop invocation occurs before this publication: Lambda initialization ran, but neither the `loop ()` argument nor B_loop ran. The published payload handle is d, with RuntimeValueKind::Computation and retained delay executable/environment, not q, a forced Unit, an inferred int, or a reconstructed thunk. Its source allocation site is A_C, while its executable code is the original argument child; these are distinct source roles.

The fresh request is yielded under the restored outer ModuleRun owner. These exact sources contain no Catch. `propagate_request` therefore saves the actual remaining main Root publication frame into the suffix, continues to the empty outer stack, and `stop_unhandled_request` registers SavedContinuation(suffix,observations). It returns `UnhandledRequest` with the unchanged A_C.site, D_C.id, d payload handle and fresh event. The main cell is not published as completed. `continuation_depth(handle).is_some()` establishes a registered saved handle; it does not establish a universal executable-resumption law, response compatibility or permission completeness.

Under E/B this finite straight-line construction reaches unhandled within the 10000-step check. The contract requires the actual paired observation; no measured count is claimed here. The same-HIR assertions must connect A_C's original callee resolution to D_C and its original CallTail occurrence/range `84..93`, separately check payload kind and saved handle, then check the CLI. `execute` formats the unhandled error from that site's range before any completed-result printing; `main` adds LF and failure status: stdout empty; exact stderr `unhandled runtime request at 84..93\n`.

No Catch candidate or local_grant/HandlerEvidence selection occurs. The closed-primitive certificate is not a permission premise for this no-handler path; in particular recursive closures are outside that classifier's closed primitive universe. Empty argument row presence selects entry and does not prove that the payload has run, has negative permission, or is globally effect-free.

## 7. Evidence, omitted cases and parent application

Pinned `runtime_control.rs::value_payload_consumes_fuel_before_publishing_a_request` and `computation_payload_is_published_without_running_it` contain these exact recipes and assert bounded exhaustion/unhandled respectively. Its preparation helper ordinarily solves and retains the same HIR; the unhandled helper checks that HIR's operation ID, payload kind and saved handle. These are read source assertions only. They do not independently establish the exact outer Apply occurrence/ranges, full stderr bytes or the constructor derivation; nothing was executed here.

Pinned `cli_entry_demand.rs` tests ordinary function ignored-argument entry on different sources. Its assertion is not evidence for these native operation call sites or declaration identities. No historical failure, closure proof, handler-extent proof or OperationV1 evidence is reused as an extra dependency. Charter §21 and the current constructors are the direct basis; §24 remains a separation boundary.

The useful result applies to the parent as exactly the declaration-row-presence → native argument-entry → request-publication edge for V/C. All six effect-hygiene parents, method M/T/A, R85 adoption and original Simple-sub/evaluator A/B remain OPEN. F1/FK1 and other independent quantifiers are unchanged. There is no theorem for arbitrary source calls/declarations, universal laziness/strictness, divergence, effects, permission, fresh receiver roles, full source/native soundness/principality or production readiness. Actual static solve and its Simple-sub generation/accumulation/propagation/levels/extrusion/qualifying intrusion/generalization are not replaced or weakened.

| Stable TODO / owner | Exact next evidence | Falsifier |
|---|---|---|
| R127-SOURCE-1 / Luna's independent source reviewer; full_parse, module/local_source/source_annotation, candidate_source/effect, shadow_apply | H/A for actual returned V/C artifacts: original declaration argument None versus Some(empty), L/P resolution, A_V/A_C CallTail identities/ranges, ordinary candidate success and same-HIR RuntimeProgram join. | Diagnostics/refusal/conflicts; wrong original annotation port/owner; lost row presence; unresolved/wrong operation/binder or Apply range/occurrence. |
| R127-ENTRY-1 / Luna's runtime/source reviewer; machine.rs Callee/OperationPayload/ReceiverReturn/OperationResultConsumer/execute and program.rs recursive walk | Review finite native postcondition and V's bounded recursive invariant/C's unexecuted payload lineage. | Native role differs from declaration argument presence; Value outer request carrier/publication before argument return; C executes delay first; payload replaced with carrier/forced value; pending Value frame bypassed. |
| R127-OBSERVE-1 / existing implementation lane and Luna verification owner | Frozen paired typed/public test and sole contract command after all three CLEAN reviews; observe V steps1000 and C same-HIR original request/Computation payload/continuation plus exact streams. | Earlier unavailable/preparation failure, V publishes request/completes, C exhausts or wrong lineage, wrong status/stream bytes, timeout/resource failure. |
| R127-REVIEW-1 / Luna | Fresh compiler/source, spec/authority and regression review of frozen packets; independent adjudication. | Unclosed blocking correspondence finding, or producer/coauthor treated as independent certification. |

TODOs grant no writes or resource expansion. The next existing-envelope result after this freeze belongs to those independent reviewers and the already leased paired observation. The contract's later method/role rotation requires a fresh grant; this producer does not start it.

## 8. Frozen direct pin/access manifest and resources

Contract and all 31 direct input pins matched before writing. Only listed source inputs were inspected; some parser/config files received hash inspection only, so a parser-shape theorem is not inferred from their pins. Startup governance/skills were already read in this current session; their workflow instructions are not added semantic dependencies. Dependency authors are UNKNOWN unless attributed in their source. Exact SHA-256 manifest:

```text
rules/design-authority.md e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1
notes/design/2026-09-29-scc-intrusion-redesign-charter.md 547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed
notes/design/2026-10-11-yulang-inference-top-level-principles.md 7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81
tools/inference-playground/tests/runtime_control.rs 2619e4c8bb006e2d98cf81887091ae372cb1ae3731de76e7b707a97db577009c
tools/inference-playground/tests/cli_entry_demand.rs 283e3518f8d28efedd171cacfe97fc7246225339b1c160d06b3c58944f86c8bc
tools/inference-playground/Cargo.toml 87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56
tools/inference-playground/src/lib.rs bdf996d0264e252e345c05bc77b2adcf625120281244171f0054f1d87a8d1e1b
tools/inference-playground/src/main.rs 75b38435f4634ee35b3e14a54fb4d021b78bda834b4fd53965302a73309e0100
tools/inference-playground/src/output.rs 04e99c5bdb562a8edb8a7e17bdcc03f7b46eaca9d8e13b20216b4dcf3032a88a
tools/inference-playground/src/runtime/machine.rs fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46
tools/inference-playground/src/runtime/mod.rs 64d208743793a03501a76f56bc2b511c50ed40cff3f789757a00b7d608fc846b
tools/inference-playground/src/runtime/program.rs c2363ad42104b895519bb29a8eb9aeda545bd0176cebbd78750d3a2df90849ca
tools/inference-playground/src/runtime/receiving.rs 8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9
tools/inference-playground/src/runtime/continuation.rs 194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3
tools/inference-playground/src/runtime/primitive.rs 97485b9439357497aaf3f19555b1d87eef4aabc955b3a2815f23cf49a65c0153
tools/inference-playground/src/runtime/literal.rs 2fff177a7ba0cabb4930251e1facc8f9be701ff3ec7baa695ce4c182fa1da35f
crates/yu-syntax/src/full_parse.rs 24fdbc0f792b748138bcb1b6fded72714dba7f02880f0d395c914fcff546a8d8
crates/yu-syntax/src/statement.rs fe8ba4e144b0c3ea5c8f451dddea42f718e9c3087aa77bb81447c61a9d213797
crates/yu-syntax/src/declaration/act_decl.rs f1af95a12df81900564c83d0aad541064eb2fff21ca41259b7a943ae3ad4fd74
crates/yu-syntax/src/declaration/binding.rs eb9b7c9b97b999d16b364531fdcfad0bfc0cb377855e86ce6d5b825f5aba3544
crates/yu-syntax/src/type_expr/mod.rs 2e08a49960cd4010ba39641ae509afb7cf59711c1464d3349f5f6db590ebf01f
crates/yu-syntax/src/expression/mod.rs 05d874dd4c2874eb7b24038467c8a74b22fa6f7821a3980f3348683ad02743f1
crates/yu-syntax/src/expression/operator_chain.rs 81db2aec4774f2cd1ddc12b64fd9206cf41cdf3eee00ed740676ffc6d7fc5669
crates/yu-syntax/src/expression/tails/delimited_tail.rs 349fe2335e04a68da7d07803f2dd2eb185887d07bf8c9475ba09af089a76a2cf
crates/yu-hir/src/module.rs 153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907
crates/yu-hir/src/module/local_source.rs 3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786
crates/yu-hir/src/source_identity.rs 7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3
crates/yu-hir/src/module/source_annotation.rs b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f
crates/yu-solver/src/candidate_source.rs 66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c
crates/yu-solver/src/candidate_effect.rs 6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0
crates/yu-solver/src/shadow_apply.rs 838d862dd34fe2b2bd70c5d92c5ce9af0aa98f10f8b6a8eddf313ae798686543
```

First explicit R127 clock: 2026-10-19 11:34:32 UTC. Final resource/stop receipt is in the assigned handoff and returned hash message. Unmeasured producer time is conservatively charged at the full 540-second allocation, without claiming that duration was observed or resetting the cap. Checks are listed-input read/hash/source inspection only: no tests/builds/CLI/probes/formatter/Git, no implementation-path edits, no children, no scratch files. Exact output inventory is this note and `tasks/agent-loop/inbox/20261019-r127-proof.md`. Frozen conditional evidence remains pending independent review and Luna intake.
