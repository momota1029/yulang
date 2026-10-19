# R126: normal-return Value arm outside its shallow Catch

Status: conditional finite source/runtime evidence, revision 1; independent review pending. Author: `/root/r118_proof_lane`; no descendants. Authority/contract owner: Luna. Requested model/effort: configured Sol/high; observed model/version/effort: UNKNOWN.

Contract: `tasks/agent-loop/sprints/normal-value-arm-outside-20261019-r126-rev2.md`, SHA-256 `80b994bb759e12f19888512fc2d99c0563eb6497a58e3af3db1b023123237be8`; baseline locator `cbb462687`. The exact grant after CLEAN pre-spec supplies scheduling authority despite the contract's preserved candidate header. Charter §§14–15 supplies the semantic direction; this note supplies only the bounded correspondence below. Top-level inference principles preserve ordinary constraint generation, accumulation, propagation, levels, extrusion, qualifying intrusion and generalization. No inference bypass or restoration requirement is introduced.

## 1. Exact parent contribution and premises

The contribution is one normal-return delimiter-exit edge, applied to two exact sources. If a returned value reaches the actual `Frame::CatchReturn`, successful installation validation is followed by first-Value-arm selection and its binding/evaluation after that frame has been removed. A subsequent fresh request therefore cannot select that removed installation in the immediate arm execution traced here. This applies §§14–15 to the normal-value constructor only. It neither subsumes the operation-arm edge nor proves general handler hygiene.

Separate premises are retained:

- **H (formation):** each exact source returns an authentic ParsedFile with the intended tree and no diagnostics, then its own HIR-owned LocalSource with the Catch, ordered arms, literal, resolved declaration and Apply occurrences described below. No executed parse result is supplied by this lane; parser shape and diagnostics remain a source-formation premise.
- **A (admission):** ordinary candidate preflight, collection and solving succeed without conflicts; RuntimeProgram construction, selection of `main` and the authentic source schedule succeed for that same HIR. Success is not implied by a constructor's existence.
- **E (consumer execution):** the concrete execution reaches the stated states with valid labels, value/view identities and owner/binding evidence; installation validation and any later owner/receiving operations succeed. The local lemma explicitly isolates the validation predicate rather than assuming a rolled-back failure.
- **B (bounded observation):** the finite transitions and public I/O finish within the selected 10000-step/test resource bound, without identity exhaustion, allocation/I/O failure or other unavailable outcome. No execution or exact step count is measured here.

The first missing factual premise for actual execution is H for each returned parse/HIR artifact; successful A and concrete E/B are also unobserved. Conditional constructor reasoning is not a certificate of those premises or parent closure.

## 2. Exact source identities and refinement

Control C: 80 UTF-8 bytes, no final LF; SHA-256 `92bfee56e9d09113e47b12cb87562c8add1a6658d94cfb6a74f24eabf23f9f2c`.

```yu
act signal:
    our ping: () -> int
my main = catch 7 { signal::ping(), k -> 9 }
```

Outside O: 105 UTF-8 bytes, no final LF; SHA-256 `9c733787af2ec9f12b4ba98a150fd0894f2817a1ad838f53b5e6a8d9cd2527cd`.

```yu
act signal:
    our ping: () -> int
my main = catch 7 { signal::ping(), k -> 9, value -> signal::ping() }
```

Let R_C and R_O denote their respective original `main` source roots; D_C and D_O their respective original `SourceOperationDeclaration`s. These independently parsed programs have independent parse/HIR identities. Equal spelling/prefix bytes do not identify D_C with D_O. Within each HIR, the pattern and every resolved operation use must refer to that HIR's own D.

| Fact under H | Owning constructor and retained fact | Consumer/application |
|---|---|---|
| Original syntax ownership | `full_parse.rs::parse_file` creates a new parse brand; `ParsedFile::source_root`, `SourceNode::children/key` preserve brand, green allocation and start. `source_identity.rs::try_source_keys` walks original ancestry. | LocalSource `key` accepts the retained original key. Source identity is not inferred from spelling or byte range. |
| Authentic `signal::ping` declaration | `module.rs` registers Act declarations before expression formation. `source_annotation.rs::declarations` forms family identity from module plus original Act key, operation identity from family plus original member key, and retains signature/name positions. | `local_source.rs::resolve_operation` uses the registered namespace. Under H both patterns resolve to their own D with Function(Unit, Int), no own/argument effects. This is not OperationV1 evidence. |
| Original Catch and ordered arms | `local_source.rs::catch` requires CatchScrutinee/CatchBlock, iterates original CatchArm children in order, skips separators, and stores `source`, `range`, `pattern`, `body`. | C retains one Operation arm; O retains Operation then Value. `RuntimeProgram::from_hir` clones those patterns/source keys/ranges and labels their original bodies. |
| Distinct binder ownership | `catch_value_pattern` forms CatchBinderId from source root, own arm key and ordinal; `k` is ordinal 1 in the Operation arm; `value` is ordinal 0 in the separate Value arm. Work::CatchArm installs only that arm's lexical binders and restores the scope. | Runtime binding uses `Binder::Catch` with this retained ID. C has no Value binder; O's `value` is bound even though its body does not read it. `k` receives no runtime binding on the normal-return path. |
| Original fresh request occurrence in O | In `local_source.rs::expression`, an empty CallTail emits Apply(callee, argument), `source_form=CallTail`; it emits synthetic Unit from the same tail, then the callee Operation from the original operation path. `set` records a fresh HIR occurrence for each expression. | O's Apply A_O has original CallTail range `101..103`. The complete written operation call spans `89..103`. Synthetic Unit shares the tail key/range but has its own HIR occurrence: range or key equality alone cannot identify A_O. |
| Static arms remain ordinary inference inputs | `candidate_source.rs::Work::CatchArms` maps a Value binder to the scrutinee endpoint and emits ordinary CatchOperation actions for resolved Operation arms; it visits every body. `Work::Finish(Catch)` emits scrutinee-effect inclusion (slot 51); without a Value arm it adds scrutinee-value inclusion (slot 52); every arm body contributes value inclusion (slot 50) and effect inclusion (slot 51). | C's unused `9` arm is still collected; O's `9` and fresh operation body are still collected. The runtime absence of a request does not suppress these constraints or establish solve success. Existing action execution and Simple-sub consumers remain responsible for A. |
| Actual code/source link | `RuntimeProgram::from_hir` requires HIR-owned LocalSource, labels child indices within that source, clones Catch/Operation/Apply forms, and puts source root, original occurrence and range into Code.site. | Frame handler is the actual Catch Code; arm.body is its original body label; `Frame::Callee.site` is A_O's Code.site. |

`shadow_apply.rs::CandidateInference::solve` uses ordinary `solve_mode(hir,false,false)`, preflights the retained LocalSource, admits only the retained declaration placeholders, collects candidate constraints and runs the candidate session. This describes the owner path, not successful inference for C/O. `lib.rs::prepare` builds one HIR Arc, passes its clone to that solver, rejects conflicts, and returns the same Arc; `execute` passes that Arc to `RuntimeProgram::from_hir` with default evidence. The typed test must likewise retain its one HIR through solving, code construction and source/request assertions. A separate parse with equal bytes is not the required identity join.

## 3. Local frame postcondition, including failure

Use stack notation F·C with the last frame on the right, where C is the actual `CatchReturn { handler: Hc, environment: e, installation: I }` and I=(occurrence i, execution owner u). Assume I is the unique live occurrence minted for this evaluation, absent from F. `evaluate(Instruction::Catch)` obtains i from `next_handler`, checked-increments it, stores the current execution owner in I, pushes C and evaluates the original scrutinee in e. This is the occurrence being removed, not every Catch with the same source or operation family.

Given `State::Return(r)` and stack F·C, `machine.rs::return_value` executes:

1. `self.frames.pop()` obtains C, leaving F **before validation**.
2. `validate_handler_installation(I)` requires `i < next_handler`, `u == current_execution_owner()`, and `owner_active(u)`. ModuleRun is always the distinct ambient owner; an invocation must be present and active. Validation does not itself reinstall or retire a handler.
3. Only after successful validation, the handler must contain `Instruction::Catch`; source/code formation supplies this invariant. The code uses `arms.iter().find` with `Value(_)`, hence the first Value arm in retained order. It does not execute an Operation arm or test an operation request's eligibility on this path.
4. For a Value Binder b, `bind(e,Binder::Catch(b.id),r')` allocates a cell and extends the current environment arena, with `r'.value=r.value`, `r'.view=r.view`, and interface Value. For wildcard it keeps e. No saved store is restored and no new invocation is entered for this value-arm binding.
5. With an arm it sets `Evaluate { code: arm.body, environment: e' }`; without a Value arm it sets `Return(r)`. Neither branch pushes C or a replacement handler frame. Therefore the immediate post-state has exactly F as its frame prefix and no installed I.

**Failure limit.** If step 2 fails, the removed frame is not restored by this function. `Machine::step` converts the error to `Stopped(Unavailable(InvalidSourceReference))`. No arm selection/binding/evaluation or successful return postcondition follows. We claim no rollback, retry, resource-capacity restoration or completed result. The successful local lemma must not be applied to this failure state. Top-level inference abnormal-path policy does not supply a runtime rollback theorem.

**Subsequent request corollary for this bounded body.** In `propagate_request`, only an actual top `CatchReturn` can be considered as a candidate; any matching arm must then pass its own installation/typed evidence checks. Otherwise propagation removes one actual outer frame into the request suffix and continues. Since this Value body contains only its original ordinary operation Apply, it neither creates a Catch nor enters a saved continuation/template. I is absent throughout this traced request construction/propagation. It cannot be selected. This is a claim about the exited occurrence I. A genuinely present outer handler would have its own occurrence and checks; a body with explicit reapplication or resumption requires further reasoning beyond this corollary.

The selected installer's owner can remain live while its Catch frame is absent. Owner liveness is one validation input, not a handler-installation registry or permission to select a removed frame.

## 4. Apply to C: preserve normal value 7

Under H/A, the Act placeholder is retained only as an admitted declaration item; it contributes no executable computation root. `from_hir` classifies `main`'s Catch as a computation and schedules it. `start`/`begin_root` enters it in environment 0 under ModuleRun with its actual Root publication frame. Evaluating its Catch pushes I_C and evaluates the original integer 7. `literal::integer` canonicalizes this admitted spelling to `7`; `ground_data` returns its handle and ground view with Value interface.

On return, I_C passes the stated ModuleRun validation under E. The lemma pops I_C, finds no Value arm, and returns that same received record. It never evaluates Operation arm body `9`, binds `k`, forms a ping request or calls its HandlerEvidence consumer. The Root frame stores the same value/view, removes its initializing marker and advances the source schedule. With no further roots the selected main cell completes with integer 7. Under B, `lib.rs::execute` formats `7` plus LF, and `main.rs` prints it and returns success: stdout `7\n`, stderr empty.

This conclusion comes from the frame/branch path. An observed integer 7 alone would not establish that no arm ran.

## 5. Apply to O: fresh request outside I_O

The same scrutinee prefix returns ground 7 to I_O. Successful post-pop validation now finds the sole Value arm after skipping the Operation arm. It binds original b_value to the existing received 7/view in e_value and evaluates that arm's original Apply A_O. `k` and its body `9` remain unevaluated. There was no original body operation request whose eligibility could be reused; the scrutinee was a literal.

The finite request construction, with I_O absent, is:

| Transition | Preserved identity/state |
|---|---|
| `evaluate(Apply)` | Push Callee with original A_O.site and evaluate its resolved Operation child. |
| Return operation value to Callee | Allocate an inert delay for the synthetic Unit in e_value; resolve the existing operation declaration D_O, require its Function signature and absent declaration effects, derive Value payload role from absent argument effects; enter a fresh operation invocation. |
| Operation argument entry | Push OperationResultConsumer(A_O.site), ReceiverReturn for that invocation, then OperationPayload(D_O,A_O.site); execute delay and evaluate Unit. Unit is ground; this is separate from scrutinee 7. |
| Return to OperationPayload | `make_request_carrier` retains exactly D_O, that Unit received record and A_O.site in `ExecutableValue::Request`. It returns an opaque computation carrier. No event has been yielded yet. |
| ReceiverReturn then OperationResultConsumer | Retire the operation invocation and restore ModuleRun; the consumer executes the carrier. Thus the request is yielded after this invocation return, with the actual outer stack. |
| `execute(Request)` | Mint one fresh event, retain declaration/payload/source, take current observations, initialize an empty suffix, and set `State::Request`. No call to local_grant or selected-I_O evidence has occurred. |
| `propagate_request` | There is no CatchReturn I_O to inspect. On this exact root path only the main Root publication frame remains; propagation saves it as an ordinary suffix frame, then reaches the empty outer stack and calls `stop_unhandled_request`. It does not publish main's partial result. |
| `stop_unhandled_request` | Register a SavedContinuation from the retained suffix/observations, return its ContinuationHandle and `UnhandledRequest` with unchanged A_O.site, D_O.id, Unit value handle and fresh event. `continuation_depth(handle).is_some()` means the actual saved handle exists; this packet claims no universal resumption law from that API. |

The saved source is passed from A_O through Callee, OperationPayload, carrier and PendingRequest to the unhandled outcome. It remains `(R_O, occurrence(A_O), 101..103)`, not the operation-pattern key, synthetic Unit occurrence, scrutinee occurrence or complete written-call span. The returned operation ID is D_O.id from this HIR's original operation declaration. Event, payload and suffix are this fresh request's lineages. No original request or expired handler grant is manufactured.

`primitive.rs::closed_primitive` withholds its whole-program negative-visibility certificate for a non-wildcard continuation pattern such as this `k`. Certificate absence is not proof of ineligibility. It is irrelevant to the successful normal-return branch and the outside request's lack of an installed handler: `local_grant`/HandlerEvidence is only consulted inside the actual matching-Catch candidate branch. Thus preparation failure or `Unavailable(HandlerEvidence)` is not substituted for this predicted unhandled result. If either occurs concretely, A/E has failed and the finite source claim is unestablished.

Under B the public `execute` unhandled branch formats exactly `unhandled runtime request at 101..103`; it returns Err before result printing. `main.rs` prints that error with LF and returns failure: stdout empty, stderr `unhandled runtime request at 101..103\n`. The typed unhandled outcome, original source identity and continuation existence are separate obligations from the CLI text.

## 6. Evidence limits, falsifiers and parent handoff

`runtime_control.rs::operation_only_catch_preserves_normal_return` and `normal_return_arm_executes_outside_the_catch` already contain these source recipes. Its helpers parse/lower, ordinarily solve, start and assert completion or same-HIR operation/Unit/continuation existence. Those are inspected source assertions only; no test ran here. Existing assertions do not establish exact Apply occurrence/range or CLI behavior, and neither existing nor proposed output assertions derive the local frame postcondition.

No R118 proof or prior failure is used as an unstated dependency. This packet derives its normal-return edge directly from pinned source; the distinct operation-arm parent remains separate. No OperationV1 witness, fresh-receiver law, general selector priority, general Catch/delimiter theorem, full source/native correspondence, soundness/principality, method M/T/A, R85 adoption, six effect parents or Simple-sub/evaluator A/B closure follows. Independent F1/FK1 and other original quantifiers remain unchanged and OPEN.

| Stable TODO / evidence owner | First missing input and required result | Exact falsifier |
|---|---|---|
| R126-SOURCE-1 / Luna's source reviewer; full_parse, module/local_source, candidate_source, shadow_apply | Returned exact C/O parsed/HIR artifacts, successful ordinary candidate/runtime admission and same-HIR source joins. Review the retained ordered arms and A_O, not a reparsed spelling proxy. | Diagnostic/refusal/conflict; reordered/wrong arm or binder owner; unresolved/different operation; A_O not original CallTail Apply at 101..103. |
| R126-RETURN-1 / Luna's runtime/source reviewer; machine.rs return_value, validate_handler_installation, propagate_request | Review the successful-validation postcondition and its use in these exact traces; retain failure-after-pop branch. | I still installed when the binder/body evaluates; arm pushes/reinstalls I; original I selects the fresh request; validation failure treated as completed/rolled back. |
| R126-OBSERVE-1 / existing implementation lane and Luna verification owner | Frozen paired typed/public test and, only after three CLEAN independent reviews, the contract's sole targeted command. Keep source, operation, Unit and saved-handle assertions separate from streams. | Either typed/CLI outcome differs, unavailable/preparation failure replaces unhandled, lost source/event/payload/continuation lineage, timeout/resource exhaustion or stream mismatch. |
| R126-REVIEW-1 / Luna | Independent compiler/source, spec/authority and regression review on these frozen bytes and the disjoint implementation packet. | Any unclosed blocking correspondence finding; producer/coauthor treated as independent certification. |

These TODOs request evidence and grant no writes, checks or new resources. Next authorized result after this producer freeze is independent review plus the already leased paired observation. Source and implementation owners remain disjoint; there is no production-code TODO or widened source domain.

## 7. Frozen input/access manifest

The contract and all 30 direct pins below matched before writing. Source inspection was limited to these listed files; startup governance/skills/current state were read for operating instructions, not as additional semantic/proof dependencies. Some listed parser/config files were hash-inspected only: their mere presence is not a derived parser-shape theorem. SHA-256 values are exact bytes; historical baseline is a locator, not a Git command observation. Dependency authors are UNKNOWN unless attributed in their own source; this producer authors only this note and its assigned handoff.

```text
rules/design-authority.md e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1
notes/design/2026-09-29-scc-intrusion-redesign-charter.md 547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed
notes/design/2026-10-11-yulang-inference-top-level-principles.md 7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81
tools/inference-playground/tests/runtime_control.rs 2619e4c8bb006e2d98cf81887091ae372cb1ae3731de76e7b707a97db577009c
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
crates/yu-syntax/src/expression/case_like.rs 6e306bc420e4084832008b64cf39c790648fc1510ba3f1de2876590f79ebe961
crates/yu-syntax/src/pattern/mod.rs 1b608422c93ce0f6947125a9b1ea88314a48b3a5e45030ed23e5154492ad7883
crates/yu-syntax/src/pattern/delimited.rs 9da9ec948775b438a85ca3f27c2805254a4f4171caddb54cabe44e563d017029
crates/yu-syntax/src/declaration/act_decl.rs f1af95a12df81900564c83d0aad541064eb2fff21ca41259b7a943ae3ad4fd74
crates/yu-syntax/src/declaration/binding.rs eb9b7c9b97b999d16b364531fdcfad0bfc0cb377855e86ce6d5b825f5aba3544
crates/yu-syntax/src/type_expr/mod.rs 2e08a49960cd4010ba39641ae509afb7cf59711c1464d3349f5f6db590ebf01f
crates/yu-hir/src/module.rs 153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907
crates/yu-hir/src/module/local_source.rs 3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786
crates/yu-hir/src/source_identity.rs 7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3
crates/yu-hir/src/module/source_annotation.rs b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f
crates/yu-solver/src/candidate_source.rs 66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c
crates/yu-solver/src/candidate_effect.rs 6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0
crates/yu-solver/src/shadow_apply.rs 838d862dd34fe2b2bd70c5d92c5ce9af0aa98f10f8b6a8eddf313ae798686543
```

Checks: listed-input source/read/hash inspection only; no executable verification, test/build/CLI/probe/formatter/Git. Only this note and `tasks/agent-loop/inbox/20261019-r126-proof.md` are written; no scratch paths or descendants. First explicit clock: 2026-10-19 11:15:57 UTC. Final elapsed time and immutable output hashes are reported in the handoff/stop receipt; unmeasured time is conservatively reserved as the full 600-second lane charge. Producer freeze is not approval or production authority.
