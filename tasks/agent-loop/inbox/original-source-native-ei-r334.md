# R334 selected source/native trace — frozen revision 1

Assignment `R334-SOURCE-NATIVE`; worker `/root/r334_trace`; sole author, no descendants. Baseline `f5c59e23cc4fb779e89c9679dfa1dfceccbe8da3`. Sprint `tasks/agent-loop/sprints/source-union-registered-r334.md`, SHA-256 `24f645db708baf4ae4e800a4bffd17e7f84c5f85f0ba6711dff544d10adac464`. Requested/observed model and effort, runtime session identifier: UNKNOWN. This is complementary **provisional source-native evidence**, not constructive theorem work or independent review. Exact writes: this handoff and `/tmp/yulang-r334-native`; no Git mutation, children, production/test/config edits, or writes to another lease.

Objective: follow the actual selected R315 nested application `(make 1) value` through declaration lookup, callee Request/response, the retained suffix, CalRet, inert argument and receiver, then identify what actually supports the unchanged R293/R306 consumer and R159 parent. Authority: computed-call-result-constructor §§2–5, especially response/current-world §3.1, receiver/result/future §3.3 and independent arms §4; source IF construction §§4–5; no new language meaning selected. Sprint rules/skill, root/base instructions and research/design/Git rules were read.

## Executable provenance and checks

Two executable classes were distinguished explicitly.

1. Workspace `target/debug/deps/yu_playground-a3f4356353b4ed8e`, SHA-256 `cc7e8ce580e3106067be9935778726202ae6bbe498d6c011985be9ed0d3788e7`, passed the selected test but exported no `R323Artifact`. It is **stale for the current R323 evidence**. Its `same-run.lean`, `native-witness.txt` and `test.log` remain scratch diagnostic evidence and were not attributed to the pinned current source.
2. Existing R324 executable `/tmp/yulang-r324-native/target/debug/deps/yu_playground-a3f4356353b4ed8e`, SHA-256 `9f8e825d35a40d157df6c5ee107a2706e3e9c094d699b5575295833a9ce60bcf`, replayed the selected test and its current mutation controls: **1 passed, 94 filtered, exit 0**. Its complete export is byte-equal to the authenticated R324 frozen artifact `85e663b65a893b0acd5de46b7b1b59e940098bf5e5a7815cada4736a3e983551` after normalizing only the two Machine `runId` encodings. Actual replay artifact: `/tmp/yulang-r334-native/r324-replay.lean`, SHA-256 `0797a9af9e5c9158978eccf674ce37f272aa65b80ad72b9814c608e7d793edb5`. All R314/R315/R323 rows in this replay come from this one execution; old R315 and R324 run-local handles are not joined across runs.

Reproduction:

```sh
YULANG_R313_NATIVE_WITNESS=/tmp/yulang-r334-native/r324-replay-native.txt \
YULANG_R323_LEAN_WITNESS=/tmp/yulang-r334-native/r324-replay.lean \
/usr/bin/time -v \
/tmp/yulang-r324-native/target/debug/deps/yu_playground-a3f4356353b4ed8e \
r313_accepted_source_callee_returns_after_request_and_observes_value_name \
--test-threads=1 --nocapture
```

R324's original source/native receipt records the build/test. Its machine/receiving/program/dispatch hashes match the pinned baseline. Read-only `git diff --name-only 7f520a3bb f5c59e23c -- crates tools/inference-playground apps tools/bench-runner tools/xtask Cargo.toml Cargo.lock .cargo` returned no differences. A baseline archive under scratch freezes **423 files / all workspace member source and manifests included in that archive**; every archived file matched its present repository bytes. The complete SHA inventory is `baseline-inputs.json` (`e2fac630585288369effd77efd14bbf2b3571b0ddac59be4c347c39998a17eb3`), with validation in `source-validation.json`. Thirty-four existing Cargo fingerprint JSON files were hashed in `r324-fingerprint-inventory.json`. This is receipt-backed reuse plus source/artifact equality; **the executable was not independently rebuilt here**, and the old compiler invocation, external registry source contents, build environment and system libraries were not independently reauthenticated. Cargo.lock is pinned below. Fingerprint existence alone is not a source-to-binary proof.

A fresh isolated `CARGO_TARGET_DIR=/tmp/yulang-r334-native/target cargo test --locked --offline -j1 -p yu-playground ... --lib` started before the primary's heavy-slot wait arrived. It was immediately interrupted through tool session `79391`, which returned **exit 130**. No fresh-build success is claimed. Partial Cargo output remains in `pinned-test.log`; target output stays in leased scratch. The primary subsequently authorized reuse of the R324 binary with the provenance limitations above. No build remains active in this lane.

## Concrete selected-source derivation

The fixture is unchanged:

```text
act io:
    our tick: int -> int
my make seed = { io::tick seed; \argument -> argument }
my relay value = make 1 value
my handle (thunk:[io] int) = catch thunk { io::tick(p), k -> handle { k 10 } }
my main = handle { relay 7 }
```

All source identities below retain realm `r312-accepted`, path `callee-history.yu`, binding name and same-name ordinal `0`; numeric occurrence, source-node ordinal, code label, invocation, value, view and declaration address are **different namespaces**.

| Stage | Actual same-run evidence |
| --- | --- |
| Selected source Apply | `relay` source node ordinal 1 / occurrence 12 / bytes 113..118 / code 8 is Apply(code 9, code 10). Callee source node 2 / occurrence 13 / code 9 is Apply(code 11, code 12). Argument source node 3 / occurrence 16 / code 10 is Observe Name of relay parameter 0. |
| Declaration/provider lookup | `make` use occurrence 14 / bytes 106..110 / code 11 is `ModuleDef(make,realm,path,0)` in environment 2, at step 18 under Invocation 1. It resolves to global cell 0 holding closure value 5/view 6, provider `make` occurrence 2 / bytes 33..88, formal 0/body code 1/environment 0; private, not public import. |
| Actual operation identity | `tick` family declaration bytes 0..32, operation declaration 12..32, name 16..20, signature 22..32, visibility Our, structural signature `int -> int`. Make source operation node ordinal 4 is occurrence 5 / code 4. Request application node ordinal 3 is occurrence 4 / bytes 59..63 / code 3. This declaration address is not a runtime request ID. |
| Callee Request | Step 32/order 14: request event 0 at make occurrence 4, live Invocation 2, payload value 7/view 8 = integer `1`. Order 15 records outer pending Callee frame F2, callee code 9/argument code 10/environment 2 and the same selected relay Apply site. |
| Response/resume | Same request 0/template 0: response value 14/view 16 = integer `10` from handle occurrence 27/bytes 191..193. Response checked at step 48 at handle occurrence 25, owner Invocation 5 live. The response is not the source Call's result. |
| Owner replay | Template root 6/count 7. Capture owner Invocation 0 stays active owner 0. Saved Invocation 1 is inactive and replays as new Invocation 6; saved Invocation 2 replays as new Invocation 7, with source-qualified original call/provider sites retained. These are later replay receipts, not response owner 5 or one shared world. |
| Actual CalRet | Step 59/order 22: same frame F2 returns callee closure value 15/view 17/interface Value, provider make occurrence 7 / bytes 65..86 (`\argument -> argument`), under return owner Invocation 6. This is the returned callable, not the whole Apply result. |
| Inert argument / receiver | Delay value 16/view 18 retains code 10/environment 2. Receiver Invocation 8 observes relay Name at step 60/orders 24–25, cell 5/value 4/view 5 = original integer `7`. At step 61/order 26, ValueEntry binds make parameter 1 into fresh cell 10/environment 7, lexical parent environment 3; original relay parameter bind was Invocation 1 / step 15 / cell 5/environment 2. |
| End of executed program | Test asserts `Completed(value 4)` and integer `7`; witness records exactly one Request. No same-run selected receiver-Return event, result/current-world slot assignment or dependent future certificate is exported. |

The saved suffix has exactly this ordered list, also recovered from live template nodes:

```text
BlockExpression(make code1, next1, environment3)
Owner(Invocation2)
Callee(F2, callee code9, argument code10, environment2, relay occurrence12)
Owner(Invocation1)
RootCompReturn(view2, receipt2, occurrence0)
```

Node 0 is Hole; node inner links are `[none,some 0,some 1,some 2,some 3,some 4,some 5]`; final node 6 is the capture-owner boundary. This supports retention of the actual observed suffix, including argument code after CalRet. It does not enumerate all semantic suffixes or independent arms.

Relevant pinned owners: `machine.rs:1369` records Request, `:1945` records checked ResumeArgument response, `:2075` eliminates Callee and captures the pre-Delay arena snapshot, `:2230` records selected closure call, `:2428` handles ReceiverReturn, `:2542` records ValueEntry binding, `:3038` captures suffix/template receipt, `:3142` records Owner replay; exporter `:5297`, selected test `:5526`. The sole arena snapshot is taken at **CalRet**, not at response step 48 or the receiver's later Return.

## First missing original field and exact consumer impact

The earliest unprovided original semantic premise is the **response-time current world/readout and its lawful whole-tuple response action**, not the existence of a native response or saved suffix. `R323ResumeObservation` contains run/request/template, ReceivedValue, source, owner/live and step. It has no response-time `Current.history`/`Current.configuration` readout, no original `Event` decoration (scope/authority/incidence/dictionary/witness), and no map interpreting those fields in the original independent sorts. Later owner replay control maps and the step-59 arena snapshot cannot be equated to that response-time world. A separate source/simulation law could derive this from authenticated execution; no such law was constructed here. This is a missing correspondence input, not a proof that its construction is impossible.

A later independent gap is actual receiver Return/result/future incidence. `Frame::ReceiverReturn` leaves the owner and returns the received value/view; this branch has no R313/R323 selected-return recorder. The existing test's final main value is an observed program result, not an original `Outcome`/result-slot/returned-provider/current-event/future construction. The native `RuntimeValue.source` of integer value 4 is main occurrence 35/bytes 223..224; it must not be substituted for either the returned closure provider or the semantic future provider by matching a value index. Even in this ground-result fixture, all original future/restriction obligations remain genuine.

At R306 `source_contribution_registered`, the same-catalogue equality, complete source `Packet`, and licensed original `DeclContribution` child remain inputs. Native trace supports their concrete source ownership/operand inventory and falsifies conflating request response10, returned callee15 and final result7, or conflating saved/replayed owners. It supplies **none** of the original `Evidence (Meaning inputs) (clause inputs ...)`, licensed Call child, semantic catalogue equality, authentic EI-All registration, independent arm family/laws, registered Checking, or original R159 source child/admission premises. R293's complete guards/world/result/future fields cannot be filled with the native live-owner booleans. No R306/R159 parent edge is claimed discharged.

## Experiment scope, falsifiers and limitations

The discriminating experiment is one deterministic existing accepted-source fixture, run with its existing negative controls. It rejects changed request source/signature/payload view; changed response value/template; fabricated owner resolution; altered template root/order/count/inner link/Callee environment/View receipt; cloned or foreign return snapshots; altered make cell interface; foreign HIR/parse/source; and same-HIR cross-run request/template/response receipts. These tests discriminate provenance/suffix corruption within this fixture. No new mutation or production instrumentation was added.

No random seeds or exhaustive range. Machine run limit 30,000 steps; observation vectors fail closed on truncation at 1,024; CalRet receiving scan bound 4,096, actual 18 views and `receivingScanTruncated=false`; name-call observation bound 64. Unsupported saved-frame/template variants (including handler forwarding) fail closed; other source programs, response values/worlds, receiver Requests, nontermination, arbitrary independent arms and future extensions were not executed. R323 alone validates only its observed suffix subset.

Oracle independence is limited: exporter, runtime and assertions share the parser/HIR/Machine implementation. Expected integer `7`, ordering and mutation assertions provide finite checks; they are not an independent original semantic interpreter or external Oracle. A checker accepting these events does not prove the source transition rules. No Lean theorem, axiom audit, full suite or fresh source-to-binary rebuild was performed.

Measured successful R324 replay: 0.15 s wall, 0.09 s user CPU, peak RSS 21,264 KB. Stale diagnostic replay: 0.14 s wall, 0.13 s user CPU, RSS 21,256 KB. Scratch clock 12:35:18–12:39:40 UTC excludes initial reading and final handoff drafting; exact total active time/aggregate CPU for the interrupted build UNKNOWN, 1,200-second assignment ceiling respected. One Cargo job was interrupted; no parallel heavy build or background process remains. Scratch artifact hashes are in `artifact-hashes.json`; source dependency hashes in `direct-dependencies.json` (`948383b72ad78ed7dc34872ffe94ed019b9d2b3a0e43a3eb19c24927d4045f8d`).

Recommended next action / mutual TODO `R334-NATIVE-WORLD-RETURN-1`: the primary source-law/proof owner should first construct the original typed response/current-world/whole-action correspondence from the genuine operation/continuation laws, using the exact R324 response and replay operands above. Then obtain an authenticated receiver Return/result/provider/current-world incidence construction before supplying the source packet/child to R306. If additional native retention is required, the primary must grant an exact implementation lease; this report grants none. Falsifier: any construction replaces response owner5 with replay owner6/7, freezes the CalRet world as response/future world, uses final main output as a selected Return certificate, or omits an original arm/future domain.

## Commit packet

- Exact leased repository path: `tasks/agent-loop/inbox/original-source-native-ei-r334.md`. Scratch: `/tmp/yulang-r334-native` only; do not commit scratch/build output.
- Baseline: `f5c59e23cc4fb779e89c9679dfa1dfceccbe8da3`; dependency hashes changed by worker: **none**.
- Direct pinned source hashes: machine `7dec51aa5d57b3ef7b5217a4c772355aa75ddf3a88adffae017cdd637ee485ef`; program `2c03ff8681c50520e0527f139a86ac8427097c27aeafcf247e76673310be4b0c`; receiving `476ef914bb11449f106c900a233e9677025830e6923cd5db6a1dc6edbcc6d613`; dispatch `d99acad3e344bc06970faf0486ff7d10ba92bc7514cfb7eec58df8bbb28f6360`; Cargo.lock `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5`.
- R306 `77fa332ef53d272fe67a0c511fdebf9a3def7bf64baebfed84a3eec739ef203e`; R293 `50b1ce82dbd81d8c17a99461a78b77a9066094896f38e046d70fb4dd69365543`; R315 `7adcf88c1ff98c5c4cf23aa788bf5713ddcb949dd09775fb0bd542fe1e2ac577`; governing EI `2f3a5461b6dacaa29e881ba8b3003120b912e441dd5e4c47fc4ccaa27d3b31a6`.
- Review: **NOT_RUN**, producer-authored evidence; research-only checkpoint candidate, no semantic/production/gate approval.
- Checks: existing R324 focused executable test passed; normalized complete-artifact equality passed; 423 baseline/current file hash comparisons passed; fresh Cargo attempt interrupted exit130; stale workspace binary rejected as current evidence; no Lean/full-suite check.
- Proposed commit message: `Record selected source Call native evidence and world/return gaps`.
- Shared-record deltas left for primary/curator: retain R306/R159/EI-All as OPEN; distinguish current R323/R324 response/suffix receipts from R321's historical omission; record stale-binary exclusion and missing original response-world plus receiver Return/future correspondence; retain all independent arms and Checking obligations.
- **Writes STOPPED after this frozen revision. No descendants or running worker-owned processes remain.**
