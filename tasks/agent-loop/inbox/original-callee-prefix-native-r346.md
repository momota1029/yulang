# R346 source/native evidence — original callee prefix

Sprint: R346, contract revision as frozen at baseline `cc9749635ea07dcfa4e92dacb1b65ade7830d7af`; contract SHA-256 `3edc4e7c15a94d596d042bd96a930144b7b2a0c290a0bf0f0e99dfef218fc0f3`.
Assignment: source/native investigation; sole writer `/root/r346_native`; no descendants. Exact leased outputs: this inbox file and `/tmp/yulang-r346-native/`.
Parent: unchanged R159 `SourceAppAdmissionR159.app_admission_iff`, full source Union catalogue, children and result correspondence. Outcome class: source-native-evidence, conditional. This handoff does not establish a theorem, source/Inputs law, EI-Result, parent-edge closure or production permission.

## Frozen prior evidence and exact dependencies

The R345 selected EI handoff at `tasks/agent-loop/inbox/original-selected-ei-result-r345.md` hashes to the packet's required `21f3e0e2e300790c657b33bb25213578c1b5c3ac5eca5da16fb831ce94648940`. It remains an obstruction handoff, not a refutation. It correctly accepts EI-Result identity at the selected generated slot while leaving the actual source phase, original arm inventory, result/future incidence and R159 Checking separate.

This inspection is at the exact R346 baseline HEAD. Relevant byte hashes are in `/tmp/yulang-r346-native/evidence-hashes.txt`. In particular the sprint's `R311 SHA ...33f559...` is `OriginalSourceContractResolutionR311.lean`; the distinct `OriginalComputedCallInterpretationR311.lean` inspected here hashes `7d230579...`. R330 is the packet's `fd8ea7...`; R331 is `2aec3d...`; R342 is `b54a3c...`.

## Concrete source equations recovered from R315/R342

The retained source initializer is fixed by `OriginalModuleContextBindingR315.make_initializer_decoded` and the displayed `makeInitializer` equation:

```lean
makeInitializer =
  .lambda seed
    (.block
      (.statementsCons
        (.expressionS (.app (.primitive tick) (.name seed)))
        .statementsNil)
      (.lambda argument (.name argument)))
```

The finite decoder is the actual R315 initializer adapter, and R342's `actual_source_projection` computes this decoded source into a typed higher-order term. Its relevant equations are:

```lean
body a receipts =
  .bind
    (sourceApply (.ret (tickValue receipts)) (.ret (.var 0)))
    (.ret (identityValue a receipts))

program a receipts seed =
  sourceApply (.ret (makeValue a receipts)) (.ret (.int seed))
```

`body_typed` is derived by `CompTyped.bind`; `actual_prefix` supplies eight constructor steps from the outer invocation through the inner `tick` request, with no request-head or finished-prefix premise. R342's `savedContext` retains the nested continuation:

```lean
.bind
  (.bind
    (.bind .hole (.ret (.var 0)))
    (.ret (identityValue a receipts)))
  (.ret (.var 0))
```

`actual_source_response_consumer` and `decoded_source_prefix_and_return` quantify over every `response` satisfying the original tick response typing judgment, preserve the same independently typed `EvalContext` suffix, and derive the resumed result/steps to the identity lambda. This is genuine selected-fixture evidence: the original source initializer is decoded, the `tick seed` source call is projected, its pending Bind body is retained, and all typed tick responses are admitted by the theorem.

Its exact limit matters. R342 proves a finite `TypedCall`/`HigherOrder` constructor path for the R315 initializer, not an interpretation of all original `Inputs`, every raw prefix, all R159 annotations/locals/children, or an independently fixed EI contract. It supplies no mapping from its `Comp`/`Event`/response objects into R331's `RawObservation s`, `Event s`, `Meaning inputs`, or `PrimitiveInput`. It does not identify its response/current state with a same-provider `CalRet` world, nor construct R330's complete source-owned arm/result interpreter. The fact that its finite continuation is typed for all typed responses does not instantiate R311's universally indexed `BindTyped`/future obligations.

## Runtime constructor comparison (read-only)

Actual implementation owners inspected:

- Source/native decoding and projection: `notes/theory/lean/YulangClosure/OriginalModuleContextBindingR315.lean` (`decodeMake`, `makeInitializer`, `make_initializer_decoded`) and `OriginalSourceContinuationR342.lean` (`project`, `actual_source_projection`, `actual_prefix`).
- Runtime Call/Delay owner: `tools/inference-playground/src/runtime/machine.rs` (`Instruction::Apply`, `Frame::Callee`, Callee return transition and `ExecutableValue::Delay`).
- Pending-continuation owner: `tools/inference-playground/src/runtime/continuation.rs` (`TemplateNode::Bind`) and `machine.rs::enter_template`.

The runtime `Instruction::Apply { callee, argument }` pushes `Frame::Callee { callee: Some(callee), argument, environment, site }`, then evaluates the callee. On return, the same frame records the actual returned value handle, receiving view, interface, dispatch and source provider in its test trace; it then allocates an inert `ExecutableValue::Delay { code: argument, environment: caller_environment }`. Delay execution later substitutes the selected environment and evaluates the delayed code. Thus it retains the caller-side argument code/environment separately from the returned callee value/provider. Pending operation continuations are captured as immutable `TemplateNode::Bind` nodes containing cloned saved frames; resume pushes those frames around the response hole. The `Callee` frame's source site, raw callee/argument labels and environment remain present in that Bind node.

The runtime tests and test-only R312/R313 export routines can observe and reject mutations of these concrete labels, views and environment coordinates. They are bounded runtime evidence. A test observation is not a universal source rule, original world law or theorem. `ReceivedValue`/source provider records also do not provide an identified map to the formal `s.Provider` and `Event s`; no current-world compatibility theorem is supplied here.

This agrees structurally with the selected R342 Bind/Delay story: the actual call first evaluates a callee, the argument remains delayed with its caller environment, and the pending ordered suffix is resumed around each response. It is not a proof that the Rust event/provider records equal R342's HigherOrder state, R331's CalRet state, or an original EI clause. No native execution was run in this assignment.

## Exact R311/R330 comparison and first missing bridge

`OriginalComputedCallInterpretationR311.goal` keeps the original source key, original owner/context, result endpoint and semantic operands. Its `.calleePrefix` phase body requests an optional `PrimitiveLeaf` at the goal built from `.callee prior` plus the actual prior observation/event. R331's `selected_prefix_requires_original_declaration` shows that any valid selected phase body entails some resolved prefix leaf. `PrimitiveLeaf` itself authenticates a registry declaration/signature and registered conclusion, but not the source key or `.calleePrefix` use; R331's `change_unchecked_reference` witnesses this interface limit.

R330 independently computes the actual selected Call at source inventory row 13 and its immediately enclosing ViewLogic owner at row 12. `Definition`/`Formed` stores a static `.evalInvoke` with declared operands and a supplied arm list. This identifies the selected source owner and retained constructor expression; it does not produce R342's runtime `prior` as an original `RawObservation`, a source-authenticated `.calleePrefix` law/action, or R331's `PrimitiveInput`. R330 expressly leaves its arm/result correspondence and result/future semantic maps open.

**First missing bridge:** an original-source-owned equation at this exact R330 incidence which maps the independently constructed R315/R342 callee/Bind/Delay history and the concrete native `Frame::Callee` history to one original `Inputs` interpretation: the exact pre-CalRet observation/event; its lawfully licensed complete Call/IF/Bind action; the pending suffix at every response/current state; and the same returned value/provider plus separate live current-event projection. The bridge must establish source-key/use authenticity if it uses R311's `PrimitiveInput`. If the original complete Call semantics instead expose these facts directly without a separately registered prefix leaf, R346 has not proved that route either.

R311's `PrimitiveLeaf` is therefore reported as a requirement of the **existing R311 encoding**, not as a requirement established by original semantics. R345 did not show that original EI semantics demand that particular registry leaf. The next discriminating construction can be a direct source-owned derivation of the original pre-CalRet Call/Bind equations at the R330 incidence, together with its lawful action and the `Inputs` projections above; it should reuse R342's equations without equating distinct semantic domains. Falsifiers remain the packet's changed provider/world, a different pending request/suffix, or an absent independent source owner/arm—not altered expected semantics.

## Parent-edge effect, rejected evidence and status

Before this handoff, the R345 blockage had no concrete selected source Call prefix equations attached to the source/runtime constructor path. R342 narrows that gap for the selected R315 fixture: the source Bind, delayed argument, nested pending continuation and every typed tick response are explicit. This is useful source evidence, but the original EI source/Union edge is unchanged: no R159 child/Checking, EI membership/result, independent catalogue, whole arm inventory, result relation or source-to-Inputs action follows.

Reused: R345's corrected positive EI-Result identity route; R330's exact owner/call locator and disjoint generated registration; R311/R331's explicit first-input condition; R315/R342 decoded source projection and arbitrary typed-suffix/response theorem; runtime frame/continuation definitions as concrete implementation evidence.

Rejected as a bridge: an arbitrary registry leaf labeled `.calleePrefix`; R342 HigherOrder/TypedCall typing as if it implied original `Inputs`; a runtime trace/test sample as a universal source law; `CalleeReturned` provider site as formal `s.Provider` equality; and any assumption that the original contract necessarily uses R311's primitive-registry encoding.

No independent production implementation is authorized by this exact investigation lease. The owners for source projection, EI construction, runtime Call/Delay and continuation are distinct, and the missing cross-owner source-to-Inputs action prevents a safe end-to-end source-to-constraints-to-propagation-to-execution edit. `NO_SAFE_CODE_SLICE` for this assignment; owner-specific dependency is the source-to-Inputs bridge above. No semantics, source domain, diagnostics, tests or compiler code changed.

## Checks, resources, freeze and stop

Read-only checks: baseline `git rev-parse HEAD`; SHA-256 checks for the sprint/handoff/formal inputs; direct source/formal/runtime definition inspection. No build, compiler, test or native execution was run; no heavy process requested. No Git mutation. Bounded source work completed within the 1200-second assignment envelope; exact active seconds were not instrumented, so unused budget is not transferred.

Requested/observed model and effort: UNKNOWN from the runtime metadata available to this child; no model identity is claimed. No model override or hot reload used. Writers stopped: repository writes are limited to this exact handoff; scratch contains only `evidence-hashes.txt`; no child processes or descendants were launched. Disposable scratch owner/cleanup: primary, `/tmp/yulang-r346-native/`.

Frozen handoff ID/revision: `R346-SOURCE-NATIVE`, revision 1. Handoff SHA-256 is reported in the completion receipt after freezing these bytes.
Parent edge/status: source/native contribution improved for the concrete R315 fixture; original EI/Union and R159 remain OPEN. Independent review and primary adjudication are pending.
