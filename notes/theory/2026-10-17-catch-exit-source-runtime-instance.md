# Catch Request-exit source/runtime instance

Status: Static source/runtime correspondence; conditional local noncoverage result. No compiler edit, accepted source execution, semantic adoption or parent closure.

Author: `/root` (Luna primary); sole author. Sprint `catch-request-exit-construction-20261017`, contract rev2 SHA-256 `fd45f91858c063665ab51ce0c581ad179dfbfc24a6d60e87d552a2c14a094781`. Baseline `8f517045d`; inherited semantic checkpoint `e855987e642a02c6060fd2bdd93864a19b0dba3f`.

## Scope and frozen inputs

This packet instantiates only the concrete producer/consumer owners and failure branch from the frozen candidate [Catch Request-exit introduction](../design/2026-10-17-catch-request-exit-introduction-proposal.md), SHA-256 `b0881f12db88442cc0cdbc0f13c08671ec1f083e78f21898bca09575f0be700f`, handoff SHA-256 `edce02b4c4736d5f59f59ba31071a5aa9cb7e31b526fc6834f9e4043982164e4`.

The original FORWARD-FIRST-CALL A/B, F1/FK1, and `CATCH-EXIT-INPUT-1/M_exit` remain OPEN. The adopted matcher-input interface is unchanged. The exact 138-byte specimen has literal SHA-256 `9a86d2e0d0004cbdbd4be96dcdc284b6648287a203518c93211c43705f8ed8d3`; its prior observation returned `UnsupportedItem` at 0..44 and `UnsupportedExpression` at 75..138. Thus the zero-conflict result and native exports refer to partial HIR only. This packet claims neither an accepted source program nor a dynamic specimen run.

Frozen static source pins used below:

```text
8c580da56de25c76146073919840f6d15dec3b11a53c0787309a082dc59e5484 crates/yu-solver/tests/candidate_operation_catch.rs
ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5 crates/yu-hir/src/module/local_source.rs
efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38 crates/yu-solver/src/candidate_source.rs
11a1477ff2c35c03dccb70bdc6121d89d3ced9fadb1921cb8cf8cd5c093b07fb crates/yu-solver/src/candidate_effect.rs
72da8a6e7b3f04ed3f7054b6151410c7d2b35f9f91b756ade1f6f008244c1ce6 crates/yu-solver/src/candidate_context.rs
b8f15e4617a9d66940183c7327499ff8a2beb1e9cae2abb997137fc1ca464b82 tools/inference-playground/src/runtime/machine.rs
194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3 tools/inference-playground/src/runtime/continuation.rs
8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9 tools/inference-playground/src/runtime/receiving.rs
83ee9f49bcf9d18be267f0d7c8297cdfd6b585ff3c5913f899f64c2dc6391ed4 notes/progress/2026-10-17-catch-source-observation.md
d94e24656854fd2d67ed0f600619349c728dfafa26ca6e312f1faa6d3f3532fa notes/design/2026-10-17-source-formation-proposals-adoption.md
cd99aa19cfd301d0ad9f2396c6ef810fc0244f3f08e877ac3f8ce92dd307ba24 notes/design/2026-10-17-catch-matcher-input-formation-proposal.md
ea0b96693114f9cbe9c8e6306b4dcff6fd522baef2c9076277de1a33801a2936 notes/theory/2026-10-17-catch-matcher-input-constructor.md
414cafbe5bbe1b940ffa96fb6f6a9c0b3a3bef5fd3a1aec0dfec3aa5be41329e notes/theory/2026-10-17-catch-exit-typed-incidence.md
064e813a0bcf82019d9379dfa25fd1c825eabd2072c5933f32b28d6d1ea284ae notes/theory/2026-10-17-source-matched-catch-actions.md
```

The proof author's five bounded transitive clause reads were independently matched to the typed-incidence audit pins. They add no semantic authority; see the frozen proof artifact §8 for hashes.

## Producer to consumer equations

The syntax/runtime edges do not line up into the adopted typed exit-input yet:

| Stage | Existing producer / consumer equation | Exact limit at this seam |
|---|---|---|
| Source syntax | `Builder::catch` resolves the declared `ping`, retains Catch/arm/body identities and creates the continuation binder at arm ordinal 1. | This creates source syntax/scope; it does not type a yielded packet or matcher operand use. |
| Candidate scheduling | `Work::CatchArms` retains `original = endpoints[scrutinee]`, scrutinee effect, arm occurrence, binder component and level, then emits `Action::CatchOperation`. | No dynamic `q`, `raw`, actual exit, or `M_exit` field is in this action. |
| Candidate constraints | `candidate_catch_operation` forms response ports under one declaration environment. Slots 62/63 connect k's Function; slots 64/65 retain entry and original full-S effects. Catch finish accumulates scrutinee/arm effects and values. | Scalar constraints and the retained scoped observations in the context engine are not the complete dependent Request-to-matcher typing. They do not provide `Δ_q` or the missing outside operand-use introduction. |
| Dynamic Request allocation | `machine::execute` allocates one event and forms `PendingRequest { declaration, payload, source, event, observations, suffix: [] }`; `receiving::observe` records the current authentic execution/view/receipt observations. | This runtime packet has concrete dynamic identities but no source typing for the original dependent `q`, complete `Δ_q`, or the adopted matcher telescope. It is not evidence that a second q was emitted at handler exit. |
| Request unwinding | `machine::propagate_request` pops actual frames and appends their saved forms to the same request's suffix. It checks current Catch installation, declaration, current local grant where needed, and payload compatibility while the Catch delimiter remains active. | The saved suffix is runtime data, not the source's typed whole continuation and future family. Historical observations do not become current-H incidence. |
| Capture and exit commit | For an eligible candidate that passes all prior premises, `capture_template` packages saved frames with the same declaration and original event. Only after capture succeeds does the path pop the Catch frame and evaluate the selected arm outside it. | Packaging records operational lineage; it does not type `M_exit`, prove preservation into the adopted entry, or construct current outside owners. The target matcher-use introduction identified in the proof artifact is still absent. |
| Resume consumer | `ResumeTemplate.original_event` carries event lineage; `enter_template` runs the retained continuation under its existing runtime control remapping. | Runtime control remapping is not a typed dependent action for all original response/admission/future coordinates. It cannot discharge F1 or FK1. |

These are exact producer-to-consumer field equations only within the pinned implementation. No field equation upgrades a runtime identity or candidate graph edge into a semantic typing derivation.

## First broken join for the specimen

The declaration has result annotation `int -> int`, and the Catch arm binds `k`. In `machine::propagate_request`, after current ownership/grant, operation declaration and payload checks, the continuation-binder branch accepts only Unit, Int, Bool or Str result annotations. For the pinned Function result it returns `RuntimeUnavailable::HandlerEvidence` before `capture_template` and before `self.frames.pop()`.

Therefore, **if control reaches this operation-matching branch for the specimen declaration**, the exact local join stops here:

```text
matched Request + Function response + continuation binder
  -> HandlerEvidence
  -/-> capture_template
  -/-> Catch pop / outside selected-arm entry
```

Earlier source lowering or ownership checks may fail first. The previous partial-HIR receipt already has errors, and no dynamic execution was performed here. This is a static playground-path noncoverage discriminator, not an observed run, a source-qualified counterexample, a language-level rejection, or a proof that all compiler/runtime implementations must reject Function responses.

For primitive response branches that pass this guard, the implementation creates a runtime Continuation and an opaque receiving view after capture. Removing the guard would still leave unanswered: the typed outside μ_H operand-use introduction; actual `M_exit`; full response/future `Δ_q`; typed consumer correspondence; and an accepted complete HIR/source path. Consequently there is no safe compiler-code slice in this seam under the present authority. The tag check cannot be removed as a substitute for those missing proofs.

## Parent application and next exact owner

The source/candidate static equations fix syntax, binder and ordinary constraint endpoints for this specimen. The runtime path exposes a precise earlier obstruction before native exit/capture. The proof candidate separately fixes historical `q/raw/Δ_q` retention equations under original Request/exit premises, but stops at first typed use of q and its packet projections at outside `μ_H`.

Together these results locate the next source owner narrowly: the original `MatchRequest_H`/typed binding/Receive transition must introduce and type its actual operand-use declarations using original q/raw and actual `C_out`; only then can `M_exit` transport the complete dependent paths, profiles and lawful actions into the adopted matcher input. Existing `IF-Use` can preserve an authentic typed occurrence after that rule supplies it. No archival tag, scalar endpoint, successful candidate solve or selected outcome can replace the missing introduction.

No compiler code, tests, fixtures, expectations or semantics changed. No tests, builds, Cargo, probes, or runtime execution were run.
