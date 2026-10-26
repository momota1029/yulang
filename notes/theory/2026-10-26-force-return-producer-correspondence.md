# Force result producer correspondence: exact source/runtime frontier

Status: frozen source-construction result for `PAPER-VIEW-INTEGRATION-RETURN-PRODUCER-20261026/r1`. This is a correspondence artifact, not a proof of the parent inference/execution theorem, not a semantic change, and not production approval. The ReturnView two-input rule and FL12 frontier argument are reused as already reviewed; neither is reproved here.

## Concrete same-execution source path

Use the existing `machine.rs::computation_completion_preserves_the_actual_result_record` Function-valued fixture:

```yulang
my relay (thunk:[] (int -> int)) = thunk
my main = relay (\x -> x)
```

The fixture table also contains symbolic `thunk:[] 'a`, forwarding through `forward(input:[] 'b)`, and an effectful/captured/replayed result whose final tuple contains a lambda. The test body checks that each `RootCompReturn` leaves the same `(ValueHandle, ParameterRole, ViewHandle, dispatch)` in `State::Return`. No test was run in this packet.

For this concrete Function result, keep the identities separate:

* **Source owner/formal/annotation.** `relay`'s retained local source formal is identified by its `HirParameterId`, source node, and source root. Its `SourceAnnotation` records that owner, the annotation position, outer `[]`, and the nested `Function { argument: int, result: int }` tree. `RootCompSchema` retains the exact `SourceSite` and cloned `LocalSourceParameter`; its constructor validates matching source roots and an outer effect annotation. It does not replace the nested tree with an inferred/profile instance.
* **Consumed root C.** The `relay` Lambda instruction carries that schema. Applying `relay` wraps its actual argument in a Delay. At computation entry the runtime creates the RootComp boundary/image from the inherited delay view and the retained schema. The exact resolved Execute-Name of formal `thunk` binds/forwards that RootComp view; `consume` mints a receipt for this same view and opens its `ExecutionView` before executing the delay. This opened, source-owned view is C for this execution.
* **Actual result W.** Executing the delayed argument evaluates the source lambda `\x -> x`, constructing its actual closure at its own source site and lexical environment. `data` creates its actual opaque value view. That closure's executable record carries its own formal/root schema (empty in this example), which describes its own entry; it is not C's result map. The whole result `ReceivedValue` is the W record of this execution.
* **Return and next consumer.** `Frame::RootCompReturn` verifies that W's view still matches W's value, closes C's exact execution occurrence, then returns the original W record unchanged. The caller can retain/cache/forward that handle. When later used as a callee, the Call dispatch selects the closure by value and enters its executable body; this path does not open the returned W view as a complete callable observation. Thus the actual result exists and survives, while the later complete-Call consumer edge remains absent from the current path.

This yields the concrete runtime relation `C --execute one delayed argument--> W`, with distinct C and W identities in one execution. It does not identify them by closure/value equality. The existing fixture establishes a source-specific preservation obligation for concrete, symbolic, captured and replayed result records; it does not derive the paper's result-path correspondence.

## Retained source evidence and first missing output

The evidence is stronger than “no runtime field is named χ.” HIR retains the source annotation owner/position and complete nested Function tree; `LocalSourceParameter` retains the formal ID, source key, range, scope and annotation. Source identity retains parameter origin, and member source retains its original member header/root parameter. The lambda body remains a `LocalSource` expression tree with owner/occurrence identity. The input needed to attempt a source derivation has not been erased at HIR formation.

The first missing output is the **result-edge exporter at `RootCompSchema::original_parameter` / the program Lambda and member-template constructors**. The current constructor output is exactly `(SourceSite, LocalSourceParameter)` packaged as `RootCompSchema { lambda, formal }`; the `Instruction::Lambda` output adds the argument ID, role, body label, and optional root/callback schemas. For the example this preserves C's declaration tree and the returned lambda's actual source site/body, but exports no source-owned, same-execution result slot that joins:

1. the nested `C.result` position/contract from C's retained formal tree,
2. the actual returned callable producer W and its source-owned typed interface/body-result derivation, and
3. the concrete source instance/substitution connecting those positions for this execution.

The consumer side confirms the boundary: `RootCompReturn` receives only the execution and actual `ReceivedValue`; it closes the execution and preserves W. No constructor between these owners emits a `CallableExport`, `C.result` edge, result-position instance, or actual `M_C` transfer into W. This is a missing exported correspondence operation, not proof that the retained tree or `Image`/`Boundary` graph could never support one. An exporter may still be derivable from the existing owner/formal/body data; its derivation must come from the actual source rules and instance, not from annotation shape alone.

The effectful nested-result discriminator should be a source derivation of the form `relay(thunk:[] (int -> [io] int)) = thunk` whose actual returned closure has an `io`-performing result and is subsequently called under a source `io` consumer. The nested row is presently retained as annotation data inside the formal tree. It is not, by itself, an inferred `T`, a profile supplier, a source instance, or proof that an `io` edge is produced. The falsifying/required consumer distinction is to compare that same-execution source path with an otherwise matching pure result and observe whether the later complete Call opens/transfers the nested result path. Runtime-tag shape inference from the returned closure is invalid.

## Reuse of ReturnView and FL12

For this execution, the established target remains

```text
ReturnView(C,W) = M_W* W union_tagged M_C* V_C
```

The direct formal-forwarding route gives a concrete candidate for `M_W` as identity on the actual returned W record's original coordinates; that identifies which result record is preserved, not a proof that every typed result path is mapped identically. The existing root image is the C-side entry evidence. It is not a constructed `M_C` over `C.result`: the source-exported result edge and its instance are the missing construction above. Keep any incidence already on W, any independently supplied C-result incidence, unknown coverage, source tags, and distinct owners separate.

FL12's already-reviewed frontier criterion applies after the actual result-producing batch and complete consumer are identified. Here the exact C execution has a normal-leave event and W is preserved, but current `RootCompReturn` contributes no explicit result-frontier batch from C to W, and the subsequent Call does not open W's complete typed view. Therefore no concrete frontier equality can be asserted for this path. This does not refute FL12 or prove the parent A/B premise false.

## Exact evidence inspected

All direct source hashes below match the sprint contract pins:

| Pinned source | SHA-256 |
| --- | --- |
| `tools/inference-playground/src/runtime/program.rs` | `6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907` |
| `tools/inference-playground/src/runtime/machine.rs` | `b621ba8ec28d7819db881a4fd5bad0236edbf23e2aa92a879eb1dd211a30c46e` |
| `tools/inference-playground/src/runtime/receiving.rs` | `57b1664e26f137e6425731dde2bb1f1559170d9914f5be7a0f17fae3a8555e26` |
| `crates/yu-hir/src/module/source_annotation.rs` | `409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f` |
| `crates/yu-hir/src/module/local_source.rs` | `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1` |
| `crates/yu-hir/src/module/source_role.rs` | `d16945ae153d25cdadea9e9071cdfc2ab73925b46d92e598a0e18e5d60f4d3e3` |
| `crates/yu-hir/src/source_identity.rs` | `4bd5fa4066a1fd445a9757374c44d602decd1d791a394cd81c6066efa063fb23` |

Relevant pinned locations: `source_annotation.rs:125–160,543–599`; `local_source.rs:63–75,572–584,1145–1169,2745–2789`; `source_role.rs:30–55,65–90`; `source_identity.rs:6–23`; `program.rs:278–286,819–850,1022–1061`; `receiving.rs:17–59,224–259`; `machine.rs:165–205,238–240,864–899,1000–1004,1087–1096,1224–1325,2469–2500,2640–2699,3115–3145`.

Reused source/proof evidence: `notes/theory/2026-10-16-runtime-function-result-view-projection.md` §3 (`ReturnView`), §§4–5 (producer/consumer and source induction), plus its owner audit; `notes/theory/2026-10-16-runtime-function-result-source-construction.md` §§3–5 (dependent Result slot, actual producer, result consumer); `notes/theory/2026-10-25-force-local-applicability.md` (FL12); `tasks/agent-loop/sprints/paper-view-exposure-20261026-r1-outcome.md` (native equations accepted, field-name impossibility rejected); and `tasks/agent-loop/inbox/paper-view-exposure-20261026-native.md` (lifecycle facts reused, no source producer mapping). No Rust behavior or semantic interpretation changed.

## Parent application and remaining owner

This narrows the current source/native obstruction from generic representation absence to a precise producer-output obligation: derive and export the same-execution `C.result` to actual W edge from the retained source owner/formal/body/result tree and its actual instance, then identify its designated complete-Call consumer. The source result/elimination owner must supply that derivation; the program Lambda/member constructor must retain/export it; `RootCompReturn` and later Call need an independently reviewed correspondence/consumer account. No safe Rust slice is justified by this source packet, so production remains OPEN and Rust remains `NO_SAFE_CODE_SLICE`.

Unresolved premises include the original full parent theorem and A/B quantifiers, source instantiation/profile construction, semantic legality of the full two-input result transport, exact FL12 satisfaction for this source producer, complete Call observation, all unrelated result forms (including symbolic/captured/replayed/operation), source/native correspondence beyond this concrete path, and production conformance. Do not turn the concrete discriminator into a source restriction.
