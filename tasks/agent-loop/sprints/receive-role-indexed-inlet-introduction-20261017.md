# Sprint receive-role-indexed-inlet-introduction-20261017 — define the first missing source clause

Status: READY / Luna-approved for candidate design and bounded preservation attempt
Branch / baseline: `research/simple-sub-intrusion` / `b89ed524f`
Contract revision: 1
Authority: user authorizes autonomous procedure changes and drafting bridge rules for independent review. No semantic adoption or compiler-code authority.

## Goal and fixed outcome

Parent Goal remains **型推論と実行器が証明込みで実装できるまで続ける**. The predecessor proposal/proof sprint ended reviewed-partial: original `F2/xi` lacks a source-local inlet and role/entry introduction, followed by independent Strict-input, joint embedding and transport obligations. Do not repeat its owner census or another Generalize proof.

This sprint isolates the first missing local primitive at original c2 `g(Unit)`. Draft concrete source clauses for an inlet and shared role/entry relation from actual declarations, definitions and uses, with its owning dependent telescope and lawful source transport; then attempt preservation at the original `F2/xi`. Separately, Luna traces selected source case `my apply f = { my step x = f x; step }` through source identity, capture/alias and fresh-use handling to runtime Lambda entry classification. The source trace may contribute evidence to the later Strict question but does not prove arbitrary c2, Pure/Handler meaning, complete I/R/IF or production acceptance.

The source clause stays an unselected proposal. Any changed fixed meaning or behavior is returned for user adoption. A missing premise is not repaired by narrowing source domains or treating a desired completed field as an input.

## Sequential bounded lanes and exact leases

### Candidate clause and preservation — Astra/medium, maximum 840 seconds

Starts only after this contract is committed/pushed. Write:

- `notes/design/2026-10-17-receive-role-indexed-inlet-introduction.md`
- `tasks/agent-loop/inbox/20261017-receive-role-indexed-inlet-introduction.md`

Use the exact previous reviewed-partial artifacts and direct dependencies below. Specify a source-local rule that constructs the first inlet and role/entry relation; it cannot accept complete `L2`, `I2`, the desired role package, `WF_Dec(F2)`, membership, `VIncl` or `Q` as opaque premises. Keep ordinary unsolved component/use constraints, original identities, typed paths and each field's owner/binder. State which dependencies are shared, description-owned and provider-dependent; the actual provider remains universally quantified and is not selected during formation.

Attempt local telescope/well-formedness and lawful substitution, graft and later-event restriction for the exact clauses, and apply them at original `F2/xi`. Distinguish proved consequences from the proposed local meaning. If the rule needs a new semantic clause, state the exact observable boundary and leave it unselected. Do not attempt complete `R/IF` construction, arbitrary joint `DescMem` representation, source `T`, native MODEL or parent closure in this sprint.

### Selected-source identity trace — Luna/high, maximum 360 seconds, after proof freeze

Write:

- `notes/theory/2026-10-17-value-entry-formal-provenance-through-local-use.md`
- `tasks/agent-loop/inbox/20261017-value-entry-formal-provenance-through-local-use.md`

Trace the selected `my apply f = { my step x = f x; step }` case from retained HIR/source Lambda and formal identities, through candidate Call capture/alias and native fresh-use remapping, to `tools/inference-playground`'s runtime Lambda `ParameterRole`. Give a field-level correspondence or identify the first identity/producer lost. Distinguish runtime Value/Computation entry classification from semantic Pure/Handler role. Record every source function/consumer and frozen dependency hash.

This is read-only source correspondence research. No production edit, fixture/test/expected-output change, test/build/probe/execution, behavior selection, or implementation readiness claim. If the source path does not supply a safe code slice, record that exact boundary; do not manufacture one.

## Frozen direct dependencies

All hashes are current bytes recomputed at sprint preparation. Recompute before reliance; any changed pin returns to Luna.

| Input | SHA-256 | Limit |
|---|---|---|
| `tasks/agent-loop/sprints/receive-function-introduction-proposal-20261017.md` | `eeca47fc455c5aac9b5f9bb4e5ce6b10b7921599a07a693e2c4ac668442a7503` | Predecessor scope; implementation gate remains closed. |
| `notes/design/2026-10-17-receive-function-inference-introduction-proposal.md` | `a021cd088a9b0bab768a3fd509602012dae061c54b13a1353045aa80c15b71d4` | Candidate clauses only; unselected. |
| `notes/theory/2026-10-17-receive-function-introduction-proposal-preservation.md` | `a895b5ecb0c3dbff0b4e1c3653e3486c40860bf63d15eaff0f5c2f129b249812` | Exact first missing law and owner TODOs. |
| `tasks/agent-loop/inbox/20261017-receive-function-inference-introduction-proposal.md` | `dc3ee83fc6bb6cc07de4eb07024721624b122b45138188991142dec5bbc995f0` | Handoff rev3; proof pins predecessor handoff rev1 separately. |
| `tasks/agent-loop/inbox/20261017-receive-function-introduction-proposal-preservation.md` | `c7fcf240746d9383bb4b52d71e1e6e8ad621eb49a28e99024091786411445ea5` | Frozen proof handoff. |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` | Original F2 direction/open fields. |
| `notes/design/2026-10-08-captured-closure-constructor-definition.md` | `6292b778e804988b32d48df663061d01e1593340ccb584fb6a8c0565bd817cfd` | Selected Strict scope, not arbitrary c2. |
| `notes/theory/2026-10-08-captured-call-closure-introduction.md` | `0f8adcf70a72d1f46bd4ca95f3984554d8cf2ff6af6434b679e991e346ffd50f` | Selected constructor's exact I/R/IF inputs. |
| `notes/design/2026-10-08-call-source-interface-definition.md` | `20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c` | IF-Insert/IF-Use incidence only. |
| `notes/design/2026-10-08-native-signature-formation-definition.md` | `e6c6cf995a3618172e45b4f8cdf4578313c057c6ec1e3e118c4dc11b6f162ab9` | Support/profile from actual primitives only. |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` | Downstream preservation/closure, not formation. |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` | Owning records and lawful transport inputs. |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` | Inference direction, safety and natural behavior. |
| `crates/yu-solver/src/candidate_call.rs` | `cbad9cf51a05343eb7a29ab77aac520891467a8aa4edc3201ea3d91f978984a1` | Original formal/name/call records and validation. |
| `crates/yu-solver/src/candidate_source.rs` | `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38` | Source identity and local-use emission. |
| `crates/yu-solver/src/candidate_scheme.rs` | `52b7281946de755003ee8f3b3d18cbc2df6cc6db5566b4e5ecf391b74a92640a` | Capture/fresh-use retained maps and current consumer. |
| `crates/yu-hir/src/source_identity.rs` | `aa97bc34be51644cf944b2813af47ad9243a8eb270850eeb6df34b9cddb3b3a2` | Original source/formal identity origins. |
| `crates/yu-hir/src/shadow.rs` | `2dffd7fd6542eed9fd3346e0672e76197c248be9c84334f341c4d612234b7ee9` | Resolved Lambda/Name/call/capture incidences. |
| `crates/yu-hir/src/module/local_source.rs` | `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5` | Retained local syntax and binder identities. |
| `tools/inference-playground/src/runtime/program.rs` | `b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748` | Runtime plan Lambda role originates from source annotation. |
| `tools/inference-playground/src/runtime/machine.rs` | `b8f15e4617a9d66940183c7327499ff8a2beb1e9cae2abb997137fc1ca464b82` | Runtime closure entry dispatch. |

## Review, resources and stop conditions

Total envelope 1800 seconds: proof 840; source trace 360; fresh compiler_referee, spec_auditor and architect reviews 120 each; coordination 120; reserve 120. Proof and source authors are sequential. Review the complete frozen bundle after both stop: compiler_referee then spec_auditor for candidate rule/parent scope, architect for source correspondence. Reviewers are fresh from both authors. Unused capacity retires.

Preserve the original universal alpha, A1/F2, xi, provider/context/world, raw continuation and future quantifiers. Keep WF_Dec, membership, VIncl, whole-inlet compatibility, CIncl and enclosing joins separate. No source-domain restriction, Unit-based role inference, W/Z selection, semantic adoption, compiler code, tests/builds/probes/execution, expected-output change, source T, anchored native MODEL, production/principality/cutover or parent closure. Luna alone writes current state and integrates/pushes explicit paths non-forced.
