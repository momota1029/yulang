# Exact receive/choose diagnostic admission correspondence

Status: candidate source correspondence; independent review NOT RUN. No theorem or production authority.
Author: /root/source_authentication_admission_proof, sole author; no descendants.
Assignment: assignment-source-authentication-admission-proof-20261017, revision 1.
Contract: source-authentication-admission-20261017 rev1, SHA-256 0d7937ca5eb5a080f73112e85a6834bb3f00aedd7301fe023ed6dd4241e8acaf.
Baseline supplied by Luna: cba9d794d1f0498262b3668f9d5cc055c16749e9; no Git operation.
Requested model/effort: gpt-6.1-sol/high. Observed model/effort/session: UNKNOWN. Observed worker identity: /root/source_authentication_admission_proof.

## Parent and actual result

The parent is CHOOSE-SOURCE-2 / RESEARCH-FIXTURE diagnostic-to-owner admission for precisely the frozen 357-byte newly authored receive/choose fixture. Every diagnostic reported for those bytes must have its own owner and admission route. This quantifier covers all three reported diagnostics; it does not cover any other program or historical artifact.

The pinned constructors distinguish one declaration placeholder and two definition-body placeholders. Static inspection predicts that the declaration placeholder is admitted through declaration_errors, that f0's body placeholder can be retained after its LocalSource preflight, and that receive's formal annotation triggers CandidateError::Unsupported before receive's placeholder retention. This is a source-level prediction, not an observed candidate execution. The prior run stopped in the harness before source/root inventory and solve. Actual solve/export outcome remains UNKNOWN.

The exact observation gap matters: the pinned run receipt records kinds, ranges and owner spellings, but omits the Debug values of HirErrorId, DefId, DefinitionRootId, HirOccurrenceId and SourceNodeKey. No raw execution transcript is a direct input. Therefore numeric error IDs below are reconstructed from the pinned ErrorSink and the reported exhaustive three-error sequence, not copied from an observed vector. Concrete parse/artifact-branded identities remain UNKNOWN; ranges never replace these identities.

## Complete diagnostic inventory

| Reported diagnostic | Reconstructed ID (raw observed ID UNKNOWN) | Originating HIR/source owner | Placeholder ownership and route |
| --- | --- | --- | --- |
| UnsupportedItem, 80..130 | HirErrorId(0) | Lowering; first direct root ActDeclaration for ctrl; HirItem::Error. DirectRootItem ordinal reconstructed as 0. Exact parse SourceNodeKey UNKNOWN. | SourceEffectDeclaration for ctrl, formed from the same ActDeclaration node, receives this exact item error ID in placeholder_errors at module.rs:1148–1164. solve_mode collects it into declaration_errors and skips the item when every item ID is in that set. It is accepted by the UnsupportedItem/declaration_errors arm of the final filter, never by permitted_errors. |
| UnsupportedExpression, 147..162 | HirErrorId(1) | Lowering; Value(DefId for f0), binding f0's body OperatorChain for ctrl::choose (). HirBinding.value is Lambda(u, Error([this ID])). Exact branded root/occurrence/key UNKNOWN. | The successful local_source::form result is inserted into local_sources under this same f0 DefinitionRootId before lower_body emits the placeholder. solve_mode obtains that owner through local_source_for, preflights it, then retain_placeholder_errors follows Lambda to Error and extends permitted_errors with this ID. Final UnsupportedExpression membership rule qualifies it if execution reaches that filter. |
| UnsupportedExpression, 328..356 | HirErrorId(2) | Lowering; Value(DefId for receive), binding receive's body OperatorChain containing the brace block. HirBinding.value is Lambda(f, Error([this ID])). Exact branded root/occurrence/key UNKNOWN. | Its own LocalSource is inserted under receive's DefinitionRootId before legacy body lowering. Structurally eligible for Lambda-to-Error retention, but actual source route preflights the carrier first. The formal f annotation fails the negative effect-row condition described below, so this ID is not reached by retain_placeholder_errors on the predicted normal path. It is absent from declaration.placeholder_errors. |

ErrorSink::push (module.rs:2563 onward) constructs HirErrorId from errors.len(). The reported zero structural recoveries produce no syntax errors; the reported complete vector has only these three kinds/ranges. lower_module_with_counters visits direct plans in source order, and lower_plan/lower_body emit them in that order. Thus the ordinal reconstruction is 0,1,2 under the receipt's exhaustive-vector premise. The receipt does not independently display these IDs; runtime confirmation remains a TODO. No additional diagnostic is silently classified.

## Owning constructor and consumer chain

The public shadow::lower_module_with_local_source forwards to module::lower_module_with_local_source (module.rs:1026 onward). That constructor enables local_source and retains parse-owned source nodes. source_annotation::declarations builds ctrl from its ActDeclaration SourceNodeKey, then builds choose from its distinct member/name/signature nodes and resolves the concrete ctrl row from the family namespace. It initially leaves placeholder_errors empty. The lowering loop later copies only the same ActDeclaration item's UnsupportedItem IDs into that declaration. No kind-only blanket permission exists.

For each admitted binding, lower_plan (module.rs:1500 onward) constructs its DefinitionRootId, calls local_source::form with SourceRootId::Definition of that root, and inserts the returned carrier under the identical root. Successful overall HIR lowering is evidence that both required formation calls returned successfully: this path propagates formation failure and does not publish a partial HIR. The prior receipt reports successful HIR lowering; it does not show the runtime roots themselves.

local_source::form retains formal parameter annotations with parse_annotation, scopes the lambda and body under the supplied owner, and Builder::set records each emitted occurrence together with its exact parse-owned source key. That carrier's occurrences are distinct from the legacy Lambda/Error occurrences. Diagnostic retention uses the legacy expression's own error vector; it does not reconstruct an error from a LocalSource range or equate these occurrence lineages.

The local-source projection for f0's application and receive's block is Unsupported for legacy simple body lowering. lower_body emits UnsupportedExpression with Value(id) and returns Error containing that exact emitted ID; lower_plan wraps each body with its admitted lambda. These source paths explain placeholders while preserving the real expression carriers.

CandidateInference::solve calls solve_mode(hir, false). solve_mode (shadow_apply.rs:274 onward) separately accumulates declaration_errors; obtains LocalSource through the same binding root, subject to owns_source_root; runs candidate_source::preflight; and only on success calls retain_placeholder_errors. The latter follows only leading Lambda bodies and retains the encountered Error's IDs. The final HIR error filter additionally checks the exact kind. Collection, constraint generation, scheduling, propagation and export occur after this boundary and are not established by this audit.

## Receiver preflight obstruction

For f0, u's unit annotation contains no effect row, and the resolved choose signature is a function with no outer computation row. Its nested [ctrl] int occurs positively under preflight_annotation(signature, true), so the concrete row satisfies that preflight test. The single family and operation form the namespace used by resolve_operation; no unresolved name is introduced by the fixture's unit call.

For receive, the formal annotation is T = Unit -> (Unit -> [ctrl] Int). parse_type_source preserves the arrow result nesting and parse_row records concrete=[ctrl], variables=[]; the parentheses do not discard the result row. preflight visits LocalSourceForm::Lambda for f and invokes preflight_formal_value(T.value, false). Expanding its actual recursive predicate:

1. The outer function calls preflight_formal(Unit, true) and preflight_formal(Unit -> [ctrl] Int, false).
2. The second call reaches preflight_formal_value of the inner function at false, then preflight_formal([ctrl] Int, false).
3. For that row the false-polarity branch requires row.concrete.is_empty() && row.variables.len() == 1. Both conjuncts fail.

Therefore candidate_source::preflight returns Unsupported for receive before retain_placeholder_errors can add receive's ID. Assuming ordinary allocations and the pinned reported HIR, the predicted path skips ctrl, preflights/retains f0, then refuses receive. Resource failure could stop earlier; no runtime first-refusal claim is made. Even if the receiver preflight were to pass for some independently justified reason, the final diagnostic filter still needs exact IDs and kinds. This packet does not change that predicate, annotation, fixture or source domain.

## Parent application, history and minimal next evidence

This replaces the previous wholly unclassified diagnostic state with an owner-by-owner candidate argument and a precise source-level admission obstruction. It does not close the parent: actual branded identity observations and the normal solve result remain missing. The minimal already-contracted implementation TODO is to remove only the example's blanket nonempty-hir.errors early stop, retain all printing and existing identity/root checks, and call the unchanged public solve path. No compiler or diagnostic change is proposed.

TODO CHOOSE-SOURCE-2-ADMISSION-OBSERVE-20261017: Luna owns the post-freeze execution receipt; the implementation lane owns only its already-leased harness delta. Required inputs are the unchanged fixture, pinned library constructors and a frozen minimal example. Record raw hir.errors IDs/attachments, declaration and LocalSource root/source identities from existing reporting where available, and exact first observed refusal or successful solve/export. Falsifier: any raw ID differs from its reconstructed owner route, a LocalSource/key is foreign or missing, any diagnostic falls outside the two exact membership/kind rules, or execution contradicts the predicted receiver preflight branch. Missing runtime IDs remain UNKNOWN until actually reported. The present reporting does not print declaration.placeholder_errors directly; do not pretend the next execution observes that field merely because its owner rule was audited.

Reused prior work: the original source-authentication handoff supplies newly authored fixture identity and the public source/solve/export path; the API-repair receipt supplies successful lowering and its three diagnostic summaries. The r2 correction is retained: the old assertion of established HIR incompatibility is withdrawn, and no prior candidate refusal or success is inferred. No historical hygiene theorem is used to discharge an owner premise here. Historical source identity, R_e, complete choose meaning, independent F1/FK1 quantifiers, First-Result adequacy, H1/H2/JOINT_DEC/F5, source-Generalize/public export, principality and production remain OPEN.

## Resources, freeze and pins

Five stages: (1) authorization/pin reconciliation; (2) reported diagnostic inventory; (3) constructor ownership; (4) candidate consumer/polarity audit and parent application; (5) artifact freeze. Cap 300 active seconds; exact active CPU/time not instrumented, conservative charge is full 300 seconds. No tests, builds, probes, Cargo, compiler execution, Git, network, descendants, scratch files or production edits. One initial read/hash command used unavailable python and failed before mutation; python3 performed the hash checks. Reads and SHA-256 checks are static evidence only.

Both exact leased paths are the only new paths. No source dependency was edited. Sole author is this worker. All writes cease after this revision and output hashing; STOPPED at assignment stop condition. Review and integration belong to Luna and a fresh independent reviewer; no self-certification.

Direct pins revalidated before reliance and immediately before writing (all 14 MATCH):

- `crates/yu-hir/src/module.rs` — `2e0c579a525efd5ac4c7ce0f06189c568ed46c7382d4576698a0b8d846c2228e`
- `crates/yu-hir/src/module/source_annotation.rs` — `b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f`
- `crates/yu-hir/src/module/local_source.rs` — `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5`
- `crates/yu-hir/src/shadow.rs` — `2dffd7fd6542eed9fd3346e0672e76197c248be9c84334f341c4d612234b7ee9`
- `crates/yu-solver/src/candidate_source.rs` — `efeacdc547cd71e2a95f83f1c844592b81b6f2649835d77aac00eeca73757d38`
- `crates/yu-solver/src/shadow_apply.rs` — `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf`
- `tools/inference-playground/src/lib.rs` — `b65cfd7200e459c9448438ec979ffeb9eddb35c282600349cebe7ddf3b759bbb`
- `crates/yu-solver/examples/research_source_registration.rs` — `60592afdafd8b545ef0f4410a693bcc5815ce929d2ae64c8b527ec28bdf0643c`
- `tasks/agent-loop/fixtures/20261017-receive-choose.yu` — `969e20e0f38a2c341a96ff4fe07028bf567ca134e0fb24602fadf6e4c723d9c0`
- `tasks/agent-loop/snapshots/20261017-research-source-registration-pre-repair.rs` — `2a58996b1085ca892dcb9a79465054fad9ac0ddfce4b02eb02c51aa9d464bfe1`
- `notes/progress/2026-10-17-source-authentication-api-repair.md` — `3e04e06afe50223241982d38cfbc7fc2903f29f23706456d7fdb39b3816ad06b`
- `notes/progress/2026-10-17-source-authentication-api-repair-r2.md` — `5a22271d31140c14de1c08c66fa6bf800509abfec25ae993709fa8eaee418429`
- `tasks/agent-loop/inbox/20261017-receive-choose-source-authentication.md` — `f52b07be8b6faef34a311fefd42ccd7254898a7476eddf858e19c6756ac3fab5`
- `crates/yu-solver/Cargo.toml` — `7a599e95800c67ca4688b0f91917609345a252aae6d2ea6cd0f413eb1c07893c`
