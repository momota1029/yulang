# Sprint PROVIDER-ROOT-CONTEXT-20261027/r1 — identify the actual provider root Context owner

Status: ADMITTED by Luna after sprint-end dispatch; no semantic expansion approved.
Branch / baseline: `yulang3` / `05ed820354baba5158a0bb3254082f6fe22ec4be`.
Authority: unchanged original Simple-sub source-preservation obligation in `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1, 3, 5; `notes/design/2026-10-11-yulang-inference-top-level-principles.md`; existing source rules in `OriginalSourceSyntax.lean` and `OriginalSourceGeneration.lean`. Dispatcher input: `/root/next_action_selector` sprint-end recommendation (read-only message, no file).

## Original outcome and success evidence

The parent remains the unchanged universal source/executor obligation: all supported original source programs, lawful finite Simple-sub histories and retained extrusion occurrences, preserving lexical/type/event scope, recursive monomorphic sharing, generalization/lawful uses, complete Call, effect hygiene and the required A/B, soundness, principal coverage, progress and inference termination. No parent quantifier or supported form is narrowed. Current parent, source/native, A/B, effect-hygiene and production gates remain OPEN.

This sprint investigates only `PSR-ROOT-CONTEXT-1`, the first missing input after the reviewed lexical bridge. For the unchanged `pub id x = x` fixture, establish the actual owner and preparation path for the incoming `OriginalSource.Context`, or establish a source-qualified `NO_SAFE_CODE_SLICE` because an authoritative constructor/classification rule is absent. Do not choose Context `[]` merely because an adapter uses `SemanticImports::empty()`, or infer binding kind, owner, component, annotation, entry, single-use flag or ordering from export identity, visibility, spelling or opaque caller payload.

Success is one of:

1. Executed source evidence traces the provider's declaration entry and complete relevant lexical/import preparation to an ordered logical `List Binding`; Lean consumes exactly those frozen rows, proves the resulting root Context equation against the existing source preparation owner and applies the unchanged conditional provider application, with every other premise explicit; or
2. `NO_SAFE_CODE_SLICE` names at least two inspected actual owners, the precise absent authoritative constructor/classification and its consumer, the exact evidence checked, and why neither path can derive a genuine root Context without adding semantics. The independent proof lane then records the exact unsupported equation and verifies the accepted lexical theorem still composes only conditionally.

The current `SemanticImports::with_source_imports` and `with_caller_evidence<T>` contracts state source-identity/artifact binding only; opaque payloads are not semantic facts. Report claims only for inspected paths. A finding that a new semantic preparation rule is required returns to Luna for authority review before dependent code is written.

## Two continuing lanes

**Source implementation/evidence lane** — registered `implementer`, Luna/high requested. Inspect actual module declaration entry, `SemanticImports` constructors/consumers, HIR `Definition`/`Parameter` and LocalSource lexical owners, exact exports and the source preparation path. If an existing approved owner establishes the root rows, extend the provider adapter to emit them after branded identity checks. If no owner does, freeze the exact negative scope and `NO_SAFE_CODE_SLICE`; preserve the accepted lexical artifacts. No language semantic or runtime/compiler behavior changes.

Exact source leases:

- `tools/inline-authentic-extraction/src/bin/original_provider_root_context.rs`
- `notes/theory/lean/YulangClosure/OriginalProviderRootContextTrace.lean`
- `tasks/agent-loop/inbox/provider-root-context-20261027-source.md`

Use `CARGO_TARGET_DIR=/tmp/yulang-provider-root-context-20261027/source/target`; all other scratch stays under `/tmp/yulang-provider-root-context-20261027/source/`. Do not access or clean the retained out-of-lease `tools/inline-authentic-extraction/target/` from the previous packet.

**Proof lane** — registered `lean_prover`, Sol/high requested. Inspect exact root Context consumers in `OriginalSourceGeneration`, owner-reification modules, and the unchanged provider conditional. If and only if source rows are authenticated by an existing constructor, define their exact translation and prove the root equation plus application to the accepted lexical bridge. Otherwise freeze a checked precise missing-input statement without promoting an arbitrary Context parameter to an instance. Do not define typing as safety or add a generic theorem whose conclusion merely assumes the missing equation.

Exact proof leases:

- `notes/theory/lean/YulangClosure/OriginalProviderRootContext.lean`
- `tasks/agent-loop/inbox/provider-root-context-20261027-proof.md`

One proof worker owns all Lake/cache writes; use an isolated project under `/tmp/yulang-provider-root-context-20261027/proof/`. No other verifier is allowed concurrently. A fresh read-only `spec_auditor` reviews both frozen handoffs, hashes, scope of negative claims, and exact theorem application; it writes no file. Luna owns all current-state and Git changes.

## Frozen dependencies and prior evidence

Baseline is the commit above. Frozen accepted lexical source/proof/outcome evidence remains:

- Source trace `OriginalProviderLexicalOwnerTrace.lean`, SHA-256 `4719fe129bee3a04fc321589d2c765413ec81cf309d7ad88d118c99b49ed57a0`.
- Lean bridge `OriginalProviderLexicalOwner.lean`, SHA-256 `bf4e6572e5f1bf9b97a4d0274488b8d20f4487528d5bf8346ad262d3c75bd2f7`.
- Source and proof handoffs SHA-256 `6af5a02351de1fd59caa1e2e38f4e8fac67b777c9274e9c9cb44b341954967bf` and `94476af7d5ed0414d1f753d408bfb2877e61b79b5f4cf31df13fb66b2c61a04a`.
- Prior outcome SHA-256 `b1cc727ff2afefb54a5b3601b729a3464fb040dd7e93f7eae97e463f2d27a405`.

Exact source hashes at admission:

| Input | SHA-256 |
|---|---|
| `crates/yu-hir/src/module.rs` | `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646` |
| `crates/yu-hir/src/module/local_source.rs` | `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1` |
| `crates/yu-hir/src/module/source_exports.rs` | `03727fd3918738a48afde7f7a875de60b63b43ac2cc620896a4ed73d8b0a9179` |
| `OriginalSourceSyntax.lean` | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| `OriginalSourceGeneration.lean` | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| `OriginalSourceOwnerReification.lean` | `95d9749ce93ecfc82d6423ba193a261f2725178a7e62cea469b57ae316af3d7e` |
| `OriginalSourceOwnerReificationInstance.lean` | `3aab685323e00b69cb9c21d847582e442590e0ff5e810fab50662b7d9127f887` |
| `OriginalSourceOwnerReificationTrace.lean` | `b9a15df005c730db27fc385c58ca07b433f1095f017e0969155106da7478fb0a` |
| `OriginalProviderPublicationCoverage.lean` | `62257d276004f6caf07872142e4a4369266d5205d992f4f3d56f36657ae69783` |
| `OriginalProviderLexicalOwner.lean` | `bf4e6572e5f1bf9b97a4d0274488b8d20f4487528d5bf8346ad262d3c75bd2f7` |
| `OriginalProviderLexicalOwnerTrace.lean` | `4719fe129bee3a04fc321589d2c765413ec81cf309d7ad88d118c99b49ed57a0` |
| `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` | `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |

Verify this exact dependency cone before writes/builds. Any changed governing input returns to Luna for re-admission. Reuse previous Lean receipts only under matching hashes; do not transfer prior resource allowances.

## Permissions, resources and stop conditions

Fresh envelope: 2400 seconds total (source 700, proof 900, Luna 300, review 400, dispatch 100); Cargo at most 2 calls with `--locked`; Lean at most 6 calls / 240 seconds; tests 0; Astra 0. One heavy build/verifier at a time, one CPU, 1 GiB process RSS and 120 seconds per command; isolated proof cache. No transfer of previous budgets. Unknown writers retain their leases and reservations. No tests, expectation edits, dependency changes, broad cleanup, semantic changes or production cutover.

Stop on first absent/ambiguous semantic classifier, wrong/foreign owner, changed dependency, resource bound, user STOP or session end. On a material authority boundary, pause dependent writes and return exact missing authority to Luna. If root Context is unowned, report `NO_SAFE_CODE_SLICE` and continue no code that guesses it.

## Review, application and integration

Freeze exact artifact and direct dependency hashes before review. Reviewer accepts only source-qualified owner claims and checked Lean theorem types/full axiom results; it checks the conditional application and every omitted premise. Any source/proof mismatch or guessed binding field is a rejection. Preserve the original parent and all gates OPEN in either outcome.

After review, Luna records a durable outcome with resource receipts, source/proof results, review message receipt (no invented review file), any scratch/out-of-lease outputs and remaining owner. Synchronize current state, run `python tools/agent_sprint.py check`, then only Luna stages explicit intended paths, inspects the outbound range and pushes. Next dispatcher trigger: actual root preparation owner found, exact missing semantic authority identified, review finding, resource exhaustion or another cross-lane seam.
