# Sprint PROVIDER-ROOT-CONTEXT-DEFINITION-20261028/r1 — draft the root preparation contract

Status: ADMITTED for research and drafting only. The candidate design produced by this packet remains `Draft`; no source semantics or implementation authority is granted.
Branch / baseline: `yulang3` / `f93b64fff351869384b0cdd0aaff520639980ab5`.
Authority: unchanged original source-preservation claim, `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1,3,5; `notes/design/2026-10-11-yulang-inference-top-level-principles.md`; existing Source constructors and rules. Sprint-end selector recommendation: `/root/next_action_selector` read-only message following reviewed `PROVIDER-ROOT-CONTEXT-20261027/r1`.

## Original outcome and success evidence

Keep the universal source/executor theorem unchanged: all supported source programs, lawful finite Simple-sub histories and retained extrusion occurrences, with original lexical/type/event scopes, recursive monomorphic sharing, complete Call, effect hygiene, A/B, soundness, required principal coverage, progress and termination. No parent gate is promoted by this packet.

The preceding reviewed result is a source-qualified `NO_SAFE_CODE_SLICE` for deriving the incoming logical `OriginalSource.Context` for the inspected `pub id x = x` provider path. The next outcome is a concrete, independently reviewed **candidate constructor contract** for `PSR-ROOT-CONTEXT-1`: identify the source declaration entry and preparation inputs; assign each `Binding` field and ordering/shadowing fact to an actual owner; cite the exact existing authority when a clause is already determined; label every unsupported clause as a proposed missing definition or unresolved alternative; state the exact root equation and consumer; and list the Lean proof obligations that would instantiate the accepted lexical bridge and unchanged conditional provider theorem.

This is research drafting, not a semantic decision. No implementation, source-rule change, new production API, Lean theorem, test, Cargo build or behavior change is authorized in this packet. A new classification, ordering or source-linking choice must pass the normal independent review and explicit user approval gate before dependent implementation. Do not call a proposed definition `Authoritative`, and do not report its assumptions as proof.

Success evidence: one frozen candidate design with a field-by-field authority matrix and unresolved decision alternatives; a separate proof-obligation document with exact source/Lean locators, quantifiers, premises, parent application and falsifiers; a source-owner handoff grounding each clause in current Rust consumers; and fresh independent review that rejects guessed fields, wrong precedence/order, opaque payloads as semantic facts, empty-context assumptions, omitted Context-dependent consumers, or claims of parent closure. If current sources cannot support a proposed clause, retain it as an explicit user decision rather than filling it by intuition.

## Two continuing lanes

**Source/implementation lane** — registered `implementer`, Luna/high requested, read-only source census and handoff. Inspect the exact path from parsed module/declaration entry through imports, HIR/LocalSource and source exports. Map actual owners for `Binding.name`, `owner`, `kind`, `component`, `annotation`, `entry`, `singleUse`, list order and shadowing. Separate proven ownership from missing authority; no code changes or Cargo calls.

Lease: `tasks/agent-loop/inbox/provider-root-context-definition-20261028-source.md`.

**Proof lane** — registered `lean_prover`, Sol/high requested, specification/proof obligations only. Reuse frozen Lean artifacts and audits; do not run Lean or change `.lean` files. State the future preparation relation/equation that must be supplied, exact source-rule consumers (including closure/capture and binding atoms), the application to the checked lexical bridge and conditional provider theorem, and every premise that remains explicit.

Leases: `notes/theory/2026-10-28-provider-root-context-preparation-obligations.md` and `tasks/agent-loop/inbox/provider-root-context-definition-20261028-proof.md`.

**Primary lane:** Luna synthesizes the two handoffs into `notes/design/2026-10-28-provider-root-context-preparation.md`, marked `Status: Draft`, with alternatives and a final approval boundary. This path is not leased to children.

After the draft and handoffs freeze, a fresh read-only `spec_auditor` reviews exact hashes, the authority matrix, source mapping, missing-definition boundary, alternatives, proof obligations and original parent preservation. It writes no file. The reviewer is not a coauthor. No new toolchain run or second review panel.

## Frozen evidence and governing inputs

Prior reviewed outcome: `tasks/agent-loop/sprints/provider-root-context-20261027-r1-outcome.md`, SHA-256 `c47e7c9ca45edfc24375ae2294e89bce0d4bbc45570345709ffaf93ed1b912df`.

| Input | SHA-256 |
|---|---|
| `rules/design-authority.md` | `e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/design/2026-10-08-source-generalize-definition.md` | `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38` |
| `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` | `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240` |
| `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` | `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` |
| `notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean` | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| `notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean` | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| `notes/theory/lean/YulangClosure/OriginalProviderLexicalOwner.lean` | `bf4e6572e5f1bf9b97a4d0274488b8d20f4487528d5bf8346ad262d3c75bd2f7` |
| `notes/theory/lean/YulangClosure/OriginalProviderRootContext.lean` | `bde05d470435f0184a9203fb30a4612126aab3540b9889f57a0a087bf7b553f3` |
| `notes/theory/lean/YulangClosure/OriginalProviderPublicationCoverage.lean` | `62257d276004f6caf07872142e4a4369266d5205d992f4f3d56f36657ae69783` |
| `crates/yu-hir/src/module.rs` | `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646` |
| `crates/yu-hir/src/module/local_source.rs` | `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1` |
| `crates/yu-hir/src/module/source_exports.rs` | `03727fd3918738a48afde7f7a875de60b63b43ac2cc620896a4ed73d8b0a9179` |
| Source handoff | `f133ccfbdb5bfd603dba1cbc58baded5ad0ef2b90172e8ee2492c12760143fe9` |
| Proof handoff | `9c92e37e2fb5f29bd4a955cf3a119bc3565bb57382dbb5f7939488f4044bacc3` |

The accepted lexical proof/module/trace hashes are frozen in the preceding outcome and proof handoff. Verify all direct inputs before drafting. Any changed authority input returns to Luna before dependent writing.

## Permissions and resources

Fresh envelope: 1800 seconds total (proof 600, source 450, Luna 300, review 350, dispatch 100); Cargo 0, Lean 0, tests 0, Astra 0. Read-only repository exploration and leased Markdown writing only. No new workers outside the two lanes and one fresh reviewer; no subteams. Preserve all existing files and UNKNOWN/quarantined leases. No `.lean`, Rust, test, expectation, dependency, configuration, or public behavior changes.

Stop when the proposed constructor requires a missing source classification/order/link rule. Record alternatives without selecting one and leave the user-approval gate explicit. Stop on changed dependencies, scope expansion, resource exhaustion, user STOP or session end. Do not start implementation while the design remains Draft/Reviewed.

## Review and handoff

The primary design must distinguish: clauses entailed by existing authoritative rules; evidence-backed compiler facts; proposed semantic definitions; unresolved alternatives; and claims still OPEN. The field matrix must include owner, kind, component, annotation, entry, single-use and ordered precedence, plus imports/prelude, module declarations and recursive groups. State how the candidate avoids treating export identity, map iteration or opaque evidence as semantic classification.

The proof obligation artifact must preserve the original universal quantifiers, state the exact root equation without assuming it, compose only after its premises are supplied, keep admission/Return/Shared/replay/publication and effect obligations explicit, and give a falsifier for each clause. The independent reviewer reports a message verdict and runtime/STOPPED receipt; no review-file hash is invented.

After review, Luna records a durable outcome and requests the user's decision on the concrete candidate before any dependent semantic implementation. All original inference/executor, source/native, A/B, principality, termination, complete Call, effect-hygiene and production gates remain OPEN. Next dispatcher trigger: reviewed candidate reaches the user-approval boundary or sources expose a contradiction.
