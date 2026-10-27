# Provider root preparation — frozen proof-obligation handoff r1

Sprint-ID / contract: `PROVIDER-ROOT-CONTEXT-DEFINITION-20261028/r1`, revision `r1`; `tasks/agent-loop/sprints/provider-root-context-definition-20261028-r1.md`, SHA-256 `58a685b51a066c7f5df913a93d9805f460237da29e100c684baf46dba7e8259e`.
Assignment-ID / handoff revision: `PROVIDER-ROOT-CONTEXT-DEFINITION-20261028-PROOF`, revision `1`.
Baseline: `f93b64fff351869384b0cdd0aaff520639980ab5`; integrated contract commit `ebfdc3631` supplied by Luna, not independently inferred as runtime evidence.
Role / actual identity / session: registered `lean_prover`, `/root/provider_root_context_definition_proof`, session `PROVIDER-ROOT-CONTEXT-DEFINITION-20261028/r1`. Collaboration launch plus the active-work acknowledgement to Luna establish this assignment. Requested Sol/high; observed model/effort/session UUID **UNKNOWN**.

Outcome class: **candidate** research obligations only; no new Lean declaration, source preparation instance, semantic adoption, self-certification or parent closure. Independent review/adjudication and integration are pending with Luna.

## Exact outputs and authors

Sole author is this worker; no descendants. Only these leased files were changed:

- `notes/theory/2026-10-28-provider-root-context-preparation-obligations.md`, SHA-256 `2ff9b278295578cac331d7044930608014b8ec3065b90a18149075993222efd6`.
- This handoff, whose actual-byte SHA-256 is sent in the submission message after its final write.

No scratch, generated outputs or cache were created. No `.lean`, Rust, root import, test/expectation, manifest/toolchain/configuration, question, shared state/index/status or other worker path was written. No Git operations, child scheduling, nested CLI or user/third-party contact.

## Original sources, corrections and concrete declarations

Read root `AGENTS.md`, `AGENTS.pre-sprint.md`, `rules/goal-driven-sprints.md`, `rules/design-authority.md`, current state, assignment protocol, exact packet, `.agents/skills/yulang-lean-proofs/SKILL.md` and both relevant references (`sources.md`, `execution.md`). The fixed packet expressly prohibits Lean/Cargo/tests/builds here, so its docs-only scope governs the usual proof-execution procedure.

Original parent is `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1,3,5. Quantifiers remain every supported original source program, every lawful finite Simple-sub history, every actual retained extrusion occurrence. Preserve original lexical/type/event scopes, recursive monomorphic sharing, lawful generalization/use, complete Call/effect hygiene and one joint source-scoped witness, with original typing conclusions, required principal coverage, A/B, soundness, ordinary progress and termination. Read the current birth-level correction §§2–6 and the authoritative top-level principles. No cross-level qualification or independently chosen marginal witnesses are restored.

Read selected source-Generalize definition §2 and construction §§3.1,3.3,5; local semantic laws remain explicit. Read the source-safety manuscript's opening correction notice as research context only. Located the original paper limitation through original parent §3; no new claim is made to have rerun or reread the reference paper's PDF.

Concrete names below have prefix `YulangClosure.`:

- `OriginalSource.{BindingKind,Binding,Context,lookupBinding,Source.bindingRecords}` (`OriginalSourceSyntax.lean:184,188,198,204,209`): seven fields in order `name`, `owner`, `kind`, `component`, `annotation`, `entry`, `singleUse`; Context is an ordered list with first-match lookup.
- `OriginalSource.{sourceRules,statementRulesK,statementsRulesK,expressionRulesK,bindingsRulesK}` (`OriginalSourceGeneration.lean:84,326,351,363,377`): actual incoming Context, formal and pattern extensions, closure/capture and Name classification, recursive internal/component preparation, initializer/binding/publication scopes.
- `OriginalProviderLexicalOwner.{translated_source,formal_context_extension,body_name_lookup}`: fixed emitted Binding/Lambda/Formal/Wild/Name decoder and universally quantified incoming Context extension/lookup.
- `OriginalProviderRootContext.{formal_context_retains_incoming,formal_lookup_does_not_determine_incoming}`: list-tail retention and distinct mathematical lists with the same formal lookup, not authenticated root contexts.
- `OriginalProviderSourceSolution.{Occurrences.bindingAtoms,provider_source_rules,complete_record_transport}` (`:42,55,364`): Context-dependent binding consumers, exact source tree equation and explicit two-consumer handle premises.
- `OriginalProviderPublicationCoverage.{Compatible,InitializerPremises,provider_from_total_completion}` (`:120,240,292`): prior-record compatibility, full original initializer quantifier tree, unchanged conditional source conclusion.
- `OriginalSourceEnvironment.{localCallOwner,Admitted,admissionKernel,foldedNameKernel}` (`:163,638,724,973`) and `OriginalSourceInterpretation.{ValueNameAtom,valueFormalAtom}` (`:866,874`): closure Context registration, genuine admission/decode and actual installed binding tuple, beyond syntactic lookup.
- `OriginalSourceOwnerReification.{CallerContextOrigin,OriginTable}` (`:113,126`): provenance has no Context equation; the instance's `caller_context_unobserved` is none, never an empty Context.

## Exact proposed targets and parent application

The note §3 proposes **unimplemented schematic interfaces** `prepareRoot`, `decodeRoot`, `incomingAt`, independently of typing/success. No current owner supplies them. Its exact future equation is

```text
∀ p e κ, SupportedEntry p e → CoordinateCoherent κ p →
  incomingAt p e = (prepareRoot p e).bind (decodeRoot κ).
```

The separate totality/coverage target for every original supported entry is

```text
∀ p e κ, SupportedEntry p e → CoordinateCoherent κ p →
  ∃ rows Γ, prepareRoot p e = some rows ∧
    decodeRoot κ rows = some Γ ∧ incomingAt p e = some Γ.
```

The names/predicates themselves require independent source definitions and approval; `SupportedEntry` cannot mean decoder success, `incomingAt` cannot be defined by the desired equation, and the equation is not assumed as a `law`. Missing coverage leaves original cases OPEN. The provider specialization requires authentic rows/Γ plus the actual entry's Source link to the frozen decoder. All consumers must use one shared identity inventory preserving the existing provider/formal coordinates; independent root indexing or shifted lexical indices need a separate justified transport.

The note §§2,4 enumerates each field's owner/premise and falsifier, ordered shadowing, imports/prelude, declaration inclusion, recursive groups, actual source-entry linkage and coordinate consistency. Formal-first lookup and root order are different obligations. Closure/capture and binding atoms receive the full incoming Context, so formal lookup equality cannot replace root equality. No root kind, optional value, single-use flag, group policy, order or empty Context is selected.

The note §5 instantiates only the *coordinate* `o` with the lexical decoder and describes the application after actual Γ is established. It retains all original outer parameters `{s : Sorts} {View : Type}`, `o`, `context`, `inputs`, `readout`, `admissions`, `original : Kernel (Payload s View)` and `environment`. Exact remaining hypotheses of `provider_from_total_completion` are `environment.replay = none`; `Compatible`; `InitializerPremises` at the completed environment's initializer entry; universally admitted Return-to-Shared evidence; and universally admitted Return-to-`Local` evidence for every binding atom. The full nested description/view/invocation/receipt/Return/Shared/EventProof quantifier order is transcribed in the note. The conclusion is `SourceJudgment (admissionKernel inputs readout admissions original) completedEnvironment Γ o.source`, conditional on every premise. Nothing now establishes its actual provider instance.

`translated_source` and `provider_source_rules` will identify the unchanged Source/tree only after the actual entry and root equations are supplied. Context preparation does not establish any semantic Sorts/Inputs/readout/admission, Lambda/capture/checking, runtime binding, compatibility, Shared, replay or publication instance. `totalCompletion` is noncomputable conditional mathematics, not native realization. Finite-support publication still fails the universal open provider judgment if a genuine Return is admitted. Import/prelude exposure needs both original handle equations for the same complete publication record.

First remaining owner is `PSR-ROOT-CONTEXT-1-AUTHORITY`, Luna/source semantic approval. After that, `PSR-EVENT-MAP-1` retains all semantic constructor/execution/publication instances. Original parent §5's joint source-strategy/native completeness bridge and all universal parent, A/B, complete Call, effect-hygiene and production gates remain OPEN.

## Frozen dependencies and receipts reused

All direct inputs in the admitted contract were hashed by read-only Python SHA-256 computation and matched; the two prior handoffs were additionally checked with `sha256sum`. The note records the key contract/authority/module hashes. Additional frozen inputs actually read:

| Input | SHA-256 |
|---|---|
| Current source-owner handoff | `b19681d96ced6979f2326287a7b697ba27c0be3ff09d8914b7734e381905546f` |
| Prior source handoff | `f133ccfbdb5bfd603dba1cbc58baded5ad0ef2b90172e8ee2492c12760143fe9` |
| Prior proof handoff | `9c92e37e2fb5f29bd4a955cf3a119bc3565bb57382dbb5f7939488f4044bacc3` |
| Prior reviewed root outcome | `c47e7c9ca45edfc24375ae2294e89bce0d4bbc45570345709ffaf93ed1b912df` |
| `OriginalProviderSourceSolution.lean` | `3bf66649fdf4baacb3140de7786165db0d2b138087ca582bd32008b87a95a21a` |
| `OriginalProviderLexicalOwnerTrace.lean` | `4719fe129bee3a04fc321589d2c765413ec81cf309d7ad88d118c99b49ed57a0` |
| `OriginalProviderRootContextTrace.lean` | `c04a8017041f332a1a30f3179291925c83f31a995bacb12af574354a8c4c26f6` |
| `OriginalSourceEnvironment.lean` | `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132` |
| `OriginalSourceInterpretation.lean` | `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef` |
| Current birth-level correction | `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae` |

Historical complete printed theorem types/axiom blocks remain in prior proof handoff §“Complete printed theorem types and transitive axioms”. They report `[propext]` for the two root data lemmas and three lexical roots; `[propext, Classical.choice, Quot.sound]` for `provider_source_rules` and `provider_from_total_completion`. The independently reviewed outcome accepted this conditional scope. This packet adds no theorem and performs no new audit or independent review. Prior material failure evidence (checker CLI failure and process-tree watchdog interruption, followed by the recorded final successful per-process audit) is retained in that immutable handoff; nothing here supersedes or erases it.

## Checks, resources, remaining evidence and STOP

Actual commands: bounded read-only `pwd`, `cat`, `sed`, `rg` (one output capped with `head`), `sha256sum`, `wc -l`, and a `python3` script computing actual dependency hashes. Read commands returned exit 0; some orchestrated output was truncated and relevant definitions were subsequently reread in bounded ranges. Two `apply_patch` writes created exactly the leased Markdown artifacts. No source tests, checker, Lean, Lake, Cargo, build or toolchain installation ran; all those counts are **0**. No new axiom result or executable version receipt exists. Read project configs: Lean pin `leanprover/lean4:v4.35.0`, no external packages, `-j1 -M1024`. Runtime model/effort and aggregate active elapsed/RSS are not instrumented here; primary owns envelope accounting. No live generated-output/cache lease is held by this worker.

Represented: exact existing source definitions and one fixed provider lexical fixture plus abstract proposed preparation targets. Omitted from established evidence: authenticated root Context and all source/native/semantic/executor instances. All other source forms, optional records, selection, annotations, recursion, effects/handlers, complete Call and lawful histories remain required by the original parent, with no added source restriction.

Mutual TODO `PSR-ROOT-CONTEXT-1-AUTHORITY`: Luna synthesizes this artifact and the frozen source-owner map, obtains fresh independent review, then identifies existing approval or presents the explicit missing classification/inclusion/order/recursive-group/entry-link definition for user decision. Required output is an independently specified source preparation owner and concrete ordered rows/field justification plus actual consumer equation. Falsifier: an already approved actual constructor providing those facts, or a supported collision/capture/recursive case violating a proposed clause. This request grants no lease or implementation authority.

Mutual TODO `PSR-EVENT-MAP-1`: after root preparation is established, Luna assigns actual source/execution owners the still-explicit semantic parameters and nested initializer/Shared/binding/publication obligations in note §5. A real admitted Return not covered by the fixed publication map or a mis-scoped shared witness is a falsifier. No worker/reviewer is appointed here.

Worker state **STOPPED**. Writes stopped after this handoff; both outputs frozen for primary intake. No descendants, processes, background writer, generated outputs or unresolved child leases. Pending fresh independent review and Luna integration; no self-certification or Git action.
