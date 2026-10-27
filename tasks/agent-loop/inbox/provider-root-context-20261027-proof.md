# Provider root Context — frozen proof handoff r1

Sprint `PROVIDER-ROOT-CONTEXT-20261027/r1`; contract SHA-256 `dd6fcf29c88051e6e3489a02ed6dc66439caa89a1dc1ef84cefd68297a0d480b`; assignment `/root/provider_root_context_proof`; handoff revision 1.
Baseline `05ed820354baba5158a0bb3254082f6fe22ec4be`; primary reported integrated contract commit `10f0f421f`. Requested registered lean_prover/Sol/high; actual runtime identity `/root/provider_root_context_proof`; observed model/effort/session UUID UNKNOWN. Sole author, no children, no Git.
Exact leases: `notes/theory/lean/YulangClosure/OriginalProviderRootContext.lean` and this handoff. All scratch/cache under `/tmp/yulang-provider-root-context-20261027/proof/`. Luna granted sole heavy verifier ownership before execution and received the all-processes-exited receipt afterward.

Outcome: **two kernel-accepted data lemmas; precise missing root-input boundary; no provider source judgment or parent closure**. Source-qualified NO_SAFE_CODE_SLICE boundary is recorded below. Independent review/adjudication remain pending. No production authority.

## Original source and preserved claim

Original parent: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1,3,5, SHA-256 `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271`: every supported original source program, every lawful finite Simple-sub history and retained extrusion occurrence. Preserve lexical/type/event scopes, recursive monomorphic sharing, generalization/lawful uses, complete Call, effect hygiene and one shared source-scoped witness; required A/B, soundness, principal coverage, progress and termination remain OPEN.
Read the current correction `notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6 and authoritative `notes/design/2026-10-11-yulang-inference-top-level-principles.md`. No cross-level qualification is restored.
The selected source rule definitions are `notes/design/2026-10-08-source-generalize-definition.md` §2 and `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` §§3.1,3.3,5: actual resolved Name, actual Lambda captures/formal/body consumer, original typed Shared/event owners and original source publication scope. `docs/yulang-source-type-safety-ja.tex` opening corrections, especially the explicit unresolved all-linker-root correspondence, are research context and add no semantic authority.

Read actual `OriginalSource.{BindingKind,Binding,Context,lookupBinding,Source.bindingRecords}`, `OriginalSource.sourceRules` Lambda (:132), binding (:317) and `bindingsRulesK` (:380); owner-reification `CallerContextOrigin`, `OriginTable.callerContext`, and the instance's `caller_context_unobserved`. The latter is `none`, explicitly not an empty Context. Read the unchanged provider `Occurrences.{initializer,source,bodyContext}`, `InitializerPremises` and `provider_from_total_completion` before constructing the new lemmas.

## Constructed facts and limits

New namespace `YulangClosure.OriginalProviderRootContext` has exactly two authored theorems:

- `formal_context_retains_incoming`: for every incoming `OriginalSource.Context`, `(OriginalProviderLexicalOwner.formalContext incoming).tail = incoming`. This is the actual Lambda extension expression, preserving the complete ordered tail.
- `formal_lookup_does_not_determine_incoming`: two distinct `Context` list values produce the same lookup of the fixed emitted formal in that extension. Both sides use the same frozen `providerOwnerRows` and logical formal identity. Witnesses are `[]` and a singleton containing the known formal record. These lists are mathematical countermodels to inference from the lookup alone; neither is claimed to be an authenticated prepared module root.

The second fact is **not** a source-qualified counterexample to the parent theorem, a closure/capture theorem, a semantic-equivalence theorem, or a classification rule. It prevents treating the accepted formal lookup as evidence selecting an incoming root. The complete Lambda Context is not discarded: the first fact shows it retains the incoming tail. No Context translator/root instance, arbitrary-context provider wrapper, typing-as-safety definition, stronger hypothesis, project axiom or semantic change was added.

Represented: fixed emitted unannotated `pub id x = x` Binding/Lambda/Formal/Wild/Name bridge and abstract incoming `List Binding` data. Omitted from this bounded result: other source constructors/annotations/recursive groups, authenticated root preparation, closure/capture correctness, semantic Sorts/Inputs/readout/admissions, initializer description/view/invocation/receipt/Return/Shared/body proofs, event history, publication compatibility and exposure, native execution/complete Call/effect hygiene. All omitted forms remain in the unchanged parent domain.

## Exact missing input and conditional parent application

Consumed the frozen source handoff `tasks/agent-loop/inbox/provider-root-context-20261027-source.md` SHA-256 `f133ccfbdb5bfd603dba1cbc58baded5ad0ef2b90172e8ee2492c12760143fe9`, adapter SHA-256 `5d046a202c3e5e756d5b0f2910f4a6230a62c5988c1b364586b0703ffd849d70` and trace SHA-256 `c04a8017041f332a1a30f3179291925c83f31a995bacb12af574354a8c4c26f6`; all three hashes independently matched before intake. Source worker reports STOPPED, final Cargo exit 0 after one repaired compile failure, fixture SHA-256 `9b830a0650483a3387ced1724463b5fb18434366fb5a082f8cf7597ca8e7519e`. I did not repeat Cargo or import/build its new trace; these are source-lane evidence receipts, not kernel-authenticated Rust identities.

**Scoped NO_SAFE_CODE_SLICE:** `crates/yu-hir/src/module.rs:777–935` (`SemanticImports`) authenticates source/import identity or opaque caller evidence, not logical Binding classifications. `module.rs:1766–1790,2022–2140` HIR declaration/source-root APIs and `module/local_source.rs` supply actual declaration/formal/body owners. `module/source_exports.rs` supplies public export identity. The source instrument executed those joins and empty-versus-retained import-environment observations; it produced no ordered Binding rows. Independently inspected Lean consumers are `OriginalSource.sourceRules` and `bindingsRulesK`, which require an incoming Context explicitly; owner-reification `CallerContextOrigin` is provenance without a Context equation. These are at least two actual owners, with a precise source/consumer gap.
No existing approved constructor in this **inspected provider fixture and owner path** supplies the required root Context equation. This is a bounded negative observation, not a theorem that no compiler entrypoint could ever supply it. The unresolved equation would identify this entry's actually prepared root with the translation of authenticated ordered Binding rows; neither side has an approved construction here. `SemanticImports::empty()` carrying no import environment does not establish root Context `[]`; `with_source_imports` retaining an environment does not classify its entries; `with_caller_evidence<T>` explicitly leaves payload meaning unvalidated. Missing classification/order returns to Luna for authority review; no new semantic preparation rule was constructed.

Checked direct parent consumers: `OriginalProviderLexicalOwner.translated_source`, `formal_context_extension`, `body_name_lookup`, `OriginalProviderSourceSolution.provider_source_rules` and `OriginalProviderPublicationCoverage.provider_from_total_completion`. The existing lexical bridge maps the emitted rows to `o := OriginalProviderLexicalOwner.occurrences providerOwnerRows`; it supplies the exact source tree and the formal extension/lookup **for an incoming Context**.
The unchanged conditional theorem then gives `SourceJudgment (admissionKernel inputs readout admissions original) {environment with publications := totalCompletion o environment inputs readout admissions} context o.source` only from all these explicit inputs: genuine `context`, Sorts/Inputs/RuntimeReadout/LocalAdmissions, original Kernel/environment, open replay, `Compatible`, every `InitializerPremises` clause in the same completed publication environment, actual Shared admission for every admitted Return, and both original binding atoms for those Returns. The exact full type and transitive axiom list are printed below. No supplied premise was discharged by an empty axiom list or by assuming LocalLaws. No new concrete application was compiled: the missing root input prevents one; the exact existing theorem and accepted lexical consumers were audited unchanged. The previous checked conditional application remains recorded in the frozen lexical proof handoff SHA-256 `94476af7d5ed0414d1f753d408bfb2877e61b79b5f4cf31df13fb66b2c61a04a`, whose accepted Lean dependencies still match.

First remaining premise/owner: **PSR-ROOT-CONTEXT-1, Luna/source preparation authority**. An independently justified constructor must produce ordered logical Binding rows for this exact provider entry and an equation identifying their translation with its genuine incoming Context. Binding.name/owner/kind/component/annotation/entry/singleUse and ordering need actual owners; identity, public export or opaque payload does not choose them. No safe dependent production slice follows from the inspected paths. Next separate owner: **PSR-EVENT-MAP-1**, initializer/environment/publication owners, for the independent semantic premises above. Parent/source-native/A-B/effect-hygiene/production gates remain OPEN.

## Actual execution, failures and resources

Read pin/config/manifest: `leanprover/lean4:v4.35.0`, no external packages, `-j1 -M1024`. Read-only `elan which lake` returned `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
Actual versions: Lake `5.0.0-src+eb6cafb` (Lean 4.35.0); native Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, x86_64 Linux Release. Isolated fresh project contains exactly the 14-module import cone and byte-identical configs. No existing shared cache was modified or reused. No full/default target, tests, Cargo, installation/dependency/default edits or Git operations.

Six-call finite budget exhausted; no further verification authorized. Commands below use the resolved native toolchain, cwd `scratch/project`; raw logs and complete command arrays are hashed below.

| Call | Native arguments | Exit | Receipt |
| --- | --- | ---: | --- |
| 1 | `lake --version` | 0 | first helper pass |
| 2 | `lake --no-cache env lean --version` | 0 | first helper pass |
| 3 | `lake --no-cache build +YulangClosure.OriginalProviderRootContext` | 1 | imported 13 modules built; `List.noConfusion` signature error at new module :39 |
| 4 | same focused build, after `by simp` inequality repair | 0 | 0.406653971s |
| 5 | `lake --no-cache env lean -j1 -M1024 --root=.../tmp .../tmp/YulangProofAudit.lean` | -9 | 0.406404724s; conservative whole-tree RSS watchdog interruption |
| 6 | native `lean -j1 -M1024 --root=.../tmp .../tmp/YulangProofAudit.lean`, `LEAN_PATH=.../project/.lake/build/lib/lean` | 0 | 0.661826169s; correct per-process RSS cap |

First helper pass calls 1–3 together took 26.687523668s; descendant maximum RSS 891016KiB. Its own process-group sampler excluded the checker-created child group, so the reported 14MiB group sample does **not** measure build RSS. Call 5's watchdog summed resident mappings across the process tree and stopped at 1,078,034,432 bytes; this was not evidence of any individual process exceeding 1GiB. Luna explicitly authorized the sixth and final call under the unchanged **per-process** cap, with no retry beyond it. Call 6 sampled peak individual RSS 1,009,504,256 bytes; wait maximum RSS 986004KiB (<1GiB). One CPU affinity `[0]` and `LEAN_NUM_THREADS=1`; each command <=110s internal/120s packet cap. Total enclosing runtimes 28.162408532s (<240s). No timeout/OOM reported. Overall model active time is not instrumented; primary owns total assignment accounting. All Lean/Lake processes exited and the heavy seam was released to Luna before source verification.

The bundled checker CLI first failed honestly at call 3. For final audit, used its exact `audit_source` generator and `validate_audit` without repeating its already executed versions/build calls. Final audit requires theorem declaration kind, complete ordered type/axiom blocks and the standard whitelist. Validation passed for all seven roots. New theorems and three lexical roots each have `[propext]`; the source-rule equation and unchanged provider conditional have `[propext, Classical.choice, Quot.sound]`. Exact output below. This is kernel/audit evidence, not independent semantic/source review or parent closure.
Exact-cone source scan found only the unchanged explanatory word `axiom` in `OriginalSourceInterpretation.lean:528`; no proof holes, project axioms, skipKernelTC or native_decide. All 17 copied source/config hashes revalidated after checking.

## Frozen files, hashes and cessation

| Artifact | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/OriginalProviderRootContext.lean` | `bde05d470435f0184a9203fb30a4612126aab3540b9889f57a0a087bf7b553f3` |
| `/tmp/yulang-provider-root-context-20261027/proof/input-hashes.json` | `28a393500b1f8c4c40eb17305f59dc11cd614d126053eb1fe116578f5dda5b61` |
| `/tmp/yulang-provider-root-context-20261027/proof/last-audit.log` | `34a0151c92bd96650b4043b3ca1ea236ef6c2249b9f346a454562ee9d014a110` |
| `/tmp/yulang-provider-root-context-20261027/proof/runtime-first-failure.json` | `2a5c6f5f3a3c6c50086c77bf0b779b6e974666f7cf2cfa1c2c1390f0eccb77b0` |
| `/tmp/yulang-provider-root-context-20261027/proof/runtime-final.json` | `f079adb01824810059835b0bf2a2a4eaf9e8b0e444cd05f04dec55758121332b` |
| `/tmp/yulang-provider-root-context-20261027/proof/runtime-last.json` | `bdc8859747a73baf5ba8bd0c2c214da280939bf5cd5205dc08b089c9af9ab55e` |
| `/tmp/yulang-provider-root-context-20261027/proof/audit-validation.txt` | `790eb2af73579d938bcc75b3f3a86051a1541bdaaffef4df59b8635e37c5d15d` |
| `/tmp/yulang-provider-root-context-20261027/proof/checker-first-failure.log` | `4ffed15f6bce243d166a97c89173fc4944f2ca6fd616878e57344b8ce9086cc0` |
| `/tmp/yulang-provider-root-context-20261027/proof/tmp/YulangProofAudit.lean` | `aa56620a7a5d64666d23a1104f176d518baafb7a5d5a2b45b4505f94b6a3d701` |

Complete copied source/config input hashes (including unchanged direct imports):

| Input | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `notes/theory/lean/YulangClosure/NativeClosureEnvironment.lean` | `39aa5cefa078dd423e54f0d9790f9a48e136326742e01f65149f317c907be957` |
| `notes/theory/lean/YulangClosure/NativeDictionaryDenotation.lean` | `d44a78f08970a09ca4c3e99a1d8dea846286a299d1a2bc91ec3b5e0eabea9070` |
| `notes/theory/lean/YulangClosure/OriginalProviderLexicalOwner.lean` | `bf4e6572e5f1bf9b97a4d0274488b8d20f4487528d5bf8346ad262d3c75bd2f7` |
| `notes/theory/lean/YulangClosure/OriginalProviderLexicalOwnerTrace.lean` | `4719fe129bee3a04fc321589d2c765413ec81cf309d7ad88d118c99b49ed57a0` |
| `notes/theory/lean/YulangClosure/OriginalProviderPublicationCoverage.lean` | `62257d276004f6caf07872142e4a4369266d5205d992f4f3d56f36657ae69783` |
| `notes/theory/lean/YulangClosure/OriginalProviderRootContext.lean` | `bde05d470435f0184a9203fb30a4612126aab3540b9889f57a0a087bf7b553f3` |
| `notes/theory/lean/YulangClosure/OriginalProviderSourceSolution.lean` | `3bf66649fdf4baacb3140de7786165db0d2b138087ca582bd32008b87a95a21a` |
| `notes/theory/lean/YulangClosure/OriginalSourceEnvironment.lean` | `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132` |
| `notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean` | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| `notes/theory/lean/YulangClosure/OriginalSourceInterpretation.lean` | `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef` |
| `notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean` | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| `notes/theory/lean/YulangClosure/SourceFunctionMembership.lean` | `8d370ee57e486ae48607d1bab493ae5135f28bf8a5a7ff1b0ef240fc0247e424` |
| `notes/theory/lean/YulangClosure/SourceIdentityWorld.lean` | `6019fd9d57cde50183e016bd0c72de2c6eee72009065d85119fb0348dbcf0168` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |

Scratch inventory: `project/` (14 `.lean` source modules, three unchanged configs, generated isolated `.lake/` outputs), `tmp/YulangProofAudit.lean`, `input-hashes.json`, `audit-theorems.json`, `run_checker.py`, `run_final.py`, `run_last_audit.py`, `checker.log`, `runtime.json`, preserved `checker-first-failure.log`/`runtime-first-failure.json`, `final-0.log`, `final-1.log`, `runtime-final.json`, `last-audit.log`, `runtime-last.json`, `audit-validation.txt`, and scratch handoff preparation. No descendants. No root import, source lane or central state writes. Independent review and Git integration remain Luna-owned.
Worker state **STOPPED**; writes stopped after this frozen handoff; no process or background writer remains. No self-certification. Next request `PSR-ROOT-CONTEXT-1-AUTHORITY`: source preparation owner supplies approved root Binding classification/order constructor and its exact source-to-Context equation; falsifier is an existing approved constructor producing those rows for this entry. Until then leave that input and the parent obligation open.

## Complete printed theorem types and transitive axioms

```text
YULANG_AUDIT_BEGIN YulangClosure.OriginalProviderRootContext.formal_context_retains_incoming
YulangClosure.OriginalProviderRootContext.formal_context_retains_incoming : ∀
  (incoming : YulangClosure.OriginalSource.Context),
  List.tail (YulangClosure.OriginalProviderLexicalOwner.formalContext incoming) = incoming
'YulangClosure.OriginalProviderRootContext.formal_context_retains_incoming' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalProviderRootContext.formal_context_retains_incoming
YULANG_AUDIT_BEGIN YulangClosure.OriginalProviderRootContext.formal_lookup_does_not_determine_incoming
YulangClosure.OriginalProviderRootContext.formal_lookup_does_not_determine_incoming : ∃ first second,
  first ≠ second ∧
    YulangClosure.OriginalSource.lookupBinding (YulangClosure.OriginalProviderLexicalOwner.formalContext first)
        (YulangClosure.OriginalProviderLexicalOwner.occurrences
            YulangClosure.OriginalProviderLexicalOwnerTrace.providerOwnerRows).formalName =
      YulangClosure.OriginalSource.lookupBinding (YulangClosure.OriginalProviderLexicalOwner.formalContext second)
        (YulangClosure.OriginalProviderLexicalOwner.occurrences
            YulangClosure.OriginalProviderLexicalOwnerTrace.providerOwnerRows).formalName
'YulangClosure.OriginalProviderRootContext.formal_lookup_does_not_determine_incoming' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalProviderRootContext.formal_lookup_does_not_determine_incoming
YULANG_AUDIT_BEGIN YulangClosure.OriginalProviderLexicalOwner.translated_source
YulangClosure.OriginalProviderLexicalOwner.translated_source : YulangClosure.OriginalProviderLexicalOwner.translate
    YulangClosure.OriginalProviderLexicalOwnerTrace.providerOwnerRows =
  Option.some
    (YulangClosure.OriginalProviderLexicalOwner.occurrences
        YulangClosure.OriginalProviderLexicalOwnerTrace.providerOwnerRows).source
'YulangClosure.OriginalProviderLexicalOwner.translated_source' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalProviderLexicalOwner.translated_source
YULANG_AUDIT_BEGIN YulangClosure.OriginalProviderLexicalOwner.formal_context_extension
YulangClosure.OriginalProviderLexicalOwner.formal_context_extension : ∀
  (incoming : YulangClosure.OriginalSource.Context),
  YulangClosure.OriginalProviderLexicalOwner.formalContext incoming =
    (YulangClosure.OriginalProviderLexicalOwner.occurrences
          YulangClosure.OriginalProviderLexicalOwnerTrace.providerOwnerRows).bodyContext
      incoming
'YulangClosure.OriginalProviderLexicalOwner.formal_context_extension' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalProviderLexicalOwner.formal_context_extension
YULANG_AUDIT_BEGIN YulangClosure.OriginalProviderLexicalOwner.body_name_lookup
YulangClosure.OriginalProviderLexicalOwner.body_name_lookup : ∀ (incoming : YulangClosure.OriginalSource.Context),
  YulangClosure.OriginalSource.lookupBinding (YulangClosure.OriginalProviderLexicalOwner.formalContext incoming)
      (YulangClosure.OriginalProviderLexicalOwner.occurrences
          YulangClosure.OriginalProviderLexicalOwnerTrace.providerOwnerRows).formalName =
    Option.some
      {
        name :=
          (YulangClosure.OriginalProviderLexicalOwner.occurrences
              YulangClosure.OriginalProviderLexicalOwnerTrace.providerOwnerRows).formalName,
        owner :=
          (YulangClosure.OriginalProviderLexicalOwner.occurrences
              YulangClosure.OriginalProviderLexicalOwnerTrace.providerOwnerRows).formal,
        kind := YulangClosure.OriginalSource.BindingKind.formal,
        entry := Option.some YulangClosure.OriginalSource.Entry.value, singleUse := Bool.true }
'YulangClosure.OriginalProviderLexicalOwner.body_name_lookup' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalProviderLexicalOwner.body_name_lookup
YULANG_AUDIT_BEGIN YulangClosure.OriginalProviderSourceSolution.provider_source_rules
YulangClosure.OriginalProviderSourceSolution.provider_source_rules : ∀
  (o : YulangClosure.OriginalProviderSourceSolution.Occurrences) (incoming : YulangClosure.OriginalSource.Context),
  YulangClosure.OriginalSource.sourceRules incoming o.source =
    YulangClosure.OriginalSource.RuleTree.initializerE o.binding
      (YulangClosure.OriginalSource.RuleTree.rule YulangClosure.OriginalSource.Rule.sequence o.closure incoming []
        (YulangClosure.OriginalSource.RuleForest.two (YulangClosure.OriginalSource.sourceRules incoming o.initializer)
          (o.bindingTail incoming)))
'YulangClosure.OriginalProviderSourceSolution.provider_source_rules' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalProviderSourceSolution.provider_source_rules
YULANG_AUDIT_BEGIN YulangClosure.OriginalProviderPublicationCoverage.provider_from_total_completion
@YulangClosure.OriginalProviderPublicationCoverage.provider_from_total_completion : ∀
  {s : YulangClosure.OriginalSourceInterpretation.Sorts} {View : Type}
  (o : YulangClosure.OriginalProviderSourceSolution.Occurrences) (context : YulangClosure.OriginalSource.Context)
  (inputs : YulangClosure.OriginalSourceInterpretation.Inputs s)
  (readout : YulangClosure.OriginalSourceEnvironment.RuntimeReadout s View)
  (admissions : YulangClosure.OriginalSourceEnvironment.LocalAdmissions s View)
  (original : YulangClosure.OriginalSource.Kernel (YulangClosure.OriginalSourceEnvironment.Payload s View))
  (environment : YulangClosure.OriginalSource.Environment (YulangClosure.OriginalSourceEnvironment.Payload s View)),
  environment.replay = Option.none →
    YulangClosure.OriginalProviderPublicationCoverage.Compatible o environment inputs readout admissions →
      YulangClosure.OriginalProviderPublicationCoverage.InitializerPremises o context
          (YulangClosure.OriginalSourceEnvironment.admissionKernel inputs readout admissions original)
          ({ root := environment.root, anchors := environment.anchors,
                publications :=
                  YulangClosure.OriginalProviderPublicationCoverage.totalCompletion o environment inputs readout
                    admissions,
                origin := environment.origin, eventPath := environment.eventPath, names := environment.names,
                frames := environment.frames, replay := environment.replay,
                initializers := environment.initializers }.enterInitializer
            o.binding) →
        (∀
            (returned :
              YulangClosure.OriginalSource.ScopedValue (YulangClosure.OriginalSourceEnvironment.Payload s View)),
            YulangClosure.OriginalSourceEnvironment.Admitted inputs readout admissions
                (environment.enterInitializer o.binding) o.returnBinder returned →
              YulangClosure.OriginalSourceEnvironment.Admitted inputs readout admissions
                (YulangClosure.OriginalProviderSourceSolution.returnedCut o
                  { root := environment.root, anchors := environment.anchors,
                    publications :=
                      YulangClosure.OriginalProviderPublicationCoverage.totalCompletion o environment inputs readout
                        admissions,
                    origin := environment.origin, eventPath := environment.eventPath, names := environment.names,
                    frames := environment.frames, replay := environment.replay,
                    initializers := environment.initializers }
                  returned)
                o.sharedBinder
                ((YulangClosure.OriginalProviderSourceSolution.returnedCut o
                      { root := environment.root, anchors := environment.anchors,
                        publications :=
                          YulangClosure.OriginalProviderPublicationCoverage.totalCompletion o environment inputs readout
                            admissions,
                        origin := environment.origin, eventPath := environment.eventPath, names := environment.names,
                        frames := environment.frames, replay := environment.replay,
                        initializers := environment.initializers }
                      returned).anchorValue
                  o.sharedBinder)) →
          (∀
              (returned :
                YulangClosure.OriginalSource.ScopedValue (YulangClosure.OriginalSourceEnvironment.Payload s View)),
              YulangClosure.OriginalSourceEnvironment.Admitted inputs readout admissions
                  (environment.enterInitializer o.binding) o.returnBinder returned →
                ∀ (premise : YulangClosure.OriginalSource.Premise),
                  premise ∈ o.bindingAtoms context →
                    YulangClosure.OriginalSource.Local
                      (YulangClosure.OriginalSourceEnvironment.admissionKernel inputs readout admissions original)
                      (YulangClosure.OriginalProviderSourceSolution.completedCut o
                        { root := environment.root, anchors := environment.anchors,
                          publications :=
                            YulangClosure.OriginalProviderPublicationCoverage.totalCompletion o environment inputs
                              readout admissions,
                          origin := environment.origin, eventPath := environment.eventPath, names := environment.names,
                          frames := environment.frames, replay := environment.replay,
                          initializers := environment.initializers }
                        returned)
                      premise) →
            YulangClosure.OriginalSource.SourceJudgment
              (YulangClosure.OriginalSourceEnvironment.admissionKernel inputs readout admissions original)
              { root := environment.root, anchors := environment.anchors,
                publications :=
                  YulangClosure.OriginalProviderPublicationCoverage.totalCompletion o environment inputs readout
                    admissions,
                origin := environment.origin, eventPath := environment.eventPath, names := environment.names,
                frames := environment.frames, replay := environment.replay, initializers := environment.initializers }
              context o.source
'YulangClosure.OriginalProviderPublicationCoverage.provider_from_total_completion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalProviderPublicationCoverage.provider_from_total_completion
```
