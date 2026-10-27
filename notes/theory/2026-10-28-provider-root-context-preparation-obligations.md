# Provider root preparation: proposed obligations and unchanged application

Status: **Draft research obligations; no adopted root semantics, new Lean theorem, or parent closure.**
Packet: `PROVIDER-ROOT-CONTEXT-DEFINITION-20261028/r1`; baseline `f93b64fff351869384b0cdd0aaff520639980ab5`; integrated contract `ebfdc3631` reported by Luna. Author: `/root/provider_root_context_definition_proof`. Only this note and its assigned proof handoff are writable by this author.

## 1. Original claim, authority and frozen evidence

The parent in `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1,3,5 quantifies over **every supported original source program, every lawful finite Simple-sub construction history, and every actual retained extrusion occurrence**. It requires original typing conclusions, required principal coverage, soundness, ordinary inference progress and termination, retaining lexical/type/event scopes, recursive monomorphic sharing, generalization/lawful uses, complete Call, effect hygiene and all correlated evidence. One joint source-admissible strategy is chosen at its original scopes. Marginal witnesses cannot replace that strategy. No case is removed by this bounded provider exercise.

Read its qualification using the current correction `notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6: both Values and every vertex on the qualification paths belong to the same immutable-birth-level induced graph. Equal birth does not identify lexical scopes, components or capture telescopes. Root preparation establishes none of the missing source-scoped joint lift at the qualified demand in parent §5. The original paper's non-let-polymorphic principality sketch, discussed in parent §3, does not prove this whole-language extension.

Existing authority: `notes/design/2026-10-11-yulang-inference-top-level-principles.md` §§1–5; `notes/design/2026-10-08-source-generalize-definition.md` §2 selects `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` §§3–5. The latter's §§3.1,3.3 require actual resolved bindings, original captures, source-selected parameter roles, complete invocation, original Shared/event ownership and simultaneous recursive relations. Its L1–L5 remain genuine local premises. Those sources do **not** select a Rust module-root-to-`Binding` classification/order rule. `docs/yulang-source-type-safety-ja.tex` opening corrections are research context and explicitly leave general source correspondence open; they add no semantic approval.

Direct admitted inputs were rehashed before drafting; all matched the contract. Additional actual dependency hashes are recorded in the handoff. Important frozen inputs:

| Input | SHA-256 |
|---|---|
| Current sprint contract | `58a685b51a066c7f5df913a93d9805f460237da29e100c684baf46dba7e8259e` |
| Original parent manuscript | `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` |
| Current birth-level correction | `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae` |
| `OriginalSourceSyntax.lean` | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| `OriginalSourceGeneration.lean` | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| `OriginalProviderLexicalOwner.lean` | `bf4e6572e5f1bf9b97a4d0274488b8d20f4487528d5bf8346ad262d3c75bd2f7` |
| `OriginalProviderRootContext.lean` | `bde05d470435f0184a9203fb30a4612126aab3540b9889f57a0a087bf7b553f3` |
| `OriginalProviderPublicationCoverage.lean` | `62257d276004f6caf07872142e4a4369266d5205d992f4f3d56f36657ae69783` |
| Prior reviewed root outcome | `c47e7c9ca45edfc24375ae2294e89bce0d4bbc45570345709ffaf93ed1b912df` |
| Current source-owner handoff | `b19681d96ced6979f2326287a7b697ba27c0be3ff09d8914b7734e381905546f` |

The last row is `tasks/agent-loop/inbox/provider-root-context-definition-20261028-source.md`. Its field/owner census is source evidence for the inspected path. The finding that these owners supply no root rows is not an executable counterexample to the original theorem or a proof that no other entrypoint exists.

## 2. Existing definitions and scope-sensitive consumers

Names in this section have prefix `YulangClosure.`. `OriginalSource.BindingKind` and `Binding` are in `OriginalSourceSyntax.lean:184,188`. Exact field order is

```text
name : Name; owner : Site; kind : BindingKind;
component : Option Site := none; annotation : Option Annotation := none;
entry : Option Entry := none; singleUse : Bool := false.
Context := List Binding.
lookupBinding Γ n := Γ.find? (fun b => b.name = n).
```

These defaults describe logical data construction, not evidence that a source row has those default values. `Name`, `Site`, `Annotation` are Nat aliases; a Rust ordinal or source spelling is not an authenticated conversion. All eight kinds remain available: external, formal, pattern, internal, local, continuation, published, family.

`OriginalSource.sourceRules` (`OriginalSourceGeneration.lean:84`) takes the incoming Context explicitly. Its Lambda branch (`:132–166`) prepends exactly the formal row, then uses its private `patternContext`, which filters new pattern rows whose names already occur in the formal Context. In the fixed Wild pattern no rows are added. Lambda capture and closure formation atoms retain the **entire incoming Γ**. The formal, receipt, entry-force/retained-entry, body, Return/pending suffix and checking atoms retain the appropriate extended Context. `OriginalSourceEnvironment.localCallOwner` (`:163`) registers a closure with the Context retained by `.closureFormation`; replacing Γ by an arbitrary lookup-equivalent list would change this registered input too.

Names use the first matching row. A `.published` or `.family` name introduces `.publishedInstance` and `.exactWholeInstance`; other kinds do not (`sourceRules` Name branch). `singletonFormalCall` also reads formal kind, annotation, value entry and `singleUse`. `OriginalSourceInterpretation.valueFormalAtom` (`:874`) tests formal/value classification; its `ValueNameAtom` (`:866`) separately requires a decoded binding address, installed-count bound and the complete installed value tuple. `OriginalSourceEnvironment.foldedNameKernel` (`:973`) requires the actual frame-prefix decode. A correct syntactic formal lookup alone supplies none of those semantic facts.

Binding consumers are not exhausted by the body Name: `OriginalProviderSourceSolution.Occurrences.bindingAtoms` (`:42`) uses Γ in `.oneShotInitializer` and `.publicationFinalRoot`, with the actual provider name and closure operand. Its `bindingTail` carries the original Return/rebind, Shared, binding and publication scopes. `OriginalSource.bindingsRulesK` (`OriginalSourceGeneration.lean:377`) preserves the current Context when lookup finds `.internal`; otherwise it prepends a `.published` tail row. `statementRulesK` (`:326`) registers recursive rows together as `.internal` with `component := some site` and publishes the group after its initializers. `statementsRulesK` (`:351`) threads ordered preceding statement records. `Source.bindingRecords` (`OriginalSourceSyntax.lean:209`) and these local equations do not specify module root preparation. `moduleS` emits `.sourceModuleLinking`; a module-root linking clause remains a genuine owner obligation.

## 3. Proposed preparation signatures and root equation — all unresolved

The following names are **schematic proposed interfaces**, not declarations present in Lean or Rust. They give exact future proof targets without implementing or assuming them. `Program`, `EntryKey`, `RootRows` and `Coordinates` must be source data fixed independently of source typing, generated satisfaction and desired provider success. `SupportedEntry p e` must keep the original supported domain; it cannot mean “the decoder succeeds.”

Proposed constructor outputs:

```text
prepareRoot  : Program → EntryKey → Option RootRows
decodeRoot   : Coordinates → RootRows → Option OriginalSource.Context
incomingAt  : Program → EntryKey → Option OriginalSource.Context
```

`prepareRoot` must be specified at actual source preparation, retaining row inclusion, source identities and ordered precedence. `decodeRoot` must translate all seven fields using one consistent coordinate inventory. `incomingAt` denotes the independently specified logical Context used at that exact source entry. It must be obtained from original source incidence/entry rules; defining it as the right side below would prove only an abbreviation. No current Rust owner supplies these three functions or their required equation.

For any approved coordinate inventory κ coherent with p, the target `ROOT-EQUATION` is:

```text
∀ p e κ, SupportedEntry p e → CoordinateCoherent κ p →
  incomingAt p e = (prepareRoot p e).bind (decodeRoot κ).
```

The separate non-vacuity/coverage target is:

```text
∀ p e κ, SupportedEntry p e → CoordinateCoherent κ p →
  ∃ rows Γ, prepareRoot p e = some rows ∧
    decodeRoot κ rows = some Γ ∧ incomingAt p e = some Γ.
```

Neither equation is a `LocalLaws`/`law` field, theorem premise offered as evidence, or completed proposition instance. They are goals to construct after the missing independent definitions are selected. Partial decoding is a representation choice only: failure on a supported entry leaves coverage OPEN; it cannot justify rejecting that source form or narrowing `SupportedEntry`.

The actual provider specialization must prove, for the authentic entry `e_id` in the exact fixture `p_id`, an explicit ordered `rows_id` and concrete `Γ_id` such that:

```text
prepareRoot p_id e_id = some rows_id
decodeRoot κ_id rows_id = some Γ_id
incomingAt p_id e_id = some Γ_id
actualSourceAt p_id e_id = OriginalProviderLexicalOwner.translate providerOwnerRows
                       = some (OriginalProviderLexicalOwner.occurrences providerOwnerRows).source
```

The final line abbreviates two equalities, not chained Lean syntax; `actualSourceAt` is another missing source-entry consumer interface, not an assumed Source. Source ownership must connect the selected parse-owned public declaration `pub id x = x`, module `std::core`, file `lib/std/core.yu`, range `0..12`, its HIR definition root, LocalSource Lambda, formal `7..8` and body `11..12`, to this **same** `e_id`. The authenticated prior trace and lexical decoder establish those fixture joins and the decoder's concrete tree; they do not establish the first three equalities or the `actualSourceAt` consumer link.

Coordinate coherence must preserve the fixed lexical decoder's `siteCoordinate`, `nameCoordinate` and `occurrences providerOwnerRows`, with injectivity and cross-inventory consistency. New root imports cannot be separately assigned indices that collide with the fixed formal/provider names or sites. If a proposed global reindexing changes those coordinates, a source-preserving transport theorem is required; this packet selects no reindexing. The actual entry, decoded Source, root rows, local atoms and semantic environments must all use the same identities.

## 4. Field, order and shadowing obligations with falsifiers

Each row needs its actual source owner and independently licensed classification before translating it. No field is chosen here for the root of `pub id x = x`.

| Obligation | Required premise/evidence and present boundary | Discriminating falsifier |
|---|---|---|
| `ROOT-NAME` | Resolved identity joins each included row and its references through κ; HIR/local spellings and export names are retained facts only. | Two distinct resolved names collapse because spellings or independent indices coincide; one real alias points to a different provider. |
| `ROOT-OWNER` | Each translated Site denotes the row's original binder/introduction, not its initializer/export by guess; definition/expression/admin sites stay distinct. | Row owner is the Lambda or export range when the actual binding introduction is another occurrence. |
| `ROOT-KIND` | Independently specify whether each entry is established external, published, Family, live internal, or another original kind. Retain full source contract/instance provenance. | Classifying a live recursive peer as published creates a fresh instance; classifying a Family as ordinary monomorphic removes `.exactWholeInstance`. |
| `ROOT-COMPONENT` | Retain the actual simultaneous recursive component, or independently justify no component; syntactic nesting and equal birth are insufficient. | Two recursive peers receive different components or independent descriptions, or an external capture is made internal. |
| `ROOT-ANNOTATION` | Translate actual written syntax and permissions at the original owner, with source final-root boundary semantics. | An inferred type becomes an annotation; an actual target or earlier boundary evidence disappears. |
| `ROOT-ENTRY` | Only independently determined original outer source role licenses `some value`/`some computation`; nonformal rows need their own rule for optionality. | Function-shaped inferred data is treated as value entry; retained computation is forced or an original Force is omitted. |
| `ROOT-USE` | Establish any `singleUse` fact from the correct resolved source scope, including latent/default uses; no equivalence to HIR evaluation class. | A second resolved use in a latent body/default is missed, enabling `singletonFormalCall` spuriously. |
| `ROOT-INCLUSION` | Specify inclusion of actual module declarations, imports/prelude, established captures and previous publications at this entry. Self/forward references and module recursion require explicit original rules. | Omitting a captured import changes closure formation; including the definition's own published row before initialization creates an unsupported self-use. |
| `ROOT-ORDER` | Preserve the source's lookup winner and retained rows using an explicit ordered construction; do not identify source traversal order with list precedence. | Reversed duplicate rows choose the wrong binder; HashMap insertion/iteration changes Γ or a shadowed capture. |
| `ROOT-IMPORT-PRECEDENCE` | Preserve explicit-import precedence over implicit prelude where that resolver applies; give ambiguity and namespace rules and their link to logical identities. This Rust fact alone does not choose list order. | Prelude wins an explicit collision, or an ambiguous import is silently selected by list position. |
| `ROOT-ENTRY-LINK` | The actual entry uses exactly Γ_id and the decoded Source, under the same artifact/module/declaration and coordinate inventory. | Correct rows from another entry/module are attached to this provider, or the real consumer receives a different Context. |

Existing list facts give exact *conditional* precedence checks, without selecting the root policy. For arbitrary Γ, n and b, `lookupBinding Γ n = some b` entails `∃ prefix suffix, Γ = prefix ++ b :: suffix ∧ b.name = n ∧ ∀ prior ∈ prefix, prior.name ≠ n`. Conversely those list premises suffice for that lookup. A duplicate with the same resolved Name is therefore significant. Whether such duplicates are valid root data, or distinct shadowing occurrences use distinct resolved Names, belongs to the resolver/source preparation contract; global uniqueness must not be added just to simplify proof.

For every Γ, the accepted `OriginalProviderLexicalOwner.body_name_lookup Γ` resolves the fixed body to the prepended formal even if Γ contains that Name. `formal_context_extension Γ` identifies that list with `o.bodyContext Γ`. `OriginalProviderRootContext.formal_context_retains_incoming Γ` retains the entire ordered tail; `formal_lookup_does_not_determine_incoming` gives distinct mathematical lists with identical formal lookup. Those lists are not authenticated module Contexts. Thus equal body lookup proves neither root equation nor capture/closure equivalence.

Unresolved alternatives to put before the user: derive a context from an independently existing approved preparation owner, if found; or select a new source-owned preparation definition covering inclusion/classification/order/entry linkage. Within the latter, root declaration visibility (sequential, simultaneous recursive, or another original rule), imports/prelude materialization, absent/retained shadow rows and optional field policy remain undecided. No alternative is selected by this note.

## 5. Exact conditional application after root preparation

Use abbreviations only in this section:

```text
o := OriginalProviderLexicalOwner.occurrences providerOwnerRows
Γ := Γ_id
V := OriginalSourceEnvironment.Payload s View
K := OriginalSourceEnvironment.admissionKernel inputs readout admissions original
E⁺ := {E with publications :=
  OriginalProviderPublicationCoverage.totalCompletion o E inputs readout admissions}
Adm E' b r := OriginalSourceEnvironment.Admitted inputs readout admissions E' b r
```

The unchanged theorem is `YulangClosure.OriginalProviderPublicationCoverage.provider_from_total_completion` (`OriginalProviderPublicationCoverage.lean:292`). Its exact outer quantifiers are `{s : OriginalSourceInterpretation.Sorts} {View : Type}`, `o : Occurrences`, `context : Context`, `inputs : Inputs s`, `readout : RuntimeReadout s View`, `admissions : LocalAdmissions s View`, `original : Kernel (Payload s View)`, and `environment : Environment (Payload s View)`. Instantiate o with the fixed decoder output and context with the **proved actual** Γ; leave every semantic parameter and all following premises unchanged:

1. `E.replay = none` (open history). A single recorded replay is not this premise, and all future admitted Return occurrences remain quantified.
2. `Compatible o E inputs readout admissions`, meaning `∀ r, Adm (E.enterInitializer o.binding) o.returnBinder r → ∀ prior, E.publications (publicationIdentity o E r) = some prior → prior = publicationRecord o E r`. Prior records win in `totalCompletion`; conflicting prior data cannot be overwritten to obtain a proof.
3. `InitializerPremises o Γ K (E⁺.enterInitializer o.binding)`; expanded below, so it is visibly uninstantiated.
4. `∀ r, Adm (E.enterInitializer o.binding) o.returnBinder r → Adm (returnedCut o E⁺ r) o.sharedBinder ((returnedCut o E⁺ r).anchorValue o.sharedBinder)`.
5. `∀ r, Adm (E.enterInitializer o.binding) o.returnBinder r → ∀ premise ∈ o.bindingAtoms Γ, Local K (completedCut o E⁺ r) premise`.

Conclusion, **only when all premises are established**:

```text
OriginalSource.SourceJudgment K E⁺ Γ o.source.
```

`OriginalProviderSourceSolution.provider_source_rules o Γ` (`:55`) supplies the unchanged syntax equation: sourceRules Γ o.source is the initializer scope containing the initializer derivation and `o.bindingTail Γ`. `OriginalProviderLexicalOwner.translated_source` supplies the fixed decoder equation. Combining these with the future entry/source and Context equations transports this conditional conclusion to the actual source entry. No helper assumes the desired source judgment. Defining the preparation target or an `InitializerPremises` proposition does not instantiate it.

For clarity, exact dependency/quantifier order inside premise 3 (`InitializerPremises`, `:240`) is:

```text
E0 := E⁺.enterInitializer o.binding
∃ d, K.admitted E0 ⟨o.formal, description, 0⟩ d ∧
∃ v, K.admitted (E0.extend ⟨o.formal, description, 0⟩ d)
                    ⟨o.closure, viewLogic, 0⟩ v ∧
let C := (E0.extend ⟨o.formal, description, 0⟩ d)
                  .extend ⟨o.closure, viewLogic, 0⟩ v
(∀ a ∈ lambdaAtoms o Γ, Local K C a) ∧
∀ i, K.admitted C ⟨o.closure, invocation, 0⟩ i →
∃ receipt, K.admitted (C.extend ⟨o.closure, invocation, 0⟩ i)
                          ⟨o.formal, receipt, 0⟩ receipt ∧
let T := (C.extend ⟨o.closure, invocation, 0⟩ i)
                 .extend ⟨o.formal, receipt, 0⟩ receipt
(∀ a ∈ entryAtoms o Γ, Local K T a) ∧
∀ r, K.admitted T ⟨o.formal, returnRebind, 0⟩ r →
let cut := T.extend ⟨o.formal, returnRebind, 0⟩ r
K.admitted cut ⟨o.formal, shared, 0⟩ (cut.anchorValue ⟨o.formal, shared, 0⟩) ∧
let B := cut.extend ⟨o.formal, shared, 0⟩ (cut.anchorValue ⟨o.formal, shared, 0⟩)
∃ proof, K.admitted B ⟨o.body, eventProof, 0⟩ proof ∧
let checked := B.extend ⟨o.body, eventProof, 0⟩ proof
(∀ a ∈ bodyAtoms o Γ, Local K checked a) ∧
(∀ a ∈ nameAtoms o Γ, Local K checked a).
```

This is mathematical transcription with unqualified BinderKind labels, not checked Lean code. Description and view are chosen before the universal invocation; receipt is chosen under it; proof is chosen under the actual Return and Shared scope. Reordering these quantifiers changes the obligation. `lambdaAtoms` contains both captureWholeEnvironment and closureFormation at Γ. `entryAtoms` contains sourceFormalRole/value, receiptFormation and entryForceReturnRebind at `o.bodyContext Γ`; `bodyAtoms` includes completeBodyConsumer, actualReturnOrPendingSuffix and its computation checking goal; `nameAtoms` retains both resolvedSameBinding and computedFetchOnce with the exact formal lookup. No complete Call, effect/guard, runtime binding or decode premise is discharged by renaming these atoms.

Owners and falsifiers for this composition remain explicit:

| Remaining semantic obligation | Owner / falsifier |
|---|---|
| Original Sorts/Inputs/local meanings, RuntimeReadout and LocalAdmissions instance | Original semantics/source lane under Luna; a degenerate instance that excludes lawful challenges or defines typing by safety fails correspondence. |
| Real description/view/receipt/invocation/Return/Shared/EventProof and every local/checking atom above | Original constructor/execution owner; a choice depending on a later challenge, lost capture, wrong raw binding tuple, or missing complete invocation refutes that instance. |
| Open admission and every returned candidate, not an empty admitted set chosen for convenience | Execution/admission owner; a genuine admitted Return absent from the coverage falsifies it. |
| Compatibility, complete prior record and capture/frame preservation | Publication owner; same publication identity with a different complete record refutes compatibility. |
| Native realization and actual execution/readout/entry correspondence | Source/native lane; an actual runtime frame/descriptor/provider differs from the logical one. |
| Both consumer exposures, if claiming import/prelude transport | Source/import owner must establish both handle equations required by `OriginalProviderSourceSolution.complete_record_transport` (`:364`) for the same record; Rust export identity alone is insufficient. |

The frozen `finite_support_no_open_provider` result in `OriginalProviderPublicationCoverage` also remains relevant: with a genuinely admitted Return, a finite-support map cannot satisfy this universal open provider judgment. A finite trace cannot replace `totalCompletion` or its universal admission coverage. `totalCompletion` is noncomputable conditional mathematics; it is not a native finite publication algorithm or evidence of actual provider realization.

## 6. Present evidence and first remaining owner

No new theorem was constructed, checked or axiom-audited in this docs-only packet. The prior reviewed outcome and its proof handoff retain complete printed types and `#print axioms` output: the two `OriginalProviderRootContext` data theorems and three lexical roots use `[propext]`; `OriginalProviderSourceSolution.provider_source_rules` and `OriginalProviderPublicationCoverage.provider_from_total_completion` use `[propext, Classical.choice, Quot.sound]`. These are retained receipts, not a new run or concrete premise instances. The current project files pin Lean 4.35.0 with no external packages, `-j1 -M1024`; no executable version was queried here.

Represented now: exact Binding data/lookup and local source-generation equations; fixed unannotated Binding/Lambda/Formal/Wild/Name lexical decoder; conditional provider/publication theorem. Not established: authentic root rows/Context, module/import/prelude/recursive-group policy, all semantic instances and native execution. Other expressions/patterns/statements, annotations, effects, handlers, records/method selection, complete Call and optional syntax remain in the parent domain; the fixture proves no universal coverage of them.

The first remaining premise is `PSR-ROOT-CONTEXT-1-AUTHORITY`: Luna must identify an already approved independent preparation owner or obtain explicit user approval for the proposed inclusion/classification/order/source-link definition after independent review. Only then can an authorized source/Lean packet construct rows, establish `ROOT-EQUATION` and coverage, run the pinned checker and apply the lexical facts. After that, `PSR-EVENT-MAP-1` still owns the actual semantic inputs, initializer/Shared/binding/admission/publication instances above. The original parent §5 joint-strategy/source-native bridge, universal soundness/principality/progress/termination, A/B, complete Call, effect hygiene and production remain OPEN throughout.

Writes stop with the associated frozen handoff. No Rust/Lean/root import/configuration/shared status/question file, scratch, generated output or cache is written; Cargo 0, Lean 0, tests 0, builds 0, descendants 0. Independent review, semantic adjudication and Git belong to Luna.
