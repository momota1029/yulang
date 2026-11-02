# R224 revision 2 — source Function elaboration stop

- Assignment: `/root/r224_r2_proof`, handoff revision 1; author: this leaf.
- Contract: `tasks/agent-loop/sprints/contextual-function-source-bridge-r224-r2.md`, SHA-256 `30e55a488f709712b421428d677de5be85ce37ff007c1ac4a74f474d5ccd2060`.
- Baseline authenticated by reading `.git/HEAD` and `.git/refs/heads/yulang3`: `579df249d52fb57a0ec38e00881036c409dc722c`, branch `yulang3`. No Git command or mutation.
- Outcome: **first missing source elaboration constructor/equation located; no theorem constructed**. This is not a counterexample or a mathematical impossibility claim. Independent review is pending.
- Leases: `notes/theory/lean/YulangClosure/ContextualFunctionSourceBridgeR224.lean` and this handoff. Only this handoff was created; the Lean path remains absent.
- Verification/cache owner: Luna. No Lean, Lake, checker, cache, compiler, Cargo or test execution by this leaf. Effective model/effort telemetry: UNKNOWN. No descendants.

## Original claim and governing source

The unchanged parent is `YulangClosure.SourceProblem.InferenceSoundness`, `Contracts.lean:128`:

```text
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

This is the existing proposition definition's source text, not a newly printed theorem. Every supported source, scope, generated constraint and solution remains quantified, and the same `e` must satisfy both conjuncts. The other original roots remain `YulangClosure.SourceProblem.SourceScopedCoverage`, `PrincipalCoverage` and `InferenceTermination`. Parent delta **0; roots 0/4; packages 0/5**.

Original scope: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1,3,5, corrected by `notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6. Value birth-level qualification does not discard cross-level source dependencies or construct a source-scoped joint strategy. `docs/yulang-whole-proof-closure-ja.md` §§1,4 retains the complete source/effect/Call target.

Original source manuscript: `docs/yulang-source-type-safety-ja.tex`, `sec:source` and `sec:all-source` (App/Lambda rows). Its opening correction notice identifies an unreviewed research construction; its four-port wording is not authority for independent effect comparisons. The selected SG construction is `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` §§3.1–3.3,4: Lambda requires actual role, source entry, receipt, designated Force, Return/rebind, body and invocation return; Call retains the inert whole argument and actual returned callee. Its L1–L5 local-law requirements do not establish concrete local instances.

Current semantic direction comes from the pinned compatibility boundary §§1,7–8, contextual membership §§1–4, and callback delivery §§1–4, particularly normative B in §2.1. Charter §§21,24 preserves independent parameter entry and corrects the universal-handler reading. The source-computation-role draft supplies a skeleton, not the missing pre-body expected-context delivery or full role-indexed interface. The mixed-row selection is compatibility boundary §9 and the pinned question receipt: only the stated allowance/compatibility and contribution-specific deep-removal case is selected.

## Constructor-to-consumer trace

All names in this table are existing declarations, inspected as source only.

| Owner | Represented construction | Exact boundary |
| --- | --- | --- |
| `YulangClosure.OriginalSource.Source`, `Mark`, `Formal`, `Binding` | Original App/Lambda, original annotation IDs, lexical context, formal entry syntax | `Annotation = Nat`; no annotation-body resolver or expected callback contract/profile is an argument to `sourceRules`. |
| `YulangClosure.OriginalSource.Formal.entry` | `outerComputation` selects retained Computation or ordinary Value | This is parameter entry; it does not select Pure/Handler receiver role. |
| `YulangClosure.OriginalSource.sourceRules`, App case, `OriginalSourceGeneration.lean:111` | One `.viewLogic` binder; descriptor/argument/certificate/incidence/image atoms; callee Value check and callable-image Computation check; both original children | The argument child is exactly `sourceRules context argument`. No declared callback boundary is delivered to it. |
| Same declaration, Lambda case, `:132` | Description/view binders, whole captures, closure, universal invocation, receipt, Value-entry execution/rebind, shared evidence, pattern, body event proof and body consumer | `.sourceFormalRole` carries the formal annotation and `.entry`; it is not an actual receiver-role constructor. The rule has no selected receiver role, resolved Function annotation boundary, or expected callback profile input. |
| Private `annotated`, `:35` | Preserves original written annotation and separate synthesis/written-target endpoints | A generic final boundary wraps the already constructed rule. This is not the selected delivery of a Function annotation boundary before generating the body. |
| `YulangClosure.OriginalSource.Kernel`, `:669` | Independent local atom/admission meanings and finite checking fields | No concrete clause here resolves the absent role/boundary or supplies complete interface formation. Taking `kernel.atom` or `kernel.admitted` as true would assume the missing source obligation. |
| `YulangClosure.OriginalSourceInterpretation.Fiber`, `Event`, `Challenge`, `CallInput` | Existing shared `nu,K,D`; assignment, history, current world, receipt, incidence, dictionary, provider input | These retain the joint tuple. They do not construct the source Function interface. |
| `YulangClosure.OriginalSourceInterpretation.FunctionAt` | Same actual provider; every independent checked challenge; actual admission and every complete/pending observation | `Inputs.functionGuards`, `checkedInlet`, `actualInlet`, `execute`, `checkedObservation` are original semantic inputs. `FunctionGuards.roleAndEntry : Prop` is an obligation, not evidence of the selected source role. |
| `YulangClosure.OriginalSourceChecking.Reading`, `FunctionShape`, `kernel` | Reads original mode/site/context/endpoints; complete finite proof with contravariant domain and same-callable observations | `FunctionShape.proof` must be constructed from real registrations. No role-first source interface/readout is supplied by renaming that proof a shape. |
| `YulangClosure.OriginalSourceCallerSchema.CallerTable` | Caller/provider/module and resolved-use locators | Its explicit scope excludes construction of an `OriginalSource.Binding`, complete source tree or typed Function boundary. |

`YulangClosure.OriginalSource.generated_constraints_imply_source_judgment` has the existing source signature:

```text
{Value : Type} → (kernel : Kernel Value) →
(environment : Environment Value) → (context : Context) →
{category : Category} → (source : Source category) →
Satisfies kernel environment (Build context source) →
SourceJudgment kernel environment context source
```

It reconstructs finite rules under the supplied original local kernel. It does not construct a concrete Function atom/admission interpretation or derive a complete role-indexed interface from raw syntax. No invocation of it closes the missing clause.

## First missing equation and named original App premise

Stable seam: **R224-ROLE-FIRST-INTERFACE-1**. Owner: **Luna's source Function elaboration / annotation-and-expected-callback boundary integration**, under callback delivery §§1–2.1 and compatibility boundary §§7–8. The selected role values themselves need no new semantic choice. The stop is at the missing source acquisition and pre-body delivery of the boundary; complete interface elaboration follows that delivery.

Two responsibilities must remain distinct. At App checking, first acquire the known callee's resolved, instantiated Function-valued formal `F_cb` and original static callback slot/profile `β, Slots(β)`. The current `sourceRules` input supplies no such resolved callee/formal-interface lookup or callback-slot output; lexical `lookupBinding` and an opaque annotation ID do not construct it. Then deliver that acquired boundary to the argument literal before any body generation. The current App argument recursion supplies only `context`, so it implements neither that delivery nor the following role-indexed interface elaboration. Callback delivery §2 assumes acquisition already happened and selects the ordering after it; it does not supply acquisition or a complete interface calculus. An explicit Function annotation likewise needs resolution of its original Function boundary before delivery.

Required equation, written schematically rather than introduced as a new Lean declaration:

```text
App checking: resolved callee -> instantiated Function-valued formal + original callback slot/profile
  -> deliver that boundary to the original argument literal before body generation
original literal + its resolved Function annotation / delivered callback boundary
  -> selected actual receiver role and original boundary/profile, before body constraints
  -> independent source parameter entry, parameter/body/result construction
  -> complete source Function interface and the original endpoint readout
```

For normative callback B the final check is the single completed-interface `F_lit <: F_cb`; the construction must not identify the literal endpoints with `F_cb`. Without Function annotation/handler expected context the literal is Pure; explicit Function annotation and expected callback select their Handler boundary. Annotation/callback overlap retains both descriptors and its separate open source rule. Existing values retain their actual introduction role and entry. No general adaptation rule is supplied here.

Name the downstream original generated App premise **R224-App-descriptorFormation**. This is a consumer to which a future equation must apply, **not the first source owner or first missing acquisition/delivery step**. For `Source.app mark callee argument`, its `.app` rule lies under the original `.viewLogic` binder. At that same extended environment `envCall`, the first local atom in the generated list requires precisely:

```text
kernel.atom envCall
  (YulangClosure.OriginalSource.atom .descriptorFormation mark.site context
    [callee.site, argument.site])
```

The associated original Value checking goal is exactly:

```text
⟨.value, mark.site, context,
  ⟨callee.site, .returnedValue⟩, ⟨mark.site, .descriptor⟩⟩
```

The subsequent original Computation goal compares `⟨mark.site,.callableImage⟩` to `⟨mark.site,.synthesis⟩`, together with `.wholeArgumentCompatibility`, `.completeCallCertificate`, `.sourceCallIncidence` and `.callableImage`. These are unchanged premises, not assumed facts. The missing equation must construct the descriptor/interface registration and readout consumed at this specific descriptor premise and check; the existing tree does not do that. If the argument is a callback literal, the same omission already appears in its generation as `sourceRules context argument`, before this interface can be formed. If the callee is a newly introduced literal, its same absent role-first formation prevents the callee-to-descriptor application.

**Application result:** no source-constructed equation was obtained, hence no App premise was discharged and no parent reduction is claimed. No conditional theorem assuming this equation, admission, interface formation, source judgment or same-scoped witness was constructed. This is the first source-construction seam, earlier than the coupled effect projection and full Function inequality; it is not the rev1 independent-port target under a new name.

## Preserved call/effect obligations and falsifiers

The original Value-entry tree retains receipt before `.executionE` Return/rebind and the body, and the selected source schedule remains `receipt; Force(D) >>= (v => B(v))`. The uninterpreted entry/consumer atoms are not an executable proof of that schedule. Future construction must derive argument observations and body observations at reached post-force states under the **same** provider, receipt, world, assignment and existing `nu,K,D`; pure divergence must remain admitted where its independent contract admits it and need not reach the body. Retained Computation entry remains available with its distinct consumption rule.

The missing complete interface must resolve both effect descriptors jointly. The intended `Fun(a,never,b,c) <: Fun(a,d,[b,d],c)` creates no independent `d <: never`. No general row union, effect meaning for `never`, new carrier, concrete-success composition, family-only suppression, or effect-dropping/re-emitting shortcut was introduced. For the selected mixed-row deep-removal case, complete source request, continuation, path, attachment and handler-image evidence remains necessary; selector/arm/re-emission/latent/later-use behavior stays in the image. These cases are **required but not constructed** by this packet. All remaining source forms, annotations, methods, optional records, scope and shared witnesses remain in the parent.

Falsifiers for the next construction: expected boundary arrives after literal body generation; receiver role is inferred from parameter entry/effect spelling; literal endpoints are copied from `F_cb`; provider/assignment is reselected between Force and body; Force precedes receipt; pending effects vanish; removal uses only family membership; or a concrete source atom is assumed instead of constructed.

## Dependency authentication and execution evidence

All contract pins matched `sha256sum` at intake and a read-only Python SHA-256 comparison immediately before this handoff; both exited 0. Baseline reference matched at both reads. The Python comparison authenticated these 13 files and confirmed the leased Lean module was absent:

| Input | SHA-256 |
| --- | --- |
| Revision 2 contract | `30e55a488f709712b421428d677de5be85ce37ff007c1ac4a74f474d5ccd2060` |
| Compatibility boundary | `5b0b4321d8644f88a7a946aff31b6b3190d37a9076ac698fa91fdfeef1470f16` |
| Contextual membership definition | `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0` |
| Callback delivery | `df4941d4c66e4f3147257024a35e7041a2c51dd528657cc80efaf3d0db62fed5` |
| Mixed-row receipt | `7cd1cea5b6b4649e68b6d57b854e1fa390a4bf671d051256c2f6823b11b2d1d3` |
| `Contracts.lean` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `OriginalSourceGeneration.lean` | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| `OriginalSourceChecking.lean` | `a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6` |
| `OriginalSourceInterpretation.lean` | `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef` |
| `OriginalSourceSyntax.lean` | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| `OriginalSourceCallerSchema.lean` | `9bb15c7f383a997c4e7d63efd521704c925e62c95072f81ad18ad2aec9ba30b9` |
| Frozen rev1 proof handoff | `c0c9518afd29a788c0fb3104b42da4ac43f645ad2204121f3ffbc6f78102f27c` |
| Frozen rev1 owner handoff | `a9818d3cba8bffb9b78660884bc5cad4dcd8045e28dccca31e4ca008d7f834ae` |

Additional source hashes read with `sha256sum` (exit 0): SG construction `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`; source manuscript `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166`; charter `547572df2d835673ab9fbdc294c00ecb8b12025b02d49807216128933d27f8ed`; role-elaboration draft `9a230eb023698666f4c3e518a527009d6915e65f658b230e6da6a29914ca3abb`; top-level principles `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`.

Read `lean-toolchain` = `leanprover/lean4:v4.35.0`, `lakefile.toml` = `-j1 -M1024`, manifest = no external packages. **Actual Lean/Lake versions NOT RUN**, by sole-verifier packet. Commands were read-only `pwd`, `cat`, focused `sed`, `rg`/`rg --files`, `sha256sum`, and the read-only Python comparison. Initial guessed rev2 handoff paths were absent (`cat` exit 1); a source locator search named two nonexistent design paths (`rg` exit 2), then located the actual SG theory and role-elaboration draft. These discovery failures produced no proof evidence or scratch output. No mathematical checker failure or actual goal was observed because no checker was run.

Delivered theorem names/types: **none**. `#check`, `#print axioms`, bundled checker/build: **NOT RUN / no delivered theorem**. No empty-axiom or kernel-acceptance claim. Source-inspected signatures above are not runtime receipts. Source/native correspondence and production authority remain open; independent review belongs to the primary's fresh reviewer.

## Resources and cessation

Zero Lean/Lake/Cargo/test processes, zero cache/generated/scratch outputs, zero Astra, no child or background process. This leaf used source reads plus one handoff write; no separate wall-time counter was instrumented, and no R224 time budget reset is asserted. It stopped at the first established equation seam inside the remaining admitted envelope rather than spending it on an assumed bridge.

The seam was sent to Luna. Luna reported that the dispatcher confirmed the exact stop boundary after freeze and independent review, and required acquisition at App checking to be distinguished from delivery before argument body generation; that distinction is incorporated above. No scheduling record or authority change was made by this leaf. Exact next input: source-owned callee/formal-interface and callback-slot acquisition, then boundary delivery before body generation at R224-ROLE-FIRST-INTERFACE-1, preserving normative B and the downstream named original App premises. Expanding or editing source owners needs a primary packet/lease decision.

**Writes stop after this handoff's final hash receipt.** Only this file was authored; the leased Lean module was not created. Rev1 artifacts, compiler, tests/expectations, root imports, task/status/index files, rules/configuration, pins/manifests, questions and all other workers' files were left untouched. No self-certification or integration is claimed.
