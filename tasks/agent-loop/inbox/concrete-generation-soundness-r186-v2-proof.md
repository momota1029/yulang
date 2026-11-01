# R186 v3 proof handoff — incomplete independent construction

Assignment `/root/r186_contextual_function_proof`, handoff revision 1. Contract revision 3: `tasks/agent-loop/sprints/concrete-generation-soundness-r186-v3.md`, SHA-256 `7bad077bbb3238b301e9c62f11f2303c5b73d118c01a84b622a3e849f538a7fa`. V3 changes source-owner pins only; this remains the original v2 1800-second grant and its two output leases. V1's mismatch-only receipt remains frozen unchanged. Baseline supplied by contract: `513af1ce8664581bd76480674e8275fb0bad1a7a`; no Git command ran. Author: this leaf only; no descendants. Requested role: `lean_prover`; effective model/effort metadata UNKNOWN.

**Outcome: INCOMPLETE. No original parent premise was discharged or refuted. No complete independent generation/satisfaction model, all-constructor proof, parent application or source-qualified counterexample exists.** Four App candidate algebra declarations individually elaborated and printed clean axiom lists during an overall failing check. This is partial construction evidence; the final module has not had a successful complete check. No independent review or production authority is claimed.

## Fixed parent, source scope and phases

`YulangClosure.SourceProblem.InferenceSoundness`, `Contracts.lean:128–130`, remains:

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

The raw accepted inventory remains the 13 expression, 11 pattern and 3 statement forms plus their ordered containers in `OriginalSource.Source`. No new supported-domain predicate or smaller source language was defined. The parent still quantifies over every solving assignment, original scope and one shared witness. Principality, inference termination and Rust/native correspondence remain separate; none is proved here.

Governing sections inspected: authoritative top-level inference principles §§1–4; selected source-Generalize definition §§2–3; selected construction §§2–4 (L1–L5, original constructor rules, checking grammar, owning telescopes, finite joint clients and `Build` generation); contextual Function selection §§2–4; Call semantic-input realization §§2–3; approved full punctured-context answer decisions 1–5. The source-safety manuscript opening correction/status, `sec:source` and its first polymorphism rules were read. Its unreviewed candidate policies were not adopted as authority.

The source program `OriginalSource.Build` is a full constructor-directed local-rule program. It is not an established concrete instance of the actual abstract Simple-sub `p.generates`/`p.solves` fields. Top-level principles require accumulation, propagation, extrusion, intrusion and generalization. No terminal-solution→original raw-constraint transport or same-scoped generalization theorem was applied here. Thus even a future proof from raw `Build` alone would not establish the full abstract algorithm without that correspondence and transport. The inspected `SimpleSub.Sub.subst` and `Store.subset` are structural tools with their explicit premises, not the missing whole scoped source bridge. They were not applied to the parent.

## Actual App data and attempted independent construction

The canonical accepted source equation is the `sourceRules` App case at `OriginalSourceGeneration.lean:112–129`. For an unannotated App at `q`, let

```text
K = [descriptorFormation, wholeArgumentCompatibility,
     completeCallCertificate, sourceCallIncidence, callableImage]
    ++ (if singletonFormalCall Γ f a then [roleAndInitialCallOrigin] else []).

sourceRules Γ (app(q,f,a))
 = existsE (q,viewLogic,0)
     (rule app q Γ
       (map (k ↦ atom(k,q,Γ,[site(f),site(a)])) K ++
        [checking(value,q,Γ,(site(f),returnedValue),(q,descriptor)),
         checking(computation,q,Γ,(q,callableImage),(q,synthesis))])
       (two (sourceRules Γ f) (sourceRules Γ a))).
```

SG §4 compiles this binder and the conjunction of these **whole joint clauses** with both children at their original scopes. Therefore the accepted source program does retain the joint carrier/context/incidence obligations. There is no demonstrated loss in the accepted generation object and no argument that a missing explicit scalar-store field proves loss.

The initial independent attempt used the ordinary four-port scalar demand

```text
G_app = G_f ++ G_a ++
        [T_f <: function T_argument E_argument E_result T_result]
```

with one valuation and a scoped endpoint namespace. This was not completed as a canonical generator across all source forms. Treating its endpoint predicates as a reconstruction of complete challenge relations would lose correlations; that was a rejected attempted interpretation, not a counterexample to the accepted source algorithm or an argument for semantic underdetermination. No standalone projection theorem or counterexample is delivered.

I then retained the actual `Build` local-clause data and attempted a raw interpretation: complete challenge input must be the original `CallInput`, complete observations the original `RawObservation`, and the descriptor membership must check **every actual provider**, every admitted whole-carrier/context tuple, all zero/admin/pending/complete observations and compatible future events. `OriginalSourceInterpretation.FunctionAt`, `CheckedDomain`, `ObservationMem` and `PhiV` expose those same indices. A candidate-independent raw-clause interpretation cannot be replaced by `Local`, `Checking`, assumed `Satisfies (Build ...)`, or by an assertion that the desired source derivation exists. No independent interpretation establishing these clauses from actual Simple-sub satisfaction was completed.

The leased Lean artifact constructs the following **raw data**, with no new witness or assignment:

```text
L = appLogical state q D O
  = { descriptors := [((q,descriptor), D)],
      interfaces := [((q,callableImage), O)],
      viewMeaning := state.viewMeaning,
      eta := state.assignment.event.eta,
      witness := state.assignment.event.witness }.

candidate = scopeCandidate environment occurrence (logical viewLogic L).
```

`D : s.Descriptor` and `O : s.Interface` remain raw arguments. They have NOT been constructed as the readout of the same solving valuation. Consequently they are not a delivered source witness and cannot discharge the parent by choosing replacement values. The individually elaborated lemmas show only the exact frame fold, the two updated slots and preservation of the existing complete event, actual value/root/binding fields, active call and source registry.

## Exact first unresolved sequent

For this actual candidate, original admission reduces through `Admitted`, `DataAdmitted` and `admitted_scoped_iff` (`OriginalSourceEnvironment.lean:610–661`) to the concrete raw obligation

```lean
admissions.logical state ⟨q, .viewLogic, 0⟩ .viewLogic
  (appLogical state q D O)
```

in the **same** environment and decoded state. The requisite independent generator/readout equation is not supplied by the source-algebra lemmas:

```text
independentlySolves (canonicalGenerate Γ (app(q,f,a))) ρ
  + legitimate child IHs in the same Γ/telescope/ρ
  ──────────────────────────────────────────────────────
  construct Dρ and Oρ from that same ρ and telescope,
  prove admissions.logical state (q,viewLogic,0) viewLogic
        (appLogical state q Dρ Oρ),
  and prove each original App local clause and both child judgments
  after extending with that exact candidate.
```

Neither `canonicalGenerate` nor `independentlySolves` above names an implemented declaration: they identify the missing independent construction, not assumed laws. In the implemented source API, `LocalAdmissions.logical` is an independent local relation; `functionKernel` installs it and leaves the original App atoms in `original.atom`. The constructor equation for `Build` carrying these obligations does not prove that actual `p.generates` plus `p.solves` entails them. Using `generated_application_checking` would assume exactly `Satisfies original environment (Build ...)`; it was not used.

This is a **formalization/construction gap**, not a proof that accepted semantics are underdetermined, that the source requires a new semantic choice, or that the accepted parent is false. No source-qualified satisfying-assignment/source-judgment counterexample was established. The retained full local clauses make a relational interpretation a possible repair; its concrete mapping and induction remain unfinished. Primary owns subsequent source/algorithm correspondence and any newly bounded continuation.

All original App premises remain: admitted `.viewLogic` candidate; descriptor formation; whole-argument compatibility; complete Call certificate; source incidence; callable image; conditional role/initial-origin clause; value checking from **callee.returnedValue** to App descriptor; computation checking from callable image to synthesis; both child derivations under the same extension. There is no legitimate child IH applied by a delivered theorem. All other expression, pattern and statement cases, publication/shared/event binders and annotations remain unproved for the independent model.

## Parent ledger before/after

| Original obligation | Before | After |
| --- | --- | --- |
| Actual generation represented by one canonical independent constraint object | Unestablished | Unestablished |
| Solving entails original constructor premises under the same assignment | OPEN | OPEN; no App admission/local clause discharged |
| Full binder/telescope extension preserves one assignment | OPEN | OPEN; one logical frame's algebra only |
| Complete original source derivation and direct InferenceSoundness application | OPEN | OPEN; no application |
| PrincipalCoverage | OPEN, separate | OPEN, separate |
| InferenceTermination | OPEN, separate | OPEN, separate |
| Rust/native correspondence | Later, separate | Later, separate; no Rust work |

## Execution and retained failure evidence

Primary explicitly confirmed this leaf as the sole existing Lean/cache/check owner. No build or installation was authorized or attempted. `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` were read: Lean 4.35.0, project `-j1 -M1024`, no external packages. `command -v elan`, `command -v lake`, `command -v lean`: exit 0; existing proxies found. Read-only `elan which lake`: exit 0, resolved native executable below.

Actual version commands, both exit 0:

```text
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake --version
Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)

/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake env lean --version
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
```

Both direct checks used exactly this command from `notes/theory/lean`:

```sh
timeout 120s env LEAN_NUM_THREADS=1 /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake env lean -j1 -M1024 YulangClosure/ConcreteGenerationSoundnessR186V2.lean
```

Check 1: exit 1. Complete diagnostic:

```text
YulangClosure/ConcreteGenerationSoundnessR186V2.lean:1:0: error: object file '/home/momota1029/rust/yulang/notes/theory/lean/.lake/build/lib/lean/YulangClosure/SimpleSubConstraintSyntax.olean' of module YulangClosure.SimpleSubConstraintSyntax does not exist
```

The unused `SimpleSubConstraintSyntax` import was removed. Its mathematical source had been read/authenticated, but no declaration from it is used by the final artifact. No dependency was built.

Check 2: exit 1. Material diagnostics (the failed declarations were subsequently removed, not claimed accepted):

```text
YulangClosure/ConcreteGenerationSoundnessR186V2.lean:26:57: error(lean.invalidDottedIdent): Invalid dotted identifier notation: The expected type of `.roleAndInitialCallOrigin` could not be determined

Hint: Using `AtomKind.roleAndInitialCallOrigin would be unambiguous:
  [apply] `AtomKind.roleAndInitialCallOrigin`
YulangClosure/ConcreteGenerationSoundnessR186V2.lean:29:0: error: Not a definitional equality: the left-hand side
  sourceRules context (Source.app { site := site } callee argument)
is not definitionally equal to the right-hand side
  RuleTree.existsE { site := site, kind := BinderKind.viewLogic }
    (RuleTree.rule Rule.app site context
      (appAtoms context site callee argument ++
        [Premise.checking
            { mode := CheckMode.value, site := site, context := context,
              lower := { site := callee.site, port := Port.returnedValue },
              upper := { site := site, port := Port.descriptor } },
          Premise.checking
            { mode := CheckMode.computation, site := site, context := context,
              lower := { site := site, port := Port.callableImage },
              upper := { site := site, port := Port.synthesis } }])
      (RuleForest.two (sourceRules context callee) (sourceRules context argument)))
YulangClosure/ConcreteGenerationSoundnessR186V2.lean:40:81: error: Type mismatch
  rfl
has type
  ?m.23 = ?m.23
but is expected to have type
  sourceRules context (Source.app { site := site } callee argument) =
    RuleTree.existsE { site := site, kind := BinderKind.viewLogic }
      (RuleTree.rule Rule.app site context
        (appAtoms context site callee argument ++
          [Premise.checking
              { mode := CheckMode.value, site := site, context := context,
                lower := { site := callee.site, port := Port.returnedValue },
                upper := { site := site, port := Port.descriptor } },
            Premise.checking
              { mode := CheckMode.computation, site := site, context := context,
                lower := { site := site, port := Port.callableImage },
                upper := { site := site, port := Port.synthesis } }])
        (RuleForest.two (sourceRules context callee) (sourceRules context argument)))
YulangClosure/ConcreteGenerationSoundnessR186V2.lean:106:2: error: Type mismatch
  admitted_scoped_iff inputs readout admissions environment { site := site, kind := BinderKind.viewLogic } state decoded
    occurrence (Payload.logical LogicalKind.viewLogic (appLogical state site descriptor output))
has type
  Admitted inputs readout admissions environment { site := site, kind := BinderKind.viewLogic }
      (scopeCandidate environment occurrence
        (Payload.logical LogicalKind.viewLogic (appLogical state site descriptor output))) ↔
    DataAdmitted inputs readout admissions state { site := site, kind := BinderKind.viewLogic }
      (Payload.logical LogicalKind.viewLogic (appLogical state site descriptor output))
but is expected to have type
  Admitted inputs readout admissions environment { site := site, kind := BinderKind.viewLogic }
      (appCandidate environment state site occurrence descriptor output) ↔
    admissions.logical state { site := site, kind := BinderKind.viewLogic } LogicalKind.viewLogic
      (appLogical state site descriptor output)
```

The failed `original_app_equation` audit printed `[propext, sorryAx, Classical.choice, Quot.sound]`; the failed `app_candidate_admission_iff` audit printed `[propext, sorryAx]`. These were Lean's recovery declarations after errors, not accepted proofs. They and their auxiliary `appAtoms` definition were removed completely from the final Lean file. An intermediate source simplification was not checked and was also removed. No third check ran. The final source contains neither failed theorem. Its four retained theorem bodies are the same bodies that individually elaborated in check 2. A final source search for `sorry`, `admit`, project `axiom`, `skipKernelTC`, `native_decide` had no matches (`rg` exit 1). This source search does not replace an indirect axiom audit.

The skill checker was not used because it builds modules and creates an audit scratch file; both activities are outside this packet. No fresh imported artifact build/hash-to-source correspondence receipt was produced: this was a direct check against the existing cache only. No successful module check, whole-source proof or integration gate is claimed.

## Actual printed types and complete axioms for retained declarations

The following are the actual check-2 printed types and axiom outputs. They show individual declarations in an overall failing module command, not final-module acceptance.

```text
@YulangClosure.ConcreteGenerationSoundnessR186V2.app_candidate_readout : ∀
  {s : YulangClosure.OriginalSourceInterpretation.Sorts} {View : Type}
  (readout : YulangClosure.OriginalSourceEnvironment.RuntimeReadout s View)
  (environment : YulangClosure.OriginalSource.Environment (YulangClosure.OriginalSourceEnvironment.Payload s View))
  (state : YulangClosure.OriginalSourceEnvironment.Decoded s View),
  YulangClosure.OriginalSourceEnvironment.decode readout environment = some state →
    ∀ (site occurrence : Nat) (descriptor : s.Descriptor) (output : s.Interface),
      YulangClosure.OriginalSourceEnvironment.decode readout
          (environment.extend { site := site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic }
            (YulangClosure.ConcreteGenerationSoundnessR186V2.appCandidate environment state site occurrence descriptor
              output)) =
        some (state.logical (YulangClosure.ConcreteGenerationSoundnessR186V2.appLogical state site descriptor output))
'YulangClosure.ConcreteGenerationSoundnessR186V2.app_candidate_readout' depends on axioms: [propext, Quot.sound]

@YulangClosure.ConcreteGenerationSoundnessR186V2.app_candidate_descriptor : ∀
  {s : YulangClosure.OriginalSourceInterpretation.Sorts} {View : Type}
  (state : YulangClosure.OriginalSourceEnvironment.Decoded s View) (site : YulangClosure.OriginalSource.Site)
  (descriptor : s.Descriptor) (output : s.Interface),
  (state.logical
            (YulangClosure.ConcreteGenerationSoundnessR186V2.appLogical state site descriptor
              output)).assignment.descriptor
      { site := site, port := YulangClosure.OriginalSource.Port.descriptor } =
    descriptor
'YulangClosure.ConcreteGenerationSoundnessR186V2.app_candidate_descriptor' depends on axioms: [propext, Quot.sound]

@YulangClosure.ConcreteGenerationSoundnessR186V2.app_candidate_output : ∀
  {s : YulangClosure.OriginalSourceInterpretation.Sorts} {View : Type}
  (state : YulangClosure.OriginalSourceEnvironment.Decoded s View) (site : YulangClosure.OriginalSource.Site)
  (descriptor : s.Descriptor) (output : s.Interface),
  (state.logical (YulangClosure.ConcreteGenerationSoundnessR186V2.appLogical state site descriptor output)).interfaces
      { site := site, port := YulangClosure.OriginalSource.Port.callableImage } =
    output
'YulangClosure.ConcreteGenerationSoundnessR186V2.app_candidate_output' depends on axioms: [propext, Quot.sound]

@YulangClosure.ConcreteGenerationSoundnessR186V2.app_candidate_keeps_shared_data : ∀
  {s : YulangClosure.OriginalSourceInterpretation.Sorts} {View : Type}
  (state : YulangClosure.OriginalSourceEnvironment.Decoded s View) (site : YulangClosure.OriginalSource.Site)
  (descriptor : s.Descriptor) (output : s.Interface),
  have next := state.logical (YulangClosure.ConcreteGenerationSoundnessR186V2.appLogical state site descriptor output);
  next.assignment.event = state.assignment.event ∧
    next.assignment.value = state.assignment.value ∧
      next.assignment.root = state.assignment.root ∧
        next.assignment.binding = state.assignment.binding ∧
          next.active = state.active ∧ next.callOwners = state.callOwners
'YulangClosure.ConcreteGenerationSoundnessR186V2.app_candidate_keeps_shared_data' does not depend on any axioms
```

## Authenticated inputs, outputs and cessation

All 18 revised/inherited inputs were authenticated before semantic reads. The v3 contract, its activation and its three added semantic owners were separately authenticated before their content reads. Direct source hashes:

- `Contracts.lean`: `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`.
- `SimpleSubConstraintSyntax.lean`: `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6`.
- `OriginalSourceSyntax.lean`: `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`.
- `OriginalSourceGeneration.lean`: `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`.
- `OriginalSourceEnvironment.lean`: `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132`.
- `OriginalSourceInterpretation.lean`: `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef`.
- `OriginalSourceChecking.lean`: `a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6`.
- Source Generalize selection: `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38`.
- Selected source Generalize construction: `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`.
- Source-safety manuscript: `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166`.
- Top-level principles: `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`.
- Contextual Function selection: `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0`.
- Call semantic-input realization: `fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a`.
- Inferred Function source views: `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1`.
- Source contracts: `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186`.
- Approved context domain: `9b63603890cd522ec80ef81e6208c52acdb1f09ab0a847a9b51368a8f563acf3`.
- Approved annotation boundaries: `e1e2ff77b181fe42edd404ee0d69cfc6d3bb0fbc99ba7e7f092710025d11fb12` (hash authenticated; contents not read).

Only the exact two leased outputs were written: the Lean artifact and this one handoff. Lean artifact SHA-256: `c8e2b5a1ad84164adde6bc454280edfeae04214645d299e143b33d62e66e9d67`. No scratch/audit file, new environment/cache, requested Lean output artifact, root import, compiler, test, manifest, shared task/status/index, question or other-worker file was written. Direct Lean was run without `-o`; no build or new dependency was produced. No Rust, Cargo, runtime, installation, child, nested CLI, scheduling, Git or third-party contact. Root and applicable skill/rules were read; the prior v1 mismatch receipt was not modified.

Resource observations: the first v2 clock observation was `2026-11-01 11:39:11 UTC`; freeze timestamp `2026-11-01 11:58:38 UTC`; measured interval between those observations `1167.395` seconds. Exact launch-before-first-observation overhead and peak CPU/RSS are UNKNOWN; no unused grant is returned or renewed. Local 1800-second grant is not reset; fully charged cumulative proof allocation remains 3600 seconds (v1 1800 + v2 1800), with independent review separately reserved by primary. The measured interval leaves at most `632.605` seconds of the local grant before accounting for unobserved startup overhead. Checks consumed 2/2; check allowance remaining 0. Both command timeout bounds were 120s, Lean thread bound 1, per-process Lean memory argument 1024 MiB.

Mutual TODO `R186-INDEPENDENT-GENERATION-1`: primary-owned continuation must construct actual canonical generation and independent type/effect satisfaction, including the retained joint App clauses and exact descriptor/interface readout at the original telescope, then derive the raw admission above and every other original constructor premise. Falsifier: an accepted source/generated-constraint solution that fails an original premise under the same scope/assignment; none delivered here. No semantic escalation or new grant requested by this leaf.

Worker STOPPED; writes stop with this frozen revision. No running command, child or unresolved descendant/generated-output lease remains. Both output leases are frozen for primary intake. This is not a success-gate or parent-closure receipt; review/integration belongs to the primary.
