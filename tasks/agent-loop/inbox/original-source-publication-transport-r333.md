# R333 publication transport — frozen handoff r1

Assignment ID: `R333-PUBLICATION-TRANSPORT`; revision: **1**.
Worker/author: `/root/r333_publication`, leaf `astra_prover`; no descendants or coauthors.
Parent-confirmed launch: role `astra_prover`, no model/effort override. Role configuration requests Astra; runtime effective model and effort **UNKNOWN**. Runtime UUID/session ID unavailable; display identity belongs to the current parent session.
Baseline: `0d5c7dfb0` (assigned; no Git executed).
Contract: `tasks/agent-loop/sprints/source-kernel-transport-r333.md`, SHA-256 `a9fb5a9a1b2d7802a31d040173c2abb41f207d7511315475277556121b85d2ad`.
Outcome: **kernel-checked exact publication transport; conditional application to three original Judgment induction edges**. Independent review and native/production authority are not claimed.

## Parent and source correspondence

The unchanged parent is real source Union, licensed child/result correspondence and original R159 application. R331 supplied an injective original environment embedding but left actual candidate/validity/publication/readback operations open. This packet proves those operations commute for arbitrary `s`, `View`, `G`, `g : G`, original environments, names/sites and ordered binding lists. Empty old View is permitted. No source subset, well-formedness assumption, admitted-candidate selection or kernel law is introduced.

Governing source: authoritative `notes/design/2026-10-08-source-generalize-definition.md` §2; original SG `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` §§3.3,5.1–5.2. Actual operation meaning is the source construction in `OriginalSourceGeneration.lean` lines 577–649, documented by `notes/theory/2026-10-26-original-source-generation-construction.md` §7.1. The original entry snapshot, completed captures, immutable catalogue and ordered initializer suffix remain distinct.

Source constructors/consumers: `Environment.prefixAtShared` → `publicationCandidate` → `publicationValid` and `publish`; `publicationName` plus immutable `publications` → `atPublication` → `restore`; `aliasPublication` copies the same identity. These are applied to the existing `Judgment.publishGroup`, `Judgment.atPublication`, and `Judgment.aliasPublication` constructors. No Rust/native owner correspondence or production operation was checked or modified.

## Results and exact application

Namespace: `YulangClosure.OriginalSourcePublicationTransportR333`.

- `prefixAtShared_commutes` maps the exact ordered prefix, including duplicates.
- `publicationCandidate_commutes` is equality of Options, preserving each failure branch as well as success. Its record maps all seven fields, retaining exact entry names/frames, completed captures, fixed history and initializer suffix. Equality of actual paths is reflected using R331 injection; no equality test is assumed.
- `publicationValid_iff` proves both directions against the fixed original catalogue. `publicationRecord_injective` prevents unequal old records from becoming equal after embedding.
- `publish_commutes` maps the exact name additions and old-name suffix; `mapM` failure is preserved. No name uniqueness, sortedness or deduplication assumption occurs.
- `publicationName_commutes`, `atPublication_commutes`, `aliasPublication_commutes` preserve first lookup, fixed-frame validation, exact identity, historical events and restored environment, including failure.
- `judgment_publishGroup`, `judgment_atPublication`, `judgment_aliasPublication` invert the ORIGINAL judgment and construct its corresponding target constructor. Their explicit premise `∀ next, Judgment oldKernel next body → Judgment newKernel (environment g next) body` is the ordinary child induction hypothesis. Publication validity and all transition equations are proved here, not supplied by that premise. The kernels are arbitrary parameters; no artificial kernel is defined.

First remaining parent premise: complete source Judgment induction needs authentic old-to-extended Local/Checking/Boundary transport and full extended universal-admission-domain coverage, plus child induction hypotheses at the same environments. Owners: primary and R333 domain/kernel lanes. The three constructor-edge theorems close only their publication subgoals. They do not establish R159 target Checking, a generated view admission, licensed Call child, whole-language soundness, or native correspondence.

Prior work reused: R331 payload/event/key injectivity, `environment`, `publications_preserved`, and `restore_commutes`. Its `publicationName_preserved` has the same statement as the short independently reproved name helper; the earlier `alias_commutes` covers successful aliasing, whereas this packet gives full Option equality. R331's admission image instance is not used as a full-domain law. Historical R331 handoff hashes were not substituted for current bytes; the actual R331 dependency below was checked.

## Frozen files and dependencies

Only these repository paths were written:

- `notes/theory/lean/YulangClosure/OriginalSourcePublicationTransportR333.lean`
- `tasks/agent-loop/inbox/original-source-publication-transport-r333.md`

Lean artifact SHA-256: `a6c9e70a159bf60a72bda0fcc873986564ae5358dd042bccfad166df877e7c22`.
Direct import `OriginalSourceEnvironmentTransportR331.lean`: `d21945af4a0230a70b1670682f818530fe21460649a3b3b66c787da52109a97c`; prior author `/root/r331_env_proof` (subsequent repository integration provenance retained by primary).
Actual operation definition `OriginalSourceGeneration.lean`: `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`.
`/tmp/yulang-r333-publication/dependency-hashes.json` records all **55** source inputs and the three project configs, verified byte-equal to the checked isolated source snapshot; SHA-256 `9bad94f848ccb2391b0799a5cf31cfb90a9f18c300f8b4b10eb55d582ed8c4b2`. The sole configuration difference is the authorized isolated `-M2048`; repository configuration remains unchanged.

## Checks and resources

Observed native tool: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
Observed versions: Lake `5.0.0-src+eb6cafb` / Lean `4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.

- Isolated `lake build +YulangClosure.OriginalSourceEnvironmentTransportR331`: exit 0, **55 jobs**, including actual R315 rebuild at `-M2048`.
- Focused `lake env lean -j1 -M2048 YulangClosure/OriginalSourcePublicationTransportR333.lean`: final exit 0, no warnings (`check6.log`). Earlier `check1.log`/`check2.log`–`check5.log` retain missing-import, naming, monad and dependent rewrite diagnostics; all were repaired. One initial copy used the wrong relative cwd and was corrected before checking.
- Bundled `check_lean.py`, 120-second bound, all 15 theorem names: module build passed (**56 jobs**); audit failed because its invocation hardcodes `-M1024`. Failure retained in `audit.log`; no success claimed for that run.
- Exact `audit_source` generated by the unchanged helper into `PublicationAudit.lean`; rerun `lake --no-cache env lean -j1 -M2048 --root=/tmp/yulang-r333-publication /tmp/yulang-r333-publication/PublicationAudit.lean`: exit 0. The unchanged helper's `validate_audit` accepted complete ordered types/axioms for **15/15** declarations; theorem kind and axiom whitelist were checked inside Lean. Full output is included below and in `audit2048.log` (SHA-256 `b0428d616240335407cd74581ac1df497f1023bc1d99b3e91a0aaa0fb4e4e7b6`).
- Complete source-dependency search found only explanatory comments and existing axiom-whitelist diagnostic strings; no `sorry`, project axiom, `native_decide` or checker bypass. `source-audit.txt` retains those matches.

Axiom sets: `exitPath_commutes` uses `[propext]`; `names_injective`, `initializer_injective`, `publicationRecord_injective`, `option_mapM_naturality` use `[propext, Quot.sound]`; the other ten use `[propext, Classical.choice, Quot.sound]`. No extra axiom appears.

Resources: granted 2400 seconds / at most eight substantive stages. Completed five stages: source/dependency examination; structural candidate proof; validity/publication/readback; constructor application; verification/freeze. Total active runtime and peak RSS were not instrumented; no invented measurement is supplied. Lean invocations were single-threaded, at most `-M2048`; final audits had 120-second process timeout. Checker ownership was coordinated with primary and released after all processes exited. No children, Git, network, production edits or default-root integration build.

All scratch paths are within `/tmp/yulang-r333-publication`: isolated `project/` (source snapshot, local config, `.lake` generated/cache outputs), `build.log`, `check1.log`–`check6.log`, `audit-command.txt`, `audit.log`, `PublicationAudit.lean`, `audit2048.log`, `dependency-hashes.json`, `source-audit.txt`. The helper's temporary `yulang-lean-audit-*` directory was automatically removed after its failed run.

## Mutual TODO and stop receipt

`R333-PUB-PARENT-1`: primary/kernel lane applies these constructor lemmas within a justified full Judgment induction; required inputs are independent local/checking transport and actual all-domain admission evidence. Falsifier: a target admitted nonimage candidate or a Local/Checking leaf whose original semantic meaning changes. No full source transport may be claimed solely from these lemmas.

`R333-PUB-REVIEW-1`: primary assigns a fresh independent reviewer to frozen bytes, matching the current R331 dependency and the actual publication definitions. Producer is not a certifier. No production TODO is licensed by this research result.

Stop condition reached: all requested publication equations and available constructor applications are checked. **All artifact and scratch writes stopped on submission; all owned checker processes exited; no descendants exist.** Next step is independent review/integration by primary, not further worker execution. Whole source/native parent remains OPEN.

## Complete checked theorem types and axiom dependencies

```text
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourcePublicationTransportR333.exitPath_commutes
@YulangClosure.OriginalSourcePublicationTransportR333.exitPath_commutes : ∀
  {s : YulangClosure.OriginalSourceInterpretation.Sorts} {View G : Type} (g : G)
  (f : YulangClosure.OriginalSource.Frame (YulangClosure.OriginalSourceEnvironment.Payload s View)),
  (YulangClosure.OriginalSourceEnvironmentTransportR331.frame g f).exitPath =
    List.map (YulangClosure.OriginalSourceEnvironmentTransportR331.step g) f.exitPath
'YulangClosure.OriginalSourcePublicationTransportR333.exitPath_commutes' depends on axioms: [propext]
YULANG_AUDIT_END YulangClosure.OriginalSourcePublicationTransportR333.exitPath_commutes
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourcePublicationTransportR333.prefixAtShared_commutes
@YulangClosure.OriginalSourcePublicationTransportR333.prefixAtShared_commutes : ∀
  {s : YulangClosure.OriginalSourceInterpretation.Sorts} {View G : Type} (g : G)
  (env : YulangClosure.OriginalSource.Environment (YulangClosure.OriginalSourceEnvironment.Payload s View))
  (site : YulangClosure.OriginalSource.Site),
  (YulangClosure.OriginalSourceEnvironmentTransportR331.environment g env).prefixAtShared site =
    List.map (YulangClosure.OriginalSourceEnvironmentTransportR331.frame g) (env.prefixAtShared site)
'YulangClosure.OriginalSourcePublicationTransportR333.prefixAtShared_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalSourcePublicationTransportR333.prefixAtShared_commutes
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourcePublicationTransportR333.publicationCandidate_commutes
@YulangClosure.OriginalSourcePublicationTransportR333.publicationCandidate_commutes : ∀
  {s : YulangClosure.OriginalSourceInterpretation.Sorts} {View G : Type} (g : G)
  (env : YulangClosure.OriginalSource.Environment (YulangClosure.OriginalSourceEnvironment.Payload s View))
  (site : YulangClosure.OriginalSource.Site),
  (YulangClosure.OriginalSourceEnvironmentTransportR331.environment g env).publicationCandidate site =
    Option.map (YulangClosure.OriginalSourcePublicationTransportR333.candidate g) (env.publicationCandidate site)
'YulangClosure.OriginalSourcePublicationTransportR333.publicationCandidate_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalSourcePublicationTransportR333.publicationCandidate_commutes
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourcePublicationTransportR333.publicationName_commutes
@YulangClosure.OriginalSourcePublicationTransportR333.publicationName_commutes : ∀
  {s : YulangClosure.OriginalSourceInterpretation.Sorts} {View G : Type} (g : G)
  (env : YulangClosure.OriginalSource.Environment (YulangClosure.OriginalSourceEnvironment.Payload s View))
  (name : YulangClosure.OriginalSource.Name),
  (YulangClosure.OriginalSourceEnvironmentTransportR331.environment g env).publicationName name =
    Option.map (YulangClosure.OriginalSourceEnvironmentTransportR331.publicationId g) (env.publicationName name)
'YulangClosure.OriginalSourcePublicationTransportR333.publicationName_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalSourcePublicationTransportR333.publicationName_commutes
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourcePublicationTransportR333.names_injective
@YulangClosure.OriginalSourcePublicationTransportR333.names_injective : ∀
  {s : YulangClosure.OriginalSourceInterpretation.Sorts} {View G : Type} (g : G),
  Function.Injective (YulangClosure.OriginalSourceEnvironmentTransportR331.names g)
'YulangClosure.OriginalSourcePublicationTransportR333.names_injective' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalSourcePublicationTransportR333.names_injective
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourcePublicationTransportR333.initializer_injective
@YulangClosure.OriginalSourcePublicationTransportR333.initializer_injective : ∀
  {s : YulangClosure.OriginalSourceInterpretation.Sorts} {View G : Type} (g : G),
  Function.Injective (YulangClosure.OriginalSourceEnvironmentTransportR331.initializer g)
'YulangClosure.OriginalSourcePublicationTransportR333.initializer_injective' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalSourcePublicationTransportR333.initializer_injective
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourcePublicationTransportR333.publicationRecord_injective
@YulangClosure.OriginalSourcePublicationTransportR333.publicationRecord_injective : ∀
  {s : YulangClosure.OriginalSourceInterpretation.Sorts} {View G : Type} (g : G),
  Function.Injective (YulangClosure.OriginalSourceEnvironmentTransportR331.publicationRecord g)
'YulangClosure.OriginalSourcePublicationTransportR333.publicationRecord_injective' depends on axioms: [propext,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalSourcePublicationTransportR333.publicationRecord_injective
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourcePublicationTransportR333.publicationValid_iff
@YulangClosure.OriginalSourcePublicationTransportR333.publicationValid_iff : ∀
  {s : YulangClosure.OriginalSourceInterpretation.Sorts} {View G : Type} (g : G)
  (env : YulangClosure.OriginalSource.Environment (YulangClosure.OriginalSourceEnvironment.Payload s View))
  (bindings : List (YulangClosure.OriginalSource.Name × YulangClosure.OriginalSource.Site)),
  (YulangClosure.OriginalSourceEnvironmentTransportR331.environment g env).publicationValid bindings ↔
    env.publicationValid bindings
'YulangClosure.OriginalSourcePublicationTransportR333.publicationValid_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalSourcePublicationTransportR333.publicationValid_iff
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourcePublicationTransportR333.option_mapM_naturality
@YulangClosure.OriginalSourcePublicationTransportR333.option_mapM_naturality : ∀ {A B C : Type} (xs : List A)
  (f : A → Option B) (h : B → C), List.mapM (fun x => Option.map h (f x)) xs = Option.map (List.map h) (List.mapM f xs)
'YulangClosure.OriginalSourcePublicationTransportR333.option_mapM_naturality' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalSourcePublicationTransportR333.option_mapM_naturality
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourcePublicationTransportR333.publish_commutes
@YulangClosure.OriginalSourcePublicationTransportR333.publish_commutes : ∀
  {s : YulangClosure.OriginalSourceInterpretation.Sorts} {View G : Type} (g : G)
  (env : YulangClosure.OriginalSource.Environment (YulangClosure.OriginalSourceEnvironment.Payload s View))
  (bindings : List (YulangClosure.OriginalSource.Name × YulangClosure.OriginalSource.Site)),
  (YulangClosure.OriginalSourceEnvironmentTransportR331.environment g env).publish bindings =
    Option.map (YulangClosure.OriginalSourceEnvironmentTransportR331.environment g) (env.publish bindings)
'YulangClosure.OriginalSourcePublicationTransportR333.publish_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalSourcePublicationTransportR333.publish_commutes
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourcePublicationTransportR333.atPublication_commutes
@YulangClosure.OriginalSourcePublicationTransportR333.atPublication_commutes : ∀
  {s : YulangClosure.OriginalSourceInterpretation.Sorts} {View G : Type} (g : G)
  (env : YulangClosure.OriginalSource.Environment (YulangClosure.OriginalSourceEnvironment.Payload s View))
  (name : YulangClosure.OriginalSource.Name),
  (YulangClosure.OriginalSourceEnvironmentTransportR331.environment g env).atPublication name =
    Option.map (YulangClosure.OriginalSourceEnvironmentTransportR331.environment g) (env.atPublication name)
'YulangClosure.OriginalSourcePublicationTransportR333.atPublication_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalSourcePublicationTransportR333.atPublication_commutes
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourcePublicationTransportR333.aliasPublication_commutes
@YulangClosure.OriginalSourcePublicationTransportR333.aliasPublication_commutes : ∀
  {s : YulangClosure.OriginalSourceInterpretation.Sorts} {View G : Type} (g : G)
  (env : YulangClosure.OriginalSource.Environment (YulangClosure.OriginalSourceEnvironment.Payload s View))
  (original aliasName : YulangClosure.OriginalSource.Name),
  (YulangClosure.OriginalSourceEnvironmentTransportR331.environment g env).aliasPublication original aliasName =
    Option.map (YulangClosure.OriginalSourceEnvironmentTransportR331.environment g)
      (env.aliasPublication original aliasName)
'YulangClosure.OriginalSourcePublicationTransportR333.aliasPublication_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalSourcePublicationTransportR333.aliasPublication_commutes
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourcePublicationTransportR333.judgment_publishGroup
@YulangClosure.OriginalSourcePublicationTransportR333.judgment_publishGroup : ∀
  {s : YulangClosure.OriginalSourceInterpretation.Sorts} {View G : Type} (g : G)
  (oldKernel : YulangClosure.OriginalSource.Kernel (YulangClosure.OriginalSourceEnvironment.Payload s View))
  (newKernel :
    YulangClosure.OriginalSource.Kernel
      (YulangClosure.OriginalSourceEnvironment.Payload (YulangClosure.OriginalInterfacePreservationR328.extended s G)
        (View ⊕ Unit)))
  (env : YulangClosure.OriginalSource.Environment (YulangClosure.OriginalSourceEnvironment.Payload s View))
  (bindings : List (YulangClosure.OriginalSource.Name × YulangClosure.OriginalSource.Site))
  (body : YulangClosure.OriginalSource.RuleTree),
  (∀ (next : YulangClosure.OriginalSource.Environment (YulangClosure.OriginalSourceEnvironment.Payload s View)),
      YulangClosure.OriginalSource.Judgment oldKernel next body →
        YulangClosure.OriginalSource.Judgment newKernel
          (YulangClosure.OriginalSourceEnvironmentTransportR331.environment g next) body) →
    YulangClosure.OriginalSource.Judgment oldKernel env
        (YulangClosure.OriginalSource.RuleTree.publishGroup bindings body) →
      YulangClosure.OriginalSource.Judgment newKernel
        (YulangClosure.OriginalSourceEnvironmentTransportR331.environment g env)
        (YulangClosure.OriginalSource.RuleTree.publishGroup bindings body)
'YulangClosure.OriginalSourcePublicationTransportR333.judgment_publishGroup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalSourcePublicationTransportR333.judgment_publishGroup
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourcePublicationTransportR333.judgment_atPublication
@YulangClosure.OriginalSourcePublicationTransportR333.judgment_atPublication : ∀
  {s : YulangClosure.OriginalSourceInterpretation.Sorts} {View G : Type} (g : G)
  (oldKernel : YulangClosure.OriginalSource.Kernel (YulangClosure.OriginalSourceEnvironment.Payload s View))
  (newKernel :
    YulangClosure.OriginalSource.Kernel
      (YulangClosure.OriginalSourceEnvironment.Payload (YulangClosure.OriginalInterfacePreservationR328.extended s G)
        (View ⊕ Unit)))
  (env : YulangClosure.OriginalSource.Environment (YulangClosure.OriginalSourceEnvironment.Payload s View))
  (name : YulangClosure.OriginalSource.Name) (body : YulangClosure.OriginalSource.RuleTree),
  (∀ (next : YulangClosure.OriginalSource.Environment (YulangClosure.OriginalSourceEnvironment.Payload s View)),
      YulangClosure.OriginalSource.Judgment oldKernel next body →
        YulangClosure.OriginalSource.Judgment newKernel
          (YulangClosure.OriginalSourceEnvironmentTransportR331.environment g next) body) →
    YulangClosure.OriginalSource.Judgment oldKernel env
        (YulangClosure.OriginalSource.RuleTree.atPublication name body) →
      YulangClosure.OriginalSource.Judgment newKernel
        (YulangClosure.OriginalSourceEnvironmentTransportR331.environment g env)
        (YulangClosure.OriginalSource.RuleTree.atPublication name body)
'YulangClosure.OriginalSourcePublicationTransportR333.judgment_atPublication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalSourcePublicationTransportR333.judgment_atPublication
YULANG_AUDIT_BEGIN YulangClosure.OriginalSourcePublicationTransportR333.judgment_aliasPublication
@YulangClosure.OriginalSourcePublicationTransportR333.judgment_aliasPublication : ∀
  {s : YulangClosure.OriginalSourceInterpretation.Sorts} {View G : Type} (g : G)
  (oldKernel : YulangClosure.OriginalSource.Kernel (YulangClosure.OriginalSourceEnvironment.Payload s View))
  (newKernel :
    YulangClosure.OriginalSource.Kernel
      (YulangClosure.OriginalSourceEnvironment.Payload (YulangClosure.OriginalInterfacePreservationR328.extended s G)
        (View ⊕ Unit)))
  (env : YulangClosure.OriginalSource.Environment (YulangClosure.OriginalSourceEnvironment.Payload s View))
  (originalName aliasName : YulangClosure.OriginalSource.Name) (body : YulangClosure.OriginalSource.RuleTree),
  (∀ (next : YulangClosure.OriginalSource.Environment (YulangClosure.OriginalSourceEnvironment.Payload s View)),
      YulangClosure.OriginalSource.Judgment oldKernel next body →
        YulangClosure.OriginalSource.Judgment newKernel
          (YulangClosure.OriginalSourceEnvironmentTransportR331.environment g next) body) →
    YulangClosure.OriginalSource.Judgment oldKernel env
        (YulangClosure.OriginalSource.RuleTree.aliasPublication originalName aliasName body) →
      YulangClosure.OriginalSource.Judgment newKernel
        (YulangClosure.OriginalSourceEnvironmentTransportR331.environment g env)
        (YulangClosure.OriginalSource.RuleTree.aliasPublication originalName aliasName body)
'YulangClosure.OriginalSourcePublicationTransportR333.judgment_aliasPublication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
YULANG_AUDIT_END YulangClosure.OriginalSourcePublicationTransportR333.judgment_aliasPublication
```
