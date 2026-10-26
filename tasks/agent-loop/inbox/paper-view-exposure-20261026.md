# PAPER-VIEW-EXPOSURE-20261026/r1 — proof handoff (frozen r1)

Outcome: **BUILT RESEARCH CANDIDATE; COMPLETE AXIOM AUDIT OPEN**. The five isolated source modules compile, including the R62 dependency cone. Final audit process exits 1 on raw private-name parsing; 110 public theorem blocks have complete printed types and allowed axiom results, while nine private source theorem audits remain missing. No independent review or production authority is asserted.

Assignment: PAPER-VIEW-EXPOSURE-20261026-PROOF/r1. Worker `/root/vep`; registered bounded Lean leaf; observed model/effort/session UUID UNKNOWN. Active receipt delivered to primary before writes. Baseline `2f9b5a2a1255563dcc9567953be1374b0662acb1`. Contract SHA-256 `40a4a48f6ee071c215b8f689b5d010bbced5a38a24803a5ec0908a6987dee172`; native intake SHA-256 `3f3660eb29930a1f6ed71f27e49efc4a0dc740a0354bd248028c5287b5549c65`. Not alone in the workspace; no other's path changed and no descendants.

## Claim and source correspondence

Original parent: execution safety for the entire declared source language, source/native correspondence, and original inference A/B with the same source scope/shared witness. Exact parent proposition definitions `YulangClosure.SourceProblem.Elaboration`, `.InferenceSoundness`, `.SourceScopedCoverage`, `.PrincipalCoverage`, `.NativeCorrespondence` in `Contracts.lean:122–148` remain definitions with concrete instances unproved. `docs/yulang-whole-proof-closure-ja.md` §1 and §4 retain the full source domain. This packet closes none of these parent propositions.

Governing research source: `docs/yulang-operational-type-safety-ja.tex` opening source-correspondence correction; :239/321, :485–493 (Force/View entry; request metadata, continuation remainder and result-path metadata), :995–1008 (constructor observation), :1014–1026 (frame typing); corrected `2026-10-24-corrected-core-value-continuation.md` §§2–6, V1/V2/V4/V5/V6. These research drafts do not approve production semantics. Exact manuscript/correction bytes retain the contract hashes.

The source determines `Force(View metadata (Delay body)) -> expose metadata body` and that expose preserves the body result type. It does not equate result-path metadata with the input metadata. Therefore this candidate supplies no `expose metadata (ret v) -> ret (view metadata v)`, request propagation/remainder, or invented metadata operation. The native intake gives useful consume/RootCompReturn/replay equations and missing correspondence; absence of a literal χ field does not prove an encoding impossible. Existing Image/Boundary chains may support an unproved relation.

## Constructed surface and parent application

All names below are under `YulangClosure.PaperTypes` unless qualified otherwise.

- Actual `PaperComputationTyped.expose` constructor, with arbitrary declarations/graph/environment/metadata/body/result, requires only the existing body derivation. No wrapper typing judgment or LocalLaws parameter was added.
- `PaperValueTyped.subst_explicit` adds the expose mutual-recursion case, mapping metadata with the same `mapViewMetadata σ` as syntax. All six existing type-transport judgments inherit it.
- `PaperValueTyped.graphWeaken` adds the expose case to its mutual recursor. All graph lookup/fresh-graph corollaries retain original premises.
- Term `renameTermComputation`, `replaceTermComputation`, `supportedTermComputation` now descend through expose; existing `PaperValueTyped.termRename`, `.termReplace`, `.termSupported` mutual recursors add its exact case. Existing termSubstitute and fresh-graph-formal theorems derive support/replacement for expose. Term operations preserve metadata exactly; type substitution transports its existing type indices.
- `PaperViewExecution.forceViewStep` selects only a Force of View of literal Delay and returns expose with identical metadata/body. `controlStep` gives every old `PaperExtendedExecution.controlStep` success priority, then tries that new rule. Definitions contain no typing premise.
- `PaperViewExecution.preservation` preserves one fixed d/g/e/result for every successful transition, with only the existing `PaperTemplateExecution.BodiesTyped d` code-table premise needed for old template execution. `force_view_delay_control` needs only initial StateTyped and uses the same exact d/g/e/metadata/body/stack/result/binder for step, target typing, erased target typing, control evidence and erased let-context evidence; no BodiesTyped premise is needed for this entry.
- `original_obstruction_entry` applies the generic result to the original R63 closed-unit witness with arbitrary metadata. The old frozen executor/relation still has its original obstruction; the new connected fallback has a typed first step to expose. No original R63 theorem or relation was edited.
- `expose_not_dispatched` explicitly proves that this partial executor then returns none on expose, for any body and existing stack. Thus it makes no progress/full-View claim even for the unit witness.

Represented cases: all previously accepted judgment constructors plus expose; arbitrary open term/type/graph environments, metadata and body; all existing ordered let stacks; old principal/control successful transitions. Omitted: nested/multiple View elimination, Call/View entry, active expose-body evaluation/frame capture, result-path/request/continuation metadata operations, non-let frames, finite constructor observation/guard, complete heap/world/lifecycle semantics and source/native generation/correspondence. The accepted source language and original quantifiers have not been narrowed; the represented formalization remains partial.

First semantic remaining premise: authoritative paper/native metadata owner must specify concrete result-path transfer and request exposure/remainder/replay operations, linked to existing metadata representation/producer. In particular, result-path χ′ cannot be assumed equal to χ. For the exact resulting unit state, supply a source-justified outgoing operation from `expose metadata (ret unit)` with matching result metadata. Owner: paper/native metadata representation owner, to be assigned by primary. R62 finite-observation premise and guard/source realization remain independently OPEN. Full safety, R23, A/B and production remain OPEN.

## Paths and frozen hashes

Sole source writes are these five files under `/tmp/yulang-paper-view-exposure-20261026/proof/notes/theory/lean/YulangClosure/`:

```text
d3a10c0891b0518fef7ed6e02c899b996d3ac6de618e07bddde11c89ef616bfe  PaperExecutionSyntax.lean
cb0941ef8842551da53fbf2b14cca181c10849178288de29cef1145f1d575cc7  PaperExecutionTypingSubstitution.lean
5fcb0334dfa77c3385f5f460669e36578a01642a54d17e357c072fd012fc73fe  PaperExecutionGraphWeakening.lean
d2dde517343a18b03a8fb0fe113b1d0fceeef2751f53792ef39886d8ed5e9c94  PaperTermSubstitution.lean
e7c6c959d2bcc780ca7198aae09a0368f4d98625001bdfe5b8f8c259c9cb3f85  PaperViewExecution.lean
```

All 30 contract input pins matched independently before construction and again at freeze. Every unchanged copied Lean dependency/project/root file matches its input pin. Static recursive internal import closure has 22 modules (21 pinned dependencies plus PaperViewExecution), recorded with complete hashes in `proof-checks.txt`; exact five source modifications confirmed. After stripping nested block/line comments, whole internal cone has no sorry/admit/project axiom/unsafe/native_decide/implemented_by/extern/debug.skipKernelTC token matches. An initial static scan's unbounded `extern` regex matched the identifier `external_request`; the corrected word-boundary scan passes. Static scanning is supplementary, not an indirect axiom audit.

Additional generated/scratch writes in that copy: `run_call.py`, `process-manifest.json`, `proof-checks.txt`, all `call-01..08.stdout/.stderr`, `notes/theory/lean/.lake/ExposureProbe.lean`, `.lake/ExposureAudit.lean`, `.lake/build` symlink to this copy's `lake-build`, and `lake-build` outputs. No repository Lean, root import, Rust, tests, expected outputs, rules, manifests, shared status/index or Git mutation occurred. Shared sole handoff is this file.

```text
e308aa82ce1909d5aa47c9f67ea22d621efd2c0819d898dd3510a899494709a2  run_call.py
ae41a24352fa158c49cee916c9d6443f8513b6f9bfcb21850add2128eedc0dde  process-manifest.json
3f38ba46fa6451c37e85a1c98d9f1a42c0195e82a5cfeb0ee081a624f91c49f2  proof-checks.txt
245ac541844db412bba2f438a99be47925954bd330aacc2fc46efb8fd2010052  notes/theory/lean/.lake/ExposureProbe.lean
0a0a3d3784fa3ed57ed5240b58d47eb472ce8fc61ebfe27a75106dbe51d599f9  notes/theory/lean/.lake/ExposureAudit.lean
```

## Actual execution and failures

Read-only `elan which lake` resolved installed native `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake` before invoking it. Project pins Lean 4.35.0; no external packages. Actual Lake `5.0.0-src+eb6cafb (Lean version 4.35.0)`; actual Lean `4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release`. Consulted pinned `src/lean/Lean/Environment.lean`, `PrivateName.lean`, `Util/CollectAxioms.lean`, and PrettyPrinter options.

All literal calls used the absolute native Lake above, cwd this copy's `notes/theory/lean`, `LEAN_NUM_THREADS=1`, project `-j1 -M1024`; manual Lean calls also pass them explicitly. Runner bounds each process group to 120s. Exact argv/pid/exit/timing/bytes/hashes are in `process-manifest.json`; all 16 captures independently matched manifest lengths/hashes.

| Call | Arguments after native Lake | Exit | Seconds |
| --- | --- | --- | --- |
| 1 | `--version` | 0 | 0.406372705 |
| 2 | `env lean --version` | 0 | 0.068064794 |
| 3 | `build +YulangClosure.PaperHeapExecution` | 0 | 42.072970594 |
| 4 | `build +YulangClosure.PaperViewExecution` | 1 | 0.639424462 |
| 5 | `build +YulangClosure.PaperViewExecution` | 0 | 0.738612574 |
| 6 | `env lean -j1 -M1024 .lake/ExposureProbe.lean` | 1 | 2.157445797 |
| 7 | `env lean -j1 -M1024 .lake/ExposureProbe.lean` | 1 | 19.672017955 |
| 8 | `env lean -j1 -M1024 .lake/ExposureAudit.lean` | 1 | 6.685957675 |

Call 3 rebuilt the 22 build jobs through PaperHeapExecution against the extended real judgment; call 5 rebuilt the new target, completing 23 build jobs. Existing linter/deprecation warning output is retained in full; no warning suppression or unrelated cleanup was introduced.

Material failures: call 4 failed only `rfl` in `controlStep_force_view_delay` and `expose_not_dispatched` with symbolic stack; repair `cases stack <;> rfl` passed call 5. Call 6 probe failed because `matches` is a reserved token. Call 7 emitted 113/114 requested origin/name receipts but exited 1 because private normalization collided for public `mapPaperValue_record_eq` with another imported private declaration; probe also initially omitted five inline `@[simp] theorem` declarations, discovered and included in the final 119 inventory. Final call 8 failed parsing every raw mangled private `.0` name: `unexpected identifier after decimal point` / invalid field notation. Final failed audit source, second probe source, and all failure outputs remain unchanged at freeze; the first probe source was repaired in place from `matches` to `found` before call 7, with its original parser diagnostic retained in call-06.stdout. Do not treat any nonzero run as complete acceptance.

Bundled checker used via its `audit_source` generator and `validate_audit` validator; no extra versions/build subprocesses were hidden. Exact 110 public marker/type/axiom blocks from call 8 validate under the helper. Distribution: 5 `[]`, 8 `[propext]`, 97 `[propext, Quot.sound]`; no Classical.choice, sorryAx or project axiom in these blocks. The 13 new module theorem axiom distribution is `{'propext, Quot.sound': 13}`; exact per-name lists appear below. Nine private theorem types/axioms are **NOT AUDITED**. Their exact kinds/origins/names were enumerated by successful individual commands inside nonzero call 7. All public origins/kinds and names were checked in call 8. Full 119 source declaration inventory: Syntax 4, TypingSubstitution 35, GraphWeakening 16, TermSubstitution 51, ViewExecution 13. Generated recursor/equation theorems are not source declarations; this inventory explicitly includes all source `theorem` declarations including inline attributes/private ones.

Primary's exact next check: independently build the frozen five sources and audit all 119 names. Numeric mangled private names must be introduced with actual runtime `Lean.Name`/`Lean.mkIdent`, not pasted as ASCII identifiers. An **UNEXECUTED suggestion** is to resolve each inventory `(sourceModule,userName)` by filtering `env.constants.toList` with both `Lean.privateToUserName actual == userName` and exact `env.getModuleIdxFor?` origin, assert one `.thmInfo`, then use:

```lean
-- UNEXECUTED sketch; primary must check actual command quotation/API.
Lean.Elab.Command.elabCommand (← `(command| #check @$(Lean.mkIdent actual)))
Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent actual)))
let axioms ← Lean.collectAxioms actual
for ax in axioms do
  unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
    throwError "unapproved axiom: {ax}"
```

Alternatively extend the bundled helper's scratch audit generator locally with this runtime name resolution; do not change the shared helper or dependencies. The public/private normalization collision is avoided by origin filtering. Complete failed audit source/capture stay frozen; primary owns its separate scratch audit lease. Fresh independent review is still required after primary verification.

## Cessation

Exactly 8 checker calls, 72.44086655599676 cumulative checker seconds, no timeout or signal. All checker process groups absent at freeze (checked by recorded group IDs). No further checker call is allowed in this packet. Full active duration/session telemetry is unavailable; approximate elapsed work under the 1800s allowance, without any budget renewal. Stop reason: literal checker-call bound reached with a coherent built candidate and nine private audits still open. STOPPED; source/scratch/capture writes stopped after this handoff; no descendants or retained writer leases.

## Complete new-module printed types and axioms (from nonzero call 8)

These are successful public declaration outputs inside an overall failed audit, not a complete acceptance receipt.

```text
YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperViewExecution.force_view_delay_inversion
@YulangClosure.PaperTypes.PaperViewExecution.force_view_delay_inversion : ∀
  {d : YulangClosure.PaperTypes.DeclarationTable} {g : YulangClosure.PaperTypes.GraphEnvironment}
  {e : YulangClosure.PaperTypes.TypeEnvironment} {metadata : YulangClosure.PaperTypes.ViewMetadata}
  {body : YulangClosure.PaperTypes.Computation} {result : YulangClosure.PaperTypes.Ty},
  YulangClosure.PaperTypes.PaperComputationTyped d g e
      (YulangClosure.PaperTypes.Computation.force
        (YulangClosure.PaperTypes.Value.view metadata (YulangClosure.PaperTypes.Value.delay body)))
      result →
    YulangClosure.PaperTypes.PaperComputationTyped d g e body result
'YulangClosure.PaperTypes.PaperViewExecution.force_view_delay_inversion' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperViewExecution.force_view_delay_inversion

YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperViewExecution.forceViewStep_preservation
@YulangClosure.PaperTypes.PaperViewExecution.forceViewStep_preservation : ∀
  {d : YulangClosure.PaperTypes.DeclarationTable} {g : YulangClosure.PaperTypes.GraphEnvironment}
  {e : YulangClosure.PaperTypes.TypeEnvironment} {head next : YulangClosure.PaperTypes.Computation}
  {result : YulangClosure.PaperTypes.Ty},
  YulangClosure.PaperTypes.PaperComputationTyped d g e head result →
    YulangClosure.PaperTypes.PaperViewExecution.forceViewStep head = Option.some next →
      YulangClosure.PaperTypes.PaperComputationTyped d g e next result
'YulangClosure.PaperTypes.PaperViewExecution.forceViewStep_preservation' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperViewExecution.forceViewStep_preservation

YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperViewExecution.controlStep_extends
@YulangClosure.PaperTypes.PaperViewExecution.controlStep_extends : ∀ {d : YulangClosure.PaperTypes.DeclarationTable}
  {binder : YulangClosure.PaperTypes.TermName} {s next : YulangClosure.PaperTypes.PaperCoreControl.State},
  YulangClosure.PaperTypes.PaperExtendedExecution.controlStep d binder s = Option.some next →
    YulangClosure.PaperTypes.PaperViewExecution.controlStep d binder s = Option.some next
'YulangClosure.PaperTypes.PaperViewExecution.controlStep_extends' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperViewExecution.controlStep_extends

YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperViewExecution.controlStep_evidence
@YulangClosure.PaperTypes.PaperViewExecution.controlStep_evidence : ∀ {d : YulangClosure.PaperTypes.DeclarationTable}
  {binder : YulangClosure.PaperTypes.TermName} {s next : YulangClosure.PaperTypes.PaperCoreControl.State},
  YulangClosure.PaperTypes.PaperViewExecution.controlStep d binder s = Option.some next →
    YulangClosure.PaperTypes.PaperViewExecution.ControlStepEvidence d binder s next
'YulangClosure.PaperTypes.PaperViewExecution.controlStep_evidence' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperViewExecution.controlStep_evidence

YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperViewExecution.evidence_preservation
@YulangClosure.PaperTypes.PaperViewExecution.evidence_preservation : ∀ {d : YulangClosure.PaperTypes.DeclarationTable}
  {g : YulangClosure.PaperTypes.GraphEnvironment} {e : YulangClosure.PaperTypes.TypeEnvironment}
  {s next : YulangClosure.PaperTypes.PaperCoreControl.State} {result : YulangClosure.PaperTypes.Ty}
  {binder : YulangClosure.PaperTypes.TermName},
  YulangClosure.PaperTypes.PaperTemplateExecution.BodiesTyped d →
    YulangClosure.PaperTypes.PaperCoreControl.StateTyped d g e s result →
      YulangClosure.PaperTypes.PaperViewExecution.ControlStepEvidence d binder s next →
        YulangClosure.PaperTypes.PaperCoreControl.StateTyped d g e next result
'YulangClosure.PaperTypes.PaperViewExecution.evidence_preservation' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperViewExecution.evidence_preservation

YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperViewExecution.preservation
@YulangClosure.PaperTypes.PaperViewExecution.preservation : ∀ {d : YulangClosure.PaperTypes.DeclarationTable}
  {g : YulangClosure.PaperTypes.GraphEnvironment} {e : YulangClosure.PaperTypes.TypeEnvironment}
  {s next : YulangClosure.PaperTypes.PaperCoreControl.State} {result : YulangClosure.PaperTypes.Ty}
  {binder : YulangClosure.PaperTypes.TermName},
  YulangClosure.PaperTypes.PaperTemplateExecution.BodiesTyped d →
    YulangClosure.PaperTypes.PaperCoreControl.StateTyped d g e s result →
      YulangClosure.PaperTypes.PaperViewExecution.controlStep d binder s = Option.some next →
        YulangClosure.PaperTypes.PaperCoreControl.StateTyped d g e next result
'YulangClosure.PaperTypes.PaperViewExecution.preservation' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperViewExecution.preservation

YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperViewExecution.plug_step
@YulangClosure.PaperTypes.PaperViewExecution.plug_step : ∀ {d : YulangClosure.PaperTypes.DeclarationTable}
  {binder : YulangClosure.PaperTypes.TermName} {head next : YulangClosure.PaperTypes.Computation},
  YulangClosure.PaperTypes.PaperViewExecution.ComputationStep d binder head next →
    ∀ (stack : List YulangClosure.PaperTypes.Computation),
      YulangClosure.PaperTypes.PaperViewExecution.ComputationStep d binder
        (YulangClosure.PaperTypes.PaperCoreControl.plug stack head)
        (YulangClosure.PaperTypes.PaperCoreControl.plug stack next)
'YulangClosure.PaperTypes.PaperViewExecution.plug_step' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperViewExecution.plug_step

YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperViewExecution.evidence_erasure
@YulangClosure.PaperTypes.PaperViewExecution.evidence_erasure : ∀ {d : YulangClosure.PaperTypes.DeclarationTable}
  {binder : YulangClosure.PaperTypes.TermName} {s next : YulangClosure.PaperTypes.PaperCoreControl.State},
  YulangClosure.PaperTypes.PaperViewExecution.ControlStepEvidence d binder s next →
    YulangClosure.PaperTypes.PaperCoreControl.erase s = YulangClosure.PaperTypes.PaperCoreControl.erase next ∨
      YulangClosure.PaperTypes.PaperViewExecution.ComputationStep d binder
        (YulangClosure.PaperTypes.PaperCoreControl.erase s) (YulangClosure.PaperTypes.PaperCoreControl.erase next)
'YulangClosure.PaperTypes.PaperViewExecution.evidence_erasure' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperViewExecution.evidence_erasure

YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperViewExecution.erasure
@YulangClosure.PaperTypes.PaperViewExecution.erasure : ∀ {d : YulangClosure.PaperTypes.DeclarationTable}
  {binder : YulangClosure.PaperTypes.TermName} {s next : YulangClosure.PaperTypes.PaperCoreControl.State},
  YulangClosure.PaperTypes.PaperViewExecution.controlStep d binder s = Option.some next →
    YulangClosure.PaperTypes.PaperCoreControl.erase s = YulangClosure.PaperTypes.PaperCoreControl.erase next ∨
      YulangClosure.PaperTypes.PaperViewExecution.ComputationStep d binder
        (YulangClosure.PaperTypes.PaperCoreControl.erase s) (YulangClosure.PaperTypes.PaperCoreControl.erase next)
'YulangClosure.PaperTypes.PaperViewExecution.erasure' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperViewExecution.erasure

YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperViewExecution.controlStep_force_view_delay
YulangClosure.PaperTypes.PaperViewExecution.controlStep_force_view_delay : ∀
  (d : YulangClosure.PaperTypes.DeclarationTable) (binder : YulangClosure.PaperTypes.TermName)
  (metadata : YulangClosure.PaperTypes.ViewMetadata) (body : YulangClosure.PaperTypes.Computation)
  (stack : List YulangClosure.PaperTypes.Computation),
  YulangClosure.PaperTypes.PaperViewExecution.controlStep d binder
      {
        head :=
          YulangClosure.PaperTypes.Computation.force
            (YulangClosure.PaperTypes.Value.view metadata (YulangClosure.PaperTypes.Value.delay body)),
        stack := stack } =
    Option.some { head := YulangClosure.PaperTypes.Computation.expose metadata body, stack := stack }
'YulangClosure.PaperTypes.PaperViewExecution.controlStep_force_view_delay' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperViewExecution.controlStep_force_view_delay

YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperViewExecution.force_view_delay_control
@YulangClosure.PaperTypes.PaperViewExecution.force_view_delay_control : ∀
  {d : YulangClosure.PaperTypes.DeclarationTable} {g : YulangClosure.PaperTypes.GraphEnvironment}
  {e : YulangClosure.PaperTypes.TypeEnvironment} {metadata : YulangClosure.PaperTypes.ViewMetadata}
  {body : YulangClosure.PaperTypes.Computation} {stack : List YulangClosure.PaperTypes.Computation}
  {result : YulangClosure.PaperTypes.Ty} {binder : YulangClosure.PaperTypes.TermName},
  YulangClosure.PaperTypes.PaperCoreControl.StateTyped d g e
      {
        head :=
          YulangClosure.PaperTypes.Computation.force
            (YulangClosure.PaperTypes.Value.view metadata (YulangClosure.PaperTypes.Value.delay body)),
        stack := stack }
      result →
    YulangClosure.PaperTypes.PaperViewExecution.controlStep d binder
          {
            head :=
              YulangClosure.PaperTypes.Computation.force
                (YulangClosure.PaperTypes.Value.view metadata (YulangClosure.PaperTypes.Value.delay body)),
            stack := stack } =
        Option.some { head := YulangClosure.PaperTypes.Computation.expose metadata body, stack := stack } ∧
      YulangClosure.PaperTypes.PaperCoreControl.StateTyped d g e
          { head := YulangClosure.PaperTypes.Computation.expose metadata body, stack := stack } result ∧
        YulangClosure.PaperTypes.PaperComputationTyped d g e
            (YulangClosure.PaperTypes.PaperCoreControl.erase
              { head := YulangClosure.PaperTypes.Computation.expose metadata body, stack := stack })
            result ∧
          YulangClosure.PaperTypes.PaperViewExecution.ControlStepEvidence d binder
              {
                head :=
                  YulangClosure.PaperTypes.Computation.force
                    (YulangClosure.PaperTypes.Value.view metadata (YulangClosure.PaperTypes.Value.delay body)),
                stack := stack }
              { head := YulangClosure.PaperTypes.Computation.expose metadata body, stack := stack } ∧
            YulangClosure.PaperTypes.PaperViewExecution.ComputationStep d binder
              (YulangClosure.PaperTypes.PaperCoreControl.erase
                {
                  head :=
                    YulangClosure.PaperTypes.Computation.force
                      (YulangClosure.PaperTypes.Value.view metadata (YulangClosure.PaperTypes.Value.delay body)),
                  stack := stack })
              (YulangClosure.PaperTypes.PaperCoreControl.erase
                { head := YulangClosure.PaperTypes.Computation.expose metadata body, stack := stack })
'YulangClosure.PaperTypes.PaperViewExecution.force_view_delay_control' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperViewExecution.force_view_delay_control

YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperViewExecution.original_obstruction_entry
YulangClosure.PaperTypes.PaperViewExecution.original_obstruction_entry : ∀
  (d : YulangClosure.PaperTypes.DeclarationTable) (binder : YulangClosure.PaperTypes.TermName)
  (metadata : YulangClosure.PaperTypes.ViewMetadata),
  YulangClosure.PaperTypes.PaperViewExecution.controlStep d binder
        {
          head :=
            YulangClosure.PaperTypes.Computation.force
              (YulangClosure.PaperTypes.Value.view metadata
                (YulangClosure.PaperTypes.Value.delay
                  (YulangClosure.PaperTypes.Computation.ret
                    (YulangClosure.PaperTypes.Value.literal YulangClosure.PaperTypes.Literal.unit)))),
          stack := [] } =
      Option.some
        {
          head :=
            YulangClosure.PaperTypes.Computation.expose metadata
              (YulangClosure.PaperTypes.Computation.ret
                (YulangClosure.PaperTypes.Value.literal YulangClosure.PaperTypes.Literal.unit)),
          stack := [] } ∧
    YulangClosure.PaperTypes.PaperCoreControl.StateTyped d [] []
        {
          head :=
            YulangClosure.PaperTypes.Computation.expose metadata
              (YulangClosure.PaperTypes.Computation.ret
                (YulangClosure.PaperTypes.Value.literal YulangClosure.PaperTypes.Literal.unit)),
          stack := [] }
        (YulangClosure.PaperTypes.Ty.base YulangClosure.PaperTypes.Base.unit) ∧
      YulangClosure.PaperTypes.PaperViewExecution.ComputationStep d binder
        (YulangClosure.PaperTypes.Computation.force
          (YulangClosure.PaperTypes.Value.view metadata
            (YulangClosure.PaperTypes.Value.delay
              (YulangClosure.PaperTypes.Computation.ret
                (YulangClosure.PaperTypes.Value.literal YulangClosure.PaperTypes.Literal.unit)))))
        (YulangClosure.PaperTypes.Computation.expose metadata
          (YulangClosure.PaperTypes.Computation.ret
            (YulangClosure.PaperTypes.Value.literal YulangClosure.PaperTypes.Literal.unit)))
'YulangClosure.PaperTypes.PaperViewExecution.original_obstruction_entry' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperViewExecution.original_obstruction_entry

YULANG_AUDIT_BEGIN YulangClosure.PaperTypes.PaperViewExecution.expose_not_dispatched
YulangClosure.PaperTypes.PaperViewExecution.expose_not_dispatched : ∀ (d : YulangClosure.PaperTypes.DeclarationTable)
  (binder : YulangClosure.PaperTypes.TermName) (metadata : YulangClosure.PaperTypes.ViewMetadata)
  (body : YulangClosure.PaperTypes.Computation) (stack : List YulangClosure.PaperTypes.Computation),
  YulangClosure.PaperTypes.PaperViewExecution.controlStep d binder
      { head := YulangClosure.PaperTypes.Computation.expose metadata body, stack := stack } =
    Option.none
'YulangClosure.PaperTypes.PaperViewExecution.expose_not_dispatched' depends on axioms: [propext, Quot.sound]
YULANG_AUDIT_END YulangClosure.PaperTypes.PaperViewExecution.expose_not_dispatched
```

## Complete source theorem inventory and dependency/axiom evidence

The following is the frozen `proof-checks.txt` content. Its complete 110 public types are retained separately in `call-08.stdout`; missing nine private type/axiom blocks remain explicitly open.

```text
SOURCE DECLARATION INVENTORY
PaperExecutionSyntax _private.YulangClosure.PaperExecutionSyntax.0.YulangClosure.PaperTypes.sizeOfRecordValue_le user=YulangClosure.PaperTypes.sizeOfRecordValue_le private=True
PaperExecutionSyntax _private.YulangClosure.PaperExecutionSyntax.0.YulangClosure.PaperTypes.sizeOfBindingValue_le user=YulangClosure.PaperTypes.sizeOfBindingValue_le private=True
PaperExecutionSyntax _private.YulangClosure.PaperExecutionSyntax.0.YulangClosure.PaperTypes.sizeOfPatternField_le user=YulangClosure.PaperTypes.sizeOfPatternField_le private=True
PaperExecutionSyntax _private.YulangClosure.PaperExecutionSyntax.0.YulangClosure.PaperTypes.sizeOfPatternDefault_le user=YulangClosure.PaperTypes.sizeOfPatternDefault_le private=True
PaperExecutionTypingSubstitution YulangClosure.PaperTypes.typingArgsSyntax_subst user=YulangClosure.PaperTypes.typingArgsSyntax_subst private=False
PaperExecutionTypingSubstitution YulangClosure.PaperTypes.mapTypeEnvironment_extendTupleEnvironment user=YulangClosure.PaperTypes.mapTypeEnvironment_extendTupleEnvironment private=False
PaperExecutionTypingSubstitution YulangClosure.PaperTypes.instantiateType_subst user=YulangClosure.PaperTypes.instantiateType_subst private=False
PaperExecutionTypingSubstitution YulangClosure.PaperTypes.instantiateFormalTypes_subst user=YulangClosure.PaperTypes.instantiateFormalTypes_subst private=False
PaperExecutionTypingSubstitution YulangClosure.PaperTypes.literalType_subst user=YulangClosure.PaperTypes.literalType_subst private=False
PaperExecutionTypingSubstitution YulangClosure.PaperTypes.lookupTypeEnvironment_subst user=YulangClosure.PaperTypes.lookupTypeEnvironment_subst private=False
PaperExecutionTypingSubstitution YulangClosure.PaperTypes.lookupGraphEnvironment_subst user=YulangClosure.PaperTypes.lookupGraphEnvironment_subst private=False
PaperExecutionTypingSubstitution YulangClosure.PaperTypes.RecordShape.subst user=YulangClosure.PaperTypes.RecordShape.subst private=False
PaperExecutionTypingSubstitution YulangClosure.PaperTypes.RecordField.subst user=YulangClosure.PaperTypes.RecordField.subst private=False
PaperExecutionTypingSubstitution YulangClosure.PaperTypes.OperationDeclarationResolved.typeTransport user=YulangClosure.PaperTypes.OperationDeclarationResolved.typeTransport private=False
PaperExecutionTypingSubstitution YulangClosure.PaperTypes.templateIdentity_mapTemplateBody user=YulangClosure.PaperTypes.templateIdentity_mapTemplateBody private=False
PaperExecutionTypingSubstitution YulangClosure.PaperTypes.TemplateDeclarationResolved.typeTransport user=YulangClosure.PaperTypes.TemplateDeclarationResolved.typeTransport private=False
PaperExecutionTypingSubstitution YulangClosure.PaperTypes.mapRecordFields_labels user=YulangClosure.PaperTypes.mapRecordFields_labels private=False
PaperExecutionTypingSubstitution YulangClosure.PaperTypes.mapPaperValue_record_eq user=YulangClosure.PaperTypes.mapPaperValue_record_eq private=False
PaperExecutionTypingSubstitution YulangClosure.PaperTypes.PaperValueTyped.subst_explicit user=YulangClosure.PaperTypes.PaperValueTyped.subst_explicit private=False
PaperExecutionTypingSubstitution YulangClosure.PaperTypes.ValuesTyped.typeTransport user=YulangClosure.PaperTypes.ValuesTyped.typeTransport private=False
PaperExecutionTypingSubstitution YulangClosure.PaperTypes.ValuesAllTyped.typeTransport user=YulangClosure.PaperTypes.ValuesAllTyped.typeTransport private=False
PaperExecutionTypingSubstitution YulangClosure.PaperTypes.RecordPayloadsTyped.typeTransport user=YulangClosure.PaperTypes.RecordPayloadsTyped.typeTransport private=False
PaperExecutionTypingSubstitution YulangClosure.PaperTypes.PaperComputationTyped.typeTransport user=YulangClosure.PaperTypes.PaperComputationTyped.typeTransport private=False
PaperExecutionTypingSubstitution YulangClosure.PaperTypes.PaperContinuationTyped.typeTransport user=YulangClosure.PaperTypes.PaperContinuationTyped.typeTransport private=False
PaperExecutionTypingSubstitution YulangClosure.PaperTypes.PaperComputationTyped.templateInversion user=YulangClosure.PaperTypes.PaperComputationTyped.templateInversion private=False
PaperExecutionTypingSubstitution YulangClosure.PaperTypes.PaperComputationTyped.splitInversion user=YulangClosure.PaperTypes.PaperComputationTyped.splitInversion private=False
PaperExecutionTypingSubstitution YulangClosure.PaperTypes.PaperComputationTyped.splitTuple user=YulangClosure.PaperTypes.PaperComputationTyped.splitTuple private=False
PaperExecutionTypingSubstitution YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInversion user=YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInversion private=False
PaperExecutionTypingSubstitution YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInjectLeft user=YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInjectLeft private=False
PaperExecutionTypingSubstitution YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInjectRight user=YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInjectRight private=False
PaperExecutionTypingSubstitution YulangClosure.PaperTypes.PaperValueTyped.wrapInversion user=YulangClosure.PaperTypes.PaperValueTyped.wrapInversion private=False
PaperExecutionTypingSubstitution YulangClosure.PaperTypes.PaperComputationTyped.callWrapped user=YulangClosure.PaperTypes.PaperComputationTyped.callWrapped private=False
PaperExecutionTypingSubstitution YulangClosure.PaperTypes.typeAbstractionSharedVariable user=YulangClosure.PaperTypes.typeAbstractionSharedVariable private=False
PaperExecutionTypingSubstitution YulangClosure.PaperTypes.typeAbstractionSharedContexts user=YulangClosure.PaperTypes.typeAbstractionSharedContexts private=False
PaperExecutionTypingSubstitution YulangClosure.PaperTypes.resumeVariableBoolInt user=YulangClosure.PaperTypes.resumeVariableBoolInt private=False
PaperExecutionTypingSubstitution YulangClosure.PaperTypes.resumeVariableWrongResponseImpossible user=YulangClosure.PaperTypes.resumeVariableWrongResponseImpossible private=False
PaperExecutionTypingSubstitution YulangClosure.PaperTypes.typeApplicationBoolVariable user=YulangClosure.PaperTypes.typeApplicationBoolVariable private=False
PaperExecutionTypingSubstitution YulangClosure.PaperTypes.rollVariable user=YulangClosure.PaperTypes.rollVariable private=False
PaperExecutionTypingSubstitution YulangClosure.PaperTypes.unrollVariable user=YulangClosure.PaperTypes.unrollVariable private=False
PaperExecutionGraphWeakening YulangClosure.PaperTypes.GraphLookupPreserved.map user=YulangClosure.PaperTypes.GraphLookupPreserved.map private=False
PaperExecutionGraphWeakening YulangClosure.PaperTypes.PaperValueTyped.graphWeaken user=YulangClosure.PaperTypes.PaperValueTyped.graphWeaken private=False
PaperExecutionGraphWeakening YulangClosure.PaperTypes.ValuesTyped.graphWeaken user=YulangClosure.PaperTypes.ValuesTyped.graphWeaken private=False
PaperExecutionGraphWeakening YulangClosure.PaperTypes.ValuesAllTyped.graphWeaken user=YulangClosure.PaperTypes.ValuesAllTyped.graphWeaken private=False
PaperExecutionGraphWeakening YulangClosure.PaperTypes.RecordPayloadsTyped.graphWeaken user=YulangClosure.PaperTypes.RecordPayloadsTyped.graphWeaken private=False
PaperExecutionGraphWeakening YulangClosure.PaperTypes.PaperComputationTyped.graphWeaken user=YulangClosure.PaperTypes.PaperComputationTyped.graphWeaken private=False
PaperExecutionGraphWeakening YulangClosure.PaperTypes.PaperContinuationTyped.graphWeaken user=YulangClosure.PaperTypes.PaperContinuationTyped.graphWeaken private=False
PaperExecutionGraphWeakening YulangClosure.PaperTypes.lookupGraphEnvironment_identity_mem user=YulangClosure.PaperTypes.lookupGraphEnvironment_identity_mem private=False
PaperExecutionGraphWeakening YulangClosure.PaperTypes.GraphLookupPreserved.freshCons user=YulangClosure.PaperTypes.GraphLookupPreserved.freshCons private=False
PaperExecutionGraphWeakening YulangClosure.PaperTypes.graphLookupPreserved_shadowing_falsifier user=YulangClosure.PaperTypes.graphLookupPreserved_shadowing_falsifier private=False
PaperExecutionGraphWeakening YulangClosure.PaperTypes.PaperValueTyped.graphFreshCons user=YulangClosure.PaperTypes.PaperValueTyped.graphFreshCons private=False
PaperExecutionGraphWeakening YulangClosure.PaperTypes.ValuesTyped.graphFreshCons user=YulangClosure.PaperTypes.ValuesTyped.graphFreshCons private=False
PaperExecutionGraphWeakening YulangClosure.PaperTypes.ValuesAllTyped.graphFreshCons user=YulangClosure.PaperTypes.ValuesAllTyped.graphFreshCons private=False
PaperExecutionGraphWeakening YulangClosure.PaperTypes.RecordPayloadsTyped.graphFreshCons user=YulangClosure.PaperTypes.RecordPayloadsTyped.graphFreshCons private=False
PaperExecutionGraphWeakening YulangClosure.PaperTypes.PaperComputationTyped.graphFreshCons user=YulangClosure.PaperTypes.PaperComputationTyped.graphFreshCons private=False
PaperExecutionGraphWeakening YulangClosure.PaperTypes.PaperContinuationTyped.graphFreshCons user=YulangClosure.PaperTypes.PaperContinuationTyped.graphFreshCons private=False
PaperTermSubstitution _private.YulangClosure.PaperTermSubstitution.0.YulangClosure.PaperTypes.recordValueSize user=YulangClosure.PaperTypes.recordValueSize private=True
PaperTermSubstitution YulangClosure.PaperTypes.TermRenamingTyped.lift user=YulangClosure.PaperTypes.TermRenamingTyped.lift private=False
PaperTermSubstitution YulangClosure.PaperTypes.TermRenamingTyped.liftN user=YulangClosure.PaperTypes.TermRenamingTyped.liftN private=False
PaperTermSubstitution YulangClosure.PaperTypes.TermRenamingTyped.typeShift user=YulangClosure.PaperTypes.TermRenamingTyped.typeShift private=False
PaperTermSubstitution _private.YulangClosure.PaperTermSubstitution.0.YulangClosure.PaperTypes.renameRecordLabels user=YulangClosure.PaperTypes.renameRecordLabels private=True
PaperTermSubstitution _private.YulangClosure.PaperTermSubstitution.0.YulangClosure.PaperTypes.renameTermValue_record_eq user=YulangClosure.PaperTypes.renameTermValue_record_eq private=True
PaperTermSubstitution YulangClosure.PaperTypes.PaperValueTyped.termRename user=YulangClosure.PaperTypes.PaperValueTyped.termRename private=False
PaperTermSubstitution YulangClosure.PaperTypes.TermSubstitutionTyped.lift user=YulangClosure.PaperTypes.TermSubstitutionTyped.lift private=False
PaperTermSubstitution YulangClosure.PaperTypes.TermSubstitutionTyped.liftN user=YulangClosure.PaperTypes.TermSubstitutionTyped.liftN private=False
PaperTermSubstitution YulangClosure.PaperTypes.TermSubstitutionTyped.typeShift user=YulangClosure.PaperTypes.TermSubstitutionTyped.typeShift private=False
PaperTermSubstitution _private.YulangClosure.PaperTermSubstitution.0.YulangClosure.PaperTypes.replaceRecordLabels user=YulangClosure.PaperTypes.replaceRecordLabels private=True
PaperTermSubstitution _private.YulangClosure.PaperTermSubstitution.0.YulangClosure.PaperTypes.replaceTermValue_record_eq user=YulangClosure.PaperTypes.replaceTermValue_record_eq private=True
PaperTermSubstitution YulangClosure.PaperTypes.PaperValueTyped.termReplace user=YulangClosure.PaperTypes.PaperValueTyped.termReplace private=False
PaperTermSubstitution YulangClosure.PaperTypes.PaperValueTyped.termSupported user=YulangClosure.PaperTypes.PaperValueTyped.termSupported private=False
PaperTermSubstitution YulangClosure.PaperTypes.ValuesTyped.termReplace user=YulangClosure.PaperTypes.ValuesTyped.termReplace private=False
PaperTermSubstitution YulangClosure.PaperTypes.ValuesAllTyped.termReplace user=YulangClosure.PaperTypes.ValuesAllTyped.termReplace private=False
PaperTermSubstitution YulangClosure.PaperTypes.RecordPayloadsTyped.termReplace user=YulangClosure.PaperTypes.RecordPayloadsTyped.termReplace private=False
PaperTermSubstitution YulangClosure.PaperTypes.PaperComputationTyped.termReplace user=YulangClosure.PaperTypes.PaperComputationTyped.termReplace private=False
PaperTermSubstitution YulangClosure.PaperTypes.PaperContinuationTyped.termReplace user=YulangClosure.PaperTypes.PaperContinuationTyped.termReplace private=False
PaperTermSubstitution YulangClosure.PaperTypes.ValuesTyped.termSupported user=YulangClosure.PaperTypes.ValuesTyped.termSupported private=False
PaperTermSubstitution YulangClosure.PaperTypes.ValuesAllTyped.termSupported user=YulangClosure.PaperTypes.ValuesAllTyped.termSupported private=False
PaperTermSubstitution YulangClosure.PaperTypes.RecordPayloadsTyped.termSupported user=YulangClosure.PaperTypes.RecordPayloadsTyped.termSupported private=False
PaperTermSubstitution YulangClosure.PaperTypes.PaperComputationTyped.termSupported user=YulangClosure.PaperTypes.PaperComputationTyped.termSupported private=False
PaperTermSubstitution YulangClosure.PaperTypes.PaperContinuationTyped.termSupported user=YulangClosure.PaperTypes.PaperContinuationTyped.termSupported private=False
PaperTermSubstitution YulangClosure.PaperTypes.PaperValueTyped.termSubstitute user=YulangClosure.PaperTypes.PaperValueTyped.termSubstitute private=False
PaperTermSubstitution YulangClosure.PaperTypes.ValuesTyped.termSubstitute user=YulangClosure.PaperTypes.ValuesTyped.termSubstitute private=False
PaperTermSubstitution YulangClosure.PaperTypes.ValuesAllTyped.termSubstitute user=YulangClosure.PaperTypes.ValuesAllTyped.termSubstitute private=False
PaperTermSubstitution YulangClosure.PaperTypes.RecordPayloadsTyped.termSubstitute user=YulangClosure.PaperTypes.RecordPayloadsTyped.termSubstitute private=False
PaperTermSubstitution YulangClosure.PaperTypes.PaperComputationTyped.termSubstitute user=YulangClosure.PaperTypes.PaperComputationTyped.termSubstitute private=False
PaperTermSubstitution YulangClosure.PaperTypes.PaperContinuationTyped.termSubstitute user=YulangClosure.PaperTypes.PaperContinuationTyped.termSubstitute private=False
PaperTermSubstitution YulangClosure.PaperTypes.termSubstituteValue_success user=YulangClosure.PaperTypes.termSubstituteValue_success private=False
PaperTermSubstitution YulangClosure.PaperTypes.termSubstituteValue_failure user=YulangClosure.PaperTypes.termSubstituteValue_failure private=False
PaperTermSubstitution YulangClosure.PaperTypes.unsupported_raw_falsifier user=YulangClosure.PaperTypes.unsupported_raw_falsifier private=False
PaperTermSubstitution YulangClosure.PaperTypes.capture_avoiding_binder user=YulangClosure.PaperTypes.capture_avoiding_binder private=False
PaperTermSubstitution YulangClosure.PaperTypes.simultaneous_order_falsifier user=YulangClosure.PaperTypes.simultaneous_order_falsifier private=False
PaperTermSubstitution YulangClosure.PaperTypes.forall_replacement_shift user=YulangClosure.PaperTypes.forall_replacement_shift private=False
PaperTermSubstitution YulangClosure.PaperTypes.TermSubstitutionTyped.compose user=YulangClosure.PaperTypes.TermSubstitutionTyped.compose private=False
PaperTermSubstitution YulangClosure.PaperTypes.TermSubstitutionTyped.graphWeaken user=YulangClosure.PaperTypes.TermSubstitutionTyped.graphWeaken private=False
PaperTermSubstitution YulangClosure.PaperTypes.graphFormalReplacements_typed user=YulangClosure.PaperTypes.graphFormalReplacements_typed private=False
PaperTermSubstitution YulangClosure.PaperTypes.PaperValueTyped.substituteFreshGraphFormals user=YulangClosure.PaperTypes.PaperValueTyped.substituteFreshGraphFormals private=False
PaperTermSubstitution YulangClosure.PaperTypes.ValuesTyped.substituteFreshGraphFormals user=YulangClosure.PaperTypes.ValuesTyped.substituteFreshGraphFormals private=False
PaperTermSubstitution YulangClosure.PaperTypes.ValuesAllTyped.substituteFreshGraphFormals user=YulangClosure.PaperTypes.ValuesAllTyped.substituteFreshGraphFormals private=False
PaperTermSubstitution YulangClosure.PaperTypes.RecordPayloadsTyped.substituteFreshGraphFormals user=YulangClosure.PaperTypes.RecordPayloadsTyped.substituteFreshGraphFormals private=False
PaperTermSubstitution YulangClosure.PaperTypes.PaperComputationTyped.substituteFreshGraphFormals user=YulangClosure.PaperTypes.PaperComputationTyped.substituteFreshGraphFormals private=False
PaperTermSubstitution YulangClosure.PaperTypes.PaperContinuationTyped.substituteFreshGraphFormals user=YulangClosure.PaperTypes.PaperContinuationTyped.substituteFreshGraphFormals private=False
PaperTermSubstitution YulangClosure.PaperTypes.freshGraphReference_application user=YulangClosure.PaperTypes.freshGraphReference_application private=False
PaperTermSubstitution YulangClosure.PaperTypes.graph_formal_order_falsifier user=YulangClosure.PaperTypes.graph_formal_order_falsifier private=False
PaperTermSubstitution YulangClosure.PaperTypes.termSubstituteValue_isSome user=YulangClosure.PaperTypes.termSubstituteValue_isSome private=False
PaperTermSubstitution YulangClosure.PaperTypes.termSubstituteComputation_isSome user=YulangClosure.PaperTypes.termSubstituteComputation_isSome private=False
PaperTermSubstitution YulangClosure.PaperTypes.tuple_pattern_binder_capture user=YulangClosure.PaperTypes.tuple_pattern_binder_capture private=False
PaperTermSubstitution YulangClosure.PaperTypes.sequential_substitution_falsifier user=YulangClosure.PaperTypes.sequential_substitution_falsifier private=False
PaperViewExecution YulangClosure.PaperTypes.PaperViewExecution.force_view_delay_inversion user=YulangClosure.PaperTypes.PaperViewExecution.force_view_delay_inversion private=False
PaperViewExecution YulangClosure.PaperTypes.PaperViewExecution.forceViewStep_preservation user=YulangClosure.PaperTypes.PaperViewExecution.forceViewStep_preservation private=False
PaperViewExecution YulangClosure.PaperTypes.PaperViewExecution.controlStep_extends user=YulangClosure.PaperTypes.PaperViewExecution.controlStep_extends private=False
PaperViewExecution YulangClosure.PaperTypes.PaperViewExecution.controlStep_evidence user=YulangClosure.PaperTypes.PaperViewExecution.controlStep_evidence private=False
PaperViewExecution YulangClosure.PaperTypes.PaperViewExecution.evidence_preservation user=YulangClosure.PaperTypes.PaperViewExecution.evidence_preservation private=False
PaperViewExecution YulangClosure.PaperTypes.PaperViewExecution.preservation user=YulangClosure.PaperTypes.PaperViewExecution.preservation private=False
PaperViewExecution YulangClosure.PaperTypes.PaperViewExecution.plug_step user=YulangClosure.PaperTypes.PaperViewExecution.plug_step private=False
PaperViewExecution YulangClosure.PaperTypes.PaperViewExecution.evidence_erasure user=YulangClosure.PaperTypes.PaperViewExecution.evidence_erasure private=False
PaperViewExecution YulangClosure.PaperTypes.PaperViewExecution.erasure user=YulangClosure.PaperTypes.PaperViewExecution.erasure private=False
PaperViewExecution YulangClosure.PaperTypes.PaperViewExecution.controlStep_force_view_delay user=YulangClosure.PaperTypes.PaperViewExecution.controlStep_force_view_delay private=False
PaperViewExecution YulangClosure.PaperTypes.PaperViewExecution.force_view_delay_control user=YulangClosure.PaperTypes.PaperViewExecution.force_view_delay_control private=False
PaperViewExecution YulangClosure.PaperTypes.PaperViewExecution.original_obstruction_entry user=YulangClosure.PaperTypes.PaperViewExecution.original_obstruction_entry private=False
PaperViewExecution YulangClosure.PaperTypes.PaperViewExecution.expose_not_dispatched user=YulangClosure.PaperTypes.PaperViewExecution.expose_not_dispatched private=False

COUNTS {'PaperExecutionSyntax': 4, 'PaperExecutionTypingSubstitution': 35, 'PaperExecutionGraphWeakening': 16, 'PaperTermSubstitution': 51, 'PaperViewExecution': 13}

FREEZE PINS: all 30 repository input pins match; all unedited copy pins match.
INTERNAL IMPORT CONE 22 modules; prohibited source tokens absent after nested comment removal.
Static scan first attempt false-positive: unbounded regex extern matched external_request; corrected word-boundary scan passed.
f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258  YulangClosure.DeclSubst
58661ddec13e1fe4abb6a9b6627597fa824dedbf36f952e56dc15906141314d1  YulangClosure.PaperCombinedExecution
71594dfb24af402f7b4835dc54b5383a46106faba959b687295cc0431361530e  YulangClosure.PaperCoreControl
6357b14217e82421eed87da981cef8e94014dcaea634d746ad0b4bb39bff6144  YulangClosure.PaperCoreStep
568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a  YulangClosure.PaperExecutionBinderLaws
5fcb0334dfa77c3385f5f460669e36578a01642a54d17e357c072fd012fc73fe  YulangClosure.PaperExecutionGraphWeakening
d3a10c0891b0518fef7ed6e02c899b996d3ac6de618e07bddde11c89ef616bfe  YulangClosure.PaperExecutionSyntax
cb0941ef8842551da53fbf2b14cca181c10849178288de29cef1145f1d575cc7  YulangClosure.PaperExecutionTypingSubstitution
a29c5cc15748e8a91338f2a068e94ff7dc58c2a19adad564ba3f5a6fea337ea7  YulangClosure.PaperExtendedExecution
7cd87b8e5fd43eea0206401de6ed91e817755f3d1ad2c5aeee1caf0dd1732925  YulangClosure.PaperFreshHeapAllocation
46a9e8e76f5745cbaffc40b7bb95ff37064941a84532fa5edc07672ddad3d59f  YulangClosure.PaperHeapExecution
19b54b87b63cdc4175b1b641ca83d0c1e9454e2439c58a0936bf31fa5bc4725f  YulangClosure.PaperHeapObservation
2f0026049554cb870158115b4bab8d42f7cbee8b030ee3f84a904763c328cac0  YulangClosure.PaperPerformLetExecution
5ab59033b0cea347144c50a5323e4dd6cb59cc6bfbdc0bffd063a4808e741935  YulangClosure.PaperResumeExecution
3ead9cf7d0f57d02d5fd8b44da24f133d7859e76dff8ee1d1b17cb233920d792  YulangClosure.PaperTemplateExecution
d2dde517343a18b03a8fb0fe113b1d0fceeef2751f53792ef39886d8ed5e9c94  YulangClosure.PaperTermSubstitution
7bc13a41a0333d885b91291a7fbb1ef18302a94c79a34f21469dbae19d76f84d  YulangClosure.PaperTupleSplitExecution
60e095545530bc784487a4bfcc1c7acfc1160b3adf8c1c8dc03ab98806154556  YulangClosure.PaperTypeApplicationPreservation
0a1834040a0201c0c472f66138f6501094f7138dd3614f2bc4439a8be0cda1c8  YulangClosure.PaperTypeBetaExecution
29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13  YulangClosure.PaperTypeFormation
02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861  YulangClosure.PaperTypeSubstitution
e7c6c959d2bcc780ca7198aae09a0368f4d98625001bdfe5b8f8c259c9cb3f85  YulangClosure.PaperViewExecution

CHANGED EXACT FIVE SOURCE HASHES
5fcb0334dfa77c3385f5f460669e36578a01642a54d17e357c072fd012fc73fe  /tmp/yulang-paper-view-exposure-20261026/proof/notes/theory/lean/YulangClosure/PaperExecutionGraphWeakening.lean
d3a10c0891b0518fef7ed6e02c899b996d3ac6de618e07bddde11c89ef616bfe  /tmp/yulang-paper-view-exposure-20261026/proof/notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean
cb0941ef8842551da53fbf2b14cca181c10849178288de29cef1145f1d575cc7  /tmp/yulang-paper-view-exposure-20261026/proof/notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean
d2dde517343a18b03a8fb0fe113b1d0fceeef2751f53792ef39886d8ed5e9c94  /tmp/yulang-paper-view-exposure-20261026/proof/notes/theory/lean/YulangClosure/PaperTermSubstitution.lean
e7c6c959d2bcc780ca7198aae09a0368f4d98625001bdfe5b8f8c259c9cb3f85  /tmp/yulang-paper-view-exposure-20261026/proof/notes/theory/lean/YulangClosure/PaperViewExecution.lean

PARTIAL AUDIT ONLY: helper validate_audit accepted complete 110 public theorem blocks from nonzero final call; nine private remain unaudited.
YulangClosure.PaperTypes.typingArgsSyntax_subst AXIOMS propext
YulangClosure.PaperTypes.mapTypeEnvironment_extendTupleEnvironment AXIOMS propext
YulangClosure.PaperTypes.instantiateType_subst AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.instantiateFormalTypes_subst AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.literalType_subst AXIOMS []
YulangClosure.PaperTypes.lookupTypeEnvironment_subst AXIOMS []
YulangClosure.PaperTypes.lookupGraphEnvironment_subst AXIOMS propext
YulangClosure.PaperTypes.RecordShape.subst AXIOMS []
YulangClosure.PaperTypes.RecordField.subst AXIOMS []
YulangClosure.PaperTypes.OperationDeclarationResolved.typeTransport AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.templateIdentity_mapTemplateBody AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.TemplateDeclarationResolved.typeTransport AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.mapRecordFields_labels AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.mapPaperValue_record_eq AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperValueTyped.subst_explicit AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.ValuesTyped.typeTransport AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.ValuesAllTyped.typeTransport AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.RecordPayloadsTyped.typeTransport AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperComputationTyped.typeTransport AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperContinuationTyped.typeTransport AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperComputationTyped.templateInversion AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperComputationTyped.splitInversion AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperComputationTyped.splitTuple AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInversion AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInjectLeft AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperComputationTyped.unionCaseInjectRight AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperValueTyped.wrapInversion AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperComputationTyped.callWrapped AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.typeAbstractionSharedVariable AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.typeAbstractionSharedContexts AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.resumeVariableBoolInt AXIOMS []
YulangClosure.PaperTypes.resumeVariableWrongResponseImpossible AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.typeApplicationBoolVariable AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.rollVariable AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.unrollVariable AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.GraphLookupPreserved.map AXIOMS propext
YulangClosure.PaperTypes.PaperValueTyped.graphWeaken AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.ValuesTyped.graphWeaken AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.ValuesAllTyped.graphWeaken AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.RecordPayloadsTyped.graphWeaken AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperComputationTyped.graphWeaken AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperContinuationTyped.graphWeaken AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.lookupGraphEnvironment_identity_mem AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.GraphLookupPreserved.freshCons AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.graphLookupPreserved_shadowing_falsifier AXIOMS propext
YulangClosure.PaperTypes.PaperValueTyped.graphFreshCons AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.ValuesTyped.graphFreshCons AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.ValuesAllTyped.graphFreshCons AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.RecordPayloadsTyped.graphFreshCons AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperComputationTyped.graphFreshCons AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperContinuationTyped.graphFreshCons AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.TermRenamingTyped.lift AXIOMS propext
YulangClosure.PaperTypes.TermRenamingTyped.liftN AXIOMS propext
YulangClosure.PaperTypes.TermRenamingTyped.typeShift AXIOMS propext
YulangClosure.PaperTypes.PaperValueTyped.termRename AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.TermSubstitutionTyped.lift AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.TermSubstitutionTyped.liftN AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.TermSubstitutionTyped.typeShift AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperValueTyped.termReplace AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperValueTyped.termSupported AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.ValuesTyped.termReplace AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.ValuesAllTyped.termReplace AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.RecordPayloadsTyped.termReplace AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperComputationTyped.termReplace AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperContinuationTyped.termReplace AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.ValuesTyped.termSupported AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.ValuesAllTyped.termSupported AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.RecordPayloadsTyped.termSupported AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperComputationTyped.termSupported AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperContinuationTyped.termSupported AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperValueTyped.termSubstitute AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.ValuesTyped.termSubstitute AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.ValuesAllTyped.termSubstitute AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.RecordPayloadsTyped.termSubstitute AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperComputationTyped.termSubstitute AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperContinuationTyped.termSubstitute AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.termSubstituteValue_success AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.termSubstituteValue_failure AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.unsupported_raw_falsifier AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.capture_avoiding_binder AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.simultaneous_order_falsifier AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.forall_replacement_shift AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.TermSubstitutionTyped.compose AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.TermSubstitutionTyped.graphWeaken AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.graphFormalReplacements_typed AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperValueTyped.substituteFreshGraphFormals AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.ValuesTyped.substituteFreshGraphFormals AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.ValuesAllTyped.substituteFreshGraphFormals AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.RecordPayloadsTyped.substituteFreshGraphFormals AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperComputationTyped.substituteFreshGraphFormals AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperContinuationTyped.substituteFreshGraphFormals AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.freshGraphReference_application AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.graph_formal_order_falsifier AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.termSubstituteValue_isSome AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.termSubstituteComputation_isSome AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.tuple_pattern_binder_capture AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.sequential_substitution_falsifier AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperViewExecution.force_view_delay_inversion AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperViewExecution.forceViewStep_preservation AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperViewExecution.controlStep_extends AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperViewExecution.controlStep_evidence AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperViewExecution.evidence_preservation AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperViewExecution.preservation AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperViewExecution.plug_step AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperViewExecution.evidence_erasure AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperViewExecution.erasure AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperViewExecution.controlStep_force_view_delay AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperViewExecution.force_view_delay_control AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperViewExecution.original_obstruction_entry AXIOMS propext, Quot.sound
YulangClosure.PaperTypes.PaperViewExecution.expose_not_dispatched AXIOMS propext, Quot.sound

CAPTURE MANIFEST VALIDATED: 8 calls, 72.44086655599676 cumulative checker seconds; no timeout/signal.
245ac541844db412bba2f438a99be47925954bd330aacc2fc46efb8fd2010052  /tmp/yulang-paper-view-exposure-20261026/proof/notes/theory/lean/.lake/ExposureProbe.lean
0a0a3d3784fa3ed57ed5240b58d47eb472ce8fc61ebfe27a75106dbe51d599f9  /tmp/yulang-paper-view-exposure-20261026/proof/notes/theory/lean/.lake/ExposureAudit.lean
e308aa82ce1909d5aa47c9f67ea22d621efd2c0819d898dd3510a899494709a2  /tmp/yulang-paper-view-exposure-20261026/proof/run_call.py
ae41a24352fa158c49cee916c9d6443f8513b6f9bfcb21850add2128eedc0dde  /tmp/yulang-paper-view-exposure-20261026/proof/process-manifest.json

```
