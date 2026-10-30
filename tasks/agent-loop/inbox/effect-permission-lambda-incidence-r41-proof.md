# R41 proof handoff — revision 1, FROZEN

Sprint `EFFECT-PERMISSION-LAMBDA-INCIDENCE/20261031-R41`; contract SHA-256 `20b446aa3ad63eeccbda603e4b054ccd76e87e492c8f64d7a5cab6aacd112ed8`. Assignment `/root/r41_proof`, registered Lean leaf, handoff revision 1. Parent NEW_TASK is the current-session launch receipt. Requested registered `lean_prover`; observed model/effort UNKNOWN. Author `/root/r41_proof`; no coauthors or descendants. Rust writer communicated planned metadata and the computation-slot-3 correction; no shared-file edits. Packet baseline `41a446c9e37d1cb9a4f88f7d8832f831d76cfd40`, supplied by primary, no Git lookup/mutation.

Outcome: kernel-accepted finite constructor/capture/FreshUse mathematics. Independent review, concrete source/native correspondence, parent theorem and production approval remain separate and OPEN. This producer does not certify its own result.

## Original source and exact application

Authoritative `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1, 1.1–1.2, 4 is the original local policy: a contravariant computation annotation grants permission; actual inflow stays constraint-derived; Catch performs subtraction; additional `write` effects remain accepted and outward. Symbolic dependencies remain connected. The whole parent retains original source scope, all supported forms, shared witnesses and original A/B quantifiers from `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` §§1, 3, with the birth-level correction `notes/design/2026-10-24-birth-level-scc-intrusion.md` §§2–6. Neither the R40 research characterization nor this finite model is semantic authority.

Inspected actual `YulangClosure.SourceProblem.InferenceSoundness`, `SourceProblem.SourceScopedCoverage`, `LocalLaws` in Contracts and the opening boundary in OriginalEffectHygiene. The first two are proposition definitions; LocalLaws packages supplied laws. None is concretely instantiated by this packet. Those roots are not imported into the checked stream.

R39 `source_lambda_exact`/`Valid` derive the owner-local Lambda from exact source expression lookup, not execution-schedule indexing. R41 retains that correction through unchanged `prepare` and `constructed_entry_publication`. Its `entry_to_exact_use` invokes the latter and `exact_row_retained`, then uses the SAME permission witness `p` throughout publication and comparison with the constructed label. All R39 hypotheses remain explicit: formal-table lookup, actual annotation row, entry-port lookup, all original Valid checks, and nonempty concrete emission branch. `empty_entry_incidence` applies R39's accepted empty/variable-only branch and records no permission, while the labelled Lambda child still exists. This is no source-language restriction.

Namespace `YulangClosure.LambdaArgumentEffectIncidenceR41`. `Ports` is the positive Lambda Function's ordered four-child projection `[argument, argumentEffect, resultEffect, result]`. `constructLambda` constructs the label and child-1 incidence together, using `negativeEffect port`; there is no assumed registration-to-child law. `capture` maps the exact Function term and all four children through ONE shared `nodes` map and the entry port through ONE shared `rowIndexes` map. It models the successful exact-Function branch only: it does not prove graph reachability, membership, interning success, or availability. `freshen` maps the captured Function and child through ONE `terms` map, its entry row through ONE `rows` map, and retains the exact pair of definition-use identity and context-use stamp. No map is required injective, so shared tails/row images do not erase labels. Rich label fields stand for source-registry coordinates; they are not a claim that Rust directly stores every field in each new record.

`lambda_origin`, `capture_preserves`, `freshuse_exact` expose the Function term, exact child-1 image and row-coordinate image. `distinct_registration_images` and `shared_row_distinct_labels` prove label distinction even when mapped rows coincide. `conditional_shared_tail_falsifier` preserves the analytic `{signal | e}` / `{write | e}` case: if signal actually arrives along the write registration, the explicitly hypothetical row-only consumer authorizes the wrong signal permission; registration-aware checking rejects it. No actual arrival, source program, implemented consumer or Rust defect is asserted.

## Source/native bridge and first remaining premise

Read-only owners inspected: `candidate_source.rs` registration and LambdaRecipe construction (registration index comes from the exact formal map); `candidate_call.rs::FormalRegistrationInput`; `lib.rs::admit_lambda_fact`; `candidate_scheme.rs` Graph/Node, Function capture, and R40 FreshUse's four-child reconstruction. R40 supplies only its reviewed structural direction and exact module-use routing.

The baseline computation formal skips slot 3 when `force_entry` is false. Therefore R41 must not infer a slot-3 forcing constraint or inferred-entry record. The concurrent Rust packet instead constructs a separate passive registration/Lambda/Function/entry origin AFTER `positive_function_term`, then captures only that exact Function endpoint, validates child 1 against the entry row, and retains graph Function/child/row coordinates and their exact use image. This paragraph records the writer's communicated plan, not an independently validated final source receipt.

First remaining premise `R41-NATIVE-INCIDENCE-REALIZATION-1`, owner Luna's fresh source reviewer / Rust lane: provide frozen final Rust bytes and demonstrate that this passive constructor's registration and Lambda occurrence refer to the same source formal as the R39 permission; that captured Function/child-1/row lookups realize the single maps used above; and that the per-use record is retained with the same ordered terms/rows vectors and exact module/context-use identities. Confirm the fallible allocation/accounting path without falsely promising whole-call rollback. A graph missing the exact Function has no claimed source incidence in this model; source review must establish skip/rejection behavior. Required falsifier: a foreign registration is attached to a different exact Function child, or a same-row image substitutes for the exact Function/child mapping.

After that bridge, `R39-ENTRY-PERMISSION-ARRIVAL-1` remains with Luna's provider/receiver source lane: relate this exact permission/registration/use witness to an actual contribution and selected Catch/residual edge. No provider arrival, Catch subtraction, nested callback annotations, negative Function construction, other constructors, full source/native simulation, complete effect hygiene, soundness, principality, progress, inference termination, original A/B closure or production conclusion follows here. Other accepted forms remain in the original parent; this finite projection proves no whole-language coverage. No compiler/test/expected-output/configuration/shared-record changes were made.

## Actual checker execution and material failures

Read root AGENTS.md and AGENTS.pre-sprint.md, active goal rules, exact packet, current state/README, Lean skill/source/execution references, pin/manifests and relevant Lean README. Skill helper inspected; not run because it builds through Lake and creates audit scratch, both prohibited by this packet. No Lake was executed. `elan which lean` read-only lookup exit 0 returned `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean` with the warning that latest-release query failed and the existing pinned version was used. Read-only version command exit 0 printed:

```text
Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
```

Every elaboration/audit stream was held entirely in Python memory: exact frozen R39 source including `import Std`, followed by R41 source with ONLY its project import line removed, followed (for final audit) by fully qualified `#check @name` and `#print axioms name` for all authored theorems. This freshly elaborates R39 and R41 together without trusting a project .olean. It does not check project import resolution or a Lake build. No generated, cache, scratch or environment files were created. All Lean processes used:

```text
bwrap --ro-bind / / --dev /dev --proc /proc /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean --stdin -j1 -M1024
```

Python `subprocess.run(..., input=stream, text=True, capture_output=True, timeout=120)` enforced the wall limit. Lean `-j1 -M1024` supplied one elaboration worker and the 1024MiB Lean memory bound; final measured child RSS was 764484 KiB, child user+system CPU 1.889982s. The first wrapper additionally set RLIMIT_AS=1GiB, RLIMIT_CPU=120 and one-CPU affinity; it failed before elaboration with exit 134 and `libc++abi: terminating due to uncaught exception of type lean::exception: failed to create thread: Resource temporarily unavailable`. Primary explicitly directed the previously successful exact command above, removing RLIMIT_AS and affinity. No larger Lean memory/time limit was used. Host CPU/thread maxima beyond `-j1` were not independently instrumented.

Material attempts:

| stream SHA-256 | seconds | Lean exit | evidence |
|---|---:|---:|---|
| `ec2e7657f3bd1de0317eb153cc1021f639f20e4c7fd7337740ab84f55aa6cdc4` | 1.332013 | 134 | RLIMIT_AS/thread setup failure before elaboration |
| `ec2e7657f3bd1de0317eb153cc1021f639f20e4c7fd7337740ab84f55aa6cdc4` | 5.202652 | 1 | actual syntax/decidability diagnostics; 760068 KiB RSS |
| `7a75ee5c39e25ff5a96b3a1d1365a82e0aa850868c190d61c49f82ff6b6bd976` | 1.389830 | 0 | repaired elaboration; no diagnostics; 771600 KiB RSS |
| `dbc1f2839a29e8b138f3b3ee1161e9148fbed5cd2b35a3f1510f7877cda60ba4` | 4.884926 | 0 | final 9-theorem type/axiom audit; complete output below |

Actual first elaboration diagnostics included `<stdin>:409:16: error: unexpected token ':='; expected command` for unsupported namespace-alias syntax, followed by cascading `Unknown identifier Entry.Action`/`Entry.Registration`/other Entry references and an unmatched namespace end. It also reported `<stdin>:607:2: error: failed to synthesize Decidable` for the analytic consumer proposition. Repair used the existing fully qualified namespace and `simp [rowOnlyAuthorizes, registrationAuthorizes]`, with no theorem strengthening. Final audit includes the later empty-concrete application theorem and final doc clarification. Final stdout contains only the complete types/axiom results; stderr is empty: ``. Source token audit found no sorry/admit/project axiom/checker bypass. Actual transitive axiom results below are authoritative for these declarations; no blanket axiom-free claim is made.

## Frozen artifacts and dependencies

| path | SHA-256 |
|---|---|
| `notes/theory/lean/YulangClosure/LambdaArgumentEffectIncidenceR41.lean` | `af7c2e3def8762287e95827896dc01d982954059bff09c476d1a94df94c0a79e` |
| `notes/theory/lean/YulangClosure/ComputationPermissionEntryR39.lean` | `748cd52ff7962962940a3767ffa6a0b2d8def16d80e65e682282d1fa2b79560e` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `212646a72982e77ec92fcbd7e1e171680f6236676d224003f3af36338f83e2f4` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |
| `notes/theory/2026-10-13-intrusion-source-preservation-proof.md` | `3142dd78111f0600ee9364e60af2d8138ce3989f9676589930c8a236837f3271` |
| `notes/design/2026-10-24-birth-level-scc-intrusion.md` | `ceedbb24ea2f9a640574840e840de7121c8f9b94a5c83ab50efc7a819badf5ae` |
| `tasks/agent-loop/inbox/effect-permission-module-use-r40-read2.md` | `29ef9e594a9175299410db966f15e5689781568b6ca998055668aec152f58627` |
| `crates/yu-solver/src/candidate_source.rs` | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` |
| `crates/yu-solver/src/candidate_call.rs` | `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f` |

Rust mutable lease paths are not Lean imports. Their original R41 contract baseline hashes remain the admitted source scope; this worker does not freeze or certify the concurrent Rust delta. Exact changed paths are this handoff and `notes/theory/lean/YulangClosure/LambdaArgumentEffectIncidenceR41.lean` only. There are no scratch paths or generated artifacts. The full 1400-second grant may be conservatively charged; total dispatch-to-stop wall time was not independently instrumented, and no resource balance is reclaimed here. No children, scheduling edits, Git mutation, external contact, dependency installation or global-default change occurred.

Writing is STOPPED after this revision. Next action is primary intake and fresh independent review of frozen bytes. No further construction or writes occur without a new exact primary instruction.

## Complete final theorem types and transitive axiom results

```text
@YulangClosure.LambdaArgumentEffectIncidenceR41.function_child_one : ∀ {T : Type}
  (p : YulangClosure.LambdaArgumentEffectIncidenceR41.Ports T), p.children[1]? = some p.argumentEffect
'YulangClosure.LambdaArgumentEffectIncidenceR41.function_child_one' depends on axioms: [propext]
@YulangClosure.LambdaArgumentEffectIncidenceR41.lambda_origin : ∀ {Id Term : Type}
  (a : YulangClosure.ComputationPermissionEntryR39.Action Id)
  (f : YulangClosure.ComputationPermissionEntryR39.Registration Id) (port : Id) (negativeEffect : Id → Term)
  (function argument returned result : Term),
  have built :=
    YulangClosure.LambdaArgumentEffectIncidenceR41.constructLambda a f port negativeEffect function argument returned
      result;
  built.origin = YulangClosure.LambdaArgumentEffectIncidenceR41.label a f port ∧
    built.function = function ∧ built.ports.children[1]? = some (negativeEffect built.origin.entry)
'YulangClosure.LambdaArgumentEffectIncidenceR41.lambda_origin' depends on axioms: [propext]
@YulangClosure.LambdaArgumentEffectIncidenceR41.capture_preserves : ∀ {Id Term : Type} (nodes : Term → Nat)
  (rows : Id → Nat) (built : YulangClosure.LambdaArgumentEffectIncidenceR41.LiveLambda Id Term),
  (YulangClosure.LambdaArgumentEffectIncidenceR41.capture nodes rows built).origin = built.origin ∧
    (YulangClosure.LambdaArgumentEffectIncidenceR41.capture nodes rows built).function = nodes built.function ∧
      (YulangClosure.LambdaArgumentEffectIncidenceR41.capture nodes rows built).ports.children[1]? =
          some (nodes built.ports.argumentEffect) ∧
        (YulangClosure.LambdaArgumentEffectIncidenceR41.capture nodes rows built).entryRow = rows built.origin.entry
'YulangClosure.LambdaArgumentEffectIncidenceR41.capture_preserves' depends on axioms: [propext]
@YulangClosure.LambdaArgumentEffectIncidenceR41.freshuse_exact : ∀ {Id Term Row DefinitionUse ContextUse : Type}
  (use : YulangClosure.LambdaArgumentEffectIncidenceR41.Use DefinitionUse ContextUse) (terms : Nat → Term)
  (rows : Nat → Row) (captured : YulangClosure.LambdaArgumentEffectIncidenceR41.Captured Id),
  have image := YulangClosure.LambdaArgumentEffectIncidenceR41.freshen use terms rows captured;
  image.origin = captured.origin ∧
    image.use = use ∧
      image.sourceFunction = captured.function ∧
        image.sourceArgumentEffect = captured.ports.argumentEffect ∧
          image.function = terms captured.function ∧
            image.ports.children[1]? = some (terms captured.ports.argumentEffect) ∧
              image.entryRow = rows captured.entryRow
'YulangClosure.LambdaArgumentEffectIncidenceR41.freshuse_exact' depends on axioms: [propext]
@YulangClosure.LambdaArgumentEffectIncidenceR41.distinct_registration_images : ∀
  {Id Term Row DefinitionUse ContextUse : Type}
  (use : YulangClosure.LambdaArgumentEffectIncidenceR41.Use DefinitionUse ContextUse) (terms : Nat → Term)
  (rows : Nat → Row) (left right : YulangClosure.LambdaArgumentEffectIncidenceR41.Captured Id),
  left.origin.registration ≠ right.origin.registration →
    (YulangClosure.LambdaArgumentEffectIncidenceR41.freshen use terms rows left).origin ≠
      (YulangClosure.LambdaArgumentEffectIncidenceR41.freshen use terms rows right).origin
'YulangClosure.LambdaArgumentEffectIncidenceR41.distinct_registration_images' does not depend on any axioms
@YulangClosure.LambdaArgumentEffectIncidenceR41.shared_row_distinct_labels : ∀
  {Id Term Row DefinitionUse ContextUse : Type}
  (use : YulangClosure.LambdaArgumentEffectIncidenceR41.Use DefinitionUse ContextUse) (terms : Nat → Term)
  (rows : Nat → Row) (left right : YulangClosure.LambdaArgumentEffectIncidenceR41.Captured Id),
  left.origin.registration ≠ right.origin.registration →
    rows left.entryRow = rows right.entryRow →
      (YulangClosure.LambdaArgumentEffectIncidenceR41.freshen use terms rows left).entryRow =
          (YulangClosure.LambdaArgumentEffectIncidenceR41.freshen use terms rows right).entryRow ∧
        (YulangClosure.LambdaArgumentEffectIncidenceR41.freshen use terms rows left).origin ≠
          (YulangClosure.LambdaArgumentEffectIncidenceR41.freshen use terms rows right).origin
'YulangClosure.LambdaArgumentEffectIncidenceR41.shared_row_distinct_labels' does not depend on any axioms
@YulangClosure.LambdaArgumentEffectIncidenceR41.entry_to_exact_use : ∀ {Id Term Row DefinitionUse ContextUse : Type}
  [inst : DecidableEq Id] (e : YulangClosure.ComputationPermissionEntryR39.Inputs Id)
  (a : YulangClosure.ComputationPermissionEntryR39.Action Id)
  (f : YulangClosure.ComputationPermissionEntryR39.Registration Id)
  (r : YulangClosure.ComputationPermissionEntryR39.Row Id) (port : Id)
  (s : YulangClosure.ComputationPermissionEntryR39.State Id),
  e.formals[a.registration]? = some f →
    a.annotation.row = some r →
      f.entry = some port →
        YulangClosure.ComputationPermissionEntryR39.Valid e a f r →
          r.concrete ≠ [] →
            ∀ (negativeEffect : Id → Term) (function argument returned result : Term) (nodes : Term → Nat)
              (rowIndexes : Id → Nat)
              (use : YulangClosure.LambdaArgumentEffectIncidenceR41.Use DefinitionUse ContextUse) (terms : Nat → Term)
              (rows : Nat → Row),
              have built :=
                YulangClosure.LambdaArgumentEffectIncidenceR41.constructLambda a f port negativeEffect function argument
                  returned result;
              have image :=
                YulangClosure.LambdaArgumentEffectIncidenceR41.freshen use terms rows
                  (YulangClosure.LambdaArgumentEffectIncidenceR41.capture nodes rowIndexes built);
              ∃ p,
                YulangClosure.ComputationPermissionEntryR39.prepare e a = some (f, r, port) ∧
                  YulangClosure.ComputationPermissionEntryR39.permissionFor a f r port = some p ∧
                    YulangClosure.ComputationPermissionEntryR39.publish a f r port true s =
                        some
                          { permissions := s.permissions ++ [p],
                            links := s.links ++ YulangClosure.ComputationPermissionEntryR39.symbolicLinks a r port,
                            inflow := s.inflow } ∧
                      p.concrete = r.concrete ∧
                        p.registration = image.origin.registration ∧
                          p.owner = image.origin.owner ∧
                            p.occurrence = image.origin.occurrence ∧
                              p.entry = image.origin.entry ∧
                                image.use = use ∧
                                  image.sourceFunction = nodes function ∧
                                    image.sourceArgumentEffect = nodes (negativeEffect port) ∧
                                      image.ports.children[1]? = some (terms (nodes (negativeEffect port))) ∧
                                        image.entryRow = rows (rowIndexes port)
'YulangClosure.LambdaArgumentEffectIncidenceR41.entry_to_exact_use' depends on axioms: [propext, Quot.sound]
@YulangClosure.LambdaArgumentEffectIncidenceR41.empty_entry_incidence : ∀ {Id Term : Type} [inst : DecidableEq Id]
  (e : YulangClosure.ComputationPermissionEntryR39.Inputs Id)
  (a : YulangClosure.ComputationPermissionEntryR39.Action Id)
  (f : YulangClosure.ComputationPermissionEntryR39.Registration Id)
  (r : YulangClosure.ComputationPermissionEntryR39.Row Id) (port : Id)
  (s : YulangClosure.ComputationPermissionEntryR39.State Id),
  e.formals[a.registration]? = some f →
    a.annotation.row = some r →
      f.entry = some port →
        YulangClosure.ComputationPermissionEntryR39.Valid e a f r →
          r.concrete = [] →
            ∀ (negativeEffect : Id → Term) (function argument returned result : Term),
              YulangClosure.ComputationPermissionEntryR39.prepare e a = some (f, r, port) ∧
                YulangClosure.ComputationPermissionEntryR39.permissionFor a f r port = none ∧
                  (YulangClosure.LambdaArgumentEffectIncidenceR41.constructLambda a f port negativeEffect function
                          argument returned result).origin =
                      YulangClosure.LambdaArgumentEffectIncidenceR41.label a f port ∧
                    (YulangClosure.LambdaArgumentEffectIncidenceR41.constructLambda a f port negativeEffect function
                              argument returned result).ports.children[1]? =
                      some (negativeEffect port)
'YulangClosure.LambdaArgumentEffectIncidenceR41.empty_entry_incidence' depends on axioms: [propext, Quot.sound]
YulangClosure.LambdaArgumentEffectIncidenceR41.conditional_shared_tail_falsifier : have signalPermission :=
  { registration := 0, tail := 7, concrete := [YulangClosure.LambdaArgumentEffectIncidenceR41.Effect.signal] };
have writePermission :=
  { registration := 1, tail := 7, concrete := [YulangClosure.LambdaArgumentEffectIncidenceR41.Effect.write] };
have arrival :=
  { registration := 1, tail := 7, effect := YulangClosure.LambdaArgumentEffectIncidenceR41.Effect.signal };
signalPermission.tail = writePermission.tail ∧
  signalPermission.registration ≠ writePermission.registration ∧
    signalPermission.concrete ≠ writePermission.concrete ∧
      arrival.registration = writePermission.registration ∧
        YulangClosure.LambdaArgumentEffectIncidenceR41.rowOnlyAuthorizes signalPermission arrival ∧
          ¬YulangClosure.LambdaArgumentEffectIncidenceR41.registrationAuthorizes signalPermission arrival
'YulangClosure.LambdaArgumentEffectIncidenceR41.conditional_shared_tail_falsifier' depends on axioms: [propext]
```
