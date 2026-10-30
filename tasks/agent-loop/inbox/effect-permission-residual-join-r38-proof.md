# R38 proof handoff — revision 1, FROZEN

Sprint-ID: EFFECT-PERMISSION-RESIDUAL-JOIN/20261031-R38. Contract revision 1, SHA-256 `6f8420b3c4b3f5ebed311f58bcfbcc1de851d10b7cc47073b8775cd2047fc6e2`. Input manifest SHA-256 `c2a1093d9b1fccfff74f24281f3236590a43d5ebac425efdb930b853a8e6c3b1`. Assignment-ID: R38-PROOF; handoff revision 1. Baseline: `c6e37750f8b454da95afe0f712710e38b4c94b85`.

Author/worker: `/root/r38_proof`, current-session actual task receipt from `/root`; no descendants or coauthors. Requested Sol/high; effective observed model/effort UNKNOWN (no runtime metadata supplied). Role: constructive proof leaf. The yulang-lean-proofs skill was applied using the contract's read-only stdin exception. Only the two assigned paths were written.

## Parent, result and precise application

Parent: authoritative `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` §§1–1.2, 3–4, in the original source domain and quantifiers: permission alone contributes no outward effect; actual selected matching contribution may be subtracted locally; every unmatched contribution, including equal-family other-boundary contributions, survives; empty inflow remains empty. This bounded candidate development does not replace that source-wide statement.

Outcome: **kernel-checked finite conditional mathematics plus a guard-independence countermodel; NO_SAFE_CODE_SLICE for the missing source permission join**. No source execution or Rust simulation is asserted. Fresh independent review remains PENDING; the author is ineligible to certify this result.

Artifact: `notes/theory/lean/YulangClosure/EffectPermissionResidualR38.lean`, SHA-256 `e5657e0b8affaaa0ffef6543c8e329957a1519a04a194392dbd245064a623642`. It imports only pinned standard `Std`; there are no project-import dependencies, supplied LocalLaws, project axioms, or assumed source simulation interfaces. R35–R37 are consulted history/dependencies only, not imported theorem premises.

`permission_guard_sound` proves exact *metadata* authentication (all FormalSite fields plus concrete membership); `foreign_formal_rejected` and `absent_family_rejected` give falsifiers. This checker issues no provider/arrival authority and is never substituted for the existing source suppression guard. `native_guard_sound` characterizes that actual bounded guard from exact operation equality, closed view, family and full provider occurrence/declaration identity. Equal family alone is insufficient.

`residual_exact`, `unmatched_preserved`, `no_permission_injection`, `same_family_other_boundary_preserved`, and `residual_append` prove preservation for arbitrary finite terminal input, without family-set collapse. `fold_correspondence` proves the accumulator invariant for *every* initial state and terminal list: forwarded endpoints are precisely the original prefix plus ordered filtering; outcomes are precisely the prefix plus one outcome per terminal. `native_fold_correspondence` and `native_fold_other_boundary` apply these results to the native guard. Identity, order and multiplicity are retained at the post-traversal terminal-list interface.

`empty_inflow` and `native_fold_empty` prove pure refinement/loop emptiness. **Actual source admission does not return an empty successful experiment**: `candidate_receiver.rs::execute_receiving_assembly` returns Err on `terminals.is_empty()`, modeled by `actual_empty_unavailable`. `unavailable_no_partial` and `admitted_exact` distinguish unavailable extraction from the successful nonempty fold. Theorems do not prove traversal coverage or mutation rollback.

`native_suppresses_without_permission` and `concrete_missing_join` exhibit guard independence. Concrete keys are family 7, declaration 11, provider occurrence 13, selected exact operation, closed member, empty permission inventory: the native guard is true and no retained permission can be found. This **falsifies the abstract claim that the existing guard certifies permission**, not the user-selected semantics and not a claim that arbitrary abstract records are emitted by source constructors. There is no native-reachability claim.

## Source correspondence and first missing transition

Pinned source trace, inspected only on permitted paths:

- `candidate_source::Action::FormalEntry`, `FormalAnnotation`, `FormalNameEffect`, `Operation`, `CatchOperation` preserve distinct action identities. The Lambda constructor schedules FormalEntry for computation-effect formals and FormalAnnotation separately.
- `candidate_effect::candidate_formal_effect_port` records negative concrete permission with parameter, Lambda occurrence, source owner, scope, full path, exact source row and concrete vector; `FormalPermission` explicitly states it is not arrival/provider/contribution/consumer evidence. `FormalSite`/`Permission` represent these fields without reconstructing authority from family.
- `candidate_effect::candidate_formal_entry_annotation` connects the entry row's symbolic variable if present and retains annotation on the action; it does not construct permission-to-provider provenance. `candidate_call::FormalRegistrationInput` separately retains parameter, owner, recipe, role and entry row.
- `candidate_effect::candidate_operation` constructs the operation signature under `SignatureContext::Operation`; `OperationOrigin` retains occurrence and resolved declaration. `Origin` represents exactly the occurrence and operation-id portion read by the receiver guard. Arc, retained byte accounting and full signature typing are outside this model.
- `candidate_source` Catch construction emits local slot 51 from the source scrutinee effect to Catch-result effect. `candidate_receiver::assemble` authenticates the provider, resolved operation, parameter-resolved scrutinee, selected arm and constrained two-definition source shape. The receiver withholds precisely the occurrence/slot-51 fact, walks canonical lowers, and forwards unsuppressed terminal endpoints with the original upper/fact/cause. `step`/`sourceFold` model only this last successful terminal loop.
- `nativeGuard` corresponds to the existing receiver's selected equality, tail absence, allowed member family and Operation-origin occurrence/declaration checks. `Terminal.other` aggregates all nonmatching terminal constructors without interpreting their identity; symbolic Support tails cause earlier unavailability. `symbolic_not_suppressed` is a pure guard property, **not** permission to publish a symbolic partial source result.

**First missing edge / owner:** no permitted `candidate_effect`/`candidate_call`/`candidate_source` producer authenticates a retained `FormalPermission` (the exact formal/owner/path/row) as licensing the *arriving* provider operation contribution at this selected Catch/residual edge; `candidate_receiver::execute_receiving_assembly` never consumes `formal_permissions`. Existing provenance identifies the operation provider but carries no formal permission boundary. This is the R38-PERMISSION-ARRIVAL-JOIN TODO, owned by Luna and the named source producer/consumer owners. No such relation is assumed in this Lean module under another name.

The remaining source-to-native application therefore requires actual construction of that missing identity edge, plus complete terminal traversal and success of each `constrain_live_effect`. The pure fold theorem applies after those transitions are established; it does not establish them. The original A/B joint witness/strategy, independent quantifiers, all-source generation/accumulation/propagation/levels/extrusion/qualifying intrusion/generalization, invocation, Grant/Catch transport, native Step/History, runtime consumption, whole-language hygiene/soundness/principality/termination and production gates remain OPEN.

## Reuse and exclusions

R35's actual permission projection, R36's computed Observe direct-use witness, R37's complete source-use inventory and their final scoped reviews were consulted. None proves computation-formal arrival licensing or runtime receipt; none was reused outside its premises. No historical theorem was relabeled as R38 source closure. No withdrawn bypass, closed annotation upper bound, family-only authorization, supplied eligibility Boolean, residual/provider/witness collapse or ordinary-inference weakening was used. The selected source is the bounded computation-formal assembly, not R36/R37's outer-effects-free callback Observe case.

## Checker receipt and resources

Observed native checker: Lean 4.35.0, x86_64-unknown-linux-gnu, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (Release), observed with the same read-only bwrap wrapper and `--version`. Installed binary resolved by read-only `elan which lean` from the pinned project. `lean-toolchain`, `lakefile.toml` and `lake-manifest.json` were read per the proof skill; no Lake executable was invoked under the explicit no-Lake contract.

Final audit command, supplied from memory by Python (no extraction/scratch file):

```text
bwrap --ro-bind / / --dev /dev --proc /proc /home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean --stdin -j1 -M1024
```

Stream: complete standalone R38 module, followed by `#check @` and `#print axioms` for every one of its 22 theorem declarations. Final stream SHA-256 `15a341cd8849f2964bb328247f560e6b4c3ed23a7306925437e7d378f0c20f33`. Final checker exit 0; empty stderr; no diagnostics; elapsed 4.406111575 seconds; per-call timeout 90 seconds; one thread, 1 GiB Lean limit. Complete types and transitive axiom outputs appear verbatim below. Standard axioms reported there are the entire observed dependency sets; there is no sorryAx, native evaluation, project axiom or checker bypass.

Material failed attempts: (1) 4.794625873 s, exit 1: implicit type-key binder was missing before two definitions, so `Id` resolved to Lean's pre-existing identity constructor; cascading errors and sorryAx diagnostics were rejected; unsupported audit option `pp.width` was also removed. (2) 0.754386012 s, exit 1: the existential native guard characterization required explicit constructor equality elimination. Both were repaired; no failed declaration is counted as proof. A subsequent module-only check passed, exit 0, 0.726320785 s, empty diagnostics; the final module adds the direct empty-fold corollary and receives the complete successful audit below. All four invocations are counted. No process persists.

Allocated proof envelope: 1,600 seconds, no transfer or renewal. Measured checker subprocess time: 10.681444245 seconds total; agent dispatch-to-stop wall time and total CPU/peak RSS UNKNOWN. No budgets were enlarged. Python only orchestrated reads, the leased module/handoff writes and stdin checker; it ran no experiment/tests. Static forbidden-proof-token scan of the standalone module found no matches for proof holes, project axioms, native evaluation, unsafe/implemented_by or skipKernelTC. No Cargo/build/Lake/tests/formatter/cache/target/copies/environments/worktrees/extraction/scratch/Git or external contact. Neither excluded runtime file was opened or searched.

## Frozen input hashes

| Input | SHA-256 | R38 manifest |
|---|---|---|
| `crates/yu-solver/src/candidate_receiver.rs` | `620b09011ec4dc4bfa71998e2b6fc1498b9299b3056662fdaa80b17376ba23c3` | MATCH |
| `crates/yu-solver/src/candidate_effect.rs` | `1f64d4fec8f2abceb11a48a51f5b615aa2cf605c9586ba742f15f9024a6a2717` | MATCH |
| `crates/yu-solver/src/candidate_call.rs` | `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f` | MATCH |
| `crates/yu-solver/src/candidate_source.rs` | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` | MATCH |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` | MATCH |
| `notes/design/INDEX.md` | `98f464f421f07459a15c60fc51fc7bc94efbdfe45d6cbc8f519a19cd50307e0a` | MATCH |
| `notes/theory/lean/YulangClosure/SourceCallbackPermissionR35.lean` | `f4d6c85dc12d9e5b9f58a6635c76ee49fba85ff732b5538f9924e1ab052dbcc9` | MATCH |
| `notes/theory/lean/YulangClosure/SourceCallbackUseR36.lean` | `9e15cb4982248cf90d7a11ef0c66ee7ee95ec0abe99c217d8187c31c488731de` | MATCH |
| `tasks/agent-loop/inbox/effect-permission-source-use-r36-review.md` | `2b2f8bb23727c82fc572046e36d2aba64b63ac2020cbb491151b871ee3779afe` | MATCH |
| `notes/theory/lean/YulangClosure/SourceUseInventoryR37.lean` | `4981f8c20dc5d9c932d9f4a843f2245c034daaa015e7fc7b97aa7a343bb7ea30` | MATCH |
| `tasks/agent-loop/inbox/effect-permission-source-inventory-r37-review.md` | `a82a806fd419224285ffa19f42d043360379598966081636eeb1c22849fc6937` | MATCH |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` | MATCH |

## Complete final theorem types and axiom audit

```text
@YulangClosure.EffectPermissionResidualR38.permission_guard_sound : ∀ {Id : Type} [inst : DecidableEq Id]
  (site : YulangClosure.EffectPermissionResidualR38.FormalSite Id) (family : Id)
  (p : YulangClosure.EffectPermissionResidualR38.Permission Id),
  YulangClosure.EffectPermissionResidualR38.permissionGuard site family p = true ↔ p.site = site ∧ family ∈ p.concrete
'YulangClosure.EffectPermissionResidualR38.permission_guard_sound' depends on axioms: [propext]
@YulangClosure.EffectPermissionResidualR38.foreign_formal_rejected : ∀ {Id : Type} [inst : DecidableEq Id]
  (site : YulangClosure.EffectPermissionResidualR38.FormalSite Id) (family : Id)
  (p : YulangClosure.EffectPermissionResidualR38.Permission Id),
  p.site ≠ site → YulangClosure.EffectPermissionResidualR38.permissionGuard site family p = false
'YulangClosure.EffectPermissionResidualR38.foreign_formal_rejected' depends on axioms: [propext]
@YulangClosure.EffectPermissionResidualR38.absent_family_rejected : ∀ {Id : Type} [inst : DecidableEq Id]
  (site : YulangClosure.EffectPermissionResidualR38.FormalSite Id) (family : Id)
  (p : YulangClosure.EffectPermissionResidualR38.Permission Id),
  ¬family ∈ p.concrete → YulangClosure.EffectPermissionResidualR38.permissionGuard site family p = false
'YulangClosure.EffectPermissionResidualR38.absent_family_rejected' depends on axioms: [propext]
@YulangClosure.EffectPermissionResidualR38.native_guard_sound : ∀ {Id : Type} [inst : DecidableEq Id]
  (s : YulangClosure.EffectPermissionResidualR38.Assembly Id)
  (t : YulangClosure.EffectPermissionResidualR38.Terminal Id),
  YulangClosure.EffectPermissionResidualR38.nativeGuard s t = true ↔
    ∃ origin family tail,
      t = YulangClosure.EffectPermissionResidualR38.Terminal.member origin family tail ∧
        s.handled = s.provider.operation ∧ tail = none ∧ family = s.provider.operation.family ∧ origin = s.provider
'YulangClosure.EffectPermissionResidualR38.native_guard_sound' depends on axioms: [propext, Quot.sound]
@YulangClosure.EffectPermissionResidualR38.other_boundary_rejected : ∀ {Id : Type} [inst : DecidableEq Id]
  (s : YulangClosure.EffectPermissionResidualR38.Assembly Id) (o : YulangClosure.EffectPermissionResidualR38.Origin Id)
  (f : Id) (tail : Option Id),
  o.occurrence ≠ s.provider.occurrence →
    YulangClosure.EffectPermissionResidualR38.nativeGuard s
        (YulangClosure.EffectPermissionResidualR38.Terminal.member o f tail) =
      false
'YulangClosure.EffectPermissionResidualR38.other_boundary_rejected' depends on axioms: [propext]
@YulangClosure.EffectPermissionResidualR38.other_operation_rejected : ∀ {Id : Type} [inst : DecidableEq Id]
  (s : YulangClosure.EffectPermissionResidualR38.Assembly Id) (o : YulangClosure.EffectPermissionResidualR38.Origin Id)
  (f : Id) (tail : Option Id),
  o.operation ≠ s.provider.operation →
    YulangClosure.EffectPermissionResidualR38.nativeGuard s
        (YulangClosure.EffectPermissionResidualR38.Terminal.member o f tail) =
      false
'YulangClosure.EffectPermissionResidualR38.other_operation_rejected' depends on axioms: [propext]
@YulangClosure.EffectPermissionResidualR38.symbolic_not_suppressed : ∀ {Id : Type} [inst : DecidableEq Id]
  (s : YulangClosure.EffectPermissionResidualR38.Assembly Id) (o : YulangClosure.EffectPermissionResidualR38.Origin Id)
  (f tail : Id),
  YulangClosure.EffectPermissionResidualR38.nativeGuard s
      (YulangClosure.EffectPermissionResidualR38.Terminal.member o f (some tail)) =
    false
'YulangClosure.EffectPermissionResidualR38.symbolic_not_suppressed' depends on axioms: [propext]
@YulangClosure.EffectPermissionResidualR38.empty_inflow : ∀ {Id : Type}
  (guard : YulangClosure.EffectPermissionResidualR38.Terminal Id → Bool),
  YulangClosure.EffectPermissionResidualR38.residual guard [] = []
'YulangClosure.EffectPermissionResidualR38.empty_inflow' does not depend on any axioms
@YulangClosure.EffectPermissionResidualR38.residual_exact : ∀ {Id : Type}
  (guard : YulangClosure.EffectPermissionResidualR38.Terminal Id → Bool)
  (input : List (YulangClosure.EffectPermissionResidualR38.Terminal Id))
  (t : YulangClosure.EffectPermissionResidualR38.Terminal Id),
  t ∈ YulangClosure.EffectPermissionResidualR38.residual guard input ↔ t ∈ input ∧ guard t = false
'YulangClosure.EffectPermissionResidualR38.residual_exact' depends on axioms: [propext]
@YulangClosure.EffectPermissionResidualR38.unmatched_preserved : ∀ {Id : Type}
  (guard : YulangClosure.EffectPermissionResidualR38.Terminal Id → Bool)
  (input : List (YulangClosure.EffectPermissionResidualR38.Terminal Id))
  (t : YulangClosure.EffectPermissionResidualR38.Terminal Id),
  t ∈ input → guard t = false → t ∈ YulangClosure.EffectPermissionResidualR38.residual guard input
'YulangClosure.EffectPermissionResidualR38.unmatched_preserved' depends on axioms: [propext]
@YulangClosure.EffectPermissionResidualR38.no_permission_injection : ∀ {Id : Type}
  (guard : YulangClosure.EffectPermissionResidualR38.Terminal Id → Bool)
  (input : List (YulangClosure.EffectPermissionResidualR38.Terminal Id))
  (t : YulangClosure.EffectPermissionResidualR38.Terminal Id),
  t ∈ YulangClosure.EffectPermissionResidualR38.residual guard input → t ∈ input
'YulangClosure.EffectPermissionResidualR38.no_permission_injection' depends on axioms: [propext]
@YulangClosure.EffectPermissionResidualR38.same_family_other_boundary_preserved : ∀ {Id : Type} [inst : DecidableEq Id]
  (s : YulangClosure.EffectPermissionResidualR38.Assembly Id)
  (input : List (YulangClosure.EffectPermissionResidualR38.Terminal Id))
  (o : YulangClosure.EffectPermissionResidualR38.Origin Id) (tail : Option Id),
  YulangClosure.EffectPermissionResidualR38.Terminal.member o s.provider.operation.family tail ∈ input →
    o.occurrence ≠ s.provider.occurrence →
      YulangClosure.EffectPermissionResidualR38.Terminal.member o s.provider.operation.family tail ∈
        YulangClosure.EffectPermissionResidualR38.residual (YulangClosure.EffectPermissionResidualR38.nativeGuard s)
          input
'YulangClosure.EffectPermissionResidualR38.same_family_other_boundary_preserved' depends on axioms: [propext]
@YulangClosure.EffectPermissionResidualR38.residual_append : ∀ {Id : Type}
  (guard : YulangClosure.EffectPermissionResidualR38.Terminal Id → Bool)
  (left right : List (YulangClosure.EffectPermissionResidualR38.Terminal Id)),
  YulangClosure.EffectPermissionResidualR38.residual guard (left ++ right) =
    YulangClosure.EffectPermissionResidualR38.residual guard left ++
      YulangClosure.EffectPermissionResidualR38.residual guard right
'YulangClosure.EffectPermissionResidualR38.residual_append' depends on axioms: [propext]
@YulangClosure.EffectPermissionResidualR38.fold_correspondence : ∀ {Id : Type}
  (guard : YulangClosure.EffectPermissionResidualR38.Terminal Id → Bool)
  (input : List (YulangClosure.EffectPermissionResidualR38.Terminal Id))
  (state : YulangClosure.EffectPermissionResidualR38.FoldState Id),
  YulangClosure.EffectPermissionResidualR38.sourceFold guard input state =
    { forwarded := state.forwarded ++ YulangClosure.EffectPermissionResidualR38.residual guard input,
      outcomes :=
        state.outcomes ++ List.map (fun t => (t, YulangClosure.EffectPermissionResidualR38.outcome guard t)) input }
'YulangClosure.EffectPermissionResidualR38.fold_correspondence' depends on axioms: [propext]
@YulangClosure.EffectPermissionResidualR38.native_fold_correspondence : ∀ {Id : Type} [inst : DecidableEq Id]
  (s : YulangClosure.EffectPermissionResidualR38.Assembly Id)
  (input : List (YulangClosure.EffectPermissionResidualR38.Terminal Id)),
  YulangClosure.EffectPermissionResidualR38.sourceFold (YulangClosure.EffectPermissionResidualR38.nativeGuard s) input
      { forwarded := [], outcomes := [] } =
    {
      forwarded :=
        YulangClosure.EffectPermissionResidualR38.residual (YulangClosure.EffectPermissionResidualR38.nativeGuard s)
          input,
      outcomes :=
        List.map
          (fun t =>
            (t,
              YulangClosure.EffectPermissionResidualR38.outcome
                (YulangClosure.EffectPermissionResidualR38.nativeGuard s) t))
          input }
'YulangClosure.EffectPermissionResidualR38.native_fold_correspondence' depends on axioms: [propext]
@YulangClosure.EffectPermissionResidualR38.native_fold_other_boundary : ∀ {Id : Type} [inst : DecidableEq Id]
  (s : YulangClosure.EffectPermissionResidualR38.Assembly Id)
  (input : List (YulangClosure.EffectPermissionResidualR38.Terminal Id))
  (o : YulangClosure.EffectPermissionResidualR38.Origin Id) (tail : Option Id),
  YulangClosure.EffectPermissionResidualR38.Terminal.member o s.provider.operation.family tail ∈ input →
    o.occurrence ≠ s.provider.occurrence →
      YulangClosure.EffectPermissionResidualR38.Terminal.member o s.provider.operation.family tail ∈
        (YulangClosure.EffectPermissionResidualR38.sourceFold (YulangClosure.EffectPermissionResidualR38.nativeGuard s)
            input { forwarded := [], outcomes := [] }).forwarded
'YulangClosure.EffectPermissionResidualR38.native_fold_other_boundary' depends on axioms: [propext]
@YulangClosure.EffectPermissionResidualR38.unavailable_no_partial : ∀ {Id : Type} [inst : DecidableEq Id]
  (s : YulangClosure.EffectPermissionResidualR38.Assembly Id),
  YulangClosure.EffectPermissionResidualR38.admittedFold s none = none
'YulangClosure.EffectPermissionResidualR38.unavailable_no_partial' does not depend on any axioms
@YulangClosure.EffectPermissionResidualR38.actual_empty_unavailable : ∀ {Id : Type} [inst : DecidableEq Id]
  (s : YulangClosure.EffectPermissionResidualR38.Assembly Id),
  YulangClosure.EffectPermissionResidualR38.admittedFold s (some []) = none
'YulangClosure.EffectPermissionResidualR38.actual_empty_unavailable' does not depend on any axioms
@YulangClosure.EffectPermissionResidualR38.admitted_exact : ∀ {Id : Type} [inst : DecidableEq Id]
  (s : YulangClosure.EffectPermissionResidualR38.Assembly Id)
  (input : List (YulangClosure.EffectPermissionResidualR38.Terminal Id))
  (state : YulangClosure.EffectPermissionResidualR38.FoldState Id),
  YulangClosure.EffectPermissionResidualR38.admittedFold s (some input) = some state ↔
    input ≠ [] ∧
      state =
        {
          forwarded :=
            YulangClosure.EffectPermissionResidualR38.residual (YulangClosure.EffectPermissionResidualR38.nativeGuard s)
              input,
          outcomes :=
            List.map
              (fun t =>
                (t,
                  YulangClosure.EffectPermissionResidualR38.outcome
                    (YulangClosure.EffectPermissionResidualR38.nativeGuard s) t))
              input }
'YulangClosure.EffectPermissionResidualR38.admitted_exact' depends on axioms: [propext]
@YulangClosure.EffectPermissionResidualR38.native_fold_empty : ∀ {Id : Type} [inst : DecidableEq Id]
  (s : YulangClosure.EffectPermissionResidualR38.Assembly Id),
  YulangClosure.EffectPermissionResidualR38.sourceFold (YulangClosure.EffectPermissionResidualR38.nativeGuard s) []
      { forwarded := [], outcomes := [] } =
    { forwarded := [], outcomes := [] }
'YulangClosure.EffectPermissionResidualR38.native_fold_empty' does not depend on any axioms
@YulangClosure.EffectPermissionResidualR38.native_suppresses_without_permission : ∀ {Id : Type} [inst : DecidableEq Id]
  (o : YulangClosure.EffectPermissionResidualR38.Origin Id),
  YulangClosure.EffectPermissionResidualR38.nativeGuard { provider := o, handled := o.operation }
        (YulangClosure.EffectPermissionResidualR38.Terminal.member o o.operation.family none) =
      true ∧
    ¬∃ p, p ∈ [] ∧ YulangClosure.EffectPermissionResidualR38.permissionGuard p.site o.operation.family p = true
'YulangClosure.EffectPermissionResidualR38.native_suppresses_without_permission' depends on axioms: [propext,
 Quot.sound]
YulangClosure.EffectPermissionResidualR38.concrete_missing_join : have op := { family := 7, declaration := 11 };
have origin := { occurrence := 13, operation := op };
YulangClosure.EffectPermissionResidualR38.nativeGuard { provider := origin, handled := op }
      (YulangClosure.EffectPermissionResidualR38.Terminal.member origin 7 none) =
    true ∧
  ¬∃ p, p ∈ [] ∧ YulangClosure.EffectPermissionResidualR38.permissionGuard p.site 7 p = true
'YulangClosure.EffectPermissionResidualR38.concrete_missing_join' depends on axioms: [propext, Quot.sound]
```

## Handoff and stop receipt

Next step: Luna assigns fresh independent review of these frozen bytes and the source-grounded NO_SAFE_CODE_SLICE. A new producer packet for R38-PERMISSION-ARRIVAL-JOIN must identify the actual formal permission→entry/provider contribution→selected Catch/residual transition, with exact source identities; falsifier: suppression remains possible through another formal/boundary, equal-family unrelated provenance, or an empty permission inventory. No proposed relation or implementation is installed here. Separate TODO R38-EMPTY-ADMISSION records that actual empty terminal input is unavailable; owning consumer is `candidate_receiver::execute_receiving_assembly`, and any change requires a newly authorized source packet rather than an empty-fold theorem alone.

Worker STOPPED; **all writes stopped after this handoff revision**. No descendants, scratch paths, generated files or unresolved child leases. New paths: exactly the Lean module and this handoff. Module bytes are FROZEN; handoff self-hash is reported externally to Luna to avoid a self-referential hash. Pending independent review/integration; parent remains OPEN. No background worker or verification continues after return.


## Sequential revision 2 — M1 source-transition correction, FROZEN

Assignment-ID: R38-PROOF; handoff revision 2. Author: `/root/r38_proof`.
This append preserves every revision 1 byte above as its exact prefix, SHA-256
`8c9c669e6b044c6c8b46333df0ffc1d3dd09f826ed89f0e84eab447189a10f5d`.
Contract revision, input manifest, Lean module bytes, theorem types and complete
axiom audits are unchanged. This correction follows Luna's exact M1 follow-up;
no new source inspection or checker execution was performed.

The admitted receiving source uses the outer concrete computation annotation
`[E] int`. Its `candidate_source::Action::FormalEntry` route reaches
`candidate_effect::candidate_formal_entry_annotation`, which does not retain
concrete computation permission. The separate `FormalAnnotation` route recurses
on root `Int`; it does not traverse a nested Function effect port and therefore
does not construct a nested Function `FormalPermission` for this annotation.
The revision 1 discussion of retained `FormalPermission` fields describes the
existing nested Function producer, not an emitted permission witness for the
admitted computation-formal source. It must not be read as evidence that this
source already supplies such a witness.

**Corrected first missing source transition:** outer concrete computation
annotation/action -> retained concrete computation-permission witness. Owners:
`candidate_source::Action::FormalEntry` / `FormalAnnotation` and
`candidate_effect::candidate_formal_entry_annotation` / formal annotation
construction. This precedes the separately missing retained permission -> actual
provider arrival -> selected Catch/residual identity join at
`candidate_receiver::execute_receiving_assembly`. Both transitions remain OPEN;
no witness, assumed correspondence law, or bridge is projected into Lean.
R38-PERMISSION-ARRIVAL-JOIN must first obtain the retained computation-permission
witness from its owning source constructor before attempting its downstream join.

The unchanged Lean guard-independence countermodel and fold theorems are bounded
conditional mathematics. They do not establish source guard correspondence or
an executable source counterexample. Their abstract empty-permission records are
not claimed to be emitted by admitted source constructors. The existing native
guard alone cannot certify the missing permission evidence; this conclusion is
distinct from native/source reachability. The original parent, all-source and
runtime/production gates remain OPEN.

Actual empty terminal admission remains unavailable, exactly as recorded by
`actual_empty_unavailable`. Pure-fold empty preservation does not establish a
successful empty source experiment. No empty-success claim is made.

Mutual TODO correction: the minimal next source packet must first construct and
authenticate retained concrete computation permission from the exact admitted
`[E] int` annotation/action, then establish the provider-arrival and selected
Catch/residual join. Falsifier: the claimed witness is only a nested Function
permission, is absent from the actual computation-formal route, or belongs to
another formal/owner/row. This append proposes no implementation and grants no
new source lease or semantics.

Requested model/effort for the assignment: Sol/high; effective observed
model/effort UNKNOWN. The M1 correction used only an in-memory read, prefix-hash
check, and append on this single leased handoff path. No Lean-module write,
checker rerun, build, test, Lake, scratch, environment, worktree, quarantined read
or Git operation occurred. No descendants or persistent process.

Revision 2 FROZEN; worker STOPPED and all writes stopped after this append.
The final handoff byte hash is reported externally to Luna. Fresh independent
review/adjudication remains Luna's responsibility.
