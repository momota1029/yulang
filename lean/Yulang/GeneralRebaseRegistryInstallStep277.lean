import Yulang.GeneralRebaseRegistryInstallModels277

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseRegistryInstallStep277
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedKernel234 (Step At Installable AlternativesSafe Committed)
open GeneralNominalVersionedInstall232 (install)
open GeneralRebaseCompiledRetag277 (retag schema_eq holds children_eq)
open GeneralRebaseRegistrySurface277 (Surface symmetric)
open GeneralRebaseRegistryDiagnostics277 (On)
open GeneralRebaseRegistryEvidence277 (frame)
open GeneralRebaseRegistryInstallModels277
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {a b : Registry} {s : State roles}

theorem alternatives {p : Plan roles} (surface : On a b s p.input.occurrence)
    (old : AlternativesSafe a s p.input) : AlternativesSafe b s p.input := by
  intro q same qFrame
  let ct := (symmetric surface).constructors.symm.trans
    (congrArg Registry.constructors qFrame.registry_eq).symm
  exact old (retag q a ct) same (frame (symmetric surface) qFrame)

theorem committed (p : Plan roles) (b : Registry) (ctors) :
    Committed s (retag p b ctors) ↔ Committed s p := by
  change GeneralNominalVersionedInstallStep232.Committed s (retag p b ctors) ↔
    GeneralNominalVersionedInstallStep232.Committed s p
  unfold GeneralNominalVersionedInstallStep232.Committed
  change (∀ model, Models s model → GeneralNominalVersionedPlans231.Holds (retag p b ctors) model ∧
      GeneralNominalVersionedEffects231.ClassEffects s.core p.packet.site.occurrence (retag p b ctors) model) ∧
    (∀ child ∈ GeneralNominalVersionedFrame231.children (GeneralRebaseCompiledRetag277.retagPacket p.packet b ctors),
      (p.packet.site.occurrence,child) ∈ s.core.erased.current.edges) ↔ _
  simp only [holds,classes,children_eq]

theorem rebound_installable (e : Effect roles) (enabled : Installable a s e)
    (scope : On a b s e.plan.packet.site.occurrence) :
    ∃ surface : Surface e.registry b e.snapshot.erased.current.context e.plan.packet.site.occurrence,
      Installable b s (rebound e b surface) := by
  have surface : Surface e.registry b e.snapshot.erased.current.context e.plan.packet.site.occurrence := by
    rw [enabled.registry_eq,enabled.snapshot_eq]
    exact scope
  refine ⟨surface,⟨rfl,enabled.snapshot_eq,GeneralRebaseRegistryLocal277.safe_forward scope enabled.safe,
    enabled.cache,?_,enabled.choice,enabled.positions,?_,?_⟩⟩
  · change (GeneralNominalVersionedPlans231.emittedSchema (retag e.plan b (retagCtors surface))).unknown = false
    rw [schema_eq]
    exact enabled.materialized
  · have around : On a b s e.plan.input.occurrence := e.plan.input_exact.symm ▸ scope
    exact alternatives around enabled.alternatives
  · obtain ⟨m,valid⟩ := enabled.common
    exact ⟨m,(installation_equiv s e b m surface).mpr valid⟩

theorem paired_install (e : Effect roles) (enabled : Installable a s e)
    (scope : On a b s e.plan.packet.site.occurrence)
    (novel : ¬ Committed s e.plan) :
    ∃ other : Effect roles, At b s e.plan.packet.site.occurrence (install s other) ∧
      other.plan.packet.declaration = e.plan.packet.declaration ∧
      other.plan.packet.site.occurrence = e.plan.packet.site.occurrence ∧
      (GeneralNominalVersionedChildren232.emitted other.plan =
        GeneralNominalVersionedChildren232.emitted e.plan) ∧
      (install s other).core.erased.current.context.state.seed =
        (install s e).core.erased.current.context.state.seed ∧
      (install s other).core.erased.current.context.state.ordinary =
        (install s e).core.erased.current.context.state.ordinary ∧
      (∀ id, GeneralNominalState.Known (install s other).core.erased.current.context.state id ↔
        GeneralNominalState.Known (install s e).core.erased.current.context.state id) ∧
      ∀ m, Models (install s other) m ↔ Models (install s e) m := by
  obtain ⟨surface,valid⟩ := rebound_installable e enabled scope
  refine ⟨rebound e b surface,.install _ valid ?_,rfl,rfl,?_,rfl,rfl,fun _ => Iff.rfl,?_⟩
  · exact fun old => novel ((committed e.plan b (retagCtors surface)).mp old)
  · exact emitted e.plan b (retagCtors surface)
  · intro m
    exact installed_models s e b m surface enabled.snapshot_eq

end Yulang.GeneralRebaseRegistryInstallStep277
