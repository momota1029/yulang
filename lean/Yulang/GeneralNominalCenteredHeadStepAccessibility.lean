import Yulang.GeneralNominalCenteredHeadStepEnumeration

/-! Ground point sources supply the finite cover for every successor step.
The theorem covers the unrestricted repaired relation and its effect ledger. -/
namespace Yulang.GeneralNominalCenteredHeadStepAccessibility
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadStepProgress GeneralNominalCenteredHeadStepTrace
open GeneralNominalCenteredHeadStepAncestry GeneralNominalCenteredHeadStepEnumeration
open GeneralNominalActualTraceSupport (pool)
open GeneralNominalOccurrenceEnumeration (basis)
open GeneralNominalSharedBudget (Signature Represents)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

def finiteCover (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit) : FiniteCover registry root (initial context root) where
  signatures := (GeneralNominalPacketCodes.codes context registry (GeneralNominalOccurrenceEnumeration.checkedFor checked source)
    (basis checked source limit) (pool registry context root limit)).map (GeneralNominalPacketCodes.signature context)
  sources := pool registry context root limit
  occurrences := basis checked source limit
  installs := by
    intro state path plan support generated enabled novel
    have registrySame := enabled.frame.registry_eq
    have parent := sites_enumerated checked source bound path plan.packet.site enabled.frame.raw_recorded
    have config := configuration_trace path
    rw [← enabled.frame.context_eq] at config
    have listed : ∀ slot, plan.packet.context.state.base.source slot ∈ pool registry context root limit := by
      rw [enabled.frame.context_eq]
      exact slot_pool source bound path
    have visible : plan.packet.declaration ∈ plan.packet.registry.declarations := by
      simpa only [registrySame] using enabled.frame.visible
    have packetChecked : ∀ declaration ∈ plan.packet.registry.declarations,
        DeclarationChecked plan.packet.registry.constructors roles declaration := by
      rw [registrySame]; exact GeneralNominalOccurrenceEnumeration.checkedFor checked source
    have codeMember := GeneralNominalPacketCodes.encoded_member context plan.packet packetChecked parent visible
      enabled.frame.located listed config.2.1.symm config.2.2.symm
    have represented := GeneralNominalPacketCodes.encode_represents context plan.packet config.1.symm config.2.1.symm config.2.2.symm
    refine ⟨_,?_,represented⟩
    have mapped := (List.mem_map (f := GeneralNominalPacketCodes.signature context)).mpr ⟨_,codeMember,rfl⟩
    subst registry
    exact mapped
  source_mem := fun _ path => (source_pool source bound path).1
  slot_mem := fun _ path => slot_pool source bound path
  center_mem := by
    intro state path site member
    obtain ⟨raw,present,same⟩ := centered_site_registered path site member
    exact same ▸ sites_enumerated checked source bound path raw present

theorem ground_cover : GroundCover roles := by
  intro registry checked context root labels source point ground
  exact ⟨finiteCover checked source (installed_depth_bound point ground)⟩

theorem ground_point_root_accessible (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root labels) :
    Acc (fun next current => Step registry root current next) (initial context root) :=
  accessible_of_cover (finiteCover checked source (installed_depth_bound point ground))

theorem progress (registry : Registry)
    (checked : (GeneralNominalCenteredHeadStepBoundary.boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles)
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadStepBoundary.boundary roles) registry root state) :
    Acc (fun next current => Step registry root current next) state :=
  GeneralNominalCenteredHeadStepProgress.progress ground_cover registry checked state root reachable

theorem terminal (registry : Registry)
    (checked : (GeneralNominalCenteredHeadStepBoundary.boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles)
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadStepBoundary.boundary roles) registry root state) :
    ∃ final, B4Target.Steps (Step registry root) state final ∧
      (∀ next, ¬ Step registry root final next) ∧ Stable registry final root ∧
      (∀ child, GeneralNominalSaturationState.Generated final.core.erased.current root child → Stable registry final child) ∧
      ∀ model, Models final model → Models state model := by
  obtain ⟨final,path,halted⟩ := GeneralNominalActualBoundary.terminal_of_accessible (progress registry checked state root reachable)
  have stable := closure halted
  exact ⟨final,path,halted,stable.1,stable.2,steps_models path⟩

end Yulang.GeneralNominalCenteredHeadStepAccessibility
