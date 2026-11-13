import Yulang.GeneralNominalPeelingExamples

/-! A family of real point sources with arbitrarily deep list inputs. The
source graph records every nominal argument and an ordinary equation fixes
the last source to Int. No invocation rank is stored in the source data. -/
namespace Yulang.GeneralNominalPeelingSources
open GeneralNominalPeelingOrigins GeneralNominalPeelingAccessibility
open GeneralDeclarationExamples (roles)
open GeneralNominalExamples (registry displayRoot)
open CommonNominalFullCarrier
open GeneralNominalAllocationSupport
open GeneralNominalActualInspectionSteps (Step)

def source (length : Nat) : GeneralNominalState.State :=
  GeneralNominalState.extend (GeneralNominalOutputGrowthModels.source length) []
    (GeneralNominalAllocation.equations (length+1) (.base .int))

def context (length : Nat) : GeneralNominalCandidates.Context :=
  ⟨source length,GeneralNominalExamples.interpretation⟩

theorem source_models (length : Nat) (model : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalState.Models (source length) model ↔
      GeneralNominalOutputGrowth.PrefixModels length model ∧ Equivalent (model (length+1)).1 (.base .int) := by
  unfold source
  rw [GeneralNominalState.extend_models,GeneralNominalOutputGrowthModels.source_models,
    GeneralNominalCaptureMerges.equations_exact]
  rfl

theorem ground_slots (length : Nat) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (source length) model) (remaining : Nat)
    (bounded : remaining ≤ length+1) :
    Equivalent (model (length+1-remaining)).1 (tower 0 .int remaining) := by
  have facts := (source_models length model).mp valid
  induction remaining with
  | zero => simpa only [Nat.sub_zero,tower] using facts.2
  | succ remaining ih =>
    have previous := ih (by omega)
    have position : length+1-(remaining+1) ≤ length := by omega
    have next : length+1-(remaining+1)+1 = length+1-remaining := by omega
    have linked := facts.1 _ position
    rw [next] at linked
    have tail := GeneralNominalPeelingExamples.nominal_congr previous 0
    exact ⟨subtype_trans linked.1 tail.1,subtype_trans tail.2 linked.2⟩

theorem ground (length : Nat) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (source length) model) :
    Equivalent (model 0).1 (tower 0 .int (length+1)) := by
  simpa only [Nat.sub_self] using ground_slots length model valid (length+1) (Nat.le_refl _)

theorem source_inhabited (length : Nat) : ∃ model, GeneralNominalState.Models (source length) model := by
  refine ⟨GeneralNominalOutputGrowth.finiteModel length,(source_models length _).mpr
    ⟨GeneralNominalOutputGrowth.finite_prefix_models length,?_⟩⟩
  change Equivalent (GeneralNominalOutputGrowth.tower (length+1-(length+1))) (.base .int)
  rw [Nat.sub_self]
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem source_support (length : Nat) : GeneralNominalState.sources (source length) ⊆
    GeneralNominalState.sources (GeneralNominalOutputGrowthModels.source length) := by
  apply extend_sources _ [] _ (fun _ member => member) (by intro _ impossible; cases impossible)
  intro atom member
  exact equation_sources (length+1) (.base .int)
    (GeneralNominalOutputGrowthModels.source_member length ⟨length+1,by omega⟩)
    (by intro _ impossible; cases impossible) atom member

theorem initial_source (length : Nat) :
    GeneralNominalSourceFormation.InitialSource registry (context length) displayRoot := by
  refine ⟨rfl,⟨rfl,GeneralDictionarySupportRecursiveExample.initial_source.metadata.2⟩,?_,
    (by intro _ _ _; exact subtype_refl _),?_,rfl⟩
  · constructor
    · intro index
      have known := slot_source (source length) (⟨0,by change 0 < length+2; omega⟩ : Fin (source length).base.slots)
      exact ⟨known,known⟩
    · intro output impossible; cases impossible
  · intro identity member
    exact (GeneralNominalOutputGrowthModels.initial_source length).below_seed identity (source_support length member)

theorem point_source (length : Nat) : GeneralNominalActualBudget.PointSource (context length) displayRoot := by
  constructor
  · intro bounds impossible; cases impossible
  · intro slot descriptor recorded bounds member
    change (if h : slot.val ≤ length then some (GeneralNominalOutputGrowthModels.descriptor length slot h) else none) = some descriptor at recorded
    split at recorded
    · cases Option.some.inj recorded
      cases List.mem_singleton.mp member
      rfl
    · cases recorded
  · intro slot descriptor recorded bounds member
    change (if h : slot.val ≤ length then some (GeneralNominalOutputGrowthModels.descriptor length slot h) else none) = some descriptor at recorded
    split at recorded
    · cases Option.some.inj recorded
      cases List.mem_singleton.mp member
    · cases recorded
  · intro index; rfl

theorem depth_bound (length : Nat) :
    GeneralNominalInvocationAncestry.InstalledDepthBound registry (context length) displayRoot (length+1) :=
  installed_depth_bound (GeneralNominalPeelingExamples.peeling (context length) rfl rfl)
    (initial_source length) rfl (by rfl) (ground length)

theorem display_accessible (length : Nat) :
    Acc (fun next current => Step registry displayRoot current next)
      (GeneralNominalSupport.initial (context length) displayRoot) :=
  GeneralNominalActualBudget.accessible_of_installed_depth_bound GeneralNominalExamples.registry_checked
    (initial_source length) (depth_bound length)

end Yulang.GeneralNominalPeelingSources
