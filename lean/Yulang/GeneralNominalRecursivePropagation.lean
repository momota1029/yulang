import Yulang.GeneralNominalRecursiveCandidates
import Yulang.GeneralNominalProjectionPropagation

/-! The old projection compiler remains usable on nominal paths in the new
recursive report. Its ordinary atoms preserve all projection side conditions. -/
namespace Yulang.GeneralNominalRecursivePropagation

open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates

def Corresponds (state : GeneralNominalState.State) (report : Report state)
    (old : List (GeneralNominalProjections.Binding state)) : Prop :=
  ∀ binding ∈ old, ∃ captured ∈ report.captures,
    binding.name = captured.name ∧ binding.bounds = .type captured.bounds ∧
    captured.origin = some (embed binding.origin) ∧ (embed binding.origin,captured.bounds) ∈ report.anchors

theorem projection_compatible (state : GeneralNominalState.State) (report : Report state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : ProjectionModels state report model)
    (old : List (GeneralNominalProjections.Binding state)) (linked : Corresponds state report old) :
    GeneralNominalProjections.Compatible state model old := by
  constructor
  · intro binding member
    obtain ⟨captured,_,_,bounds,_,anchor⟩ := linked binding member
    obtain ⟨actual,seen⟩ := (valid.1 _ anchor).1
    refine ⟨.inl actual,recover_observation model binding.origin actual seen,?_⟩
    rw [bounds]
    exact (valid.1 _ anchor).2 actual seen
  · intro first one last two same
    obtain ⟨a,am,an,_,ao,aa⟩ := linked first one
    obtain ⟨b,bm,bn,_,bo,ba⟩ := linked last two
    obtain ⟨x,hx⟩ := (valid.1 _ aa).1
    obtain ⟨y,hy⟩ := (valid.1 _ ba).1
    exact ⟨.inl x,.inl y,recover_observation model first.origin x hx,recover_observation model last.origin y hy,
      valid.2.2.2 a am b bm (an.symm.trans (same.trans bn)) _ _ ao bo x y hx hy⟩

theorem branch_compiles (registry : GeneralDeclarations.Registry) (context : Context)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : GeneralDeclarations.Declaration)
    (checked : GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state)) (model : GeneralNominalCommonBridge.Assignment)
    (models : BranchModels registry context root declaration checked bounds model)
    (old : List (GeneralNominalProjections.Binding context.state))
    (linked : Corresponds context.state (report context declaration bounds) old) :
    ∃ atoms, GeneralNominalProjectionPropagation.compile context.state old = some atoms ∧
      GeneralNominalState.Models (GeneralNominalState.extend context.state [] atoms) model ∧
      GeneralNominalProjections.Compatible context.state model old := by
  have compatible := projection_compatible context.state _ model models.2.1 old linked
  obtain ⟨atoms,compiled,holds⟩ := GeneralNominalProjectionPropagation.compile_sound context.state model old compatible
  exact ⟨atoms,compiled,(GeneralNominalState.extend_models ..).mpr
    ⟨(branch_interval_sound _ _ _ _ _ _ _ models).1,holds⟩,compatible⟩

theorem existing_projection_preserved (registry : GeneralDeclarations.Registry) (context : Context)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : GeneralDeclarations.Declaration)
    (checked : GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state))
    (model : GeneralNominalCommonBridge.Assignment)
    (models : BranchModels registry context root declaration checked bounds model)
    (old : List (GeneralNominalProjections.Binding context.state))
    (linked : Corresponds context.state (report context declaration bounds) old) :
    GeneralNominalProjections.Models ⟨context.state,old⟩ model :=
  ⟨(branch_interval_sound _ _ _ _ _ _ _ models).1,projection_compatible context.state _ model models.2.1 old linked⟩

end Yulang.GeneralNominalRecursivePropagation
