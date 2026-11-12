import Yulang.GeneralNominalOutputGrowthRefresh
import Yulang.GeneralNominalFeedbackWellFounded

/-! Two failed installation measures on a real source-formed update: arbitrary
model denotations can remain equal, and the least finite input height is one
both before installation and for the ready emitted child after refresh.
These facts do not by themselves refute accessibility of the complete Step. -/
namespace Yulang.GeneralNominalOutputGrowthMeasures

open GeneralNominalOutputGrowth GeneralNominalOutputGrowthModels GeneralNominalOutputGrowthPackets
open GeneralNominalOutputGrowthRefresh
open GeneralNominalSaturationState CommonNominalFullCarrier

/-- Minimum height among finite unary nominal denotations in the entire model
set. The existence conjunct prevents empty model sets from yielding a minimum. -/
def MinimumHeight (models : GeneralNominalCommonBridge.Assignment → Prop) (source height : Nat) : Prop :=
  (∃ model, models model ∧ Equivalent (model source).1 (tower height)) ∧
    ∀ model, models model → ∀ depth, Equivalent (model source).1 (tower depth) → height ≤ depth

private theorem int_not_nominal (arguments : List Argument) :
    ¬ Subtype (.base .int) (nominal 0 arguments) := by
  intro below
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.nominalHead 0 arguments.length) ⟨rfl,by simp⟩

private theorem nonzero_height (model : GeneralNominalCommonBridge.Assignment) (source depth : Nat)
    (nominalHead : ∃ arguments, Equivalent (model source).1 (nominal 0 arguments))
    (height : Equivalent (model source).1 (tower depth)) : 1 ≤ depth := by
  cases depth with
  | zero =>
    obtain ⟨arguments,equal⟩ := nominalHead
    exact False.elim (int_not_nominal arguments (subtype_trans height.2 equal.1))
  | succ depth => omega

theorem initial_minimum (length : Nat) : MinimumHeight (Models (snapshot length)) length 1 := by
  constructor
  · refine ⟨finiteModel length,(snapshot_models length _).mpr (finite_prefix_models length),?_⟩
    have one : length+1-length = 1 := by omega
    change Equivalent (tower (length+1-length)) (tower 1)
    rw [one]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · intro model valid depth same
    exact nonzero_height model length depth
      ⟨[.inl (model (length+1)).1],(snapshot_models length model).mp valid length (Nat.le_refl _)⟩ same

theorem installed_child_minimum (length : Nat) : MinimumHeight (Models (installed length)) (length+1) 1 := by
  constructor
  · refine ⟨finiteModel (length+1),installed_models length,?_⟩
    have one : length+1+1-(length+1) = 1 := by omega
    change Equivalent (tower (length+1+1-(length+1))) (tower 1)
    rw [one]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · intro model valid depth same
    exact nonzero_height model (length+1) depth ⟨[.inl (model (output length)).1],
      packet_output_equation length model (valid.2.1 (packet length)
        (by simp [installed,GeneralNominalFeedbackSites.install]))⟩ same

theorem refreshed_child_minimum : MinimumHeight (Models refreshed) 1 1 := by
  have previous := installed_child_minimum 0
  exact ⟨by obtain ⟨model,valid,height⟩ := previous.1; exact ⟨model,(refresh_models model).mpr valid,height⟩,
    fun model valid depth height => previous.2 model ((refresh_models model).mp valid) depth height⟩

theorem minimum_unique (models : GeneralNominalCommonBridge.Assignment → Prop) (source first last : Nat)
    (one : MinimumHeight models source first) (two : MinimumHeight models source last) : first = last := by
  obtain ⟨model,valid,height⟩ := one.1
  obtain ⟨other,validOther,heightOther⟩ := two.1
  exact Nat.le_antisymm (one.2 other validOther last heightOther) (two.2 model valid first height)

theorem minimum_does_not_descend (first last : Nat)
    (before : MinimumHeight (Models (snapshot 0)) 0 first)
    (after : MinimumHeight (Models refreshed) 1 last) : ¬ last < first := by
  have one := minimum_unique _ _ _ _ before (initial_minimum 0)
  have two := minimum_unique _ _ _ _ after refreshed_child_minimum
  omega

theorem boundary_example_whereAccessible
    (evidence : GeneralNominalFeedbackBoundary.Evidence GeneralDeclarationExamples.roles) (length : Nat) :
    Acc (CommonRoleOutermostResolver.Child
      (B4TargetV3.Local (GeneralNominalFeedbackBoundary.boundary GeneralDeclarationExamples.roles evidence)
        registry (snapshot length))) (root length) := by
  have existing := fixed_snapshot_whereAccessible length
  generalize root length = demand at existing ⊢
  induction existing with
  | intro demand below ih =>
    refine Acc.intro demand ?_
    rintro child ⟨key,children,localRule,member⟩
    exact ih child ⟨key,children,
      (GeneralNominalFeedbackBoundary.local_correspondence _ evidence registry (snapshot length) demand _).mp localRule,
      member⟩

end Yulang.GeneralNominalOutputGrowthMeasures
