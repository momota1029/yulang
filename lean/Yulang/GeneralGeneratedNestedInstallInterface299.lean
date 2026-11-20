import Yulang.GeneralGeneratedNestedPredictions299

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralGeneratedNestedInstallInterface299
open GeneralGeneratedNestedSource299 (root initial)
open GeneralGeneratedNestedInitial299 (actual_initial)
open GeneralGeneratedNestedPredictions299
open GeneralNominalExamples (registry)
open GeneralDeclarationExamples (roles)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedJournal232 (Effect Models)
open GeneralNominalVersionedMixedKernel234 (Installable Committed)
open GeneralNominalVersionedInstall232 (install installed_child)
open GeneralNominalVersionedFrame231 (children)
open GeneralNominalSaturationState (Generated)
open B4Target (Steps)

theorem root_edge {e : Effect roles} (shape : e.plan.packet = parentPacket) :
    e.plan.packet.site.occurrence = root ∧ children e.plan.packet = [middle] := by
  rw [shape]
  exact ⟨rfl,parent_children⟩

theorem first_not_committed {e : Effect roles} (shape : e.plan.packet = parentPacket) :
    ¬ Committed initial e.plan := by
  intro committed
  have impossible := committed.2 middle ((root_edge shape).2 ▸ List.mem_singleton_self _)
  cases impossible

theorem middle_generated {e : Effect roles} (shape : e.plan.packet = parentPacket) :
    Generated (install initial e).core.erased.current root middle := by
  obtain ⟨origin,child⟩ := root_edge shape
  have e01 := installed_child (state := initial) (effect := e) (child ▸ List.mem_singleton_self _)
  rw [origin] at e01
  exact .child .root e01

theorem only_first_edge {e : Effect roles} (shape : e.plan.packet = parentPacket) :
    (install initial e).core.erased.current.edges = [(root,middle)] := by
  change [] ++ GeneralNominalVersionedChildren232.edges e.plan = _
  unfold GeneralNominalVersionedChildren232.edges
  rw [(root_edge shape).1,(root_edge shape).2]
  rfl

theorem second_not_committed {e₁ e₂ : Effect roles} (shape : e₁.plan.packet = parentPacket)
    (focus : e₂.plan.packet.site.occurrence = middle)
    (target : children e₂.plan.packet = [terminal]) :
    ¬ Committed (install initial e₁) e₂.plan := by
  intro committed
  have eq := committed.2 terminal (target ▸ List.mem_singleton_self _)
  rw [focus,only_first_edge shape] at eq
  have impossible := (Prod.mk.inj (List.mem_singleton.mp eq)).1
  exact different_occurrences.1 (congrArg (fun q => q.identity) impossible.symm)

/-- No operational claim without both actual installability proofs.
Their states are sequential, not two certificates from the same snapshot. -/
theorem cascade {e₁ e₂ : Effect roles} (shape : e₁.plan.packet = parentPacket)
    (first : Installable compiled initial e₁)
    (focus : e₂.plan.packet.site.occurrence = middle)
    (target : children e₂.plan.packet = [terminal])
    (second : Installable compiled (install initial e₁) e₂) :
    Steps ((boundary roles).Step registry root) initial (install (install initial e₁) e₂) ∧
      B4TargetV8.Reachable (boundary roles) registry root (install (install initial e₁) e₂) ∧
      Generated (install (install initial e₁) e₂).core.erased.current root terminal ∧
      ∀ m, Models (install (install initial e₁) e₂) m → Models initial m := by
  have one : (boundary roles).Step registry root initial (install initial e₁) :=
    ⟨_,(root_edge shape).1.symm ▸ .root,.install e₁ first (first_not_committed shape)⟩
  have two : (boundary roles).Step registry root (install initial e₁)
      (install (install initial e₁) e₂) :=
    ⟨_,focus.symm ▸ middle_generated shape,.install e₂ second (second_not_committed shape focus target)⟩
  have track := Steps.tail (Steps.tail .refl one) two
  refine ⟨track,⟨initial,actual_initial,track⟩,?_,?_⟩
  · have kept : (root,middle) ∈
      (install (install initial e₁) e₂).core.erased.current.edges := by
      apply List.mem_append_left
      rw [only_first_edge shape]
      exact List.mem_singleton_self _
    have later := installed_child (state := install initial e₁) (effect := e₂)
      (target ▸ List.mem_singleton_self _)
    rw [focus] at later
    exact .child (.child .root kept) later
  · exact fun _ valid => GeneralNominalVersionedMixedSourceBoundary234.stepModels one
      (GeneralNominalVersionedMixedSourceBoundary234.stepModels two valid)

end Yulang.GeneralGeneratedNestedInstallInterface299
