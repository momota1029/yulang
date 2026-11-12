import Yulang.GeneralNominalJointCandidates

/-! Exact variable-child provenance from a retained recursive capture and its
recorded observation anchor. Repeated captures use the existing merged interval
correspondence; no arbitrary value fitting a broad interval becomes an origin.
Computing a complete annotated child list remains separate. -/
namespace Yulang.GeneralNominalCapturedChildOrigins

open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates

private theorem occurrence_entry (state : GeneralNominalState.State) (result : Report state)
    (name : Nat) (interval : GeneralSourceState.Interval) :
    interval ∈ GeneralNominalAllocation.occurrences (bindings state result) name ↔
      ∃ capture ∈ result.captures, capture.name = name ∧
        (state.base.source capture.bounds.1,state.base.source capture.bounds.2) = interval := by
  simp [GeneralNominalAllocation.occurrences,bindings,List.mem_map,List.mem_filter]

theorem captured_child_origin (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state))
    (model : GeneralNominalCommonBridge.Assignment) (models : BranchModels registry context root declaration checked bounds model)
    (capture : Capture context.state) (member : capture ∈ (report context declaration bounds).captures)
    (declared : capture.name ∈ declaration.inputNames) (origin : Origin) (recorded : capture.origin = some origin)
    (anchored : (origin,capture.bounds) ∈ (report context declaration bounds).anchors)
    (clause : Clause) (valid : clause.Signature roles) (index : Fin (roles clause.role).arity)
    (pattern : GeneralDeclarationPatterns.normalize (clause.arguments[index.val]'(by rw [valid.1]; exact index.isLt)) = .var capture.name) :
    let child := GeneralDeclarationDemands.childDemand declaration clause valid
      (GeneralNominalAllocation.capture context.state registry root.identity declaration.id
        (bindings context.state (report context declaration bounds)))
      (GeneralNominalAllocation.allocation context.state registry root.identity declaration.id clause)
    (∃ actual, Observes model origin actual) ∧
      ∀ actual, Observes model origin actual → GeneralNominalCaptureMerges.Fits model (child.arguments index) actual := by
  dsimp only
  have existsActual := (models.2.1.1 (origin,capture.bounds) anchored).1
  have present : (context.state.base.source capture.bounds.1,context.state.base.source capture.bounds.2) ∈
      GeneralNominalAllocation.occurrences (bindings context.state (report context declaration bounds)) capture.name :=
    (occurrence_entry ..).mpr ⟨capture,member,rfl,rfl⟩
  have nonempty : GeneralNominalAllocation.occurrences
      (bindings context.state (report context declaration bounds)) capture.name ≠ [] := by
    intro empty; rw [empty] at present; cases present
  refine ⟨existsActual,?_⟩
  intro actual seen
  apply (branch_child_correspondence registry context root declaration checked bounds model models capture.name
    declared nonempty actual clause valid index pattern).mpr
  intro interval present
  obtain ⟨other,otherMember,same,rfl⟩ := (occurrence_entry ..).mp present
  exact projected_capture_sound context.state (report context declaration bounds) model models.2.1
    capture other member otherMember same.symm origin recorded actual seen

end Yulang.GeneralNominalCapturedChildOrigins
