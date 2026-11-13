import Yulang.GeneralDictionarySemanticCollapseSchema

/-! A terminal nested branch across certified-style descriptor replacement.
The single captured binder has point leaf bounds; outer interval precision may
improve and capture multiplicity drops. Named output schemas are replayed, not
assumed valid in the new context. No emitted children are claimed here. -/
namespace Yulang.GeneralDictionarySemanticCollapseBranch
open GeneralDictionarySemanticCollapse GeneralDictionarySemanticCollapseAllocation
open GeneralNominalReobservationSteps GeneralNominalRecursiveInspection
open GeneralNominalAllocation GeneralDeclarations GeneralNominalRecursiveCandidates
variable {roles : Roles.RoleDecls} {state : GeneralNominalSaturationState.State roles}
variable {revision : Revision state}

def currentContext (revision : Revision state) : Context := ⟨revision.snapshot,state.context.interpretation⟩
def oldRootReport (s : Shape revision) : Report state.context.state :=
 {beforeReport s with checked := (s.root,s.root) :: (beforeReport s).checked}
def newRootReport (s : Shape revision) : Report revision.snapshot :=
 {afterReport s with checked := (s.root,s.root) :: (afterReport s).checked}

theorem reports (s : Shape revision) (declaration : Declaration)
    (queries : GeneralNominalInspection.queries state.context.state state.context.interpretation declaration = [query s]) :
    report state.context declaration [(s.root,s.root)] = oldRootReport s ∧
    report (currentContext revision) declaration [(s.root,s.root)] = newRootReport s := by
  have newQueries : GeneralNominalInspection.queries revision.snapshot state.context.interpretation declaration = [query s] := queries
  constructor
  · simp [report,queries,inspectMany,before_exact,oldRootReport,beforeReport,Report.append]
  · simp [report,currentContext,newQueries,inspectMany,after_exact,newRootReport,afterReport,Report.append] <;> rfl

theorem terminal_requests (context : Context) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (captures : Bindings) (terminal : declaration.requirements = []) :
    GeneralNominalMaterialization.requests context.state registry root declaration checked captures =
      GeneralNominalMaterialization.rootRequests declaration root := by
  have empty : GeneralCanonicalChildOrder.canonicalEmit root.identity declaration checked
      (capture context.state registry root.identity declaration.id captures)
      (allocation context.state registry root.identity declaration.id) = [] := by
    apply List.eq_nil_of_length_eq_zero
    simp [GeneralCanonicalChildOrder.canonicalEmit,GeneralDeclarationDemands.emitAll,
      GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,terminal]
  simp only [GeneralNominalMaterialization.requests,empty,List.flatMap_nil,List.append_nil]

theorem branch (s : Shape revision) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (queries : GeneralNominalInspection.queries state.context.state state.context.interpretation declaration = [query s])
    (names : declaration.inputNames = [s.binder]) (terminal : declaration.requirements = [])
    (firstPoint : s.first.1 = s.first.2) (lastPoint : s.last.1 = s.last.2)
    (scope : ∀ entry ∈ (generated registry state.context root declaration checked [(s.root,s.root)]).variables,
      entry.name ∉ declaration.outputNames → entry.name = s.binder)
    (model : GeneralNominalCommonBridge.Assignment)
    (old : BranchModels registry state.context root declaration checked [(s.root,s.root)] model)
    (current : GeneralNominalState.Models revision.snapshot model) :
    BranchModels registry (currentContext revision) root declaration checked [(s.root,s.root)] model := by
  have reports := reports s declaration queries
  have projection : ProjectionModels state.context.state
      (inspect state.context.state (query s) (s.root,s.root) none) model := by
    rw [before_exact]
    have h := old.2.1
    rw [reports.1] at h
    exact h
  have oldProp := (GeneralNominalState.extend_models ..).mp old.1 |>.1
  change GeneralNominalState.Models (propagate state.context.state registry root.identity declaration
    (bindings state.context.state (report state.context declaration [(s.root,s.root)]))) model at oldProp
  rw [reports.1] at oldProp
  have prop : GeneralNominalState.Models (propagate state.context.state registry root.identity declaration
    (bindings state.context.state (inspect state.context.state (query s) (s.root,s.root) none))) model := by
    rw [before_exact]; exact oldProp
  have newProp := current_propagation s registry root.identity declaration model names prop current
  refine ⟨?_,?_,?_⟩
  · unfold privateState
    rw [reports.2]
    apply (GeneralNominalState.extend_models ..).mpr
    constructor
    · rw [after_exact] at newProp
      exact newProp
    · intro atom member
      unfold selfChecks at member
      obtain ⟨bounds,inside,rfl⟩ := List.mem_map.mp member
      have point : bounds.1 = bounds.2 := by
        change bounds ∈ [(s.root,s.root),(s.root,s.root),(s.lower,s.lower),s.first] at inside
        rcases List.mem_cons.mp inside with rfl | inside
        · rfl
        rcases List.mem_cons.mp inside with rfl | inside
        · rfl
        rcases List.mem_cons.mp inside with rfl | inside
        · rfl
        have eq := List.mem_singleton.mp inside
        subst bounds
        exact firstPoint
      change CommonNominalFullCarrier.Subtype (model ((currentContext revision).state.base.source bounds.1)).1
        (model ((currentContext revision).state.base.source bounds.2)).1
      rw [point]
      exact CommonNominalFullCarrier.subtype_refl _
  · rw [reports.2]
    have h := current_projection s model current projection
    rw [after_exact] at h
    exact h
  · have sameSchema : generated registry (currentContext revision) root declaration checked [(s.root,s.root)] =
        generated registry state.context root declaration checked [(s.root,s.root)] := by
      unfold generated
      rw [terminal_requests _ _ _ _ _ _ terminal,terminal_requests _ _ _ _ _ _ terminal]
      rfl
    have materialized := old.2.2
    rw [reports.1] at materialized
    have materialized' : GeneralNominalMaterialization.Models state.context.state declaration
        (GeneralDictionarySemanticCollapseSchema.oldCapture s registry root.identity declaration)
        (inspect state.context.state (query s) (s.root,s.root) none)
        (generated registry state.context root declaration checked [(s.root,s.root)]) model := by
      unfold GeneralDictionarySemanticCollapseSchema.oldCapture
      rw [before_exact]
      exact materialized
    have result := GeneralDictionarySemanticCollapseSchema.replay s registry root.identity declaration
      (generated registry state.context root declaration checked [(s.root,s.root)]) model
      (by simp [names]) scope projection firstPoint lastPoint prop materialized'
    rw [sameSchema,reports.2]
    unfold GeneralDictionarySemanticCollapseSchema.newCapture at result
    rw [after_exact] at result
    exact result
end Yulang.GeneralDictionarySemanticCollapseBranch
