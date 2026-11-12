import Yulang.GeneralDictionaryVariableTree

/-! Materialization of finite scalar requests at already observed source slots.
The certificate is syntactic/source-observational, not generated Models. -/
namespace Yulang.GeneralDictionaryObservedScalarRequests
open GeneralDeclarations GeneralNominalMaterialization GeneralNominalRecursiveInspection
open CommonNominalFullCarrier

/-- Targets are actual existing source slots with checked scalar observations.
The requests may originate from named outputs or compound child arguments. -/
def Observed (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (requests : List Request) : Prop :=
  ∀ request ∈ requests, ∃ slot : Fin state.base.slots, ∃ base : Inference.Base,
    request.target = state.base.source slot ∧ state.view.heads slot = .scalar base ∧
    GeneralNominalInspection.translate state.constructors interpretation
      (GeneralDeclarationPatterns.normalize request.pattern) = .scalar base

theorem source_scalar (state : GeneralNominalState.State)
    (slot : Fin state.base.slots) (base : Inference.Base)
    (observed : state.view.heads slot = .scalar base)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models state model) :
    Equivalent (model (state.base.source slot)).1 (.base base) := by
  have checked := GeneralNominalState.normalized_models state model valid slot (.base base)
    (by simp [observed,GeneralNormalizedObservation.Head.term])
  exact checked

theorem generated_shape (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (requests : List Request)
    (observed : Observed state interpretation requests) :
    (generated state interpretation requests).variables = [] ∧
    (generated state interpretation requests).unknown = false ∧
    ∀ test ∈ (generated state interpretation requests).tests,
      ∃ slot : Fin state.base.slots, ∃ base : Inference.Base,
        test = (.source (state.base.source slot),Test.scalar base) ∧
        state.view.heads slot = .scalar base := by
  induction requests with
  | nil => simp [generated]
  | cons request rest ih =>
    obtain ⟨slot,base,target,head,query⟩ := observed request (by simp)
    have tail := ih (fun r member => observed r (by simp [member]))
    simp only [generated,List.map_cons,List.foldr_cons,query,schema,Schema.append]
    change [] ++ (generated state interpretation rest).variables = [] ∧
      (false || (generated state interpretation rest).unknown) = false ∧ _
    refine ⟨by simpa using tail.1,by simpa using tail.2.1,?_⟩
    intro test member
    simp only [List.mem_append,List.mem_singleton] at member
    rcases member with rfl | old
    · exact ⟨slot,base,by rw [target],head⟩
    · exact tail.2.2 test old

/-- Variable-only where clauses leave the named root requests intact. -/
theorem requests_root (state : GeneralNominalState.State) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (captures : GeneralNominalAllocation.Bindings)
    (variables : GeneralDictionaryVariableRequirements.VariableClauses declaration) :
    requests state registry root declaration checked captures = rootRequests declaration root := by
  unfold requests
  have empty : (GeneralCanonicalChildOrder.canonicalEmit root.identity declaration checked
      (GeneralNominalAllocation.capture state registry root.identity declaration.id captures)
      (GeneralNominalAllocation.allocation state registry root.identity declaration.id)).flatMap emissionRequests = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro emission member
    unfold GeneralCanonicalChildOrder.canonicalEmit GeneralDeclarationDemands.emitAll at member
    obtain ⟨clause,_,rfl⟩ := List.mem_map.mp member
    have present : clause.val ∈ declaration.requirements :=
      (GeneralCanonicalChildOrder.canonicalRequirements_perm declaration.requirements).mem_iff.mpr clause.property
    exact GeneralDictionaryVariableRequirements.emission_empty _ _ _ _ _ _
      (variables clause.val present).1 (variables clause.val present).2
  rw [empty,List.append_nil]

/-- Arbitrary finite scalar equations hold in every source model. There are
no generated-variable constraints to omit: their absence is proved above. -/
theorem generated_models (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (requests : List Request)
    (observed : Observed state interpretation requests)
    (declaration : Declaration) (capture : GeneralDeclarationDemands.Capture)
    (report : Report state) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state model) :
    Models state declaration capture report (generated state interpretation requests) model := by
  have shape := generated_shape state interpretation requests observed
  refine ⟨?_,?_,?_,?_⟩
  · intro test member
    obtain ⟨slot,base,rfl,head⟩ := shape.2.2 test member
    refine ⟨⟨_,.source _⟩,?_⟩
    intro actual observation
    cases observation
    exact source_scalar state slot base head model valid
  · intro entry member; rw [shape.1] at member; cases member
  · intro first member; rw [shape.1] at member; cases member
  · intro entry member; rw [shape.1] at member; cases member
end Yulang.GeneralDictionaryObservedScalarRequests
