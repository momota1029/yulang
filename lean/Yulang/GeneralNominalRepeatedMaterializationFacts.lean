import Yulang.GeneralNominalRepeatedBranchFacts
import Yulang.GeneralNominalLinearMaterializationFacts

/-! A repeated nominal binder's same-head associated output has no independent
materialization residual. Observed equality and allocation equations remain. -/
namespace Yulang.GeneralNominalRepeatedMaterializationFacts
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralNominalBinaryCaptureFacts GeneralNominalRepeatedCaptureFacts
open GeneralDeclarations CommonNominalFullCarrier

def headSchema (state : GeneralNominalState.State) (slot : Fin state.base.slots)
    (name binder : Nat) : GeneralNominalMaterialization.Schema where
  variables := [⟨binder,.nominal (.source (state.base.source slot)) name 0,.actual⟩,
    ⟨binder,.nominal (.source (state.base.source slot)) name 1,.actual⟩]
  tests := [(.source (state.base.source slot),.nominal name 2)]

theorem schema_models (state : GeneralNominalState.State) (registry : Registry) (invocation : Nat)
    (declaration : Declaration) (noOutputBinders : declaration.outputNames = [])
    (slot : Fin state.base.slots) (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals slot = some descriptor) (binder : Nat)
    (declared : binder ∈ declaration.inputNames)
    (left right : GeneralNominalInspection.Bounds state)
    (parameters : descriptor.arguments = [.type left,.type right])
    (model : GeneralNominalCommonBridge.Assignment) (models : GeneralNominalState.Models state model)
    (same : SameParameters model (state.base.source slot) descriptor.declaration.name)
    (merges : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.merges state registry invocation declaration
        (bindings state (captured state slot descriptor.declaration.name binder binder left right)))) :
    GeneralNominalMaterialization.Models state declaration
      (GeneralNominalAllocation.capture state registry invocation declaration.id
        (bindings state (captured state slot descriptor.declaration.name binder binder left right)))
      (captured state slot descriptor.declaration.name binder binder left right)
      (headSchema state slot descriptor.declaration.name binder) model := by
  have arg0 := nominal_argument_bounds state model models slot descriptor recorded 0 left (by rw [parameters]; rfl)
  have arg1 := nominal_argument_bounds state model models slot descriptor recorded 1 right (by rw [parameters]; rfl)
  have occurrences : GeneralNominalAllocation.occurrences
      (bindings state (captured state slot descriptor.declaration.name binder binder left right)) binder =
      [(state.base.source left.1,state.base.source left.2),(state.base.source right.1,state.base.source right.2)] := by
    simp [GeneralNominalAllocation.occurrences,bindings,captured]
  have merged (actual : Ty) := GeneralNominalCaptureMerges.capture_interval_exact state registry invocation declaration
    (bindings state (captured state slot descriptor.declaration.name binder binder left right)) model merges binder declared
    (by rw [occurrences]; simp) actual
  have fits0 (actual : Ty) (observed : Observes model (.nominal (.source (state.base.source slot)) descriptor.declaration.name 0) actual) :
      GeneralNominalCaptureMerges.Fits model
        ((GeneralNominalAllocation.capture state registry invocation declaration.id
          (bindings state (captured state slot descriptor.declaration.name binder binder left right))).inputs binder) actual := by
    apply (merged actual).mpr
    rw [occurrences]
    intro bounds member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact arg0.2 actual observed
    · obtain ⟨other,seen⟩ := arg1.1
      have fit := arg1.2 other seen
      have eq := same actual other observed seen
      exact ⟨subtype_trans fit.1 eq.2,subtype_trans eq.1 fit.2⟩
  have fits1 (actual : Ty) (observed : Observes model (.nominal (.source (state.base.source slot)) descriptor.declaration.name 1) actual) :
      GeneralNominalCaptureMerges.Fits model
        ((GeneralNominalAllocation.capture state registry invocation declaration.id
          (bindings state (captured state slot descriptor.declaration.name binder binder left right))).inputs binder) actual := by
    apply (merged actual).mpr
    rw [occurrences]
    intro bounds member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · obtain ⟨other,seen⟩ := arg0.1
      have fit := arg0.2 other seen
      have eq := same other actual seen observed
      exact ⟨subtype_trans fit.1 eq.1,subtype_trans eq.2 fit.2⟩
    · exact arg1.2 actual observed
  refine ⟨?_,?_,?_,?_⟩
  · intro test member
    have eq := List.mem_singleton.mp member
    subst test
    refine ⟨⟨_,.source _⟩,?_⟩
    intro actual observed
    cases observed
    obtain ⟨values,fits,equal⟩ := models.2.1 slot descriptor recorded
    refine ⟨values,?_,equal⟩
    rw [GeneralNominalLinearMaterializationFacts.fitsAll_length state.base model descriptor.arguments values fits,parameters]
    rfl
  · intro entry member
    simp only [headSchema,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · refine ⟨arg0.1,?_⟩
      intro actual observed
      simpa [GeneralNominalMaterialization.VariableHolds,noOutputBinders] using fits0 actual observed
    · refine ⟨arg1.1,?_⟩
      intro actual observed
      simpa [GeneralNominalMaterialization.VariableHolds,noOutputBinders] using fits1 actual observed
  · intro first ha last hb _ _ _ a b ha' hb'
    simp only [headSchema,List.mem_cons,List.not_mem_nil,or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact nominal_observation_unique model (.argument (.source (state.base.source slot)) descriptor.declaration.name 0) a b ha' hb'
    · exact same a b ha' hb'
    · exact ⟨(same b a hb' ha').2,(same b a hb' ha').1⟩
    · exact nominal_observation_unique model (.argument (.source (state.base.source slot)) descriptor.declaration.name 1) a b ha' hb'
  · intro entry ha capture hb _ _ origin found a b ha' hb'
    simp only [headSchema,List.mem_cons,List.not_mem_nil,or_false] at ha
    simp only [captured,List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> cases Option.some.inj found
    · exact nominal_observation_unique model (.argument (.source (state.base.source slot)) descriptor.declaration.name 0) a b ha' hb'
    · exact same a b ha' hb'
    · exact ⟨(same b a hb' ha').2,(same b a hb' ha').1⟩
    · exact nominal_observation_unique model (.argument (.source (state.base.source slot)) descriptor.declaration.name 1) a b ha' hb'

/-- For a terminal declaration returning the repeated nominal head at the
same source, the entire branch has exactly the observed equality and fresh
merge-equation residuals. Materialization is proved, not a premise. -/
theorem branch_models_iff (context : Context) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (terminal : declaration.requirements = []) (equation : Equation)
    (associated : declaration.associated = [equation])
    (slot : Fin context.state.base.slots) (descriptor : GeneralNominalState.Descriptor context.state.base.slots)
    (recorded : context.state.nominals slot = some descriptor) (binder : Nat)
    (declared : binder ∈ declaration.inputNames)
    (left right : GeneralNominalInspection.Bounds context.state)
    (parameters : descriptor.arguments = [.type left,.type right])
    (query : GeneralNominalInspection.queries context.state context.interpretation declaration =
      [.nominal descriptor.declaration.name [.variables [binder],.variables [binder]]])
    (output : root.demand.outputs = [⟨equation.name,context.state.base.source slot⟩])
    (translated : GeneralNominalInspection.translate context.state.constructors context.interpretation
      (GeneralDeclarationPatterns.normalize equation.rhs) =
        .nominal descriptor.declaration.name [.variables [binder],.variables [binder]])
    (model : GeneralNominalCommonBridge.Assignment) :
    BranchModels registry context root declaration checked [(slot,slot)] model ↔
      GeneralNominalState.Models context.state model ∧
      SameParameters model (context.state.base.source slot) descriptor.declaration.name ∧
      PresenceNormalForm.All CommonNominalFullCarrier.model model
        (GeneralNominalAllocation.merges context.state registry root.identity declaration
          (bindings context.state (report context declaration [(slot,slot)]))) := by
  rw [GeneralNominalRepeatedBranchFacts.branch_models_iff_residual context registry root declaration
    checked slot descriptor recorded binder left right parameters query model]
  constructor
  · rintro ⟨models,same,merges,_⟩
    exact ⟨models,same,merges⟩
  · rintro ⟨models,same,merges⟩
    refine ⟨models,same,merges,?_⟩
    have generated_eq : generated registry context root declaration checked [(slot,slot)] =
        headSchema context.state slot descriptor.declaration.name binder := by
      unfold generated
      rw [GeneralNominalLinearMaterializationFacts.root_requests_exact context.state registry root declaration
        checked _ terminal equation associated slot output]
      simp [GeneralNominalMaterialization.generated,translated,GeneralNominalMaterialization.schema,
        GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.Schema.append,headSchema]
    rw [generated_eq]
    have calculated := report_exact context declaration slot descriptor recorded binder binder left right parameters query
    rw [calculated] at merges ⊢
    exact schema_models context.state registry root.identity declaration
      (GeneralNominalLinearMaterializationFacts.no_output_binders declaration checked terminal)
      slot descriptor recorded binder declared left right parameters model models same merges

end Yulang.GeneralNominalRepeatedMaterializationFacts
