import Yulang.GeneralDictionaryRecordedBatchModels

/-! Assembly of variable-free request batches. Unlike arbitrary materialization
schemas, these have no cross-request variable equalities to check. -/
namespace Yulang.GeneralDictionaryRequestBatchAssembly
open GeneralNominalMaterialization

theorem shape_of_singletons (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (batch : List Request)
    (single : ∀ request ∈ batch,
      (generated state interpretation [request]).variables = [] ∧
      (generated state interpretation [request]).unknown = false) :
    (generated state interpretation batch).variables = [] ∧
    (generated state interpretation batch).unknown = false := by
  induction batch with
  | nil => exact ⟨rfl,rfl⟩
  | cons request rest ih =>
    have one := single request List.mem_cons_self
    have tail := ih (fun other present => single other (List.mem_cons_of_mem _ present))
    rw [GeneralDictionaryRecordedBatchModels.generated_cons]
    exact ⟨by simp [Schema.append,one.1,tail.1],by simp [Schema.append,one.2,tail.2]⟩

theorem variables_of_singletons (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (batch : List Request)
    (single : ∀ request ∈ batch, (generated state interpretation [request]).variables = []) :
    (generated state interpretation batch).variables = [] := by
  induction batch with
  | nil => rfl
  | cons request rest ih =>
    rw [GeneralDictionaryRecordedBatchModels.generated_cons]
    change _ ++ _ = []
    rw [single request List.mem_cons_self,
      ih (fun other present => single other (List.mem_cons_of_mem _ present))]
    rfl

theorem models_of_singletons (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (batch : List Request)
    (declaration : GeneralDeclarations.Declaration) (capture : GeneralDeclarationDemands.Capture)
    (report : GeneralNominalRecursiveInspection.Report state)
    (model : GeneralNominalCommonBridge.Assignment)
    (single : ∀ request ∈ batch,
      (generated state interpretation [request]).variables = [] ∧
      Models state declaration capture report (generated state interpretation [request]) model) :
    Models state declaration capture report (generated state interpretation batch) model := by
  induction batch with
  | nil => exact empty_models state declaration capture report model
  | cons request rest ih =>
    have one := single request List.mem_cons_self
    have tail := ih (fun other present => single other (List.mem_cons_of_mem _ present))
    have closed := variables_of_singletons state interpretation rest
      (fun other present => (single other (List.mem_cons_of_mem _ present)).1)
    rw [GeneralDictionaryRecordedBatchModels.generated_cons]
    refine ⟨?_,?_,?_,?_⟩
    · intro test member
      rcases List.mem_append.mp member with head | last
      · exact one.2.1 test head
      · exact tail.1 test last
    all_goals
      intro entry member
      change entry ∈ _ ++ _ at member
      rw [one.1,closed] at member
      cases member
end Yulang.GeneralDictionaryRequestBatchAssembly
