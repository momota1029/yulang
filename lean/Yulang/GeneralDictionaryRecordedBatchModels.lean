import Yulang.GeneralDictionaryRecordedRequestModels

/-! Current request batches assembled from different recorded packets.
Coverage and variable-freedom remain explicit; initial output observations and
one common packet are not required. -/
namespace Yulang.GeneralDictionaryRecordedBatchModels
open GeneralNominalMaterialization GeneralNominalSaturationState
open GeneralDeclarations GeneralSourceDictionaries
variable {roles : Roles.RoleDecls}

/-- Syntactic provenance for every current request, possibly from different
historical packets. This is not a semantic validity assumption. -/
def Covered (state : State roles) (batch : List Request) : Prop :=
  ∀ request ∈ batch, ∃ packet ∈ state.packets,
    request ∈ requests packet.context.state packet.registry packet.site.occurrence
      packet.declaration packet.checked packet.bindings ∧
    (generated packet.context.state packet.context.interpretation [request]).variables = []

theorem covered_nil (state : State roles) : Covered state [] := by
  intro request member; cases member

theorem covered_append (state : State roles) (first last : List Request) :
    Covered state (first ++ last) ↔ Covered state first ∧ Covered state last := by
  simp only [Covered,List.mem_append,or_imp,forall_and]

theorem generated_cons (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (request : Request) (rest : List Request) :
    generated state interpretation (request :: rest) =
      (generated state interpretation [request]).append (generated state interpretation rest) := by
  simp [generated,Schema.append]

theorem reachable_shape (registry : Registry) (root : Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (batch : List Request) (covered : Covered state.current batch) :
    (generated state.current.context.state state.current.context.interpretation batch).variables = [] ∧
    (generated state.current.context.state state.current.context.interpretation batch).unknown = false := by
  induction batch with
  | nil => exact ⟨rfl,rfl⟩
  | cons request rest ih =>
    obtain ⟨packet,recorded,member,closed⟩ := covered request (List.mem_cons_self)
    have currentClosed : (generated state.current.context.state state.current.context.interpretation [request]).variables = [] := by
      rw [GeneralDictionaryRecordedRequestModels.reachable_coherent registry root state reachable packet recorded [request]]
      exact closed
    have currentKnown := GeneralDictionaryRecordedRequestModels.reachable_subset_known registry root state reachable packet recorded [request]
      (by intro other present; have same := List.mem_singleton.mp present; subst other; exact member)
    have tail := ih (fun other present => covered other (List.mem_cons_of_mem _ present))
    rw [generated_cons]
    exact ⟨by simp [Schema.append,currentClosed,tail.1],by simp [Schema.append,currentKnown,tail.2]⟩

theorem reachable_models (registry : Registry) (root : Occurrence roles)
    (state : GeneralNominalSupport.Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (batch : List Request) (covered : Covered state.current batch)
    (declaration : Declaration) (capture : GeneralDeclarationDemands.Capture)
    (report : GeneralNominalRecursiveInspection.Report state.current.context.state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    GeneralNominalMaterialization.Models state.current.context.state declaration capture report
      (generated state.current.context.state state.current.context.interpretation batch) model := by
  have closed := (reachable_shape registry root state reachable batch covered).1
  refine ⟨?_,?_,?_,?_⟩
  · induction batch with
    | nil => intro test member; cases member
    | cons request rest ih =>
      obtain ⟨packet,recorded,member,free⟩ := covered request List.mem_cons_self
      have one := GeneralDictionaryRecordedRequestModels.recorded_variableFree_models state.current
        (GeneralDictionaryRecordedRequestModels.reachable_coherent registry root state reachable) packet recorded [request]
        (by intro other present; have same := List.mem_singleton.mp present; subst other; exact member)
        free declaration capture report model valid
      intro test present
      rw [generated_cons] at present
      change test ∈ _ ++ _ at present
      rcases List.mem_append.mp present with head | tail
      · exact one.1 test head
      · exact ih (fun other present => covered other (List.mem_cons_of_mem _ present))
          (reachable_shape registry root state reachable rest (fun other present => covered other (List.mem_cons_of_mem _ present))).1 test tail
  · intro entry member; rw [closed] at member; cases member
  · intro entry member; rw [closed] at member; cases member
  · intro entry member; rw [closed] at member; cases member
end Yulang.GeneralDictionaryRecordedBatchModels
