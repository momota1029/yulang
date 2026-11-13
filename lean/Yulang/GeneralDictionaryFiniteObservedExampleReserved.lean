import Yulang.GeneralDictionaryFiniteObservedExample

/-! A reserved output identity need not have an initial carrier slot. This
countermodel isolates why observed-target proofs cannot justify its installation.
The identity is reserved, not allocated by a transition in this module. -/
namespace Yulang.GeneralDictionaryFiniteObservedExampleReserved
open GeneralDictionaryFiniteObservedExample (interpretation model declaration registry checked)
open GeneralDeclarationExamples (roles)
open GeneralNominalMaterialization GeneralNominalRecursiveInspection
open CommonNominalFullCarrier

abbrev state : GeneralNominalState.State :=
  { GeneralDictionaryFiniteObservedExample.state with seed := 2, reserved := [2] }
abbrev request : Request := ⟨GeneralDictionaryFiniteObservedExample.request.pattern,2,.actual⟩
abbrev demand : GeneralSourceState.Demand roles := ⟨1,fun _ => (1,1),[⟨0,2⟩],by
  intro output member
  have same := List.mem_singleton.mp member
  subst output
  exact ⟨none,rfl⟩⟩
abbrev root : GeneralSourceDictionaries.Occurrence roles := ⟨156,demand⟩

theorem reserved_source : 2 ∈ GeneralNominalState.sources state := by
  simp [GeneralNominalState.sources,state]

theorem no_target_slot : ¬ ∃ slot : Fin state.base.slots, state.base.source slot = 2 := by
  rintro ⟨slot,same⟩
  have bound := slot.isLt
  change slot.val = 2 at same
  change slot.val < 2 at bound
  omega

theorem not_observed : ¬ GeneralDictionaryObservedFiniteRequests.Observed state interpretation [request] := by
  intro observed
  obtain ⟨slot,same,_⟩ := observed request (List.mem_singleton_self _)
  exact no_target_slot ⟨slot,same.symm⟩

theorem source_models : GeneralNominalState.Models state model :=
  GeneralDictionaryFiniteObservedExample.state_models

theorem actual_requests_exact (captures : GeneralNominalAllocation.Bindings) :
    requests state registry root declaration checked captures = [request] := by
  rw [GeneralDictionaryObservedScalarRequests.requests_root _ _ _ _ _ _ (by
    intro clause member; cases member)]
  rfl

abbrev context : GeneralNominalCandidates.Context := ⟨state,interpretation⟩
abbrev start := GeneralNominalSupport.initial context root

theorem initial_source : GeneralNominalSourceFormation.InitialSource registry context root where
  roles_agree := rfl
  metadata := GeneralDictionaryFiniteObservedExample.metadata
  linked := by
    constructor
    · intro index; constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ]
    · intro output member
      have same := List.mem_singleton.mp member
      subst output
      exact reserved_source
  intervals := fun _ _ _ => CommonNominalFullCarrier.subtype_refl _
  below_seed := by
    intro id member
    simp [GeneralNominalState.sources,List.ofFn_succ] at member
    rcases member with h | h | h | h | h <;> subst id <;> decide +kernel
  unallocated := rfl

theorem initial_reachable :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root start :=
  ⟨start,⟨context,initial_source,rfl⟩,.refl⟩

theorem tests_exact : (generated state interpretation [request]).tests =
    [(.source 2,.nominal 0 3),
     (.nominal (.source 2) 0 0,.scalar .int),
     (.nominal (.source 2) 0 1,.scalar .int),
     (.nominal (.source 2) 0 2,.scalar .int)] := by
  simp [generated,request,
    GeneralNominalInspection.translate,GeneralDeclarationPatterns.normalize,
    GeneralDeclarationPatterns.normalizeArgs,interpretation,
    GeneralDictionaryFiniteObservedExample.interpretation,GeneralNominalExamples.interpretation,
    GeneralDictionaryFiniteObservedExample.constructors,
    schema,schemas,Schema.append]

/-- Reserving an output identity does not constrain its value to the required
nominal. A valid initial model therefore refutes the generated request. -/
theorem initial_countermodel (capture : GeneralDeclarationDemands.Capture)
    (report : Report state) :
    GeneralNominalState.Models state model ∧
    ¬ Models state declaration capture report (generated state interpretation [request]) model := by
  refine ⟨source_models,?_⟩
  intro valid
  have member : (Origin.source 2,Test.nominal 0 3) ∈ (generated state interpretation [request]).tests := by
    rw [tests_exact]; simp
  have holds := (valid.1 _ member).2 _ (Observes.source 2)
  obtain ⟨arguments,_,same⟩ := holds
  have below : Subtype (.base .int) (nominal 0 arguments) := same.1
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.nominalHead 0 arguments.length) ⟨rfl,by simp⟩

end Yulang.GeneralDictionaryFiniteObservedExampleReserved
