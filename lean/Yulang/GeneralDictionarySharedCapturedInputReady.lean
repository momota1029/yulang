import Yulang.GeneralDictionarySharedCapturedRefresh
import Yulang.GeneralDictionarySharedTrustTransport
namespace Yulang.GeneralDictionarySharedCapturedInputReady
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSharedSupport GeneralNominalSharedCaptures
open GeneralNominalOriginTerms GeneralNominalRecursiveInspection
open GeneralDictionarySharedCapturedTargets GeneralDictionarySharedCapturedModel
open GeneralDictionarySharedCapturedGuards GeneralDictionarySharedCapturedInstallable
open GeneralDictionarySharedCapturedInstallation GeneralDictionarySharedCapturedRefresh
open GeneralDictionarySharedOutputBinderScope CommonNominalFullCarrier

local instance : NeZero source.base.slots := ⟨by change 3 ≠ 0; omega⟩
abbrev input : Fact GeneralDeclarationExamples.roles := .inputs packet []

theorem old_guard : GeneralNominalSupportChoices.PacketGuard start packet [] :=
  ⟨⟨decisions.1,decisions.2.1,
    decisions.2.2 capturedProposal (by simp) rfl [(⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩)] located⟩,decisions⟩

theorem facts : after.facts = [input,.outputs packet []] := by
  change GeneralNominalSupportChoices.installedFacts start packet ++ [] = _
  rw [GeneralNominalSupportChoices.empty_alternatives start packet rfl old_guard]
  rfl

theorem input_trusted : Trusted after [input] [] := by
  apply Trusted.input packet [] Trusted.source
  · rw [facts]; exact List.mem_cons_self
  · intro slot read test observation head assignment valid
    exact GeneralCanonicalObservations.recorded_sound packet.context.state assignment valid.1 (head_recorded head)
  · intro entry member actual
    have zero : entry.name = 0 := by
      rw [input_schema] at member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl <;> rfl
    have cap : (⟨0,(2,2),some origin⟩ : Capture source) ∈ (GeneralNominalPacketSupport.report packet).captures := by
      rw [captures]; simp
    have anchor : (origin,(2,2)) ∈ (GeneralNominalPacketSupport.report packet).anchors := by
      rw [report_exact]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
    refine ⟨origin,⟨?_,?_⟩,?_⟩
    · refine ⟨⟨0,(2,2),some origin⟩,?_,zero.symm,rfl⟩
      rw [inherited]; exact List.mem_singleton_self _
    · intro captured included same
      rw [inherited] at included
      cases List.mem_singleton.mp included
      refine ⟨origin,rfl,?_⟩
      intro assignment valid
      have seen := valid.2.2.1.1 _ anchor
      refine ⟨seen.1,seen.1,?_⟩
      intro a b one two
      exact valid.2.2.1.2.2.2 _ cap _ cap rfl origin origin rfl rfl a b one two
    · intro assignment valid inputs
      exact retained_use inputs.2.2 member actual ⟨0,(2,2),some origin⟩ cap zero rfl
        (inputs.2.1.1 _ anchor).1

theorem refreshed_trusted : Trusted refreshed [input] [] :=
  GeneralDictionarySharedTrustTransport.trusted_at GeneralDictionarySharedCapturedRefresh.step.choose_spec.2 input_trusted
private theorem nominal_congr (a b : Ty) (eq : Equivalent a b) :
    Equivalent (nominal 0 [.inl a]) (nominal 0 [.inl b]) := by
  constructor
  all_goals
    apply (nominal_regular_invariant_exact ..).mpr
    refine ⟨rfl,rfl,?_⟩
    intro i x y one two
    have zero : i = 0 := by
      have h := (List.getElem?_eq_some_iff.mp one).1
      simp only [List.length_cons,List.length_nil] at h
      omega
    subst i
    cases one; cases two
  · exact eq
  · exact ⟨eq.2,eq.1⟩

/-- Shape tests and the actual variable use together determine a point
nominal descriptor; the finite witness is not used here. -/
theorem input_endpoint_equation (assignment : GeneralNominalCommonBridge.Assignment)
    (inputs : GeneralNominalPacketSupport.Inputs packet assignment) (endpoint : Nat) (which : endpoint = lo ∨ endpoint = hi) :
    Equivalent (assignment endpoint).1 (nominal 0 [.inl (assignment 2).1]) := by
  have shape : Test.Holds (.nominal 0 1) (assignment endpoint).1 := by
    have tested : (.source endpoint,Test.nominal 0 1) ∈ (GeneralNominalPacketSupport.inputSchema packet).tests := by
      rw [input_schema]
      rcases which with rfl | rfl <;> simp
    exact (inputs.2.2.1 _ tested).2 _ (.source endpoint)
  have use : (⟨0,.nominal (.source endpoint) 0 0,.actual⟩ : GeneralNominalMaterialization.Use) ∈
      (GeneralNominalPacketSupport.inputSchema packet).variables := by
    rw [input_schema]
    rcases which with rfl | rfl <;> simp
  obtain ⟨actual,seen⟩ := (inputs.2.2.2.1 _ use).1
  have same := GeneralNominalSharedCaptures.point_use inputs.2.2 use rfl
    (by simp [Declaration.outputNames]) capture_input
  have actualEq := same.2.2 actual (assignment 2).1 seen (.source 2)
  obtain ⟨args,size,equal⟩ := shape
  cases seen with
  | nominal previous observed found =>
    cases previous
    have invariant := (nominal_regular_invariant_exact _ _ _ _).mp (subtype_trans equal.2 observed.1)
    cases args with
    | nil => cases size
    | cons first tail =>
      have tailNil : tail = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at size; omega)
      subst tail
      have compared := invariant.2.2 0 first (.inl actual) rfl found
      cases first with
      | inr => cases compared
      | inl original =>
        have lifted := nominal_congr original (assignment 2).1
          ⟨subtype_trans compared.1 actualEq.1,subtype_trans actualEq.2 compared.2⟩
        exact ⟨subtype_trans equal.1 lifted.1,subtype_trans lifted.2 equal.2⟩

theorem lo_ready : GeneralNominalSharedSupport.ReadyAt refreshed lo := by
  let observation := GeneralCanonicalObservations.Observation.nominal base (3 : Fin 5) lastDescriptor
  have head : Head snapshot lo (.nominal 0 1) observation :=
    Head.nominal (snapshot := snapshot) 3 lastDescriptor rfl
  refine ⟨.nominal 0 1,observation,head,[input],[],refreshed_trusted,snapshot,observation,head,?_⟩
  intro assignment valid
  change GeneralNominalState.Denotes base assignment 3 lastDescriptor
  apply (GeneralNominalState.denotes_singleton_exact base assignment 3 2 lastDescriptor rfl).mpr
  exact input_endpoint_equation assignment (valid.2 input List.mem_cons_self) lo (Or.inl rfl)

theorem hi_ready : GeneralNominalSharedSupport.ReadyAt refreshed hi := by
  let observation := GeneralCanonicalObservations.Observation.nominal base (4 : Fin 5) lastDescriptor
  have head : Head snapshot hi (.nominal 0 1) observation :=
    Head.nominal (snapshot := snapshot) 4 lastDescriptor rfl
  refine ⟨.nominal 0 1,observation,head,[input],[],refreshed_trusted,snapshot,observation,head,?_⟩
  intro assignment valid
  change GeneralNominalState.Denotes base assignment 4 lastDescriptor
  apply (GeneralNominalState.denotes_singleton_exact base assignment 4 2 lastDescriptor rfl).mpr
  exact input_endpoint_equation assignment (valid.2 input List.mem_cons_self) hi (Or.inr rfl)

end Yulang.GeneralDictionarySharedCapturedInputReady
