import Yulang.GeneralDictionaryGroundCopy218Install
import Yulang.GeneralNominalVersionedMixedSourceBoundary234
import Yulang.GeneralNominalVersionedConservative231
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
/-! Initial-source and nonterminal parent-packet port for regression 218.
This is not yet an operational install path or a completed child rejection. -/
namespace Yulang.GeneralDictionaryMixedGround218Packet234
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryGroundCopy218Install
open GeneralNominalVersionedPlans231
open GeneralNominalCenters
open CommonNominalFullCarrier

noncomputable abbrev initial := GeneralNominalVersionedJournal232.initial context root

theorem initial_source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial sourceRegistry root initial :=
  ⟨start,GeneralDictionaryGroundCopy218Source.initial_source,rfl⟩

theorem reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) sourceRegistry root initial :=
  ⟨initial,initial_source,.refl⟩

theorem initial_model : GeneralNominalVersionedJournal232.Models initial model :=
  (GeneralNominalVersionedJournal232.lift_models start model).mpr start_model

theorem capture (name : Nat) (member : name = 0 ∨ name = 1) :
    (GeneralNominalVersionedFrame231.capture packet).inputs name = (2,3) := by
  rcases member with rfl | rfl
  all_goals
    unfold GeneralNominalVersionedFrame231.capture GeneralNominalVersionedFrame231.frame
    rw [bindings_exact]
    rfl

theorem ordinary : Ordinary packet model := by
  refine ⟨packet_models.2.1.1.1,?_,packet_models.2.1.1.2.2⟩
  rw [bindings_exact]
  exact PresenceNormalForm.all_nil _ _

theorem head_schema : SchemaHolds plan plan.headSchema model := by
  have old := heads
  rw [GeneralDictionaryGroundCopy218Install.head_schema] at old ⊢
  unfold Plan.SchemaHolds at old
  unfold SchemaHolds
  simpa only [List.mem_cons,List.not_mem_nil,forall_eq_or_imp,forall_false,implies_true,and_true,ite_true,
    GeneralNominalVersionedFrame231.binder_eq] using old

theorem emitted_schema : emittedSchema plan =
    ⟨[⟨2,.lower,.variable 0⟩,⟨3,.upper,.variable 0⟩,
      ⟨2,.lower,.variable 1⟩,⟨3,.upper,.variable 1⟩],false⟩ := by
  unfold emittedSchema emittedRequests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,canonical_declaration]
  unfold GeneralNominalVersionedFrame231.capture GeneralNominalVersionedFrame231.frame
  rw [bindings_exact]
  rfl

theorem outputs : Outputs plan model := by
  unfold Outputs
  rw [emitted_schema]
  intro equation member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals
    change Equivalent _ _
    simp only [GeneralNominalCenteredHeadMatExpressions.value,variables]
    change Equivalent _ _
    first | rw [capture 0 (Or.inl rfl)] | rw [capture 1 (Or.inr rfl)]
    exact ⟨subtype_refl _,subtype_refl _⟩

theorem child_arguments_new (valid : clause.Signature roles) (i) :
    (GeneralNominalVersionedFrame231.childSite plan clause valid).occurrence.demand.arguments i = (2,3) := by
  change Fin 2 at i
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with rfl | rfl
  · change (GeneralNominalVersionedFrame231.capture packet).inputs 0 = _
    exact capture 0 (Or.inl rfl)
  · change (GeneralNominalVersionedFrame231.capture packet).inputs 1 = _
    exact capture 1 (Or.inr rfl)

theorem child_holds_new (valid : clause.Signature roles) :
    (GeneralNominalVersionedFrame231.childSite plan clause valid).Holds model := by
  intro i
  rw [child_arguments_new,GeneralNominalVersionedFrame231.childSite_center_eq]
  exact (child_arguments i) ▸ child_holds i

theorem packet_holds : Holds plan model := by
  refine ⟨source_model,⟨ordinary,packet_models.2.1.2.1,packet_models.2.1.2.2.1,?_,head_schema,?_,?_⟩,outputs⟩
  · intro name needed
    have member : name = 0 ∨ name = 1 := by
      rcases needed with member | ⟨c,member,within⟩
      · change name ∈ [0,1] at member; simpa using member
      · cases List.mem_singleton.mp member
        change name ∈ [0,1] at within; simpa using within
    rw [capture name member,GeneralNominalVersionedFrame231.binder_eq]
    exact (capture_exact name member) ▸ binders_fit name member
  · intro equation member _
    exact outputs equation member
  · intro c member valid
    cases List.mem_singleton.mp member
    rw [GeneralNominalVersionedPlans231.childSchema_eq]
    refine ⟨child_holds_new valid,?_⟩
    rw [child_schema]
    intro equation member
    rcases List.mem_cons.mp member with rfl | member
    · change Equivalent _ _
      simp only [GeneralNominalCenteredHeadMatExpressions.value,variables,GeneralNominalVersionedFrame231.binder_eq]
      exact ⟨subtype_refl _,subtype_refl _⟩
    · cases List.mem_singleton.mp member
      change Equivalent _ _
      simp only [GeneralNominalCenteredHeadMatExpressions.value,variables,GeneralNominalVersionedFrame231.binder_eq]
      exact ⟨subtype_refl _,subtype_refl _⟩
end Yulang.GeneralDictionaryMixedGround218Packet234
