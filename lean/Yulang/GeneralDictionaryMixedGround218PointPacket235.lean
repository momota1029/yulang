import Yulang.GeneralDictionaryMixedGround218Point235
import Yulang.GeneralDictionaryGroundCopy218SaturatedParent
import Yulang.GeneralDictionaryMixedGround218Packet234
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
namespace Yulang.GeneralDictionaryMixedGround218PointPacket235
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryGroundCopy218Install (declaration declaration_checked clause model)
open GeneralDictionaryMixedGround218Point235
open GeneralNominalCenters CommonNominalFullCarrier
open GeneralNominalVersionedPlans231
noncomputable abbrev plan := GeneralDictionaryGroundCopy218SaturatedParent.planFor allocated reserved ordinary
noncomputable abbrev packet := plan.packet

theorem context_eq : packet.context = point.core.erased.current.context := by
  change GeneralNominalCandidates.Context.mk _ interpretation = GeneralNominalCandidates.Context.mk _ interpretation
  exact congrArg (fun s => GeneralNominalCandidates.Context.mk s interpretation) point_snapshot.symm

theorem bindings_exact : packet.bindings = [(0,4,4),(1,5,5)] :=
  GeneralDictionaryGroundCopy218SaturatedParent.bindings_exact _ _ _

theorem capture (name : Nat) (member : name = 0 ∨ name = 1) :
    (GeneralNominalVersionedFrame231.capture packet).inputs name = (if name=0 then (4,4) else (5,5)) := by
  rcases member with rfl | rfl
  all_goals
    unfold GeneralNominalVersionedFrame231.capture GeneralNominalVersionedFrame231.frame
    rw [bindings_exact]
    rfl

theorem old_holds : GeneralNominalCenteredHeadMatStepPackets.Holds plan model := by
  refine ⟨?_,(GeneralDictionaryGroundCopy218SaturatedParent.inputs_same _ _ _ _).mpr
    GeneralDictionaryGroundCopy218Reinstall.packet_models.2.1,
    (GeneralDictionaryGroundCopy218SaturatedParent.outputs_same _ _ _ _).mpr
    GeneralDictionaryGroundCopy218Reinstall.packet_models.2.2⟩
  rw [context_eq]
  exact point_model.1.1

theorem emitted_schema : emittedSchema plan =
    ⟨[⟨4,.lower,.variable 0⟩,⟨4,.upper,.variable 0⟩,
      ⟨5,.lower,.variable 1⟩,⟨5,.upper,.variable 1⟩],false⟩ := by
  unfold emittedSchema emittedRequests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,GeneralDictionaryGroundCopy218Install.canonical_declaration]
  unfold GeneralNominalVersionedFrame231.capture GeneralNominalVersionedFrame231.frame
  rw [bindings_exact]
  rfl

theorem outputs (given : GeneralNominalCommonBridge.Assignment) : Outputs plan given := by
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

theorem head_schema : SchemaHolds plan plan.headSchema model := by
  have old := old_holds.2.1.2.2.2.2.1
  rw [GeneralDictionaryGroundCopy218SaturatedParent.head_schema_same,
    GeneralDictionaryGroundCopy218Reinstall.head_schema] at old ⊢
  unfold Plan.SchemaHolds at old
  unfold SchemaHolds
  simpa only [List.mem_cons,List.not_mem_nil,forall_eq_or_imp,forall_false,implies_true,and_true,ite_true,
    GeneralNominalVersionedFrame231.binder_eq] using old

theorem binder (name : Nat) : plan.binder name = GeneralDictionaryGroundCopy218Reinstall.newPlan.binder name :=
  GeneralDictionaryGroundCopy218SaturatedParent.binder_same _ _ _ name

theorem fit (name : Nat) (member : name=0 ∨ name=1) :
    GeneralNominalCaptureMerges.Fits model ((GeneralNominalVersionedFrame231.capture packet).inputs name)
      (model (GeneralNominalVersionedFrame231.binder plan name)).1 := by
  rw [capture name member,GeneralNominalVersionedFrame231.binder_eq,binder]
  rcases member with rfl | rfl
  · rw [GeneralDictionaryGroundCopy218Reinstall.binder_zero]; exact ⟨subtype_refl _,subtype_refl _⟩
  · rw [GeneralDictionaryGroundCopy218Reinstall.binder_one]; exact ⟨subtype_refl _,subtype_refl _⟩

theorem packet_holds : Holds plan model := by
  refine ⟨old_holds.1,⟨?_,old_holds.2.1.2.1,old_holds.2.1.2.2.1,?_,head_schema,?_,?_⟩,outputs model⟩
  · refine ⟨old_holds.2.1.1.1,?_,old_holds.2.1.1.2.2⟩
    rw [bindings_exact]
    exact PresenceNormalForm.all_nil _ _
  · intro name needed
    apply fit name
    rcases needed with member | ⟨c,member,within⟩
    · change name ∈ [0,1] at member; simpa using member
    · cases List.mem_singleton.mp member
      change name ∈ [0,1] at within; simpa using within
  · intro equation member _; exact outputs model equation member
  · intro c member valid
    cases List.mem_singleton.mp member
    rw [GeneralNominalVersionedPlans231.childSchema_eq]
    constructor
    · intro i
      change Fin 2 at i
      have cases : i=0 ∨ i=1 := by omega
      rcases cases with rfl | rfl
      · exact fit 0 (Or.inl rfl)
      · exact fit 1 (Or.inr rfl)
    · rw [GeneralDictionaryGroundCopy218SaturatedParent.child_schema_same,
        GeneralDictionaryGroundCopy218Reinstall.child_schema]
      intro equation member
      rcases List.mem_cons.mp member with rfl | member
      · change Equivalent _ _
        simp only [GeneralNominalCenteredHeadMatExpressions.value,variables,GeneralNominalVersionedFrame231.binder_eq,binder]
        exact ⟨subtype_refl _,subtype_refl _⟩
      · cases List.mem_singleton.mp member
        change Equivalent _ _
        simp only [GeneralNominalCenteredHeadMatExpressions.value,variables,GeneralNominalVersionedFrame231.binder_eq,binder]
        exact ⟨subtype_refl _,subtype_refl _⟩
end Yulang.GeneralDictionaryMixedGround218PointPacket235
