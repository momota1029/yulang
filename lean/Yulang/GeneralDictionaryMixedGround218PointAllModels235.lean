import Yulang.GeneralDictionaryMixedGround218PointFrame235
import Yulang.GeneralNominalNamedArgumentReadback
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
namespace Yulang.GeneralDictionaryMixedGround218PointAllModels235
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryGroundCopy218Install (declaration clause)
open GeneralDictionaryMixedGround218Point235
open GeneralDictionaryMixedGround218PointPacket235 (packet plan capture binder emitted_schema outputs)
open GeneralNominalCenters CommonNominalFullCarrier
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalVersionedPlans231
variable (model : GeneralNominalCommonBridge.Assignment)

theorem projected_zero (valid : GeneralNominalState.Models packet.context.state model) : (∃ actual, Observes model (.nominal (.source 6) 5 0) actual) ∧
    ∀ actual, Observes model (.nominal (.source 6) 5 0) actual → GeneralNominalCaptureMerges.Fits model (4,4) actual :=
  nominal_argument_bounds packet.context.state model valid 6 exactCopy rfl 0 (4,4) rfl

theorem projected_one (valid : GeneralNominalState.Models packet.context.state model) : (∃ actual, Observes model (.nominal (.source 6) 5 1) actual) ∧
    ∀ actual, Observes model (.nominal (.source 6) 5 1) actual → GeneralNominalCaptureMerges.Fits model (5,5) actual :=
  nominal_argument_bounds packet.context.state model valid 6 exactCopy rfl 1 (5,5) rfl
theorem projections (valid : GeneralNominalState.Models packet.context.state model) : ProjectionModels packet.context.state (report packet.context declaration [(6,6)]) model := by
  rw [GeneralDictionaryGroundCopy218SaturatedParent.report_exact]
  refine ⟨?_,(by intro test member; cases member),?_,?_⟩
  · intro anchor member
    rcases List.mem_cons.mp member with rfl | member
    · exact projected_zero model valid
    · cases List.mem_singleton.mp member; exact projected_one model valid
  · intro a aMem b bMem same ref refEq actual observed
    simp only [List.mem_cons,List.not_mem_nil,or_false] at aMem bMem
    rcases aMem with rfl | rfl <;> rcases bMem with rfl | rfl
    all_goals try cases same
    all_goals
      cases Option.some.inj refEq
      first | exact (projected_zero model valid).2 actual observed | exact (projected_one model valid).2 actual observed
  · intro a aMem b bMem same x y firstEq lastEq u v firstSeen lastSeen
    simp only [List.mem_cons,List.not_mem_nil,or_false] at aMem bMem
    rcases aMem with rfl | rfl <;> rcases bMem with rfl | rfl
    all_goals try cases same
    all_goals
      cases Option.some.inj firstEq
      cases Option.some.inj lastEq
      exact nominal_observation_unique model (.argument (.source 6) 5 _) u v firstSeen lastSeen

theorem heads (valid : GeneralNominalState.Models packet.context.state model) : SchemaHolds plan plan.headSchema model := by
  rw [GeneralDictionaryGroundCopy218SaturatedParent.head_schema_same,GeneralDictionaryGroundCopy218Reinstall.head_schema]
  constructor
  · intro test member
    cases List.mem_singleton.mp member
    exact GeneralNominalNamedArgumentReadback.nominal_head packet.context.state
      (models := GeneralNominalState.Models packet.context.state) (fun _ h => h) 6 exactCopy rfl [(4,4),(5,5)] rfl model valid
  · intro entry member
    rcases List.mem_cons.mp member with rfl | member
    · change GeneralNominalOriginTerms.Same model (.nominal (.source 6) 5 0) (.source (GeneralNominalVersionedFrame231.binder plan 0))
      rw [GeneralNominalVersionedFrame231.binder_eq,binder,GeneralDictionaryGroundCopy218Reinstall.binder_zero]
      refine ⟨(projected_zero model valid).1,⟨_,.source _⟩,?_⟩
      intro a b seen one; cases one
      exact ⟨((projected_zero model valid).2 a seen).2,((projected_zero model valid).2 a seen).1⟩
    · cases List.mem_singleton.mp member
      change GeneralNominalOriginTerms.Same model (.nominal (.source 6) 5 1) (.source (GeneralNominalVersionedFrame231.binder plan 1))
      rw [GeneralNominalVersionedFrame231.binder_eq,binder,GeneralDictionaryGroundCopy218Reinstall.binder_one]
      refine ⟨(projected_one model valid).1,⟨_,.source _⟩,?_⟩
      intro a b seen one; cases one
      exact ⟨((projected_one model valid).2 a seen).2,((projected_one model valid).2 a seen).1⟩

theorem ordinary : Ordinary packet model := by
  constructor
  · intro a one b two same
    rw [GeneralDictionaryMixedGround218PointPacket235.bindings_exact] at one two
    simp only [List.mem_cons,List.not_mem_nil,or_false] at one two
    rcases one with rfl | rfl <;> rcases two with rfl | rfl
    all_goals first | exact subtype_refl _ | cases same
  constructor
  · rw [GeneralDictionaryMixedGround218PointPacket235.bindings_exact]
    exact PresenceNormalForm.all_nil _ _
  · unfold GeneralNominalPacketSupport.report
    rw [GeneralDictionaryGroundCopy218SaturatedParent.report_exact]
    intro atom member
    change atom ∈ [.tyLe (.var 6) (.var 6),.tyLe (.var 6) (.var 6),.tyLe (.var 4) (.var 4),.tyLe (.var 5) (.var 5)] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> exact subtype_refl _

theorem fit (name : Nat) (member : name=0 ∨ name=1) :
    GeneralNominalCaptureMerges.Fits model ((GeneralNominalVersionedFrame231.capture packet).inputs name)
      (model (GeneralNominalVersionedFrame231.binder plan name)).1 := by
  rw [capture name member,GeneralNominalVersionedFrame231.binder_eq,binder]
  rcases member with rfl | rfl
  · rw [GeneralDictionaryGroundCopy218Reinstall.binder_zero]; exact ⟨subtype_refl _,subtype_refl _⟩
  · rw [GeneralDictionaryGroundCopy218Reinstall.binder_one]; exact ⟨subtype_refl _,subtype_refl _⟩

theorem packet_holds (valid : GeneralNominalState.Models packet.context.state model) : Holds plan model := by
  refine ⟨valid,⟨ordinary model,projections model valid,?_,?_,heads model valid,?_,?_⟩,outputs model⟩
  · exact GeneralNominalCenters.point_root_holds _ root (fun _ => rfl) model
  · intro name needed
    apply fit model name
    rcases needed with member | ⟨c,member,within⟩
    · change name ∈ [0,1] at member; simpa using member
    · cases List.mem_singleton.mp member
      change name ∈ [0,1] at within; simpa using within
  · intro equation member _; exact outputs model equation member
  · intro c member check
    cases List.mem_singleton.mp member
    rw [GeneralNominalVersionedPlans231.childSchema_eq]
    constructor
    · intro i
      change Fin 2 at i
      have cases : i=0 ∨ i=1 := by omega
      rcases cases with rfl | rfl
      · exact fit model 0 (Or.inl rfl)
      · exact fit model 1 (Or.inr rfl)
    · rw [GeneralDictionaryGroundCopy218SaturatedParent.child_schema_same,GeneralDictionaryGroundCopy218Reinstall.child_schema]
      intro equation member
      rcases List.mem_cons.mp member with rfl | member
      · change Equivalent _ _
        simp only [GeneralNominalCenteredHeadMatExpressions.value,variables,GeneralNominalVersionedFrame231.binder_eq,binder]
        exact ⟨subtype_refl _,subtype_refl _⟩
      · cases List.mem_singleton.mp member
        change Equivalent _ _
        simp only [GeneralNominalCenteredHeadMatExpressions.value,variables,GeneralNominalVersionedFrame231.binder_eq,binder]
        exact ⟨subtype_refl _,subtype_refl _⟩

theorem all_models (model) (held : GeneralNominalVersionedJournal232.Models point model) : Holds plan model := by
  apply packet_holds
  rw [GeneralDictionaryMixedGround218PointPacket235.context_eq]
  exact held.1.1
end Yulang.GeneralDictionaryMixedGround218PointAllModels235
