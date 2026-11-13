import Yulang.GeneralNominalSettledIntervalOutputs

/-! Branch models with fixed input endpoints and arbitrarily many distinct
associated tails. Operational iteration is treated separately in the note. -/
namespace Yulang.GeneralNominalSettledIntervalObstruction
open GeneralNominalSettledIntervalDeclarations GeneralNominalSettledIntervalSource
open GeneralNominalSettledIntervalOutputs GeneralNominalSaturationState
open GeneralNominalRecursiveInspection CommonNominalFullCarrier

theorem branch_family (a : Ty) (value : Common.Ty) : packet.Holds (family a value) := by
  apply (GeneralNominalPacketSupport.packet_exact ..).mpr
  refine ⟨source_models ..,⟨?_,?_,GeneralNominalPacketSupport.outputs_inputs packet (family a value) (packet_outputs a value)⟩,
    packet_outputs a value⟩
  · unfold GeneralNominalPacketSupport.Ordinary
    rw [packet_bindings,report_exact]
    refine ⟨?_,?_,?_⟩
    · intro first one last two same
      simp only [List.mem_cons,List.not_mem_nil,or_false] at one two
      rcases one with rfl | rfl <;> rcases two with rfl | rfl
      all_goals first | exact subtype_refl _ | exact interval_order | cases same
    · change PresenceNormalForm.All CommonNominalFullCarrier.model _ []
      exact PresenceNormalForm.all_nil _ _
    · intro atom member
      simp only [selfChecks,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl
      all_goals first | exact subtype_refl _ | exact interval_order
  · rw [report_exact]
    simp [ProjectionModels]

theorem children_empty : packet.children = [] := by
  have sorted : GeneralCanonicalChildOrder.canonicalDeclaration w = w := by
    simp only [GeneralCanonicalChildOrder.canonicalDeclaration,
      GeneralCanonicalChildOrder.canonicalRequirements,w,List.mergeSort_nil]
  unfold Packet.children GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children
  simp only [GeneralCanonicalChildOrder.canonicalEmit,sorted]
  rfl

theorem int_not_variant (value : Ty) : ¬ Equivalent (.base .int) (V value) := by
  intro equal
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (equal.1 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.variant 0 .trivial) ⟨rfl,trivial⟩

theorem variant_cancel {first last : Ty} (equal : Equivalent (V first) (V last)) :
    Equivalent first last :=
  ⟨(common_variant_iff 0 _ _).mp equal.1,(common_variant_iff 0 _ _).mp equal.2⟩

def tower : Nat → Common.Ty
  | 0 => .base .int
  | n+1 => Common.variant 0 (tower n)

theorem tower_separated (first last : Nat)
    (equal : Equivalent (CommonNominalFullModelMap.value (tower first))
      (CommonNominalFullModelMap.value (tower last))) : first = last := by
  induction first generalizing last with
  | zero =>
      cases last with
      | zero => rfl
      | succ last => exact False.elim (int_not_variant _ equal)
  | succ first ih =>
      cases last with
      | zero => exact False.elim (int_not_variant _ ⟨equal.2,equal.1⟩)
      | succ last => exact congrArg Nat.succ (ih last (variant_cancel equal))

/-- The full branch condition, not merely a hand-selected output equation,
allows each positive tower as tail with the identical unnamed endpoints. -/
theorem fixed_inputs_unbounded_tails (a : Ty) :
    (∀ n, packet.Holds (family a (tower n))) ∧
    (∀ m n index, (family a (tower m) (leafRoot.demand.arguments index).1).1 =
        (family a (tower n) (leafRoot.demand.arguments index).1).1 ∧
      (family a (tower m) (leafRoot.demand.arguments index).2).1 =
        (family a (tower n) (leafRoot.demand.arguments index).2).1) ∧
    (∀ m n, Equivalent (family a (tower m) 8).1 (family a (tower n) 8).1 → m = n) :=
  ⟨fun n => branch_family a (tower n),fun m n => same_input_endpoints a (tower m) (tower n),
    fun _ _ same => tower_separated _ _ (variant_cancel same)⟩

/-- Each finite refinement horizon uses finite trees over the one base leaf. -/
theorem finite_horizon (height index : Nat) (before : index < height) :
    CommonNominalFullModelMap.value (tower (height-index+1)) =
      V (CommonNominalFullModelMap.value (tower (height-(index+1)+1))) ∧
    Subtype (V .bottom) (CommonNominalFullModelMap.value (tower (height-(index+1)+1))) ∧
    Subtype (CommonNominalFullModelMap.value (tower (height-(index+1)+1))) (V .top) := by
  have arithmetic : height-index+1 = (height-(index+1)+1)+1 := by omega
  rw [arithmetic]
  exact ⟨rfl,interval_contains (tower (height-(index+1)))⟩

end Yulang.GeneralNominalSettledIntervalObstruction
