import Yulang.GeneralRebaseTowerEndpoint285

#print axioms Yulang.GeneralRebaseTowerEndpoint285.subtype_eq
#print axioms Yulang.GeneralRebaseTowerEndpoint285.requires_lower
#print axioms Yulang.GeneralRebaseTowerEndpoint285.requires_present_rank
#print axioms Yulang.GeneralRebaseTowerEndpoint285.descriptor_iff

example : ¬ Yulang.CommonNominalFullCarrier.Subtype
    (Yulang.GeneralNominalOutputGrowth.tower 7) (Yulang.GeneralNominalOutputGrowth.tower 6) := by
  intro h
  exact (by decide : (7 : Nat) ≠ 6) ((Yulang.GeneralRebaseTowerEndpoint285.subtype_eq 7 6).mp h)
