import Yulang.GeneralRebaseRowSourceLeaf287
import Yulang.GeneralRebaseLeafOutput288

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 16000000
namespace Yulang.GeneralRebaseRowLeafWitness288
open GeneralRebaseRowChildSource287
open GeneralRebaseRowChildRaw287 (SourceCheck exact_source)
open GeneralRebaseRowParentPacket287 (child plan sole_child)
open GeneralRebaseRowParentFrame287 (after after_model)
open GeneralRebaseRowTrustedBoundary287 (raw_after source_sites)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedSupport233 (Discharged SliceModels Trusted)
open GeneralRebaseInertLeaf288 (SourceSlice Leaf)
open GeneralRebaseLeafOutput288 (Child Parent)

theorem source_exact (choice : Bool) (m : Assignment) :
    SourceSlice (after choice) m ↔ SourceCheck m := by
  constructor
  · intro h
    exact (exact_source m).mp h.1
  · intro h
    exact ⟨(exact_source m).mpr h,source_sites choice m,by intro _ impossible; cases impossible⟩

theorem leaf : Leaf (registry true) (after true) (child true) 1 GeneralRebaseRowWholeChild287.plan :=
  ⟨GeneralRebaseRowWholeChild287.child_frame,GeneralRebaseRowLocal287.child_safe,
    GeneralRebaseRowAfterSafety287.merged_clear true _,GeneralRebaseRowLocal287.child_unique,
    GeneralRebaseRowWholeChild287.no_children,GeneralRebaseRowWholeChild287.requests_empty,
    ⟨model Common.rowEmpty,(source_exact true _).mpr ((exact_source _).mp (raw_model Common.rowEmpty))⟩,
    fun m src => GeneralRebaseRowSourceLeaf287.holds_from_raw m
      ((raw_after true m).mpr ((source_exact true m).mp src))⟩

theorem no_leaf (key : Nat) (p : GeneralNominalCenters.Plan roles) :
    ¬ Leaf (registry false) (after false) (child false) key p := by
  intro cert
  have frame := cert.frame
  have prepared := frame.prepared
  rw [GeneralRebaseRowLocal287.child_at_role false _ frame.visible frame.role_eq] at prepared
  exact GeneralRebaseRowGeneratedChild287.not_prepared prepared

theorem child_iff (choice : Bool) : Child (registry choice) (after choice) (child choice) ↔ choice = true := by
  cases choice
  · constructor
    · rintro (old | ⟨key,p,cert⟩)
      · exact (GeneralRebaseRowSettlement287.no_discharge false old).elim
      · exact (no_leaf key p cert).elim
    · intro impossible; cases impossible
  · exact ⟨fun _ => rfl,fun _ => .inr ⟨1,_,leaf⟩⟩

theorem parent_iff (choice : Bool) : Parent (registry choice) (after choice) (plan choice) ↔ choice = true := by
  constructor
  · intro h
    apply (child_iff choice).mp
    apply h.2
    rw [sole_child choice]
    exact List.mem_singleton_self _
  · intro h
    refine ⟨List.mem_singleton_self _,?_⟩
    intro focus member
    rw [sole_child choice] at member
    cases List.mem_singleton.mp member
    exact (child_iff choice).mpr h

end Yulang.GeneralRebaseRowLeafWitness288
