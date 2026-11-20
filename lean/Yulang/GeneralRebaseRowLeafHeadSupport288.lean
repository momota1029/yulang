import Yulang.GeneralRebaseRowLeafReceipt288

/-! The root nominal head of the positive leaf has precise, independently
typed support. Its row port is needed on arbitrary assignments, but it is
not a new filter among assignments already admitted by the original source. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 18500000
namespace Yulang.GeneralRebaseRowLeafHeadSupport288
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentFrame287 (after)
open GeneralRebaseRowLedger288 (supplemented)
open GeneralRebaseRowLeafSourceHeads288 (inputObservation source_supported)
open GeneralRebaseRowChildRaw287 (changeAmbient fullRow different_rows exact_source)
open GeneralRebaseRowLeafWitness288 (source_exact)
open GeneralRebaseRowMinimal287 (Determines changeType missed_type missed_row type_mismatch)
open GeneralRebaseInertLeaf288 (SourceSlice)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent subtype_refl)

variable {context : GeneralNominalCandidates.Context}

theorem inner_denotes_iff (m : Assignment) :
    GeneralNominalState.Denotes raw.base m (0 : Fin 3) inner ↔ Equivalent (m 0).1 (R (m 0).2) := by
  constructor
  · rintro ⟨args,fits,represented⟩
    change GeneralNominalState.FitsAll raw.base m [.row (0,0)] args at fits
    cases fits with
    | @cons _ value _ rest fitted tail =>
      cases tail
      cases value with
      | inl value => cases fitted
      | inr row =>
        have same : row = (m 0).2 := Common.rowLe_antisymm fitted.2 fitted.1
        rw [same] at represented
        exact represented
  · intro rowChecked
    exact ⟨[.inr (m 0).2],.cons ⟨Common.rowLe_refl _,Common.rowLe_refl _⟩ .nil,rowChecked⟩

theorem exact_head_check (cert : Refresh supplemented context) (m : Assignment) :
    (inputObservation cert).Holds m ↔ Equivalent (m 0).1 (R (m 0).2) :=
  (GeneralRebaseSourceHeadTransport288.denotes_iff cert.refines m (0 : Fin 3) inner).trans (inner_denotes_iff m)

theorem typed_support_minimal (cert : Refresh supplemented context) (types rows : List Nat) :
    Determines types rows (inputObservation cert).Holds ↔ 0 ∈ types ∧ 0 ∈ rows := by
  constructor
  · intro claim
    have good : (inputObservation cert).Holds (model Common.rowEmpty) :=
      (exact_head_check cert _).mpr ⟨subtype_refl _,subtype_refl _⟩
    constructor
    · by_cases has : 0 ∈ types
      · exact has
      · have held := (claim _ _ (missed_type 0 has _)).mp good
        exact (type_mismatch ((exact_head_check cert _).mp held)).elim
    · by_cases has : 0 ∈ rows
      · exact has
      · have held := (claim _ _ (missed_row has _)).mp good
        exact (different_rows ((exact_head_check cert _).mp held)).elim
  · rintro ⟨ty,row⟩ a b same
    rw [exact_head_check,exact_head_check,same.1 0 ty,same.2 0 row]

theorem source_never_loses_head (cert : Refresh supplemented context) (m : Assignment)
    (given : SourceSlice (refresh supplemented context) m) : (inputObservation cert).Holds m :=
  source_supported cert m given

end Yulang.GeneralRebaseRowLeafHeadSupport288
