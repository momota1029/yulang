import Yulang.GeneralRebaseRowLeafHeadSupport288

/-! A certified mark has only the two public type ports it actually needs,
even though a whole raw model has an additional independent row port. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 18500000
namespace Yulang.GeneralRebaseRowOutputHeadSupport288
open GeneralRebaseRowChildSource287
open GeneralRebaseRowLedger288 (supplemented)
open GeneralRebaseRowSemanticMark287 (outputDescriptor)
open GeneralRebaseRowRefreshShape288 (actually_nominal point any_comparable_is_middle)
open GeneralRebaseRowMinimal287 (Determines changeType missed_type type_mismatch)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalState (Known)
open GeneralCanonicalObservations (Observation Recorded)
open GeneralNominalRefinements (renameDescriptor)
open CommonNominalFullCarrier (Equivalent subtype_refl subtype_trans nominal_regular_invariant_exact)

variable {context : GeneralNominalCandidates.Context}

noncomputable def markedRead (cert : Refresh supplemented context) : Observation :=
  .nominal context.state.base (cert.refines.base.embed (2 : Fin 3))
    (renameDescriptor cert.refines.base.embed outputDescriptor)

theorem actually_recorded (cert : Refresh supplemented context) (new : Known context.state 2) :
    Recorded context.state (markedRead cert) :=
  .nominal _ _ (actually_nominal context cert new)

theorem prior_descriptor_meaning (m : Assignment) :
    GeneralNominalState.Denotes raw.base m (2 : Fin 3) outputDescriptor ↔ Equivalent (m 2).1 (F (m 1).1) := by
  constructor
  · rintro ⟨args,fits,represented⟩
    change GeneralNominalState.FitsAll raw.base m [.type (1,1)] args at fits
    cases fits with
    | @cons _ value _ rest fitted tail =>
      cases tail
      cases value with
      | inr value => cases fitted
      | inl value =>
        have same : Equivalent (F value) (F (m 1).1) :=
          GeneralNominalCenteredHeadMatCompilerSemantics.nominal_congr 0 (.cons ⟨fitted.2,fitted.1⟩ .nil)
        exact ⟨subtype_trans represented.1 same.1,subtype_trans same.2 represented.2⟩
  · intro checked
    exact ⟨[.inl (m 1).1],.cons ⟨subtype_refl _,subtype_refl _⟩ .nil,checked⟩

theorem exact_read (cert : Refresh supplemented context) (m : Assignment) :
    (markedRead cert).Holds m ↔ Equivalent (m 2).1 (F (m 1).1) :=
  (GeneralRebaseSourceHeadTransport288.denotes_iff cert.refines m (2 : Fin 3) outputDescriptor).trans (prior_descriptor_meaning m)

theorem no_private_or_row_read (cert : Refresh supplemented context) (types rows : List Nat) :
    Determines types rows (markedRead cert).Holds ↔ 1 ∈ types ∧ 2 ∈ types := by
  constructor
  · intro claim
    have good : (markedRead cert).Holds (model Common.rowEmpty) :=
      (exact_read cert _).mpr ⟨subtype_refl _,subtype_refl _⟩
    constructor
    · by_cases has : 1 ∈ types
      · exact has
      · have held := (exact_read cert _).mp ((claim _ _ (missed_type 1 has _)).mp good)
        change Equivalent (F point) (F (.base .int)) at held
        have inner := ((nominal_regular_invariant_exact 0 0 _ _).mp held.1).2.2 0
          (.inl point) (.inl (.base .int)) rfl rfl
        exact ((by decide : (3 : Nat) ≠ 1) (any_comparable_is_middle 3 (.inr inner.1))).elim
    · by_cases has : 2 ∈ types
      · exact has
      · have held := (exact_read cert _).mp ((claim _ _ (missed_type 2 has _)).mp good)
        exact (type_mismatch held).elim
  · rintro ⟨one,two⟩ a b same
    rw [exact_read,exact_read,same.1 1 one,same.1 2 two]

end Yulang.GeneralRebaseRowOutputHeadSupport288
