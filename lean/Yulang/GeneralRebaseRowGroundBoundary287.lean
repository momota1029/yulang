import Yulang.GeneralRebaseRowChildRaw287

/-! The actual initial journal can satisfy source formation while missing the
stronger ground-root boundary. A single fixed closed denotation cannot
stand for both possible values of its row-bearing root. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 10000000
namespace Yulang.GeneralRebaseRowGroundBoundary287
open GeneralRebaseRowChildSource287
open GeneralRebaseRowChildRaw287 (fullRow different_rows)
open CommonNominalFullCarrier
open GeneralNominalGroundAccessibility (GroundRoots)
open GeneralDeclarationPatterns (Pattern)

theorem roots_differ : ¬ Equivalent (model Common.rowEmpty 1).1 (model fullRow 1).1 := by
  intro same
  change Equivalent (F (R Common.rowEmpty)) (F (R fullRow)) at same
  have invariant := (nominal_regular_invariant_exact 0 0 _ _).mp same.1
  exact different_rows (invariant.2.2 0 (.inl (R Common.rowEmpty)) (.inl (R fullRow)) rfl rfl)

theorem cannot_ground (labels : List Pattern) : ¬ GroundRoots ctx root labels := by
  rintro ⟨length,witness⟩
  let i : Fin (roles root.demand.role).arity := ⟨0,by decide +kernel⟩
  obtain ⟨term,_closed,h⟩ := witness i
  have empty := h (model Common.rowEmpty) (raw_model Common.rowEmpty)
  have large := h (model fullRow) (raw_model fullRow)
  exact roots_differ ⟨subtype_trans empty.1 large.2,subtype_trans large.1 empty.2⟩

theorem formed_but_not_ground (variant : Bool) :
    GeneralNominalSourceFormation.InitialSource (registry variant) ctx root ∧
    ∀ labels, ¬ GroundRoots ctx root labels :=
  ⟨source variant,cannot_ground⟩

end Yulang.GeneralRebaseRowGroundBoundary287
