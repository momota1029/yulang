import Yulang.GeneralNominalState

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalKnownBit304

def present (s : GeneralNominalState.State) (slot : Fin s.base.slots) : Bool :=
  match s.view.graph slot with
  | .unresolved => (s.nominals slot).isSome
  | _ => true

theorem present_exact (s : GeneralNominalState.State) (slot : Fin s.base.slots) :
    present s slot = true ↔
      s.view.graph slot ≠ .unresolved ∨ ∃ descriptor, s.nominals slot = some descriptor := by
  unfold present
  cases h : s.view.graph slot <;> simp [Option.isSome_iff_exists]

/-- Computes raw knownness by scanning finite slots; no model search or
availability of a candidate declaration is used. -/
def knownBit (s : GeneralNominalState.State) (source : Nat) : Bool :=
  (List.finRange s.base.slots).any fun slot =>
    (s.base.source slot == source) && present s slot

theorem known_exact (s : GeneralNominalState.State) (source : Nat) :
    knownBit s source = true ↔ GeneralNominalState.Known s source := by
  unfold knownBit GeneralNominalState.Known
  simp only [List.any_eq_true,List.mem_finRange,Bool.and_eq_true,beq_iff_eq,present_exact,true_and]

end Yulang.GeneralNominalKnownBit304
