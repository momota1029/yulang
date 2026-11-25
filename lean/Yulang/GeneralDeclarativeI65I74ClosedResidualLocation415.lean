import Yulang.GeneralDeclarativeI65I74ClosedResidualPriority415

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ClosedResidual415
open GeneralDeclarativeI65
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_trans record_congr)
open CommonNominalFullCarrier (record Equivalent)
open Checker408 (Problem)

structure ResidualLocation where
  parentOccurrence : List Nat
  childOccurrence : List Nat
  root : Nat
  removed : Nat
  remaining : Nat
  residual : Nat
  parentDecl : Nat
  parentOrdinal : Nat
  childDecl : Nat
  childOrdinal : Nat
  clause : Nat
  parentBinder : Nat
  childBinder : Nat
  deriving DecidableEq, Repr

def VerifiedClosed.location {p : Problem} (v : VerifiedClosed p) : ResidualLocation :=
  ⟨p.root.occurrence,(query415 p.root v.parent.childRole v.rows.residual).occurrence,
    v.rows.root,v.rows.x,v.rows.y,v.rows.residual,v.parent.candidate.decl.id,
    v.parent.candidate.ordinal,v.child.candidate.decl.id,v.child.candidate.ordinal,v.parent.clauseID,
    v.parent.binder,v.child.binder⟩

def locate (p : Problem) (w : ClosedWire) : Option ResidualLocation :=
  (replayClosed415 p w).map VerifiedClosed.location

/-- Both the known prefix and the actually captured tail keep their
original logical model in the retained split; no model equality is
consulted when choosing which name to capture. -/
theorem exact_same_model_split_value415 {s q} (a : ClosedRows s q)
    (m : I72.Model) (fit : Fits s m) :
    Equivalent (m.assignment a.root).1 (record a.x (.base .int) (m.assignment a.residual).1) := by
  have cut := fit.1.1.2 _ a.retainedSplit
  have int := fit.1.1.2 _ a.integer
  change Equivalent (m.assignment a.intSlot).1 (.base .int) at int
  change Equivalent (m.assignment a.root).1
    (record a.x (m.assignment a.intSlot).1 (m.assignment a.residual).1) at cut
  exact eqv_trans cut (record_congr _ int (eqv_refl _))

theorem two_replays_cannot_relocate_original_residual415 {p : Problem} (u v : ClosedWire)
    {a b : ResidualLocation} (first : locate p u = some a) (second : locate p v = some b) :
    a.root = b.root ∧ a.removed = b.removed ∧ a.remaining = b.remaining ∧
      a.residual = b.residual ∧ a.childOccurrence = b.childOccurrence := by
  unfold locate at first second
  cases x : replayClosed415 p u with
  | none => simp [x] at first
  | some c =>
    cases y : replayClosed415 p v with
    | none => simp [y] at second
    | some d =>
      simp only [x,Option.map_some,Option.some.injEq] at first
      simp only [y,Option.map_some,Option.some.injEq] at second
      subst a
      subst b
      obtain ⟨root,removed,_i,kept,_str,addr⟩ := original_coordinate_is_independent_of_wire415 c.rows d.rows
      exact ⟨root,removed,kept,addr,rfl⟩

end Yulang.GeneralDeclarativeI65.I72.ClosedResidual415
