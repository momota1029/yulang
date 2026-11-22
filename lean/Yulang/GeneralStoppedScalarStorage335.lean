import Yulang.GeneralStoppedSourceRefinement335

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralStoppedScalarStorage335
open GeneralNominalRefinements (Refines)
open GeneralStoppedLower335 (lower collect slotRows headAt descriptorAt)
open GeneralStoppedLowerOrigin335 (exists_entry)
open GeneralStoppedSourceRefinement335 (ScalarStorage preserves)
open CommonNominalFullCarrier (Subtype Equivalent Row)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_symm eqv_trans)
open GeneralDeclarativeGrowth327 (Extends)

theorem scalar_separated (first last : Inference.Base)
    (holds : Subtype (.base first) (.base last)) : first = last := by
  let env : CommonNominalFullDemand.Environment Row := ⟨fun _ => .bottom,fun _ => []⟩
  have distinguished := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (holds 0)
    0 env (.base last) (by rfl)
  exact distinguished

theorem structural_not_supported (sk : GeneralSourceState.Shape slots)
    (children : Fin sk.arity → Fin slots) :
    GeneralStoppedShape335.headExpr (sk.term children) = none := by
  cases sk <;> rfl

theorem inspect_storage {r : GeneralNominalState.State} (made : lower r = some s)
    (k : Fin r.base.slots) : ∃ es, headAt r k = some es := by
  unfold lower at made
  obtain ⟨_,known,_⟩ := Option.map_eq_some_iff.mp made
  obtain ⟨_,got⟩ := exists_entry known (List.mem_ofFn.mpr ⟨k,rfl⟩)
  cases check : headAt r k with
  | none => simp [slotRows,check] at got
  | some rows => exact ⟨rows,rfl⟩

/-- Within this accepted projection fragment, an actual model and
checked source refinement force originally observed scalar identity.
The normalized scalar cannot be relabelled; structural tables would
have failed the fragment's real encoder, and a lost head contradicts
ordinary raw knownness. -/
theorem storage_of_inhabited {before after : GeneralNominalState.State}
    (g : Refines before after) (made : lower after = some t)
    (fit : GeneralNominalState.Models after m) :
    ScalarStorage before after g := by
  intro slot original old
  have knownBefore : before.base.graph slot ≠ .unresolved := by
    intro notKnown
    cases row : before.base.heads slot <;>
      simp [GeneralSourceState.State.graph,row,GeneralSourceState.Head.node,
        GeneralSourceState.Head.equation] at old notKnown
  have knownAfter := g.base.known slot knownBefore
  obtain ⟨es,projected⟩ := inspect_storage made (g.base.embed slot)
  cases current : after.base.heads (g.base.embed slot) with
  | unresolved => exact (knownAfter (by
      change (after.base.heads (g.base.embed slot)).node = _
      rw [current]; rfl)).elim
  | scalar written =>
    have now : (after.base.heads (g.base.embed slot)).equation = some (.base written) := by rw [current]; rfl
    have oldTruth := GeneralNominalCommonBridge.rewrites_sound (g.heads slot (.base original) old) m fit.1
    have newTruth := fit.1.2.1 _ _ now
    change Equivalent (m (after.base.source (g.base.embed slot))).1 (.base original) at oldTruth
    change Equivalent (m (after.base.source (g.base.embed slot))).1 (.base written) at newTruth
    have exactId : written = original :=
      scalar_separated _ _ (eqv_trans (eqv_symm newTruth) oldTruth).1
    subst written
    rfl
  | structural atKind child =>
    have rejected := structural_not_supported (after.base.shapes atKind) child
    change GeneralStoppedLower335.record _ GeneralStoppedShape335.headExpr
      (after.base.heads (g.base.embed slot)).equation = some es at projected
    simp [current,GeneralSourceState.Head.equation,GeneralStoppedLower335.record,rejected] at projected

theorem inhabited_refinement {before after : GeneralNominalState.State}
    (g : Refines before after)
    (origin : lower before = some s) (made : lower after = some t)
    (fit : GeneralNominalState.Models after m) : Extends s t :=
  preserves g (storage_of_inhabited g made fit) origin made

end Yulang.GeneralStoppedScalarStorage335
