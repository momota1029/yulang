import Yulang.CommonNominalRigidInspection

/-!
# A demand-expressiveness limit of the current nominal carrier

Distinct zero-argument nominal heads share only the trivial existing probe,
so their union is currently demand-equivalent to top. This module records
that actual-model fact and a finite head-set test that separates them.

The head-set test is an explicit candidate additional demand, not a change
to the existing carrier, language semantics or source typing. This does not
prove B5 false, source reachability, or finite solved-family impossibility.
-/

namespace Yulang.CommonNominalUnionObservationBoundary

open CommonNominalCarrier

theorem distinct_nominals_union_top (first last : Nat) (different : first ≠ last) :
    Equivalent (.union (nominal first []) (nominal last [])) .top := by
  constructor
  · exact CommonNominalTypeBounds.type_below_top _
  · intro depth
    apply (CommonNominalFinite.producerLe_iff_probe _ _).mpr
    intro rank env obs accepted
    cases rank <;> cases obs <;>
      simp_all [observeTy, nominal, CommonNominalSyntax.Layer.evalAt,
        CommonNominalFinite.ProbeAt, CommonNominalFinite.ProbeStep, CommonNominalFinite.MaskedProbeStep]
    all_goals exact False.elim (different (by grind))

/-- Outer nominal head sets are finite syntax and do not inspect payloads.
Lattice operations use the same demand conjunction/disjunction convention.
This is a candidate missing observation, not a new Subtype definition. -/
def headSet (allowed : List Nat) : Ty → Bool
  | .bottom => true
  | .top => false
  | .union first last => headSet allowed first && headSet allowed last
  | .inter first last => headSet allowed first || headSet allowed last
  | .mask _ source => headSet allowed source
  | .nominal name _ => decide (name ∈ allowed)
  | _ => false

theorem finite_head_set_separates (first last : Nat) :
    headSet [first, last] (.union (nominal first []) (nominal last [])) = true ∧
      headSet [first, last] .top = false := by
  simp [headSet, nominal]

theorem current_equivalence_does_not_preserve_head_sets :
    ∃ first last : Ty, Equivalent first last ∧ headSet [0, 1] first ≠ headSet [0, 1] last := by
  exact ⟨.union (nominal 0 []) (nominal 1 []), .top,
    distinct_nominals_union_top 0 1 (by decide), by decide⟩

/-- The same current collapse propagates into a dedicated invariant nominal
argument; this does not invent a source annotation or bypass EOF decisions. -/
theorem invariant_box_current_collapse (box first last : Nat) (different : first ≠ last) :
    Equivalent (nominal box [.inl (.union (nominal first []) (nominal last []))])
      (nominal box [.inl .top]) := by
  have same := distinct_nominals_union_top first last different
  constructor
  · apply (nominal_regular_invariant_exact _ _ _ _).mpr
    refine ⟨rfl, rfl, ?_⟩
    intro index before after left right
    cases index with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at left right
        subst before; subst after
        exact same
    | succ index => simp at left
  · apply (nominal_regular_invariant_exact _ _ _ _).mpr
    refine ⟨rfl, rfl, ?_⟩
    intro index before after left right
    cases index with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at left right
        subst before; subst after
        exact ⟨same.2, same.1⟩
    | succ index => simp at left

end Yulang.CommonNominalUnionObservationBoundary
