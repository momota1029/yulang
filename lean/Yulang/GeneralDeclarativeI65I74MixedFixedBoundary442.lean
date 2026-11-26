import Yulang.GeneralDeclarativeI65I74MixedFixedSource442

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Yulang.GeneralDeclarativeI65.I72.MixedFixed442
open GeneralDeclarativeI65
open GeneralDeclarativeI65.I72
open CommonDeclaredNominalInspection (Kind)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralDeclarativeHead320 (environment)
open CommonNominalFullCarrier (Equivalent subtype_trans)

def valueOnly (l : List (Nat × Kind)) : Bool :=
  l.all (fun slot => decide (slot.2 = .value))

theorem valueOnly_append (a b : List (Nat × Kind)) :
    valueOnly (a ++ b) = (valueOnly a && valueOnly b) := by
  simp [valueOnly,List.all_append]

theorem legacy_fixed_value_emission_iff_original_typed_footprint {s slots c p}
    (tree : NamedMixedTree401 s slots c p) :
    (fixedValueCode403 tree).isSome = valueOnly (mixedRhsNeeds401 tree) := by
  refine MixedRhs401.rec
    (motive_1 := fun _ _ t => (fixedValueCode403 t).isSome = valueOnly (mixedRhsNeeds401 t))
    (motive_2 := fun _ _ _ a => (fixedValueArgCode403 a).isSome = valueOnly (mixedArgNeeds401 a))
    (motive_3 := fun _ _ _ as => (fixedValueArgsCode403 as).isSome = valueOnly (mixedArgsNeeds401 as))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ tree
  · intro c n cap; rfl
  · intro c a b tag lhs rhs lh rh
    simp only [fixedValueCode403,mixedRhsNeeds401,valueOnly_append,← lh,← rh]
    cases fixedValueCode403 lhs <;> cases fixedValueCode403 rhs <;> rfl
  · intro c p tag t h
    simp only [fixedValueCode403,mixedRhsNeeds401,← h]
    cases fixedValueCode403 t <;> rfl
  · intro c a b lhs rhs lh rh
    simp only [fixedValueCode403,mixedRhsNeeds401,valueOnly_append,← lh,← rh]
    cases fixedValueCode403 lhs <;> cases fixedValueCode403 rhs <;> rfl
  · intro ps c params n use tags table args h
    simp only [fixedValueCode403,mixedRhsNeeds401,← h]
    cases fixedValueArgsCode403 args <;> rfl
  · intro c n base use legal; rfl
  · intro c n use legal; rfl
  · intro c n use legal; rfl
  · intro c a b n use legal lhs rhs lh rh
    simp only [fixedValueCode403,mixedRhsNeeds401,valueOnly_append,← lh,← rh]
    cases fixedValueCode403 lhs <;> cases fixedValueCode403 rhs <;> rfl
  · intro c param n kind compute mark; rfl
  · intro c param n kind compute mark; rfl
  · intro c param n kind compute mark; rfl
  · intro c param n kind compute mark; rfl
  · intro params p c kind compound child h
    exact h
  · intro c
    rfl
  · intro c param ps p pats first rest a b
    simp only [fixedValueArgsCode403,mixedArgsNeeds401,valueOnly_append,← a,← b]
    cases fixedValueArgCode403 first <;> cases fixedValueArgsCode403 rest <;> rfl

theorem any_original_row_need_excludes_legacy_fixed_value_code
    {s slots c p n} (tree : NamedMixedTree401 s slots c p)
    (needle : (n,.row) ∈ mixedRhsNeeds401 tree) :
    fixedValueCode403 tree = none := by
  have eq := legacy_fixed_value_emission_iff_original_typed_footprint tree
  cases found : fixedValueCode403 tree with
  | none => rfl
  | some _ =>
    rw [found] at eq
    have all : valueOnly (mixedRhsNeeds401 tree) = true := eq.symm
    have conflict := List.all_eq_true.mp all (n,.row) needle
    cases conflict

theorem any_event_row_need_excludes_old_retained_row_path
    {s : I72.State} {q : I72.Request} (event : I72.Event s q)
    (i : Fin q.demand.outputs.length) (n : Nat)
    (typed : (n,.row) ∈ mixedRhsNeeds401 (event.outputs i).rhs) :
    ¬ RetainedTypedValueRows403 event := by
  rintro keep
  obtain ⟨rhs,code,_⟩ := keep i
  rw [any_original_row_need_excludes_legacy_fixed_value_code _ typed] at code
  cases code


/-- No old expression receives the effect-row component as an input. -/
theorem old_expr_reads_only_value_projection442 (p q : Model)
    (same : ∀ n, (p.assignment n).1 = (q.assignment n).1)
    (rhs : Expr) (mode : GeneralNominalMaterialization.Mode) :
    value (environment p.assignment) mode rhs =
      value (environment q.assignment) mode rhs := by
  have eq : environment p.assignment = environment q.assignment := funext (fun _ => funext same)
  rw [eq]

/-- Under independently varying row payload, this rules out even an
arbitrary old Expr denotation, not only a failed structural translation.
It does not exclude additional genuine constraints in other states. -/
theorem independently_varying_original_effect_excludes_any_old_denotation442
    {s : I72.State} {q : Request} {f : AuthoredBodyFrame393 s.core q} {i : Fin q.demand.outputs.length}
    (source : OriginalOutput (s := s) f i) (p r : Model) (pf : I72.Fits s p) (rf : I72.Fits s r)
    (same : ∀ n, (p.assignment n).1 = (r.assignment n).1)
    (different : (p.assignment source.rowCap.center).2 ≠ (r.assignment source.rowCap.center).2) :
    ¬ ∃ rhs : Expr, ∀ m, I72.Fits s m →
      Equivalent (value (environment m.assignment) .actual rhs) (source.actualValue m) := by
  rintro ⟨rhs, meanings⟩
  have left := meanings p pf
  have right := meanings r rf
  have prev := old_expr_reads_only_value_projection442 p r same rhs .actual
  rw [prev] at left
  have together := subtype_trans left.2 right.1
  have all := (CommonNominalFullCarrier.nominal_regular_invariant_exact _ _ _ _).mp together
  apply different
  exact all.2.2 0 (.inr ((p.assignment source.rowCap.center).2))
    (.inr ((r.assignment source.rowCap.center).2)) rfl rfl

/-- The old equality on a variable remains a valid relay, but only
when the independently sourced carrier slot already means the mixed output.
Authored Views/nativeSyntax alone are not that equality. -/
theorem old_alias_target_relays_only_independent_mixed_equality442
    {s : I72.State} {q : Request} {f : AuthoredBodyFrame393 s.core q} {i : Fin q.demand.outputs.length}
    (a : OriginalOutput (s := s) f i) {rhs : Nat} (m : Model) (fit : I72.Fits s m)
    (actualRow : (⟨q.demand.outputs[i].target,.variable rhs⟩ : GeneralDeclarativeHead320.Equation)
      ∈ s.core.current.ordinary.equations) :
    Equivalent (m.assignment q.demand.outputs[i].target).1 (a.actualValue m) ↔
    Equivalent (m.assignment rhs).1 (a.actualValue m) := by
  have eq := fit.1.1.2 _ actualRow
  change Equivalent (m.assignment q.demand.outputs[i].target).1 (m.assignment rhs).1 at eq
  exact ⟨fun y => ⟨subtype_trans eq.2 y.1,subtype_trans y.2 eq.1⟩,
    fun y => ⟨subtype_trans eq.1 y.1,subtype_trans y.2 eq.2⟩⟩

end Yulang.GeneralDeclarativeI65.I72.MixedFixed442
