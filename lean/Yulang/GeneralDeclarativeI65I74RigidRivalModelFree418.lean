import Yulang.GeneralDeclarativeI65I74RigidRivalNoHead418

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RigidRival418
open GeneralDeclarativeI65
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalMaterialization (Mode)
open GeneralDeclarativeHead320 (Read Equation)
open GeneralDeclarativeSubstitution320 (EquationRead)
open PlainMerged416 (PlainRows variantPayload variantRow416)
open GeneralDeclarativeWitnessDeclaredState357 (point)
open GeneralDeclarativeNormalized320 (Center)
open GeneralDeclarationPatterns (Pattern)
open CommonRoleOutermostResolver (All₂)

theorem nullary_str_read_uses_literal_row418 {s : GeneralDeclarativeHead320.State}
    {capture : Nat → Capture} {mode : Mode} {slot : Nat} {expr : Expr}
    (read : Read s capture mode slot expr) (literal : expr = strNull) :
    (⟨slot,strNull⟩ : Equation) ∈ s.equations := by
  cases read with
  | capture _ _ => cases literal
  | nominal _ _ _ _ => cases literal
  | record _ _ _ => cases literal
  | variant _ _ => cases literal
  | join _ _ _ => cases literal
  | primitive sour child matched _ =>
    change Expr.primitive _ (List.ofFn child) = Expr.primitive (.scalar .str) [] at literal
    have same := Expr.primitive.inj literal
    have empty := congrArg List.length same.2
    simp only [List.length_ofFn,List.length_nil] at empty
    have emptySource : List.ofFn (fun i => Expr.variable (sour i)) = [] :=
      List.length_eq_zero_iff.mp (List.length_ofFn.trans empty)
    simpa [strNull,same.1,emptySource] using matched

theorem structural_rival_read_uses_the_same_payload_row418 {s q} {r : PlainRows s q}
    {capture : Nat → Capture} {mode : Mode}
    (observation : Read s.core.current.ordinary capture mode r.root (rivalCode418 r.tag)) :
    (⟨r.payload,strNull⟩ : Equation) ∈ s.core.current.ordinary.equations := by
  change Read s.core.current.ordinary capture mode r.root (.variant r.tag strNull) at observation
  cases observation with
  | variant row inner =>
    rename_i child
    have filtered : variantRow416 r.root r.tag child ∈
        s.core.current.ordinary.equations.filter (variantPayload r.root r.tag) :=
      List.mem_filter.mpr ⟨row,by simp [variantPayload,variantRow416]⟩
    rw [r.uniquePayload] at filtered
    have same := Expr.variant.inj (congrArg Equation.right (List.mem_singleton.mp filtered))
    have exactSlot := Expr.variable.inj same.2
    exact exactSlot ▸ nullary_str_read_uses_literal_row418 inner rfl

theorem equation_rival_read_must_use_a_direct_whole_or_payload_row418
    {s q} {r : PlainRows s q} {capture : Nat → Capture} {mode : Mode}
    (observation : EquationRead s.core.current.ordinary capture mode r.root (rivalCode418 r.tag)) :
    (⟨r.root,rivalCode418 r.tag⟩ : Equation) ∈ s.core.current.ordinary.equations ∨
      (⟨r.payload,strNull⟩ : Equation) ∈ s.core.current.ordinary.equations := by
  cases observation with
  | whole eq => exact .inl eq
  | structural read => exact .inr (structural_rival_read_uses_the_same_payload_row418 read)
theorem no_rival_center_in_a_checked_scan418 {s q} (a : Winner s q)
    {capture : Nat → Capture}
    (candidate : Center s.core.current.ordinary capture (point a.rows.root) (rivalCode418 a.rows.tag)) :
    False := by
  cases candidate with
  | direct fact =>
    rcases equation_rival_read_must_use_a_direct_whole_or_payload_row418 fact with whole|leaf
    · exact a.noConflictingRawRival.whole whole
    · exact a.noConflictingRawRival.leaf leaf
  | endpoints _ _ lower _ =>
    rcases equation_rival_read_must_use_a_direct_whole_or_payload_row418 lower with whole|leaf
    · exact a.noConflictingRawRival.whole whole
    · exact a.noConflictingRawRival.leaf leaf

/-- Every possible original source-head constructor is ruled out in
the checked snapshot, without quantifying over or supplying a model.
The final check gates add a negative raw-receipt consistency cut, not
an inference from failed matching or from absence of source typing. -/
theorem actual_checked_rival_has_no_source_head_without_a_model418 {s q} (a : Winner s q) :
    ¬ Nonempty (SourceHead s.core q a.mismatch.rival.candidate.decl) := by
  rintro ⟨head⟩
  cases head with
  | joined inferred =>
    have literal := (List.cons.inj (inferred.head.symm.trans a.mismatch.rival.literal)).1
    have impossible := inferred.normalized
    rw [literal] at impossible
    change Pattern.variant a.rows.tag (.app a.mismatch.rival.strName []) =
      Pattern.variant inferred.tag (.join _ _) at impossible
    cases (Pattern.variant.inj impossible).2
  | ordered capture arguments =>
    have supplied : All₂ (DeepHead s.core capture) [point a.rows.root]
        [rivalHead418 a.rows.tag a.mismatch.rival.strName] := by
      simpa only [a.rows.requested,a.mismatch.rival.literal] using arguments
    cases supplied with
    | cons one _ =>
      cases one with
      | declared alleged _ =>
        have wrong := alleged.syntaxHead
        change Pattern.variant a.rows.tag (.app a.mismatch.rival.strName []) = .app _ _ at wrong
        cases wrong
      | ordinary observed =>
        obtain ⟨_,code,translated,center⟩ := observed
        rw [literal_rival_translation418 a.mismatch.rival] at translated
        cases Option.some.inj translated
        exact no_rival_center_in_a_checked_scan418 a center

end Yulang.GeneralDeclarativeI65.I72.RigidRival418
