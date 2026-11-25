import Yulang.GeneralDeclarativeI65I74RigidRivalPriority418

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RigidRival418
open GeneralDeclarativeI65
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry point)
open GeneralNominalCenteredHeadMatExpressions (Expr translate translateMany value)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWhere319 (Capture variables)
open GeneralDeclarationPatterns (Pattern normalize)
open CommonRoleOutermostResolver (All₂)
open CommonNominalFullCarrier (Subtype Equivalent variant common_variant_iff subtype_trans)
open GeneralNominalCenteredHeadMatCompilerSemantics (compiled_normalized)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)
open PlainMerged416 (PlainRows)

theorem literal_rival_translation418 {s q} {rows : PlainRows s q} (a : Rival rows) :
    translate (authoredRegistry s.core.current).constructors
      (interpretation s.core.current.environment.source.snapshot) (rivalHead418 rows.tag a.strName) =
    some (rivalCode418 rows.tag) := by
  simp [rivalHead418,rivalCode418,strNull,translate,translateMany,a.kind]

theorem every_original_observation_at_entry_is_the_same_int_origin418
    {s q} {rows : PlainRows s q} (a : RigidMismatch rows) {o : Origin}
    (found : o ∈ s.core.origins) (same : o.slot = rows.payload) :
    o = a.source.original := by
  obtain ⟨only,one⟩ := List.length_eq_one_iff.mp a.originalOnly
  have l : o ∈ s.core.origins.filter (fun o => o.slot == rows.payload) :=
    List.mem_filter.mpr ⟨found,by simp [same]⟩
  have r : a.source.original ∈ s.core.origins.filter (fun o => o.slot == rows.payload) :=
    List.mem_filter.mpr ⟨a.source.member,by simp [a.source.slot]⟩
  rw [one] at l r
  exact (List.mem_singleton.mp l).trans (List.mem_singleton.mp r).symm

theorem no_other_original_type_is_available_at_that_slot418
    {s q} {rows : PlainRows s q} (a : RigidMismatch rows) :
    ¬ ∃ o ∈ s.core.origins, o.slot = rows.payload ∧ o.endpoint = .ordinary (.base .str) := by
  rintro ⟨o,whereAt,whichSlot,asStr⟩
  rw [every_original_observation_at_entry_is_the_same_int_origin418 a whereAt whichSlot,
    a.source.typed] at asStr
  cases asStr

theorem actual_variant_does_not_satisfy_the_full_rigid_str_head418
    {s q} {rows : PlainRows s q} (a : RigidMismatch rows) (m : I72.Model) (fit : Fits s m) :
    ¬ Subtype (m.assignment rows.root).1 (variant rows.tag (.base .str)) := by
  intro comparison
  have original : Equivalent (m.assignment rows.root).1
      (variant rows.tag (m.assignment rows.payload).1) := fit.1.1.2 _ rows.rootRow
  exact (original_int_point_cannot_fit_str418 a m fit).2
    ((common_variant_iff ..).mp (subtype_trans original.2 comparison))

theorem actual_rival_has_no_source_head_in_any_fitting_model418
    {s q} {rows : PlainRows s q} (a : RigidMismatch rows) (m : I72.Model) (fit : Fits s m) :
    ¬ Nonempty (SourceHead s.core q a.rival.candidate.decl) := by
  rintro ⟨head⟩
  cases head with
  | joined inferred =>
    have literal := (List.cons.inj (inferred.head.symm.trans a.rival.literal)).1
    have impossible := inferred.normalized
    rw [literal] at impossible
    change Pattern.variant rows.tag (.app a.rival.strName []) =
      Pattern.variant inferred.tag (.join _ _) at impossible
    cases (Pattern.variant.inj impossible).2
  | ordered capture arguments =>
    have supplied : All₂ (DeepHead s.core capture) [point rows.root]
        [rivalHead418 rows.tag a.rival.strName] := by
      simpa only [rows.requested,a.rival.literal] using arguments
    cases supplied with
    | cons one _ =>
      cases one with
      | declared alleged _ =>
        have wrong := alleged.syntaxHead
        change Pattern.variant rows.tag (.app a.rival.strName []) = .app _ _ at wrong
        cases wrong
      | ordinary observed =>
        have represented := GeneralDeclarativeAssembly320.head_sound observed m.assignment fit.1.1
        have decoded := compiled_normalized (variables := variables capture m.assignment) (literal_rival_translation418 a.rival)
        have same : Equivalent (m.assignment rows.root).1 (variant rows.tag (.base .str)) :=
          eqv_trans represented.1 ⟨decoded.2,decoded.1⟩
        exact actual_variant_does_not_satisfy_the_full_rigid_str_head418 a m fit same.1

end Yulang.GeneralDeclarativeI65.I72.RigidRival418
