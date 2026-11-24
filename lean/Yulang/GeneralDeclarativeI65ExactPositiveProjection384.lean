import Yulang.GeneralDeclarativeI65ExactDependencies384

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open CommonRoleOutermostResolver (All₂ Classify Dictionary Frontier Resolves Result Summarizes Tree)

/-- The exact positive frontier keeps the proof-carrying support
vector, not just an existence claim for each producer request.
Other outcomes remain outside this positive projection. -/
def ExactPositiveFrontier384 (source : ExactSelectedRule384)
    (ordinary : LogicalOutputEquation383) (tagged : ChosenTaggedBinding383) (s : State)
    (q : Request) : Frontier Request → Prop
  | .selected key kids =>
      ∃ needs, source s q needs key kids ∧
        Nonempty (ExactSupportForest384 source ordinary tagged s needs)
  | _ => False

theorem exact_selected_projects_exact_frontier384 {source ordinary tagged s q d}
    (p : ExactSelected384 source ordinary tagged s q d) :
    Classify (ExactPositiveFrontier384 source ordinary tagged s) q (.selected d) := by
  exact ExactSelected384.rec
    (motive_1 := fun q d _ => Classify (ExactPositiveFrontier384 source ordinary tagged s) q (.selected d))
    (motive_2 := fun _ _ => True)
    (motive_3 := fun qs ds _ => ∃ trees : List Tree,
      All₂ (Resolves (ExactPositiveFrontier384 source ordinary tagged s)) qs trees ∧
      All₂ Summarizes trees (ds.map Result.selected))
    (fun rule supports _ _ finished => by
      obtain ⟨trees,found,summary⟩ := finished
      exact ⟨.selected _ trees,.selected ⟨_,rule,⟨supports⟩⟩ found,.selected summary (.selected rfl)⟩)
    True.intro
    (fun _ _ _ _ _ => True.intro)
    ⟨[],.nil,.nil⟩
    (fun _ _ first rest => by
      obtain ⟨t,tAt,tSummary⟩ := first
      obtain ⟨ts,atRest,restSummary⟩ := rest
      exact ⟨t::ts,.cons tAt atRest,.cons tSummary restSummary⟩)
    p

section
variable {source : ExactSelectedRule384} {ordinary : LogicalOutputEquation383}
  {tagged : ChosenTaggedBinding383} {s : State}

mutual
theorem exact_projection_has_selected384
    (t : Tree) {q : Request} {d : Dictionary}
    (read : Resolves (ExactPositiveFrontier384 source ordinary tagged s) q t)
    (summary : Summarizes t (.selected d)) :
    Nonempty (ExactSelected384 source ordinary tagged s q d) := by
  cases read with
  | pending _ => cases summary
  | rejected _ => cases summary
  | ambiguous _ => cases summary
  | selected current subtrees =>
    obtain ⟨_,rule,⟨exactSupports⟩⟩ := current
    cases summary with
    | selected summaries decision =>
      cases decision with
      | selected identity =>
        subst_vars
        obtain ⟨literalWhere⟩ := exact_projection_has_where_forest384 _ _ subtrees summaries
        exact ⟨.selected rule exactSupports literalWhere⟩
termination_by sizeOf t

theorem exact_projection_has_where_forest384
    (trees : List Tree) (ds : List Dictionary) {qs : List Request}
    (read : All₂ (Resolves (ExactPositiveFrontier384 source ordinary tagged s)) qs trees)
    (summaries : All₂ Summarizes trees (ds.map Result.selected)) :
    Nonempty (ExactWhereForest384 source ordinary tagged s qs ds) := by
  cases ds with
  | nil =>
    cases summaries; cases read
    exact ⟨.nil⟩
  | cons head tail =>
    cases summaries with
    | cons first rest =>
      cases read with
      | cons atFirst atRest =>
        obtain ⟨root⟩ := exact_projection_has_selected384 _ atFirst first
        obtain ⟨later⟩ := exact_projection_has_where_forest384 _ _ atRest rest
        exact ⟨.cons root later⟩
termination_by sizeOf trees
end

theorem exact_selected_iff_its_positive_projection384 {q : Request} {d : Dictionary} :
    Nonempty (ExactSelected384 source ordinary tagged s q d) ↔
      Classify (ExactPositiveFrontier384 source ordinary tagged s) q (.selected d) := by
  constructor
  · rintro ⟨selected⟩
    exact exact_selected_projects_exact_frontier384 selected
  · rintro ⟨t,read,summary⟩
    exact exact_projection_has_selected384 t read summary

end
end Yulang.GeneralDeclarativeI65
