import Yulang.GeneralDeclarativeI65FiniteCompletion383

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open CommonRoleOutermostResolver (All₂ Classify Tree Dictionary Result Resolves Summarizes)

/-- Build the literal support forest from already available finite
selected proofs. There is no scheduling, search, or order of obtaining
them in this statement. -/
theorem completed_forest_at_literal_requests383
    {source : SelectedSourceRule383} {s : State} (requests : List Request)
    (completed : ∀ q ∈ requests, FiniteCompleted383 source s q) :
    ∃ ds, Nonempty (SelectedSourceForest383 source s requests ds) := by
  induction requests with
  | nil => exact ⟨[],⟨.nil⟩⟩
  | cons first rest ih =>
    obtain ⟨d,⟨head⟩⟩ := completed first List.mem_cons_self
    obtain ⟨ds,⟨tail⟩⟩ := ih (fun q present => completed q (List.mem_cons_of_mem _ present))
    exact ⟨d::ds,⟨.cons head tail⟩⟩

section
variable {source : SelectedSourceRule383} {s : State}

mutual
/-- Recover an exact finite positive derivation from its structured
positive judgment. The producer subproofs are already carried by
the local membership evidence, not recovered from the key list. -/
theorem projected_selected_has_finite_proof383
    (t : Tree) {q : Request} {d : Dictionary}
    (derived : Resolves (SupportedSelectedFrontier383 source s) q t)
    (summary : Summarizes t (.selected d)) :
    Nonempty (SelectedSourceProof383 source s q d) := by
  cases derived with
  | pending _ => cases summary
  | ambiguous _ => cases summary
  | rejected _ => cases summary
  | selected localStep actualKids =>
    obtain ⟨deps,rule,completed⟩ := localStep
    obtain ⟨supportDicts,⟨supports⟩⟩ := completed_forest_at_literal_requests383 deps completed
    cases summary with
    | selected summaries decision =>
      cases decision with
      | selected literal =>
        subst_vars
        obtain ⟨whereProof⟩ := projected_where_forest_has_finite_proof383 _ _ actualKids summaries
        exact ⟨.selected rule supports whereProof⟩
termination_by sizeOf t

theorem projected_where_forest_has_finite_proof383 (trees : List Tree) (dicts : List Dictionary)
    {kids : List Request}
    (derived : All₂ (Resolves (SupportedSelectedFrontier383 source s)) kids trees)
    (summaries : All₂ Summarizes trees (dicts.map Result.selected)) :
    Nonempty (SelectedSourceForest383 source s kids dicts) := by
  cases dicts with
  | nil =>
    cases summaries
    cases derived
    exact ⟨.nil⟩
  | cons head tail =>
    cases summaries with
    | cons first next =>
      cases derived with
      | cons derivedFirst derivedNext =>
        obtain ⟨ready⟩ := projected_selected_has_finite_proof383 _ derivedFirst first
        obtain ⟨rest⟩ := projected_where_forest_has_finite_proof383 _ _ derivedNext next
        exact ⟨.cons ready rest⟩
termination_by sizeOf trees
end

/-- Exact I-67 completion equivalence at the *positive source-rule
interface*. It supplies neither the actual selected source rules nor
the remaining diagnostic cases of the general classifier. -/
theorem finite_selected_iff_projected_classifies383 {q : Request} {d : Dictionary} :
    Nonempty (SelectedSourceProof383 source s q d) ↔
      Classify (SupportedSelectedFrontier383 source s) q (.selected d) := by
  constructor
  · rintro ⟨proof⟩
    exact selected_proof_projects_literal_where383 proof
  · rintro ⟨t,sourceProof,summary⟩
    exact projected_selected_has_finite_proof383 t sourceProof summary

theorem finite_completion_iff_projected_selected_exists383 {q : Request} :
    FiniteCompleted383 source s q ↔
      ∃ d, Classify (SupportedSelectedFrontier383 source s) q (.selected d) := by
  constructor
  · rintro ⟨d,proof⟩
    exact ⟨d, finite_selected_iff_projected_classifies383.mp proof⟩
  · rintro ⟨d,chosen⟩
    exact ⟨d, finite_selected_iff_projected_classifies383.mpr chosen⟩

end
end Yulang.GeneralDeclarativeI65
