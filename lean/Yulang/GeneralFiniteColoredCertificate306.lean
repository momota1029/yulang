import Yulang.GeneralFiniteColoredQuotient306

namespace Yulang.GeneralFiniteColoredCertificate306
open GeneralFiniteColoredRounds306 (Closed On)
open GeneralFiniteColoredQuotient306 (fastQuotient fast_exact projection_minimal)
variable {α β κ : Type} [DecidableEq α] [DecidableEq β] [DecidableEq κ]

def closureCheck (edges : α → List α) (nodes : List α) : Bool :=
  nodes.all fun s => (edges s).all fun t => decide (t ∈ nodes)

theorem closure_exact (edges : α → List α) (nodes : List α) :
    closureCheck edges nodes = true ↔ Closed edges nodes := by
  simp only [closureCheck,Closed,List.all_eq_true,decide_eq_true_eq]

def checkPair (edges : α → List α) (color : α → β) (project : α → κ) (s t : α) : Bool :=
  if project s = project t then
    decide (color s = color t) && GeneralFiniteBisimRefinement306.refine edges
      (fun a b => decide (project a = project b)) s t
  else true

def certificate (edges : α → List α) (color : α → β) (project : α → κ) (nodes : List α) : Bool :=
  closureCheck edges nodes && nodes.all fun s => nodes.all fun t => checkPair edges color project s t

theorem certificate_exact (edges : α → List α) (color : α → β) (project : α → κ) (nodes : List α) :
    certificate edges color project nodes = true ↔
      Closed edges nodes ∧ On edges color nodes (fun a b => project a = project b) := by
  rw [certificate,Bool.and_eq_true_iff,closure_exact]
  apply and_congr Iff.rfl
  simp only [List.all_eq_true]
  constructor
  · intro each x xm y ym yes
    have pair := each x xm y ym
    simpa only [checkPair,ite_eq_left yes,GeneralFiniteBisimRefinement306.refine,
      Bool.and_eq_true_iff,decide_eq_true_eq,List.all_eq_true,List.any_eq_true] using pair
  · intro supplied x xm y ym
    by_cases same : project x = project y
    · have pair := supplied x xm y ym same
      simpa only [checkPair,ite_eq_left same,GeneralFiniteBisimRefinement306.refine,
        Bool.and_eq_true_iff,decide_eq_true_eq,List.all_eq_true,List.any_eq_true] using pair
    · simp [checkPair,same]

theorem checked_edges {edges : α → List α} {color : α → β} {project : α → κ} {nodes : List α}
    (checked : certificate edges color project nodes = true) {s t : α} (sm : s ∈ nodes) (tm : t ∈ nodes)
    (same : project s = project t) (goal : κ) :
    goal ∈ (edges s).map project ↔ goal ∈ (edges t).map project := by
  have guard := (certificate_exact ..).mp checked |>.2 s sm t tm same
  rw [List.mem_map,List.mem_map]
  constructor
  · rintro ⟨a,edge,eq⟩
    obtain ⟨b,step,matching⟩ := guard.2.1 a edge
    exact ⟨b,step,matching.symm.trans eq⟩
  · rintro ⟨b,edge,eq⟩
    obtain ⟨a,step,matching⟩ := guard.2.2 b edge
    exact ⟨a,step,matching.trans eq⟩

theorem verified_submission_refines_minimum {edges : α → List α} {color : α → β}
    {project : α → κ} {nodes : List α} (checked : certificate edges color project nodes = true)
    {s t : α} (sm : s ∈ nodes) (tm : t ∈ nodes) (same : project s = project t) :
    (fastQuotient edges color nodes).project s = (fastQuotient edges color nodes).project t := by
  obtain ⟨closed,valid⟩ := (certificate_exact ..).mp checked
  rw [fast_exact]
  exact projection_minimal closed valid sm tm same

end Yulang.GeneralFiniteColoredCertificate306
