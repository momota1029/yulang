import Yulang.GeneralDeclarativeAssembly320

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 13000
set_option maxHeartbeats 3200000
namespace Yulang.GeneralDeclarativeBatch320
open CommonRoleOutermostResolver (All₂)

def zipFacts (f : α → β → Option (List γ)) : List α → List β → Option (List γ)
  | [],[] => some []
  | a::as,b::bs => do
      let one ← f a b
      let tail ← zipFacts f as bs
      pure (one ++ tail)
  | _,_ => none

/-- The finite compilation retains positions and rejects a length mismatch.
Every reported batch is a subset of the actual ordered compiled result. -/
theorem zip_sound {f : α → β → Option (List γ)} {as : List α} {bs : List β} {facts : List γ}
    (compiled : zipFacts f as bs = some facts) :
    All₂ (fun a b => ∃ one, f a b = some one ∧ one ⊆ facts) as bs := by
  induction as generalizing bs facts with
  | nil =>
    cases bs with
    | nil => exact .nil
    | cons => cases compiled
  | cons a as ih =>
    cases bs with
    | nil => cases compiled
    | cons b bs =>
      cases first : f a b with
      | none => simp [zipFacts,first] at compiled
      | some h =>
        cases rest : zipFacts f as bs with
        | none => simp [zipFacts,first,rest] at compiled
        | some tail =>
          have exacts : h ++ tail = facts := by simpa [zipFacts,first,rest] using compiled
          subst facts
          refine .cons ⟨h,first,List.subset_append_left _ _⟩ ?_
          exact GeneralDeclarativeNormalized320.ordered_map (ih rest)
            (fun _ _ _ _ ⟨f,found,included⟩ =>
              ⟨f,found,fun e h => List.mem_append_right _ (included h)⟩)

def collect (f : α → Option (List γ)) : List α → Option (List γ)
  | [] => some []
  | a::as => do
    let one ← f a
    let tail ← collect f as
    pure (one ++ tail)

theorem collect_sound {f : α → Option (List γ)} {as : List α} {facts : List γ}
    (compiled : collect f as = some facts)
    (a : α) (present : a ∈ as) : ∃ one, f a = some one ∧ one ⊆ facts := by
  induction as generalizing facts with
  | nil => cases present
  | cons first tail ih =>
    cases hx : f first with
    | none => simp [collect,hx] at compiled
    | some h =>
      cases hy : collect f tail with
      | none => simp [collect,hx,hy] at compiled
      | some rest =>
        have eq : h ++ rest = facts := by simpa [collect,hx,hy] using compiled
        subst facts
        rcases List.mem_cons.mp present with rfl|later
        · exact ⟨_,hx,List.subset_append_left _ _⟩
        · obtain ⟨f,found,sub⟩ := ih hy later
          exact ⟨f,found,fun _ used => List.mem_append_right _ (sub used)⟩

end Yulang.GeneralDeclarativeBatch320
