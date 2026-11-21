import Yulang.GeneralDeclarativePriority321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeFrontier327
open GeneralDeclarations (Declaration Registry Checked)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeLowerKnown321 (Ready Delayed ready_iff_not_delayed)
open GeneralDeclarativePriority321 (Candidates Visible Survives Blocked Recurs Local)
open CommonRoleOutermostResolver (Frontier)

/-- Opposite of the open lower-authorization/K2 interaction. This
excludes an unchanged undecided boundary, not a new rule of Yulang. -/
def NoOverlap (s : State) (r : Registry) (i : GeneralNominalInspection.Interpretation) {done : Nat → Prop}
    (p : Supported s done) (tests : Candidates) (d : Demand) : Prop :=
  ¬(Delayed p d ∧ Recurs s r i tests d)

def Unique (r : Registry) (tests : Candidates) (d : Demand) (decl : Declaration) : Prop :=
  Survives r tests d decl ∧ ∀ rival, Survives r tests d rival → rival.id = decl.id

def CanGenerate (s : State) (r : Registry) (i : GeneralNominalInspection.Interpretation) {done : Nat → Prop}
    (p : Supported s done) (tests : Candidates)
    (generates : Demand → Declaration → List Demand → Prop) (d : Demand) : Prop :=
  Ready p d → ¬Recurs s r i tests d → ¬Blocked r tests d →
    ∀ decl, Unique r tests d decl → ∃ kids, generates d decl kids

theorem unique_declaration {r : Registry} (checked : Checked r)
    (d : Demand) (picked : Unique r tests d decl) (rival : Survives r tests d other) :
    other = decl := by
  have join {xs : List Declaration} (ids : (xs.map Declaration.id).Nodup)
      (a : other ∈ xs) (b : decl ∈ xs) (same : other.id = decl.id) : other = decl := by
    induction xs with
    | nil => cases a
    | cons x rest ih =>
      obtain ⟨excluded,tail⟩ := List.nodup_cons.mp ids
      rcases List.mem_cons.mp a with rfl|l <;> rcases List.mem_cons.mp b with rfl|q
      · rfl
      · exact False.elim (excluded (same.symm ▸ List.mem_map.mpr ⟨decl,q,rfl⟩))
      · exact False.elim (excluded (same ▸ List.mem_map.mpr ⟨other,l,rfl⟩))
      · exact ih tail l q
  exact join checked.1 rival.1.1 picked.1.1.1 (picked.2 other rival)

/-- Every local outcome is already available except at the known
unsettled overlap, or at a unique positive candidate whose real child
production has not been established. Never turn either absence into
a new pending/rejected verdict. -/
theorem coverage {s : State} {p : Supported s done} (checked : Checked r) :
    (∃ f, Local s r i p tests generates d f) ↔
      NoOverlap s r i p tests d ∧ CanGenerate s r i p tests generates d := by
  classical
  constructor
  · rintro ⟨f,found⟩
    refine ⟨fun ⟨delayed,recursive⟩ => GeneralDeclarativePriority321.overlap_outside_fragment delayed recursive found,?_⟩
    intro ready safe unblocked decl picked
    cases found with
    | unsupported later _ => exact False.elim ((ready_iff_not_delayed p d).mp ready later)
    | recursive _ recurs => exact False.elim (safe recurs)
    | unresolved _ _ blocked => exact False.elim (unblocked blocked)
    | noCandidate _ _ _ excludes => exact False.elim (excludes decl picked.1)
    | ambiguous _ _ _ h k different =>
      exact False.elim (different ((picked.2 _ h).trans (picked.2 _ k).symm))
    | selected _ _ _ existsHere _ children =>
      cases unique_declaration checked d picked existsHere
      exact ⟨_,children⟩
  · rintro ⟨separate,generated⟩
    by_cases later : Delayed p d
    · exact ⟨_,.unsupported later (fun recurs => separate ⟨later,recurs⟩)⟩
    have ready := (ready_iff_not_delayed p d).mpr later
    by_cases recursive : Recurs s r i tests d
    · exact ⟨_,.recursive ready recursive⟩
    by_cases blocked : Blocked r tests d
    · exact ⟨_,.unresolved ready recursive blocked⟩
    by_cases existsHere : ∃ decl, Survives r tests d decl
    · obtain ⟨decl,viable⟩ := existsHere
      by_cases tied : ∃ other, Survives r tests d other ∧ other.id ≠ decl.id
      · obtain ⟨other,survives,different⟩ := tied
        exact ⟨_,.ambiguous ready recursive blocked survives viable different⟩
      have only : ∀ other, Survives r tests d other → other.id = decl.id :=
        fun other some => Classical.byContradiction fun different => tied ⟨other,some,different⟩
      obtain ⟨kids,exactChildren⟩ := generated ready recursive blocked decl ⟨viable,only⟩
      exact ⟨_,.selected ready recursive blocked viable only exactChildren⟩
    · exact ⟨_,.noCandidate ready recursive blocked (fun decl some => existsHere ⟨decl,some⟩)⟩

end Yulang.GeneralDeclarativeFrontier327
