import Yulang.GeneralDeclarativeOpaqueNested328
import Yulang.GeneralDeclarativeTermOccurrences322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOpaqueCapture328
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeOpaqueNested328 (Named run occurrences Builds)
open GeneralDeclarativeOpaquePlan328 (Plan)
open GeneralDeclarativeTermWalk322 (Occurrence Binds)
open GeneralDeclarativeTermOccurrences322 (actual_positions)
open GeneralDeclarativeNFHead324 (fact)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeTraceNames321 (names)
open GeneralDeclarationPatterns (normalize)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralDeclarativeEqualities322 (entails)

def choose (fallback : Nat → Capture) (key : Nat) : List (Nat × Capture) → Capture
  | [] => fallback key
  | (n,span) :: rest => if key = n then span else choose fallback key rest

theorem choice_exact (keys : (captures.map Prod.fst).Nodup)
    (given : (key,span) ∈ captures) :
    choose fallback key captures = span := by
  induction captures with
  | nil => cases given
  | cons named rest ih =>
    obtain ⟨n,supported⟩ := named
    obtain ⟨notUsed,tail⟩ := List.nodup_cons.mp keys
    rcases List.mem_cons.mp given with same|inRest
    · cases same
      simp [choose]
    · have diff : key ≠ n := by
        intro eq
        exact notUsed (eq ▸ List.mem_map.mpr ⟨(key,span),inRest,rfl⟩)
      simp [choose,diff,ih tail inRest]

theorem actual_binds {s : State} (plain : (captures.map Prod.fst).Nodup) :
    Binds s (fun n => choose fallback n captures) (occurrences captures) := by
  intro o existsHere
  obtain ⟨⟨key,span⟩,there,rfl⟩ := List.mem_map.mp existsHere
  change GeneralDeclarativeEqualities322.Derives s (.variable span.center)
      (.variable (choose fallback key captures).center)
  rw [choice_exact plain there]
  exact .refl _

theorem ordered_keys {s : State} {arg : Capture} (fixed : Builds s keep arg plan) :
    (run keep s arg plan).binds.map Prod.fst = names plan.code := by
  simpa only [occurrences,List.map_map,Function.comp_def] using (actual_positions fixed.ordered).1

/-- For an actual finite shape with distinct source binders, captured
centers/intervals come directly from the interpreted ordered occurrence
list. This builds the ordinary head batch, not a new candidate filter. -/
theorem result {s : State} {arg : Capture} (fixed : Builds s keep arg plan)
    (linear : (names plan.code).Nodup)
    (printed : translate c i (normalize pat) = some plan.code) (fallback : Nat → Capture) :
    let built := run keep s arg plan
    let capture := fun n => choose fallback n built.binds
    Result built.state (fact c i capture arg pat) ∧
      ∀ binder ∈ names plan.code, Bounds built.state (capture binder) := by
  have known := ordered_keys fixed
  have fresh : ((run keep s arg plan).binds.map Prod.fst).Nodup := known.symm ▸ linear
  refine ⟨GeneralDeclarativeForwardHead325.by_walk printed (entails fixed.center)
    fixed.ordered (actual_binds fresh),?_⟩
  intro binder tracked
  rw [← known] at tracked
  obtain ⟨⟨key,span⟩,member,rfl⟩ := List.mem_map.mp tracked
  dsimp only
  rw [choice_exact fresh member]
  exact fixed.bounds _ member

end Yulang.GeneralDeclarativeOpaqueCapture328
