import Yulang.GeneralDeclarativeOpaqueGroup328

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOpaqueShared328
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeOpaqueConserve328 (Retains chain refl)
open GeneralDeclarativeOpaqueGroup328 (group group_exact Sharing linked_group form_group reading)
open GeneralDeclarativeAggregate324 (ready span now_bounds)
open GeneralDeclarativeGrowth327 (restrict derives fits)
open GeneralDeclarativeEqualities322 (Derives entails)
open GeneralDeclarativeOpaqueNested328 (run Builds occurrences)
open GeneralDeclarativeOpaqueCapture328 (ordered_keys)
open GeneralDeclarativeTermWalk322 (Occurrence Binds)
open GeneralDeclarativeNFHead324 (fact)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarationPatterns (normalize)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralDeclarativeTraceNames321 (names)

structure Chosen where
  state : State
  captures : Nat → Capture

def build (keep : List Nat) (seen : List (Nat × Capture)) (base : Nat → Capture)
    (s : State) : List Nat → Chosen
  | [] => ⟨s,base⟩
  | key :: more =>
    match group key seen with
    | [] => build keep seen base s more
    | seed :: rest =>
      let next := build keep seen base (ready s keep seed rest) more
      ⟨next.state,fun n => if n = key then span s keep seed rest else next.captures n⟩

theorem built {s : State} (keep : List Nat) (base : Nat → Capture) (keys : List Nat)
    (intervals : ∀ member ∈ seen, Bounds s member.2) (sharing : Sharing s seen) :
    let b := build keep seen base s keys
    Retains s b.state keep ∧
      ∀ key ∈ keys, ∀ span, (key,span) ∈ seen →
        Bounds b.state (b.captures key) ∧
        Derives b.state (.variable span.center) (.variable (b.captures key).center) := by
  induction keys generalizing s with
  | nil =>
    refine ⟨refl s keep,?_⟩
    intro key none
    cases none
  | cons head more ih =>
    cases stored : group head seen with
    | nil =>
      simp only [build,stored]
      obtain ⟨lift,tied⟩ := ih intervals sharing
      refine ⟨lift,?_⟩
      intro key present span got
      rcases List.mem_cons.mp present with rfl|other
      · have same := (group_exact _ seen).mpr got
        rw [stored] at same
        exact False.elim (List.not_mem_nil same)
      · exact tied key other span got
    | cons seed rest =>
      simp only [build,stored]
      have fitsGroup : ∀ a ∈ seed::rest, Bounds s a :=
        fun a h => intervals (head,a) ((group_exact head seen).mp (stored ▸ h))
      have lift := form_group fitsGroup (linked_group sharing stored) keep
      have nextSharing : Sharing (ready s keep seed rest) seen := by
        intro m valid
        exact sharing m (restrict lift.grows m valid)
      obtain ⟨later,tied⟩ := ih (fun _ listed => fits lift.grows (intervals _ listed)) nextSharing
      refine ⟨chain lift later,?_⟩
      intro key present capture known
      by_cases isSame : key = head
      · subst key
        simp only [ite_true]
        have inGroup := (group_exact head seen).mpr known
        rw [stored] at inGroup
        exact ⟨fits later.grows (now_bounds s keep seed rest),
          derives later.grows (reading fitsGroup keep inGroup)⟩
      · have remains : key ∈ more := (List.mem_cons.mp present).resolve_left isSame
        simpa only [isSame,ite_false] using tied key remains capture known

/-- After naming nested actual occurrences, merge *all* repeated
binders independently according to the approved interval join/meet
law. The one semantic requirement is that actual occurrences of each
binder are equal in every current ordinary model; that requirement is
not inferred from candidate endpoint compatibility. -/
theorem complete {s : State} {arg : Capture} (readback : Builds s keep arg plan)
    (sharing : Sharing (run keep s arg plan).state (run keep s arg plan).binds)
    (printed : translate c i (normalize pat) = some plan.code) (base : Nat → Capture) :
    let known := run keep s arg plan
    let merged := build keep known.binds base known.state (known.binds.map Prod.fst)
    Retains s merged.state keep ∧
    Result merged.state (fact c i merged.captures arg pat) ∧
    ∀ key ∈ names plan.code, Bounds merged.state (merged.captures key) := by
  let known := run keep s arg plan
  let merged := build keep known.binds base known.state (known.binds.map Prod.fst)
  obtain ⟨pushed,recorded⟩ := built keep base (known.binds.map Prod.fst) readback.bounds sharing
  have centers : Binds merged.state merged.captures (occurrences known.binds) := by
    intro o inList
    obtain ⟨⟨key,span⟩,old,rfl⟩ := List.mem_map.mp inList
    exact (recorded key (List.mem_map.mpr ⟨_,old,rfl⟩) span old).2
  refine ⟨chain readback.modeled pushed,GeneralDeclarativeForwardHead325.by_walk printed
    (entails (derives pushed.grows readback.center)) readback.ordered centers,?_⟩
  intro key used
  rw [← ordered_keys readback] at used
  obtain ⟨⟨binder,span⟩,inList,rfl⟩ := List.mem_map.mp used
  exact (recorded _ (List.mem_map.mpr ⟨_,inList,rfl⟩) _ inList).1

end Yulang.GeneralDeclarativeOpaqueShared328
