import Yulang.GeneralDeclarativeStableOrigin329

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStableGraph329
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeStableTies329 (Use rows row)
open GeneralDeclarativeStableOrigin329 (same_direct_heads)
open GeneralDeclarativeLowerKnown321 (Alias alias_refl)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Graph321 (Descends Path aliasView View)
open GeneralDeclarativeK2Alias321 (AliasCycle)

inductive Linked (s : State) (selected : Nat → Capture) (uses : List Use) : Nat → Nat → Prop where
  | old : Alias s a b → Linked s selected uses a b
  | forward : u ∈ uses → Linked s selected uses (selected u.1).center u.2
  | backward : u ∈ uses → Linked s selected uses u.2 (selected u.1).center
  | trans : Linked s selected uses a b → Linked s selected uses b c → Linked s selected uses a c

theorem aliases {s : State} (selected : Nat → Capture) (uses : List Use) :
    Alias (appendFacts s (rows selected uses)) a b ↔ Linked s selected uses a b := by
  constructor
  · intro current
    induction current with
    | bounds lo hi => exact .old (.bounds lo hi)
    | @forward a b present =>
      rcases List.mem_append.mp present with before|after
      · exact .old (.forward before)
      · obtain ⟨u,found,tied⟩ := List.mem_map.mp after
        have left := congrArg Equation.left tied
        have right := congrArg Equation.right tied
        change (selected u.1).center = a at left
        change (GeneralNominalCenteredHeadMatExpressions.Expr.variable u.2) = .variable b at right
        cases left
        cases right
        exact .forward (List.mem_filter.mp found).1
    | @backward a b present =>
      rcases List.mem_append.mp present with before|after
      · exact .old (.backward before)
      · obtain ⟨u,found,tied⟩ := List.mem_map.mp after
        have left := congrArg Equation.left tied
        have right := congrArg Equation.right tied
        change (selected u.1).center = a at left
        change (GeneralNominalCenteredHeadMatExpressions.Expr.variable u.2) = .variable b at right
        cases left
        cases right
        exact .backward (List.mem_filter.mp found).1
    | trans _ _ h k => exact .trans h k
  · intro known
    induction known with
    | old before =>
      exact GeneralDeclarativeLowerKnown321.alias_mono (s := s) (t := appendFacts s (rows selected uses))
        rfl (fun _ v => List.mem_append_left _ v) before
    | @forward u src =>
      by_cases same : u.2 = (selected u.1).center
      · rw [same]; exact alias_refl _
      · exact .forward (List.mem_append_right _
          (List.mem_map.mpr ⟨u,List.mem_filter.mpr ⟨src,by simp [same]⟩,rfl⟩))
    | @backward u src =>
      by_cases same : u.2 = (selected u.1).center
      · rw [same]; exact alias_refl _
      · exact .backward (List.mem_append_right _
          (List.mem_map.mpr ⟨u,List.mem_filter.mpr ⟨src,by simp [same]⟩,rfl⟩))
    | trans _ _ h k => exact .trans h k

def view (s : State) (selected : Nat → Capture) (uses : List Use) : View :=
  fun root tag => ∃ owner, Linked s selected uses root owner ∧ observed s owner tag

theorem edge {s : State} (selected : Nat → Capture) (uses : List Use) :
    Descends (aliasView (appendFacts s (rows selected uses)) (observed (appendFacts s (rows selected uses)))) a b ↔
      Descends (view s selected uses) a b := by
  constructor
  · rintro ⟨tag,⟨owner,alias,real⟩,member⟩
    exact ⟨tag,⟨owner,(aliases selected uses).mp alias,(same_direct_heads selected uses owner tag).mp real⟩,member⟩
  · rintro ⟨tag,⟨owner,alias,real⟩,member⟩
    exact ⟨tag,⟨owner,(aliases selected uses).mpr alias,(same_direct_heads selected uses owner tag).mpr real⟩,member⟩

theorem paths {s : State} (selected : Nat → Capture) (uses : List Use) :
    Path (aliasView (appendFacts s (rows selected uses)) (observed (appendFacts s (rows selected uses)))) a b ↔
      Path (view s selected uses) a b := by
  constructor
  · intro based
    induction based with
    | refl => exact .refl _
    | next e _ rest => exact .next ((edge selected uses).mp e) rest
  · intro simplified
    induction simplified with
    | refl => exact .refl _
    | next e _ rest => exact .next ((edge selected uses).mpr e) rest

/-- The selected equality batch can affect K2 only through exactly
the induced old alias classes plus the new center identifications;
the ordinary constructor observations themselves do not change. -/
theorem cycles {s : State} (selected : Nat → Capture) (uses : List Use) (n : Nat) :
    AliasCycle (appendFacts s (rows selected uses)) (observed (appendFacts s (rows selected uses))) n ↔
      ∃ a b, Descends (view s selected uses) n a ∧ Path (view s selected uses) a b ∧
        Linked s selected uses b n := by
  constructor
  · rintro ⟨a,b,first,later,closed⟩
    exact ⟨a,b,(edge selected uses).mp first,(paths selected uses).mp later,(aliases selected uses).mp closed⟩
  · rintro ⟨a,b,first,later,closed⟩
    exact ⟨a,b,(edge selected uses).mpr first,(paths selected uses).mpr later,(aliases selected uses).mpr closed⟩

end Yulang.GeneralDeclarativeStableGraph329
