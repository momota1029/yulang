import Yulang.GeneralDeclarativeI65I72GroundedCanonical405

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open GeneralDeclarativeWhere319 (Capture)
open CommonRoleOutermostResolver (Result)

def changeOnlyCenters405 (before : Nat → Capture) (next : Nat → Nat) : Nat → Capture :=
  fun n => { before n with center := next n }

/-- The declaration-only native guard/capture-endpoint witness does
not observe any choice of a center name. Context/mode, type and row
bounds, syntactic positions, and the *same* ordered binding leaves
are preserved. This does not rename an actual chosen event. -/
noncomputable def declared_guard_ignores_centers405 {s : GeneralDeclarativeI65.State}
    {capture ctx pat lo hi leaves} (read : DeepRead s capture ctx pat lo hi leaves) (next : Nat → Nat) :
    DeepRead s (changeOnlyCenters405 capture next) ctx pat lo hi leaves := by
  exact DeepRead.rec (s := s) (capture := capture)
    (motive_1 := fun ctx p lo hi found _ => DeepRead s (changeOnlyCenters405 capture next) ctx p lo hi found)
    (motive_2 := fun ctx params pats lo hi found _ =>
      DeepArguments s (changeOnlyCenters405 capture next) ctx params pats lo hi found)
    (motive_3 := fun ctx param pat lo hi found _ =>
      DeepArgument s (changeOnlyCenters405 capture next) ctx param pat lo hi found)
    (fun actual => .bind ⟨actual.lowToSlot,actual.slotToLow,actual.highToSlot,actual.slotToHigh⟩)
    (fun use names table _ children => .nominal use names table children)
    .nil
    (fun _ _ head tail => .cons head tail)
    (fun _ result => .covariantValue result)
    (fun _ result => .contravariantValue result)
    (fun _ _ left right => .invariantValue left right)
    (fun coverage => .unusedValue coverage)
    (fun links => .covariantRow ⟨links.lowToSlot,links.slotToLow,links.highToSlot,links.slotToHigh⟩)
    (fun links => .contravariantRow ⟨links.lowToSlot,links.slotToLow,links.highToSlot,links.slotToHigh⟩)
    (fun first second => .invariantRow ⟨first.lowToSlot,first.slotToLow,first.highToSlot,first.slotToHigh⟩ ⟨second.lowToSlot,second.slotToLow,second.highToSlot,second.slotToHigh⟩)
    (fun coverage => .unusedRow coverage)
    read

/-- Precise negative control on a proposed proof of native selection:
even fixing the exact outer endpoint pair and binding list does not
let the guard alone recover a literal binder-center name. This is
underdetermination of the old proof carrier, not a language behavior
or permission to replace the independently supplied actual center. -/
theorem declared_guard_alone_cannot_name_selected_center405
    {s : GeneralDeclarativeI65.State} {capture ctx pat lo hi leaves}
    (read : DeepRead s capture ctx pat lo hi leaves) (name : Nat) :
    ¬ ∃ actual : Nat, ∀ (other : Nat → Capture),
      (∀ n, (other n).lower = (capture n).lower ∧ (other n).upper = (capture n).upper) →
      Nonempty (DeepRead s other ctx pat lo hi leaves) → (other name).center = actual := by
  rintro ⟨actual,guard⟩
  have center := guard (changeOnlyCenters405 capture (fun _ => actual+1))
    (fun _ => ⟨rfl,rfl⟩) ⟨declared_guard_ignores_centers405 read _⟩
  change actual + 1 = actual at center
  omega

def changeRequestCenters405 (q : Request) (next : Nat → Nat) : Request :=
  { q with demand := { q.demand with arguments := List.map (fun a : Capture => { a with center := next a.center }) q.demand.arguments } }

theorem raw_k2_observes_only_demand_lower_names405 (s : State) (q : Request) (next : Nat → Nat) :
    RootCycle s (changeRequestCenters405 q next) ↔ RootCycle s q := by
  constructor
  · rintro ⟨arg,there,cyclic⟩
    obtain ⟨old,atOld,equal⟩ := List.mem_map.mp there
    subst arg
    exact ⟨old,atOld,cyclic⟩
  · rintro ⟨old,atOld,cyclic⟩
    exact ⟨{old with center := next old.center},List.mem_map_of_mem atOld,cyclic⟩

def NativeEntryAddress405.replaceRequestCenters {s q row need}
    (address : NativeEntryAddress405 s q row need) (next : Nat → Nat) :
    NativeEntryAddress405 s (changeRequestCenters405 q next) row need where
  entry :=
    { visibleRow := address.entry.visibleRow
      input := { address.entry.input with center := next address.entry.input.center }
      exactInput := by simp [changeRequestCenters405,address.entry.exactInput]
      written := address.entry.written
      exactHead := address.entry.exactHead
      key := address.entry.key
      child := address.entry.child
      dispatch := address.entry.dispatch
      actualLower := address.entry.actualLower
      lowerChild := address.entry.lowerChild
      lowerTerm := address.entry.lowerTerm
      upper := address.entry.upper
      upperAuthored := address.entry.upperAuthored
      upperRoute := address.entry.upperRoute
      upperChild := address.entry.upperChild
      upperSyntax := address.entry.upperSyntax
      query := address.entry.query
      exactChild := address.entry.exactChild
      inspecting := address.entry.inspecting }
  visibleOrdinal := address.visibleOrdinal
  visitedRow := address.visitedRow
  rawOrdinal := address.rawOrdinal
  fromVisible := address.fromVisible
  visitedOriginal := address.visitedOriginal

def GroundedK2Rejection405.replaceRequestCenters {s q} (run : GroundedK2Rejection405 s q)
    (next : Nat → Nat) : GroundedK2Rejection405 s (changeRequestCenters405 q next) :=
  match run with
  | .raw cyclic => .raw ((raw_k2_observes_only_demand_lower_names405 s q next).mpr cyclic)
  | .entered safe support i lookup address recurrent =>
    .entered (fun hit => safe ((raw_k2_observes_only_demand_lower_names405 s q next).mp hit))
      support i lookup (address.replaceRequestCenters next) recurrent

/-- For the actual represented rejection rules, changing only a
demand-center spelling leaves the exact recorded candidate addresses
and diagnostic unchanged. It does not justify changing the center of
a chosen body, its ties, or its generated requests. -/
theorem k2_replay_ignores_center_spelling405 {s q} (run : GroundedK2Rejection405 s q) (next : Nat → Nat) :
    (run.replaceRequestCenters next).visits = run.visits ∧
      Classifies completedChoiceSource404 s (changeRequestCenters405 q next) .rejected := by
  refine ⟨?_,k2_replay_rejects_without_model405 (run.replaceRequestCenters next)⟩
  cases run <;> rfl

end Yulang.GeneralDeclarativeI65.I72
