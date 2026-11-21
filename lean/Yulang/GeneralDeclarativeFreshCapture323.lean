import Yulang.GeneralDeclarativeSemanticSharing323
import Yulang.GeneralDeclarativeNewNames321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeFreshCapture323
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralDeclarativeTermCapture322 (first repr_found)
open GeneralDeclarativeTraceNames321 (names)
open GeneralDeclarativeFootprint321 (stateNames value_same)
open GeneralDeclarativeNewNames321 (after before_after)
open GeneralDeclarativeFresh321 (Fresh old_name extend preserves_and_extends)
open GeneralDeclarativeEntailment320 (appendFacts literal model_append)
open GeneralDeclarativeSemanticSharing323 (FirstNames SameBinder SharedAt sufficient)
open GeneralDeclarativeRepeatedActual323 (eqAt)
open GeneralNominalCommonBridge (Assignment)

def avoid (s : State) (protect : List Nat) (seen : List Occurrence) : List Nat :=
  (stateNames s ++ protect) ++ seen.flatMap fun use => names use.term

def center (s : State) (protect : List Nat) (seen : List Occurrence) (binder : Nat) : Nat :=
  after (avoid s protect seen) + binder

def capture (s : State) (protect : List Nat) (seen : List Occurrence)
    (endpoints : Nat → Capture) (binder : Nat) : Capture :=
  { endpoints binder with center := center s protect seen binder }

def definitions (s : State) (protect : List Nat) (seen : List Occurrence) : List Equation :=
  seen.filterMap fun use => (first seen use.binder).map fun rep =>
    ⟨center s protect seen use.binder,rep.term⟩

theorem origin {s : State} {seen : List Occurrence}
    (used : row ∈ definitions s protect seen) :
    ∃ binder rep, first seen binder = some rep ∧ row = ⟨center s protect seen binder,rep.term⟩ := by
  obtain ⟨item,_,chosen⟩ := List.mem_filterMap.mp used
  cases h : first seen item.binder with
  | none => simp [h] at chosen
  | some rep => exact ⟨item.binder,rep,h,by simpa [h] using chosen.symm⟩

theorem has_definition {s : State} {seen : List Occurrence}
    (found : first seen binder = some rep) :
    (⟨center s protect seen binder,rep.term⟩ : Equation) ∈ definitions s protect seen := by
  obtain ⟨present,hasId,_⟩ := repr_found found
  exact List.mem_filterMap.mpr ⟨rep,present,by simp [hasId,found]⟩

theorem avoids {s : State} {seen : List Occurrence}
    (willKeep : n ∈ avoid s protect seen) : center s protect seen binder ≠ n :=
  Nat.ne_of_gt (Nat.lt_of_lt_of_le (before_after willKeep) (Nat.le_add_right ..))

theorem fresh {s : State} {seen : List Occurrence} :
    Fresh s (definitions s protect seen) := by
  refine ⟨?_,?_,?_⟩
  · intro row used appears
    obtain ⟨b,rep,_,rfl⟩ := origin used
    exact avoids (List.mem_append_left _ (List.mem_append_left _ appears)) rfl
  · intro row a other b same
    obtain ⟨firstBinder,rep,x,rfl⟩ := origin a
    obtain ⟨lastBinder,rep',y,rfl⟩ := origin b
    have sameBinder : firstBinder = lastBinder := Nat.add_left_cancel same
    subst lastBinder
    exact congrArg Occurrence.term (Option.some.inj (x.symm.trans y))
  · intro row a other b namesIt
    obtain ⟨_,rep,hasRep,rfl⟩ := origin a
    obtain ⟨_,_,_,rfl⟩ := origin b
    have keep : _ ∈ avoid s protect seen :=
      List.mem_append_right _ (List.mem_flatMap.mpr ⟨rep,(repr_found hasRep).1,namesIt⟩)
    exact avoids keep rfl

theorem anchors {s : State} {seen : List Occurrence} :
    FirstNames (appendFacts s (definitions s protect seen)) seen (capture s protect seen endpoints) :=
  fun _ _ found => literal (List.mem_append_right _ (has_definition found))

theorem model_projection {s : State} {seen : List Occurrence} (m : Assignment) :
    Models s m ↔ ∃ m', Models (appendFacts s (definitions s protect seen)) m' ∧
      ∀ n ∈ avoid s protect seen, m' n = m n := by
  constructor
  · intro valid
    refine ⟨extend m (definitions s protect seen),(preserves_and_extends fresh m valid).1,?_⟩
    intro n old
    exact old_name (fun row h => by obtain ⟨_,_,_,rfl⟩ := origin h; exact avoids old)
  · rintro ⟨m',valid,unchanged⟩
    exact (GeneralDeclarativeFootprint321.preserves_models s
      (fun n h => unchanged n (List.mem_append_left _ (List.mem_append_left _ h)))).mp
      ((model_append m').mp valid).1

/-- Exact model-independent naming without a premise that each compound
already has a name. The only new ordinary facts are fresh definitions of
first observations. This does not convert a fixed associated target to
a fresh one, nor force formerly unequal actual occurrences to agree. -/
theorem fresh_shared {s : State} {seen : List Occurrence}
    (mode : ∀ o ∈ seen, o.mode = .actual) (actualEquality : SameBinder s seen) :
    SharedAt (appendFacts s (definitions s protect seen)) seen (capture s protect seen endpoints) :=
  sufficient mode
    (fun o ho p hp same m valid => actualEquality o ho p hp same m ((model_append m).mp valid).1)
    anchors

end Yulang.GeneralDeclarativeFreshCapture323
