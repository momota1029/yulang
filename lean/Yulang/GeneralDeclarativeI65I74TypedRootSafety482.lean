import Yulang.GeneralDeclarativeI65I74ScopedRouteSound480
import Yulang.GeneralDeclarativeI65I74FiniteCheckedObservation473

namespace Yulang.GeneralDeclarativeI65.I72.TypedRootSafety482
open ObservationAlternatives473 (Positions oldPosition graphOf)
open LiteralVisits473 (Checkpoint GuardedObservationInput readCheck
  checkpoint_does_not_substitute_a_place_or_change_its_bit
  independent_checkpoint_reifies_the_exact_site_and_sign)
open QuotientObservation471 (ReturnsUpToEquality)
open RetainedFull445 (FullProblem)

def noRootReturnBool (s : GeneralDeclarativeI65.State) (pos : Positions n)
    (rel : List (Fin n × Fin n)) : List Nat → List (Checkpoint n) → Bool
  | [], [] => true
  | lower :: rest, node :: nodes =>
    decide (readCheck s pos rel (.logical lower) node = some false) &&
    noRootReturnBool s pos rel rest nodes
  | _, _ => false

def AllRootSafe (s : GeneralDeclarativeI65.State) (pos : Positions n) : List Nat → List (Fin n) → Prop
  | [], [] => True
  | lower :: rest, node :: nodes =>
    oldPosition pos node = .logical lower ∧
    ¬ReturnsUpToEquality (graphOf s pos) node ∧ AllRootSafe s pos rest nodes
  | _, _ => False

theorem allRootCheckSound (s : GeneralDeclarativeI65.State) (pos : Positions n)
    (rel : List (Fin n × Fin n)) (lowers : List Nat) (nodes : List (Checkpoint n))
    (ran : noRootReturnBool s pos rel lowers nodes = true) :
    AllRootSafe s pos lowers (nodes.map Checkpoint.which) := by
  induction lowers generalizing nodes with
  | nil => cases nodes <;> simp_all [noRootReturnBool,AllRootSafe]
  | cons lower rest ih =>
    cases nodes with
    | nil => simp [noRootReturnBool] at ran
    | cons node nodes =>
      have exactRun := Bool.and_eq_true_iff.mp ran
      have actual := checkpoint_does_not_substitute_a_place_or_change_its_bit (of_decide_eq_true exactRun.1)
      exact ⟨actual.1,fun cycle => Bool.false_ne_true (actual.2.mpr cycle),ih _ exactRun.2⟩

theorem allRootCheckComplete (s : GeneralDeclarativeI65.State) (pos : Positions n)
    (rel : List (Fin n × Fin n)) (lowers : List Nat) (coordinates : List (Fin n))
    (exactAt : AllRootSafe s pos lowers coordinates)
    (guarded : ∀ i ∈ coordinates, GuardedObservationInput s pos rel i) :
    ∃ nodes : List (Checkpoint n), nodes.map Checkpoint.which = coordinates ∧
      noRootReturnBool s pos rel lowers nodes = true := by
  induction lowers generalizing coordinates with
  | nil =>
    cases coordinates with
    | nil => exact ⟨[],rfl,rfl⟩
    | cons => exact False.elim exactAt
  | cons lower rest ih =>
    cases coordinates with
    | nil => exact False.elim exactAt
    | cons node nodes =>
      obtain ⟨located,safe,tail⟩ := exactAt
      have sign : false = true ↔ ReturnsUpToEquality (graphOf s pos) node :=
        ⟨fun bad => False.elim (Bool.false_ne_true bad),fun cyc => False.elim (safe cyc)⟩
      obtain ⟨w,which,read⟩ := independent_checkpoint_reifies_the_exact_site_and_sign
        (guarded node (List.mem_cons_self ..)) false sign
      rw [located] at read
      obtain ⟨ws,each,covers⟩ := ih nodes tail (fun i mem => guarded i (List.mem_cons_of_mem _ mem))
      exact ⟨w :: ws,by simp only [List.map_cons,which,each],
        by simp [noRootReturnBool,read,covers]⟩

def requestRootCheck (p : FullProblem) (pos : Positions n) (rel : List (Fin n × Fin n))
    (nodes : List (Checkpoint n)) : Bool :=
  noRootReturnBool p.old.state.core pos rel (p.old.root.demand.arguments.map (fun a => a.lower)) nodes

theorem requestRootCheckSound (p : FullProblem) (pos : Positions n) (rel : List (Fin n × Fin n))
    (nodes : List (Checkpoint n)) (ran : requestRootCheck p pos rel nodes = true) :
    AllRootSafe p.old.state.core pos (p.old.root.demand.arguments.map (fun a => a.lower))
      (nodes.map Checkpoint.which) :=
  allRootCheckSound _ _ _ _ _ ran

theorem allRootCheckCovers (s : GeneralDeclarativeI65.State) (pos : Positions n)
    (lowers : List Nat) (ixs : List (Fin n))
    (valid : AllRootSafe s pos lowers ixs) :
    ∀ lower ∈ lowers, ∃ i ∈ ixs,
      oldPosition pos i = .logical lower ∧ ¬ReturnsUpToEquality (graphOf s pos) i := by
  induction lowers generalizing ixs with
  | nil => simp
  | cons head rest ih =>
    cases ixs with
    | nil => exact False.elim valid
    | cons first tail =>
      intro lower mem
      obtain ⟨loc,safe,remaining⟩ := valid
      rcases List.mem_cons.mp mem with h | h
      · subst lower
        exact ⟨first,List.mem_cons_self ..,loc,safe⟩
      · obtain ⟨i,inside,same,yes⟩ := ih tail remaining lower h
        exact ⟨i,List.mem_cons_of_mem _ inside,same,yes⟩

theorem actualRequestRootCoverage (p : FullProblem) (pos : Positions n) (rel : List (Fin n × Fin n))
    (nodes : List (Checkpoint n)) (ran : requestRootCheck p pos rel nodes = true) :
    ∀ argument ∈ p.old.root.demand.arguments, ∃ i ∈ nodes.map Checkpoint.which,
      oldPosition pos i = .logical argument.lower ∧
      ¬ReturnsUpToEquality (graphOf p.old.state.core pos) i := by
  intro argument mem
  exact allRootCheckCovers _ _ _ _ (requestRootCheckSound _ _ _ _ ran) _
    (List.mem_map.mpr ⟨argument,mem,rfl⟩)


end Yulang.GeneralDeclarativeI65.I72.TypedRootSafety482
