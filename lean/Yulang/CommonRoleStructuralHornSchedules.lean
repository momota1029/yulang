import Yulang.CommonRoleStructuralAssociatedReplay

/-! Arbitrary causal schedules for the finite mixed structural closure.
Only fresh atomic additions are counted; no fairness premise or bounded-depth
cutoff is hidden. A maximal finite schedule is exact, and the actual computed
schedule is proved maximal. This is not arbitrary language-level scheduling. -/
namespace Yulang.CommonRoleStructuralHornSchedules
open PresenceNormalForm (Atom All)
open Core.PresenceGeneration (Comp)
open CommonRoleStructuralHornClosure (Clause Derives carrierAtoms saturate generated)
open CommonRoleFiniteStructuralClosure (compose)

/-- One independent causal step, with all premises in the preceding cache. -/
inductive Step (seeds : List (Atom (Fin n))) (clauses : List (Clause n))
    (seen : List (Atom (Fin n))) : Atom (Fin n) → Prop
  | seed (a) : a ∈ seeds → Step seeds clauses seen a
  | split (a b) : a ∈ seen → b ∈ CommonRoleStructuralDecomposition.atom a → Step seeds clauses seen b
  | trans (a b c) : a ∈ seen → b ∈ seen → c ∈ compose a b → Step seeds clauses seen c
  | clause (r) : r ∈ clauses → (∀ a ∈ r.premises, a ∈ seen) → Step seeds clauses seen r.conclusion

/-- Independent execution may choose any enabled fresh atom at each step. -/
inductive Execution (seeds : List (Atom (Fin n))) (clauses : List (Clause n)) :
    List (Atom (Fin n)) → List (Atom (Fin n)) → Prop
  | done (seen) : Execution seeds clauses seen []
  | step (a) : a ∉ seen → Step seeds clauses seen a →
      Execution seeds clauses (a :: seen) rest → Execution seeds clauses seen (a :: rest)

def finish (seen trace : List (Atom (Fin n))) := trace.reverse ++ seen
def Closed (seeds : List (Atom (Fin n))) (clauses : List (Clause n)) (seen : List (Atom (Fin n))) :=
  ∀ a, Step seeds clauses seen a → a ∈ seen

theorem step_sound {seeds : List (Atom (Fin n))} {clauses : List (Clause n)} {seen a}
    (known : ∀ b ∈ seen, Derives seeds clauses b) (step : Step seeds clauses seen a) :
    Derives seeds clauses a := by
  cases step with
  | seed a member => exact .seed a member
  | split a b member split => exact .split _ _ (known a member) split
  | trans a b c ma mb trans => exact .trans _ _ _ (known a ma) (known b mb) trans
  | clause r member premises => exact .clause r member (fun a h => known a (premises a h))

theorem execution_sound {seeds : List (Atom (Fin n))} {clauses : List (Clause n)} {seen trace}
    (run : Execution seeds clauses seen trace) (known : ∀ a ∈ seen, Derives seeds clauses a) :
    ∀ a ∈ finish seen trace, Derives seeds clauses a := by
  induction run with
  | done seen => exact known
  | @step seen rest a fresh step run ih =>
    have next : ∀ b ∈ a :: seen, Derives seeds clauses b := by
      intro b member
      rcases List.mem_cons.mp member with rfl | member
      · exact step_sound known step
      · exact known b member
    simpa only [finish,List.reverse_cons,List.append_assoc,List.singleton_append] using ih next

theorem execution_nodup {seeds : List (Atom (Fin n))} {clauses : List (Clause n)} {seen trace}
    (run : Execution seeds clauses seen trace) (distinct : seen.Nodup) : (finish seen trace).Nodup := by
  induction run with
  | done seen => exact distinct
  | step a fresh _ _ ih =>
    simpa only [finish,List.reverse_cons,List.append_assoc,List.singleton_append] using
      ih (List.nodup_cons.mpr ⟨fresh,distinct⟩)

/-- Every legal fresh execution consumes the same finite syntax capacity,
regardless of its choices. This also excludes infinite fresh executions. -/
theorem execution_bounded {seeds : List (Atom (Fin n))} {clauses : List (Clause n)} {seen trace}
    (run : Execution seeds clauses seen trace) (distinct : seen.Nodup)
    (known : ∀ a ∈ seen, Derives seeds clauses a) :
    trace.length + seen.length ≤ (carrierAtoms seeds clauses).length := by
  have bound := (execution_nodup run distinct).length_le_of_subset
    (fun a member => CommonRoleStructuralHornClosure.derives_coverage (execution_sound run known a member))
  simpa only [finish,List.length_append,List.length_reverse] using bound

/-- A closed cache contains every independent derivation, not just every step
that happened to be chosen during an execution. -/
theorem closed_complete {seeds : List (Atom (Fin n))} {clauses : List (Clause n)} {seen a}
    (closed : Closed seeds clauses seen) (derived : Derives seeds clauses a) : a ∈ seen := by
  induction derived with
  | seed a member => exact closed a (.seed a member)
  | split a b _ member ih => exact closed b (.split a b ih member)
  | trans a b c _ _ member iha ihb => exact closed c (.trans a b c iha ihb member)
  | clause r member _ ih => exact closed r.conclusion (.clause r member ih)

/-- Maximal finite executions have one exact least result, with no chosen
candidate, successful model, or caller-supplied carrier assumption. -/
theorem execution_exact {seeds : List (Atom (Fin n))} {clauses : List (Clause n)} {trace}
    (run : Execution seeds clauses [] trace) (closed : Closed seeds clauses (finish [] trace)) (a) :
    a ∈ finish [] trace ↔ Derives seeds clauses a :=
  ⟨execution_sound run (by simp) a,closed_complete closed⟩

theorem schedules_confluent {seeds : List (Atom (Fin n))} {clauses : List (Clause n)} {left right}
    (lrun : Execution seeds clauses [] left) (lclosed : Closed seeds clauses (finish [] left))
    (rrun : Execution seeds clauses [] right) (rclosed : Closed seeds clauses (finish [] right)) (a) :
    a ∈ finish [] left ↔ a ∈ finish [] right :=
  (execution_exact lrun lclosed a).trans (execution_exact rrun rclosed a).symm

/-- Decode a compiled rule witness into the independent one-step judgment. -/
theorem enabled_step (seeds : List (Atom (Fin n))) (clauses : List (Clause n)) (seen : List (Atom (Fin n)))
    (a : Atom (Fin n)) (enabled : FiniteHorn.Enabled (CommonRoleStructuralHornClosure.rules seeds clauses) seen a) :
    Step seeds clauses seen a := by
  obtain ⟨r,member,same,premises⟩ := enabled
  subst a
  rcases List.mem_append.mp member with ordinary | role
  · rcases List.mem_append.mp ordinary with early | trans
    · rcases List.mem_append.mp early with seed | split
      · obtain ⟨a,seedMem,rfl⟩ := List.mem_map.mp seed
        exact .seed a seedMem
      · obtain ⟨a,_,split⟩ := List.mem_flatMap.mp split
        obtain ⟨b,splitMem,rfl⟩ := List.mem_map.mp split
        exact .split a b (premises _ (by simp)) splitMem
    · obtain ⟨a,_,trans⟩ := List.mem_flatMap.mp trans
      obtain ⟨b,_,trans⟩ := List.mem_flatMap.mp trans
      obtain ⟨c,transMem,rfl⟩ := List.mem_map.mp trans
      exact .trans a b c (premises _ (by simp)) (premises _ (by simp)) transMem
  · exact .clause r role premises

/-- The real firstFresh instrumented execution obeys the independent rules. -/
theorem generated_execution (seeds : List (Atom (Fin n))) (clauses : List (Clause n)) :
    Execution seeds clauses [] (generated seeds clauses) := by
  have transfer (seen trace : List (Atom (Fin n)))
      (raw : CommonRoleStructuralSaturationTrace.Execution
        (CommonRoleStructuralHornClosure.rules seeds clauses) seen trace) :
      Execution seeds clauses seen trace := by
    induction raw with
    | done seen => exact .done seen
    | step a fresh enabled _ ih => exact .step a fresh (enabled_step _ _ _ _ enabled) ih
  exact transfer [] _ (CommonRoleStructuralHornClosure.generated_execution_complete seeds clauses).1

theorem saturated_closed (seeds : List (Atom (Fin n))) (clauses : List (Clause n)) :
    Closed seeds clauses (saturate seeds clauses) := by
  intro a step
  exact (CommonRoleStructuralHornClosure.saturate_exact ..).mpr
    (step_sound (fun b h => (CommonRoleStructuralHornClosure.saturate_exact ..).mp h) step)

/-- Actual termination and exactness meet at a concrete independent schedule. -/
theorem generated_complete (seeds : List (Atom (Fin n))) (clauses : List (Clause n)) :
    Execution seeds clauses [] (generated seeds clauses) ∧
      Closed seeds clauses (finish [] (generated seeds clauses)) ∧
      (generated seeds clauses).length ≤ (carrierAtoms seeds clauses).length := by
  refine ⟨generated_execution seeds clauses,?_,?_⟩
  · simpa only [finish,List.append_nil,CommonRoleStructuralHornClosure.generated_reverse] using saturated_closed seeds clauses
  · simpa using execution_bounded (generated_execution seeds clauses) (by simp) (by simp)

/-- Any maximal legal schedule has the same all-model semantics as the actual
implementation; no list-order equality is required. Fresh complete caches
have the same multiplicities, as the permutation theorem below makes explicit. -/
theorem schedule_models {seeds : List (Atom (Fin n))} {clauses : List (Clause n)} {trace}
    (run : Execution seeds clauses [] trace) (closed : Closed seeds clauses (finish [] trace))
    (v : Fin n → Comp Common.model) :
    All Common.model v (finish [] trace) ↔ All Common.model v (saturate seeds clauses) :=
  forall_congr' fun a => imp_congr_left ((execution_exact run closed a).trans
    (CommonRoleStructuralHornClosure.saturate_exact seeds clauses a).symm)

/-- Structural materialization is identical, not merely model equivalent,
after any maximal legal ordinary/associated firing order. -/
theorem schedule_materialize {seeds : List (Atom (Fin n))} {clauses : List (Clause n)} {trace}
    (run : Execution seeds clauses [] trace) (closed : Closed seeds clauses (finish [] trace))
    (slots : Nat → Fin n) (form : CommonRoleCaptureNormalization.Form) :
    CommonRoleStructuralOrdinaryMaterialization.materialize (finish [] trace) slots form =
      CommonRoleStructuralOrdinaryMaterialization.materialize (saturate seeds clauses) slots form :=
  CommonRoleStructuralOrdinaryMaterialization.materialize_congr _ _
    (fun a => (execution_exact run closed a).trans (CommonRoleStructuralHornClosure.saturate_exact seeds clauses a).symm)
    slots form

/-- Fresh complete caches agree as multisets, not just as sets. In particular,
no schedule can do more atomic insertions by repeating a previously known atom. -/
theorem schedules_perm {seeds : List (Atom (Fin n))} {clauses : List (Clause n)} {left right}
    (lrun : Execution seeds clauses [] left) (lclosed : Closed seeds clauses (finish [] left))
    (rrun : Execution seeds clauses [] right) (rclosed : Closed seeds clauses (finish [] right)) :
    (finish [] left).Perm (finish [] right) :=
  (List.perm_ext_iff_of_nodup (execution_nodup lrun (by simp)) (execution_nodup rrun (by simp))).mpr
    (schedules_confluent lrun lclosed rrun rclosed)

/-- Equal atomic insertion count does not assert equal runtime or equal numbers
of diagnostic tree rebuilds, which may depend on the intermediate schedule. -/
theorem schedules_length {seeds : List (Atom (Fin n))} {clauses : List (Clause n)} {left right}
    (lrun : Execution seeds clauses [] left) (lclosed : Closed seeds clauses (finish [] left))
    (rrun : Execution seeds clauses [] right) (rclosed : Closed seeds clauses (finish [] right)) :
    left.length = right.length := by
  simpa only [finish,List.length_append,List.length_reverse,List.length_nil,Nat.add_zero] using
    (schedules_perm lrun lclosed rrun rclosed).length_eq

/-- Every complete causal schedule builds literally the same final diagnostic
root and all child branches for a fixed registry and source mapping. -/
theorem schedule_tree {seeds : List (Atom (Fin n))} {clauses : List (Clause n)} {trace}
    (run : Execution seeds clauses [] trace) (closed : Closed seeds clauses (finish [] trace))
    (registry : List CommonRoleStablePaterson.Declaration) (checked : CommonRoleIntervalWorkClosure.Checked registry)
    (slots : Nat → Fin n) (sources : CommonRoleGuardedIntervalPlans.Sources) (goal : CommonRoleIntervalPaterson.Goal) :
    CommonRoleGuardedIntervalFrontier.build registry checked slots sources
      (CommonRoleStructuralOrdinaryMaterialization.materializeGoal (finish [] trace) slots goal) =
    CommonRoleGuardedIntervalFrontier.build registry checked slots sources
      (CommonRoleStructuralOrdinaryMaterialization.materializeGoal (saturate seeds clauses) slots goal) := by
  apply congrArg (CommonRoleGuardedIntervalFrontier.build registry checked slots sources)
  unfold CommonRoleStructuralOrdinaryMaterialization.materializeGoal
  congr 1
  apply List.map_congr_left
  intro pair _
  simp only [schedule_materialize run closed slots]

end Yulang.CommonRoleStructuralHornSchedules
