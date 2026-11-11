import Yulang.CommonRoleDerivedStructuralMaterialization

/-! Input-computed saturation traces for the existing finite ordinary rules.
Fresh carrier indices are emitted in actual firstFresh order; their atoms are consumed
by the full structural diagnostic replay. No caller batches, trace, fuel or
finite carrier are supplied. Role-to-ordinary feedback and fresh allocation
remain outside this finite seed/split/trans driver. -/
namespace Yulang.CommonRoleStructuralSaturationTrace
open PresenceNormalForm (Atom All)
open Core.PresenceGeneration (Comp)
open CommonRoleStructuralMaterializationProgress (Included Chain)
open CommonRoleStablePaterson (Declaration)
open CommonRoleIntervalPaterson (Goal)
open CommonRoleIntervalWorkClosure (Checked)
open CommonRoleGuardedIntervalPlans (Sources)
open CommonRoleSettledConstraints (State)

/-- Trace the existing executable rule selection, with an internal capacity. -/
def discoveries [DecidableEq α] (rules : List (FiniteHorn.Rule α)) (carrierList : List α) :
    Nat → List α → List α
  | 0, _ => []
  | capacity + 1, seen =>
    match FiniteHorn.firstFresh rules seen carrierList with
    | none => []
    | some fact => fact :: discoveries rules carrierList capacity (fact :: seen)

/-- The instrumented algorithm has exactly the old final cache, including order. -/
theorem discoveries_result [DecidableEq α] (rules : List (FiniteHorn.Rule α)) (carrierList : List α)
    (capacity : Nat) (seen : List α) :
    FiniteHorn.run rules carrierList capacity seen = (discoveries rules carrierList capacity seen).reverse ++ seen := by
  induction capacity generalizing seen with
  | zero => rfl
  | succ capacity ih =>
    simp only [FiniteHorn.run,discoveries]
    cases found : FiniteHorn.firstFresh rules seen carrierList with
    | none => rfl
    | some fact => simp only [ih,List.reverse_cons,List.append_assoc,List.singleton_append]

theorem discoveries_length [DecidableEq α] (rules : List (FiniteHorn.Rule α)) (carrierList : List α)
    (capacity : Nat) (seen : List α) : (discoveries rules carrierList capacity seen).length ≤ capacity := by
  induction capacity generalizing seen with
  | zero => exact Nat.le_refl _
  | succ capacity ih =>
    simp only [discoveries]
    cases found : FiniteHorn.firstFresh rules seen carrierList with
    | none => simp
    | some fact => simp only [List.length_cons]; exact Nat.add_le_add_right (ih _) 1

abbrev carrierList (seeds : List (Atom (Fin n))) := seeds ++ CommonRoleFiniteStructuralClosure.carrier seeds

def generated (seeds : List (Atom (Fin n))) : List (Atom (Fin n)) :=
  let u := carrierList seeds
  (discoveries (CommonRoleFiniteStructuralClosure.rules seeds u) (List.finRange u.length) u.length []).map
    (fun index => u[index])

def finalAtoms (seeds : List (Atom (Fin n))) := seeds ++ generated seeds

/-- The final atom multiset keeps discovery order, while membership is exactly
the independently defined ordinary derivation. No successful model is assumed. -/
theorem final_membership (seeds : List (Atom (Fin n))) (atom : Atom (Fin n)) :
    atom ∈ finalAtoms seeds ↔ CommonRoleStructuralCarrierCoverage.Derives seeds atom := by
  rw [← CommonRoleStructuralCarrierCoverage.normalize_membership]
  simp only [finalAtoms,generated,CommonRoleFiniteStructuralClosure.normalize,
    CommonRoleFiniteStructuralClosure.close,CommonRoleFiniteStructuralClosure.seen,FiniteHorn.saturate,
    discoveries_result,List.length_finRange,List.append_nil,List.mem_append,List.mem_map,List.mem_reverse]

/-- A computed carrier controls rule firings; payload-size costs remain explicit. -/
theorem generated_length (seeds : List (Atom (Fin n))) :
    (generated seeds).length ≤ (carrierList seeds).length := by
  simp only [generated,List.length_map]
  exact discoveries_length _ _ _ _

/-- Exhaustion is a real closure test, not a plateau in role materialization. -/
theorem terminal_closed (seeds : List (Atom (Fin n))) :
    let u := carrierList seeds
    FiniteHorn.firstFresh (CommonRoleFiniteStructuralClosure.rules seeds u)
      (discoveries (CommonRoleFiniteStructuralClosure.rules seeds u) (List.finRange u.length) u.length []).reverse
      (List.finRange u.length) = none := by
  dsimp only
  have eq := discoveries_result (CommonRoleFiniteStructuralClosure.rules seeds (carrierList seeds))
    (List.finRange (carrierList seeds).length) (carrierList seeds).length []
  simp only [List.append_nil] at eq
  rw [← eq]
  simpa only [CommonRoleFiniteStructuralClosure.seen,FiniteHorn.saturate,List.length_finRange] using
    CommonRoleFiniteStructuralClosure.stopped seeds (carrierList seeds)

theorem final_models (seeds : List (Atom (Fin n))) (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (finalAtoms seeds) ↔ All Common.model assignment seeds := by
  have same (a : Atom (Fin n)) : a ∈ finalAtoms seeds ↔ a ∈ CommonRoleFiniteStructuralClosure.normalize seeds :=
    (final_membership seeds a).trans (CommonRoleStructuralCarrierCoverage.normalize_membership seeds a).symm
  rw [← CommonRoleFiniteStructuralClosure.normalize_exact seeds assignment]
  exact forall_congr' fun a => imp_congr_left (same a)

/-- Each discovered index contributes its atom in discovery order. Different
indices may carry equal atoms. No earlier atom or
multiplicity is removed; initial constraints remain literally at the front. -/
def accumulate (initial : List (Atom (Fin n))) : List (Atom (Fin n)) → List (List (Atom (Fin n)))
  | [] => []
  | atom :: rest => (initial ++ [atom]) :: accumulate (initial ++ [atom]) rest

theorem accumulate_length (initial extra : List (Atom (Fin n))) :
    (accumulate initial extra).length = extra.length := by
  induction extra generalizing initial with
  | nil => rfl
  | cons atom rest ih => simp only [accumulate,List.length_cons,ih]

theorem accumulate_chain (initial extra : List (Atom (Fin n))) : Chain initial (accumulate initial extra) := by
  induction extra generalizing initial with
  | nil => trivial
  | cons atom rest ih => exact ⟨fun _ h => List.mem_append_left _ h,ih _⟩

theorem accumulate_cover (initial extra : List (Atom (Fin n))) :
    ∀ state ∈ initial :: accumulate initial extra, Included state (initial ++ extra) := by
  induction extra generalizing initial with
  | nil => intro state member; simpa using (List.mem_singleton.mp member ▸ (fun _ h => h) : Included state initial)
  | cons atom rest ih =>
    intro state member
    rcases List.mem_cons.mp member with same | later
    · subst state; exact fun _ h => List.mem_append_left _ h
    · have covered := ih (initial ++ [atom]) state later
      simpa only [List.append_assoc,List.singleton_append] using covered

theorem accumulate_original (initial extra : List (Atom (Fin n))) :
    ∀ state ∈ initial :: accumulate initial extra, Included initial state := by
  induction extra generalizing initial with
  | nil =>
    intro state member
    have eq : state = initial := List.mem_singleton.mp member
    subst state
    exact fun _ h => h
  | cons atom rest ih =>
    intro state member
    rcases List.mem_cons.mp member with same | later
    · subst state; exact fun _ h => h
    · exact fun a h => ih _ state later a (List.mem_append_left _ h)

/-- Every actually generated snapshot has exactly the original model set,
including inconsistent inputs. This is stronger than mere existence preservation. -/
theorem snapshot_models (seeds state : List (Atom (Fin n)))
    (member : state ∈ seeds :: accumulate seeds (generated seeds)) (assignment : Fin n → Comp Common.model) :
    All Common.model assignment state ↔ All Common.model assignment seeds := by
  constructor
  · intro models a ha; exact models a (accumulate_original seeds _ state member a ha)
  · intro models a ha
    exact (final_models seeds assignment).mpr models a (accumulate_cover seeds _ state member a ha)

/-- Runs the real ordinary solver once on the original checked State. All later
snapshots preserve exactly that model set. The finite rule trace is generated
internally, and every snapshot is processed even when a role tree is unchanged. -/
def run (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (goal : Goal) (initial : State n) : Option (CommonRoleStructuralFrontierReplay.Replay n) :=
  if CommonRoleOpenPropagation.consistent initial then
    CommonRoleStructuralFrontierReplay.run registry slots sources goal initial.atoms
      (accumulate initial.atoms (generated initial.atoms))
  else none

theorem run_exact (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (goal : Goal) (initial : State n) (output : CommonRoleStructuralFrontierReplay.Replay n) :
    run registry slots sources goal initial = some output ↔
      initial.Models ∧ ∃ checked : Checked registry,
        output = CommonRoleStructuralFrontierReplay.replay registry checked slots sources goal initial.atoms
          (accumulate initial.atoms (generated initial.atoms)) := by
  unfold run
  split
  · rename_i valid
    rw [CommonRoleStructuralFrontierReplay.run_exact]
    exact (and_iff_right ((CommonRoleOpenPropagation.consistent_exact initial).mp valid)).symm
  · rename_i invalid
    constructor
    · intro impossible; cases impossible
    · rintro ⟨models,_⟩
      exact False.elim (invalid ((CommonRoleOpenPropagation.consistent_exact initial).mpr models))

/-- An entirely computed finite ordinary driver and recursive role replay.
This does not generate new role-to-ordinary equations or dynamically fresh names. -/
theorem run_computed_bound (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (goal : Goal) (initial : State n) (output : CommonRoleStructuralFrontierReplay.Replay n)
    (returned : run registry slots sources goal initial = some output) :
    ∃ bound, CommonRoleStructuralMaterializationDomain.workDomain registry (finalAtoms initial.atoms)
        slots goal = some bound ∧
      output.snapshots.length ≤ 1 + (carrierList initial.atoms).length ∧
      output.rebuilds ≤ 1 + 2 * CommonRoleMaterializationProgress.potential goal ∧
      output.visits ≤ (1 + 2 * CommonRoleMaterializationProgress.potential goal) * bound.length ∧
      ∀ tree ∈ output.snapshots, ∀ target ∈ CommonRoleFrontierReachability.goals tree, target ∈ bound := by
  obtain ⟨_,checked,rfl⟩ := (run_exact ..).mp returned
  refine ⟨_,(CommonRoleStructuralMaterializationDomain.workDomain_exact ..).mpr ⟨checked,rfl⟩,?_,?_,?_,?_⟩
  · rw [CommonRoleStructuralFrontierReplay.replay_snapshots,List.length_map,List.length_cons,accumulate_length]
    have h := generated_length initial.atoms
    omega
  · exact (CommonRoleStructuralFrontierReplay.replay_bounded registry checked slots sources goal
      initial.atoms _ _ (accumulate_chain _ _) (accumulate_cover _ _)).1
  · exact (CommonRoleStructuralFrontierReplay.replay_bounded registry checked slots sources goal
      initial.atoms _ _ (accumulate_chain _ _) (accumulate_cover _ _)).2
  · intro tree member target node
    exact CommonRoleStructuralFrontierReplay.replay_work_present registry checked slots sources goal
      initial.atoms _ _ (accumulate_cover _ _) tree member target node


/-- The discovered atom order differs from the older cache order, but the final
materialized syntax is exactly the normalized original-state observation. -/
theorem final_materialize (seeds : List (Atom (Fin n))) (slots : Nat → Fin n)
    (form : CommonRoleCaptureNormalization.Form) :
    CommonRoleStructuralOrdinaryMaterialization.materialize (finalAtoms seeds) slots form =
      CommonRoleDerivedStructuralMaterialization.materialize seeds slots form :=
  CommonRoleStructuralOrdinaryMaterialization.materialize_congr _ _
    (fun a => (final_membership seeds a).trans
      (CommonRoleStructuralCarrierCoverage.normalize_membership seeds a).symm) slots form

/-- Every snapshot's graph family is exact over the original assignment, not
just over a selected solver model. Regenerated role demands remain explicit. -/
theorem snapshot_graph_models_exact (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (seeds state : List (Atom (Fin n))) (member : state ∈ seeds :: accumulate seeds (generated seeds))
    (old : CommonRoleGuardedIntervalPlans.Plan (Fin n)) (goal : Goal) (assignment : Fin n → Comp Common.model) :
    (∃ output, CommonRoleStructuralOrdinaryMaterialization.run registry slots sources state old goal = some output ∧
      CommonRoleFrontierGraphs.Represents output.2 assignment) ↔
      Checked registry ∧ All Common.model assignment seeds ∧ ∃ sourceValues,
        CommonRoleCaptureBatchModels.SharedFits assignment sourceValues old ∧
          CommonRoleGuardedIntervalPlans.Derives registry slots sources assignment sourceValues
            (CommonRoleStructuralOrdinaryMaterialization.materializeGoal state slots goal) := by
  change (∃ output, CommonRoleFrontierGraphs.run registry slots sources state old
      (CommonRoleStructuralOrdinaryMaterialization.materializeGoal state slots goal) = some output ∧
      CommonRoleFrontierGraphs.Represents output.2 assignment) ↔ _
  rw [CommonRoleFrontierGraphs.run_models_exact,snapshot_models seeds state member assignment]

/-- Refreshes ordinary graphs at every generated snapshot while retaining exact
cached diagnostics. The old demands are indexed by generated occurrence. -/
def runGraphs (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (goal : Goal) (initial : State n) (old : Nat → CommonRoleGuardedIntervalPlans.Plan (Fin n)) :=
  if CommonRoleOpenPropagation.consistent initial then
    CommonRoleStructuralFrontierReplay.runGraphs registry slots sources goal initial.atoms
      (accumulate initial.atoms (generated initial.atoms)) old
  else none

/-- No trace, graph, work list or successful role result is supplied. Fresh
public graph outputs are equal at every computed ordinary-state occurrence. -/
theorem runGraphs_exact (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (goal : Goal) (initial : State n) (old : Nat → CommonRoleGuardedIntervalPlans.Plan (Fin n))
    (output : CommonRoleStructuralFrontierReplay.Replay n)
    (returned : run registry slots sources goal initial = some output) :
    ∃ graphs, runGraphs registry slots sources goal initial old = some (output,graphs) ∧
      graphs.map some = (initial.atoms :: accumulate initial.atoms (generated initial.atoms)).mapIdx
        (fun i atoms => CommonRoleStructuralOrdinaryMaterialization.run registry slots sources atoms (old i) goal) := by
  have valid := (CommonRoleOpenPropagation.consistent_exact initial).mpr ((run_exact ..).mp returned).1
  simp only [runGraphs,valid,ite_true]
  apply CommonRoleStructuralFrontierReplay.runGraphs_exact
  simpa only [run,valid,ite_true] using returned

end Yulang.CommonRoleStructuralSaturationTrace

namespace Yulang.CommonRoleStructuralSaturationTrace
/-- An independent small-step certificate for the discovery sequence. Every
new carrier fact is absent from the prior cache and enabled by already present
premises. This judgment does not call firstFresh, run or discoveries. -/
inductive Execution (rules : List (FiniteHorn.Rule α)) : List α → List α → Prop where
  | done (seen) : Execution rules seen []
  | step (fact) : fact ∉ seen → FiniteHorn.Enabled rules seen fact →
      Execution rules (fact :: seen) rest → Execution rules seen (fact :: rest)

/-- Every actual iteration has a causal rule witness at that exact earlier
cache, not merely a derivation in the eventual closure. -/
theorem discoveries_execution [DecidableEq α] (rules : List (FiniteHorn.Rule α)) (facts : List α)
    (capacity : Nat) (seen : List α) : Execution rules seen (discoveries rules facts capacity seen) := by
  induction capacity generalizing seen with
  | zero => exact .done seen
  | succ capacity ih =>
    simp only [discoveries]
    cases found : FiniteHorn.firstFresh rules seen facts with
    | none => exact .done seen
    | some fact =>
      have selected := FiniteHorn.firstFresh_some rules seen facts found
      exact .step fact selected.2.1 selected.2.2 (ih _)

/-- The syntax-generated finite execution is both causally valid and terminal.
Unlike a temporary role-tree plateau, no enabled fresh carrier fact remains. -/
theorem generated_execution_complete (seeds : List (PresenceNormalForm.Atom (Fin n))) :
    let u := carrierList seeds
    let rules := CommonRoleFiniteStructuralClosure.rules seeds u
    let discovered := discoveries rules (List.finRange u.length) u.length []
    Execution rules [] discovered ∧
      FiniteHorn.firstFresh rules discovered.reverse (List.finRange u.length) = none :=
  ⟨discoveries_execution _ _ _ _,terminal_closed seeds⟩
end Yulang.CommonRoleStructuralSaturationTrace
