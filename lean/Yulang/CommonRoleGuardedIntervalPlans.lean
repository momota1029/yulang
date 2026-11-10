import Yulang.CommonRoleIntervalWorkClosure

/-! Finite guarded plans for fixed interval syntax. Alternative declarations are
not conjoined; every child of a chosen declaration is required. One global
source valuation relates all chosen branches to real ordinary constraints.
This is not state-dependent saturation, K2 classification, or dictionary selection.
The invocation source map remains an explicit elaborator boundary input. -/
namespace Yulang.CommonRoleGuardedIntervalPlans
open CommonRoleStablePaterson (Declaration)
open CommonRoleIntervalPaterson (Goal expand size)
open CommonRoleIntervalCapture (Bindings total)
open CommonRoleIntervalCandidates (Accepts inspect)
open CommonRoleIntervalWorkClosure (Checked)
open CommonRoleCaptureBatchModels (SharedFits HeadFits demands)
open CommonRoleWhereSourceModels (captureJob)
open CommonRoleSourceIntervalBatches (Demand)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

/-- Equal goal/declaration/binder tuples necessarily share a key in this local
adapter. An occurrence-sensitive invocation allocator is not represented. -/
abbrev Sources := Goal → Declaration → Nat → Nat
abbrev Plan (α : Type) := List (Demand α)

/-- Cartesian conjunction retains order and duplicates. The empty conjunction
has one empty plan; an impossible child makes the entire conjunction empty. -/
def products : List (List (Plan α)) → List (Plan α)
  | [] => [[]]
  | first :: rest => first.flatMap fun before => (products rest).map (before ++ ·)

theorem shared_append (assignment : α → Comp Common.model) (values : Nat → Common.Ty)
    (first last : Plan α) :
    SharedFits assignment values (first ++ last) ↔
      SharedFits assignment values first ∧ SharedFits assignment values last :=
  List.forall_mem_append

/-- Choices are made under one fixed valuation, so sibling aliases cannot be
satisfied by different witnesses. This is not independent existential checking. -/
theorem products_exact (assignment : α → Comp Common.model) (values : Nat → Common.Ty)
    (alternatives : List (List (Plan α))) :
    (∃ plan ∈ products alternatives, SharedFits assignment values plan) ↔
      ∀ choices ∈ alternatives, ∃ plan ∈ choices, SharedFits assignment values plan := by
  induction alternatives with
  | nil => simp [products, SharedFits]
  | cons first rest ih =>
    constructor
    · rintro ⟨plan, member, fits⟩
      obtain ⟨before, present, suffixes⟩ := List.mem_flatMap.mp member
      obtain ⟨suffix, included, rfl⟩ := List.mem_map.mp suffixes
      obtain ⟨left, right⟩ := (shared_append ..).mp fits
      have tail := ih.mp ⟨suffix, included, right⟩
      intro choices member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨before, present, left⟩
      · exact tail choices member
    · intro all
      obtain ⟨before, present, left⟩ := all first (List.mem_cons_self)
      obtain ⟨suffix, included, right⟩ := ih.mpr (fun c h => all c (List.mem_cons_of_mem _ h))
      exact ⟨before ++ suffix, List.mem_flatMap.mpr ⟨before, present,
        List.mem_map.mpr ⟨suffix, included, rfl⟩⟩, (shared_append ..).mpr ⟨left, right⟩⟩

/-- Successful inspections, retaining their independent acceptance proof. -/
def candidates (registry : List Declaration) (goal : Goal) :
    List { entry : Declaration × Bindings // entry.1 ∈ registry ∧ Accepts entry.1 goal entry.2 } :=
  registry.attach.flatMap fun declaration =>
    match found : inspect declaration.val goal with
    | some (some bindings) => [⟨(declaration.val, bindings), declaration.property,
        (CommonRoleIntervalCandidates.inspect_accepts_exact ..).mp found⟩]
    | _ => []

theorem candidates_complete (registry : List Declaration) (goal : Goal)
    (d : Declaration) (b : Bindings) (present : d ∈ registry) (accepted : Accepts d goal b) :
    ∃ entry ∈ candidates registry goal, entry.val = (d, b) := by
  unfold candidates
  refine ⟨⟨(d,b), present, accepted⟩, ?_, rfl⟩
  apply List.mem_flatMap.mpr
  refine ⟨⟨d,present⟩, List.mem_attach _ _, ?_⟩
  dsimp only
  have found := (CommonRoleIntervalCandidates.inspect_accepts_exact d goal b).mpr accepted
  split <;> simp_all

/-- Finite executable complete plans. Descent is from the declaration checker,
not a depth cutoff or an assumed successful child solver. -/
def compile (registry : List Declaration) (checked : Checked registry)
    (slots : Nat → α) (sources : Sources) (goal : Goal) : List (Plan α) :=
  (candidates registry goal).flatMap fun entry =>
    let d := entry.val.1
    let b := entry.val.2
    let localDemands := demands slots (captureJob d goal (sources goal d)) b
    let alternatives := (expand d (total b)).attach.map fun next =>
      compile registry checked slots sources next.val
    (products alternatives).map (localDemands ++ ·)
termination_by size goal.arguments
decreasing_by
  obtain ⟨requirement, included, equal⟩ := List.mem_map.mp next.property
  rw [← equal]
  exact CommonRoleIntervalCandidates.accepted_child_decreases _
    (checked _ entry.property.1) _ _ entry.property.2 _ included

/-- Independent finite declaration derivation. All children must derive at the
same source valuation; unsupported captures have no local derivation. Absence
of this judgment is not a language-visible rejected result. -/
inductive Derives (registry : List Declaration) (slots : Nat → α) (sources : Sources)
    (assignment : α → Comp Common.model) (values : Nat → Common.Ty) : Goal → Prop
  | step (goal : Goal) (d : Declaration) (b : Bindings) :
      d ∈ registry → Accepts d goal b →
      HeadFits (fun n => (assignment (slots n)).1) (values ∘ sources goal d)
        d.head goal.arguments →
      (∀ next ∈ expand d (total b), Derives registry slots sources assignment values next) →
      Derives registry slots sources assignment values goal

theorem local_models_exact (slots : Nat → α) (sources : Sources)
    (assignment : α → Comp Common.model) (values : Nat → Common.Ty)
    (d : Declaration) (goal : Goal) (b : Bindings) (accepted : Accepts d goal b) :
    SharedFits assignment values (demands slots (captureJob d goal (sources goal d)) b) ↔
      HeadFits (fun n => (assignment (slots n)).1) (values ∘ sources goal d)
        d.head goal.arguments := by
  have captured : CommonRoleCaptureBatchModels.Captures (captureJob d goal (sources goal d)) b :=
    ⟨accepted.2.1, accepted.2.2.2.1⟩
  exact (CommonRoleCaptureBatchModels.demands_fits slots assignment values _ b captured).trans
    (CommonRoleWhereSourceModels.normalized_heads _ _ _ _)

/-- Full soundness and completeness for the fixed-syntax guarded fragment.
There is no model, successful-child, fuel, or finite-visit premise. -/
theorem compile_exact (registry : List Declaration) (checked : Checked registry)
    (slots : Nat → α) (sources : Sources) (assignment : α → Comp Common.model)
    (values : Nat → Common.Ty) (goal : Goal) :
    (∃ plan ∈ compile registry checked slots sources goal, SharedFits assignment values plan) ↔
      Derives registry slots sources assignment values goal := by
  rw [compile]
  constructor
  · rintro ⟨plan, member, fits⟩
    obtain ⟨entry, _, member⟩ := List.mem_flatMap.mp member
    obtain ⟨suffix, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨localFits, childrenFit⟩ := (shared_append ..).mp fits
    apply Derives.step goal entry.val.1 entry.val.2 entry.property.1 entry.property.2
      ((local_models_exact slots sources assignment values _ _ _ entry.property.2).mp localFits)
    intro next included
    have all := (products_exact assignment values _).mp ⟨suffix, present, childrenFit⟩
    have hit := all _ (List.mem_map.mpr ⟨⟨next,included⟩, List.mem_attach _ _, rfl⟩)
    exact (compile_exact registry checked slots sources assignment values next).mp hit
  · intro derivation
    cases derivation with
    | step goal d b present accepted head children =>
      obtain ⟨entry, member, same⟩ := candidates_complete registry goal d b present accepted
      have all : ∀ choices ∈ (expand entry.val.1 (total entry.val.2)).attach.map
          (fun next => compile registry checked slots sources next.val),
          ∃ plan ∈ choices, SharedFits assignment values plan := by
        intro choices included
        obtain ⟨next, _, rfl⟩ := List.mem_map.mp included
        apply (compile_exact registry checked slots sources assignment values next.val).mpr
        apply children next.val
        simpa only [same] using next.property
      obtain ⟨suffix, included, fits⟩ := (products_exact assignment values _).mpr all
      refine ⟨_, List.mem_flatMap.mpr ⟨entry, member, List.mem_map.mpr ⟨suffix,included,rfl⟩⟩, ?_⟩
      apply (shared_append ..).mpr
      refine ⟨?_, fits⟩
      simpa only [same] using (local_models_exact slots sources assignment values d goal b accepted).mpr head
termination_by size goal.arguments
decreasing_by
  · obtain ⟨requirement, used, equal⟩ := List.mem_map.mp included
    rw [← equal]
    exact CommonRoleIntervalCandidates.accepted_child_decreases _
      (checked _ entry.property.1) _ _ entry.property.2 _ used
  · obtain ⟨requirement, used, equal⟩ := List.mem_map.mp next.property
    rw [← equal]
    have decrease := CommonRoleIntervalCandidates.accepted_child_decreases _
      (checked _ entry.property.1) _ _ entry.property.2 _ used
    subst_vars
    exact decrease

/-- Real ordinary constraints for each complete alternative. All old/new and
cross-sibling comparisons are emitted together, never independently satisfied. -/
def ordinary (registry : List Declaration) (checked : Checked registry)
    (slots : Nat → α) (sources : Sources) (old : Plan α) (goal : Goal) :=
  (compile registry checked slots sources goal).map fun plan =>
    CommonRoleSourceIntervalBatches.generate (old ++ plan)

/-- All-model outer theorem, with a single shared valuation outside the entire
recursive derivation. It is a finite grammar theorem, not general B4. -/
theorem ordinary_exact (registry : List Declaration) (checked : Checked registry)
    (slots : Nat → α) (sources : Sources) (old : Plan α) (goal : Goal)
    (assignment : α → Comp Common.model) :
    (∃ atoms ∈ ordinary registry checked slots sources old goal, All Common.model assignment atoms) ↔
      ∃ values, SharedFits assignment values old ∧
        Derives registry slots sources assignment values goal := by
  constructor
  · rintro ⟨atoms, member, fits⟩
    obtain ⟨plan, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨values, shared⟩ := CommonRoleCaptureBatchModels.models_shared_exact assignment _ |>.mp
      ((CommonRoleSourceIntervalBatches.generate_exact assignment _).mp fits)
    obtain ⟨previous, localFits⟩ := (shared_append ..).mp shared
    exact ⟨values, previous, (compile_exact registry checked slots sources assignment values goal).mp
      ⟨plan,present,localFits⟩⟩
  · rintro ⟨values, previous, derivation⟩
    obtain ⟨plan, present, fits⟩ :=
      (compile_exact registry checked slots sources assignment values goal).mpr derivation
    refine ⟨_, List.mem_map.mpr ⟨plan,present,rfl⟩, ?_⟩
    apply (CommonRoleSourceIntervalBatches.generate_exact assignment _).mpr
    exact (CommonRoleCaptureBatchModels.models_shared_exact assignment _).mpr
      ⟨values, (shared_append ..).mpr ⟨previous,fits⟩⟩

/-- The public computation checks the registry and keeps every unsupported scan
in a separate boundary list. An empty plan list is not a language rejection. -/
def run (registry : List Declaration) (slots : Nat → α) (sources : Sources)
    (old : Plan α) (goal : Goal) :=
  if checked : registry.all CommonRoleStablePaterson.check = true then
    some (ordinary registry (List.all_eq_true.mp checked) slots sources old goal,
      CommonRoleIntervalWorkClosure.boundaries registry (List.all_eq_true.mp checked) goal)
  else none

/-- No checker proof is supplied by the caller. Successful complete plans are
exactly the independent finite derivations with shared original-source models.
This theorem does not require the separately returned boundary list to be empty. -/
theorem run_models_exact (registry : List Declaration) (slots : Nat → α) (sources : Sources)
    (old : Plan α) (goal : Goal) (assignment : α → Comp Common.model) :
    (∃ output, run registry slots sources old goal = some output ∧
      ∃ atoms ∈ output.1, All Common.model assignment atoms) ↔
    Checked registry ∧ ∃ values, SharedFits assignment values old ∧
      Derives registry slots sources assignment values goal := by
  by_cases checked : registry.all CommonRoleStablePaterson.check = true
  · have wf : Checked registry := List.all_eq_true.mp checked
    constructor
    · rintro ⟨output, returned, models⟩
      have same : (ordinary registry wf slots sources old goal,
          CommonRoleIntervalWorkClosure.boundaries registry wf goal) = output := by
        simpa [run, checked] using returned
      subst output
      exact ⟨wf, (ordinary_exact registry wf slots sources old goal assignment).mp models⟩
    · rintro ⟨_, models⟩
      exact ⟨(ordinary registry wf slots sources old goal,
        CommonRoleIntervalWorkClosure.boundaries registry wf goal), by simp [run, checked],
        (ordinary_exact registry wf slots sources old goal assignment).mpr models⟩
  · have notChecked : ¬ Checked registry := fun wf => checked (List.all_eq_true.mpr wf)
    simp [run, checked, notChecked]

/-- The public result exposes precisely every unsupported inspection at every
potentially reachable goal, including alternatives not chosen in a complete plan. -/
theorem run_boundaries_exact (registry : List Declaration) (slots : Nat → α) (sources : Sources)
    (old : Plan α) (root goal : Goal) (d : Declaration) (output)
    (returned : run registry slots sources old root = some output) :
    (goal, d) ∈ output.2 ↔
      CommonRoleIntervalWorkClosure.Reach registry root goal ∧ d ∈ registry ∧ inspect d goal = none := by
  unfold run at returned
  split at returned
  · rename_i checked
    cases returned
    exact CommonRoleIntervalWorkClosure.boundaries_exact registry (List.all_eq_true.mp checked) root goal d
  · cases returned

end Yulang.CommonRoleGuardedIntervalPlans
