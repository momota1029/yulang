import Yulang.CommonRoleRepeatedCaptureChecks
import Yulang.CommonRoleSourceIntervalBatches

/-! Original declaration heads and source-named interval batches.
This is the existing finite structural capture boundary, not general candidate
eligibility. Resolved source names and ambient endpoint slots remain separate
inputs. No central type is selected by the executable collector. Declaration
requirements are retained in jobs but their child materialization is separate. -/
namespace Yulang.CommonRoleCaptureBatchModels
open CommonRoleCaptureNormalization (Form)
open CommonRoleStablePaterson (Declaration)
open CommonRoleIntervalPaterson (Argument Goal)
open CommonRoleIntervalCapture (Bindings Capture CaptureArguments captureArguments)
open CommonRoleSourceIntervalBatches (Demand State)
open Core.PresenceGeneration (Comp TyTerm)
open CommonRoleIntervals (Fits evaluate)
open PresenceNormalForm (Atom All)

def HeadFits (ambient locals : Nat → Common.Ty) : List Form → List Argument → Prop
  | [], [] => True
  | form :: forms, argument :: arguments =>
      Fits (evaluate (Form.eval ambient) argument) (form.eval locals) ∧
        HeadFits ambient locals forms arguments
  | _, _ => False

def BindingFits (ambient locals : Nat → Common.Ty) (bindings : Bindings) : Prop :=
  ∀ binding ∈ bindings, Fits (evaluate (Form.eval ambient) binding.2) (locals binding.1)

private theorem binding_append (ambient locals : Nat → Common.Ty) (first last : Bindings) :
    BindingFits ambient locals (first ++ last) ↔
      BindingFits ambient locals first ∧ BindingFits ambient locals last :=
  List.forall_mem_append

private theorem fits_pair (a b c d x y : Common.Ty) :
    Fits (Common.pair a b, Common.pair c d) (Common.pair x y) ↔
      Fits (a,c) x ∧ Fits (b,d) y := by
  change (Common.model.subTy (Common.pair a b) (Common.pair x y) ∧
    Common.model.subTy (Common.pair x y) (Common.pair c d)) ↔ _
  rw [Common.common_pair_iff, Common.common_pair_iff]
  exact ⟨fun ⟨⟨a,b⟩,⟨c,d⟩⟩ => ⟨⟨a,c⟩,⟨b,d⟩⟩,
    fun ⟨⟨a,c⟩,⟨b,d⟩⟩ => ⟨⟨a,b⟩,⟨c,d⟩⟩⟩

private theorem fits_tick (a b x : Common.Ty) :
    Fits (Common.variant 0 a, Common.variant 0 b) (Common.variant 0 x) ↔ Fits (a,b) x := by
  change (Common.model.subTy (Common.variant 0 a) (Common.variant 0 x) ∧
    Common.model.subTy (Common.variant 0 x) (Common.variant 0 b)) ↔ _
  rw [Common.common_variant_iff, Common.common_variant_iff]
  rfl

/-- Exactness against the original head, including repeated occurrences.
The capture derivation states the finite structural boundary explicitly. -/
theorem capture_fits (ambient locals : Nat → Common.Ty)
    (captured : Capture form argument bindings) :
    Fits (evaluate (Form.eval ambient) argument) (form.eval locals) ↔
      BindingFits ambient locals bindings := by
  induction captured with
  | var name argument => simp [BindingFits, Form.eval]
  | int => simp [BindingFits, Fits, evaluate, Form.eval, Common.subtype_refl]
  | pair before after ihFirst ihLast =>
      change Fits (Common.pair _ _, Common.pair _ _) (Common.pair _ _) ↔ _
      rw [fits_pair, binding_append]
      exact and_congr ihFirst ihLast
  | tick inner ih =>
      change Fits (Common.variant 0 _, Common.variant 0 _) (Common.variant 0 _) ↔ _
      exact (fits_tick ..).trans ih

theorem capture_arguments_fits (ambient locals : Nat → Common.Ty)
    (captured : CaptureArguments forms arguments bindings) :
    HeadFits ambient locals forms arguments ↔ BindingFits ambient locals bindings := by
  induction captured with
  | nil => simp [HeadFits, BindingFits]
  | cons first rest ih =>
      change (_ ∧ _) ↔ _
      rw [capture_fits ambient locals first, ih]
      exact (binding_append ..).symm

/-- The map is the enclosing elaborator's resolved source identity, not the
binder's spelling and not equality of endpoint type values. -/
structure Job where
  declaration : Declaration
  goal : Goal
  source : Nat → Nat

def Captures (job : Job) (bindings : Bindings) : Prop :=
  job.declaration.role = job.goal.role ∧
    CaptureArguments job.declaration.head job.goal.arguments bindings

def captureJob (job : Job) : Option Bindings :=
  if job.declaration.role = job.goal.role then
    captureArguments job.declaration.head job.goal.arguments else none

theorem capture_job_exact (job : Job) (bindings : Bindings) :
    captureJob job = some bindings ↔ Captures job bindings := by
  by_cases same : job.declaration.role = job.goal.role
  · simp [captureJob, Captures, same, CommonRoleIntervalCapture.capture_arguments_exact]
  · simp [captureJob, Captures, same]

def demands (slots : Nat → α) (job : Job) (bindings : Bindings) : List (Demand α) :=
  bindings.map fun binding => (job.source binding.1,
    ((CommonRoleRepeatedCaptureChecks.term binding.2.1).rename slots,
     (CommonRoleRepeatedCaptureChecks.term binding.2.2).rename slots))

def SharedFits (assignment : α → Comp Common.model) (values : Nat → Common.Ty)
    (requests : List (Demand α)) : Prop :=
  ∀ request ∈ requests,
    Fits (evaluate (CommonRoleIntervalGeneration.eval assignment) request.2) (values request.1)

private theorem shared_append (assignment : α → Comp Common.model)
    (values : Nat → Common.Ty) (first last : List (Demand α)) :
    SharedFits assignment values (first ++ last) ↔
      SharedFits assignment values first ∧ SharedFits assignment values last :=
  List.forall_mem_append

/-- The proof-level witness is shared by every occurrence of a resolved name. -/
theorem models_shared_exact (assignment : α → Comp Common.model) (requests : List (Demand α)) :
    CommonRoleSourceIntervalBatches.Models assignment requests ↔
      ∃ values, SharedFits assignment values requests := by
  constructor
  · intro models
    refine ⟨fun name => Classical.choose (models name), ?_⟩
    intro request member
    exact Classical.choose_spec (models request.1) request member rfl
  · rintro ⟨values, fits⟩ name
    refine ⟨values name, ?_⟩
    intro request member same
    simpa [same] using fits request member

theorem demands_fits (slots : Nat → α) (assignment : α → Comp Common.model)
    (values : Nat → Common.Ty) (job : Job) (bindings : Bindings)
    (captured : Captures job bindings) :
    SharedFits assignment values (demands slots job bindings) ↔
      HeadFits (fun name => (assignment (slots name)).1) (values ∘ job.source)
        job.declaration.head job.goal.arguments := by
  have fits := capture_arguments_fits (fun name => (assignment (slots name)).1)
    (values ∘ job.source) captured.2
  apply Iff.trans ?_ fits.symm
  simp only [SharedFits, demands, List.forall_mem_map, BindingFits, evaluate,
    CommonRoleIntervalGeneration.eval, TyTerm.eval_rename,
    CommonRoleRepeatedCaptureChecks.term_eval, Function.comp_def]

def collect (slots : Nat → α) : List Job → Option (List (List (Demand α)))
  | [] => some []
  | job :: jobs => do
      let bindings ← captureJob job
      let rest ← collect slots jobs
      pure (demands slots job bindings :: rest)

/-- Independent structural derivations, with original declaration and goal
retained; it is not a call to the collector or ordinary solver. -/
inductive Captured (slots : Nat → α) : List Job → List (List (Demand α)) → Prop where
  | nil : Captured slots [] []
  | cons : Captures job bindings → Captured slots jobs batches →
      Captured slots (job :: jobs) (demands slots job bindings :: batches)

theorem collect_exact (slots : Nat → α) (jobs : List Job) (batches : List (List (Demand α))) :
    collect slots jobs = some batches ↔ Captured slots jobs batches := by
  constructor
  · intro returned
    induction jobs generalizing batches with
    | nil => simp [collect] at returned; subst batches; exact .nil
    | cons job jobs ih =>
        cases first : captureJob job with
        | none => simp [collect, first] at returned
        | some bindings =>
            cases rest : collect slots jobs with
            | none => simp [collect, first, rest] at returned
            | some later =>
                have same : demands slots job bindings :: later = batches := by
                  simpa [collect, first, rest] using returned
                subst batches
                exact .cons ((capture_job_exact ..).mp first) (ih _ rest)
  · intro captured
    induction captured with
    | nil => rfl
    | cons first rest ih => simp [collect, (capture_job_exact ..).mpr first, ih]

def HeadsFit (slots : Nat → α) (assignment : α → Comp Common.model)
    (values : Nat → Common.Ty) (jobs : List Job) : Prop :=
  ∀ job ∈ jobs, job.declaration.role = job.goal.role ∧
    HeadFits (fun name => (assignment (slots name)).1) (values ∘ job.source)
      job.declaration.head job.goal.arguments

theorem captured_fits (slots : Nat → α) (assignment : α → Comp Common.model)
    (values : Nat → Common.Ty) (captured : Captured slots jobs batches) :
    SharedFits assignment values batches.flatten ↔ HeadsFit slots assignment values jobs := by
  induction captured with
  | nil => simp [SharedFits, HeadsFit]
  | @cons job bindings jobs batches first rest ih =>
      rw [List.flatten_cons, shared_append]
      rw [demands_fits slots assignment values job bindings first, ih]
      simp only [HeadsFit, List.forall_mem_cons, first.1, true_and]

/-- All original declaration heads and all prior demands share one semantic
valuation. No model-consistency assumption is needed. -/
theorem run_models_exact (slots : Nat → α) (assignment : α → Comp Common.model)
    (old : List (Demand α)) (jobs : List Job) (batches : List (List (Demand α)))
    (captured : Captured slots jobs batches) :
    All Common.model assignment
      (CommonRoleSourceIntervalBatches.run (CommonRoleSourceIntervalBatches.start old) batches).atoms ↔
    ∃ values, SharedFits assignment values old ∧ HeadsFit slots assignment values jobs := by
  rw [CommonRoleSourceIntervalBatches.run_exact, models_shared_exact]
  apply exists_congr
  intro values
  rw [shared_append]
  rw [captured_fits slots assignment values captured]

def run (slots : Nat → α) (old : List (Demand α)) (jobs : List Job) : Option (State α) :=
  (collect slots jobs).map (CommonRoleSourceIntervalBatches.run
    (CommonRoleSourceIntervalBatches.start old))

/-- Public positive-return exactness has no capture-success or model premise.
Structural failure is not classified as semantic rejection by this theorem. -/
theorem run_exact (slots : Nat → α) (assignment : α → Comp Common.model)
    (old : List (Demand α)) (jobs : List Job) (state : State α) :
    (run slots old jobs = some state ∧ All Common.model assignment state.atoms) ↔
      ∃ batches, Captured slots jobs batches ∧
        CommonRoleSourceIntervalBatches.run (CommonRoleSourceIntervalBatches.start old) batches = state ∧
        ∃ values, SharedFits assignment values old ∧ HeadsFit slots assignment values jobs := by
  simp only [run, Option.map_eq_some_iff, collect_exact]
  constructor
  · rintro ⟨⟨batches, captured, rfl⟩, model⟩
    exact ⟨batches, captured, rfl, (run_models_exact slots assignment old jobs batches captured).mp model⟩
  · rintro ⟨batches, captured, rfl, model⟩
    exact ⟨⟨batches, captured, rfl⟩, (run_models_exact slots assignment old jobs batches captured).mpr model⟩

/-- Successful collection is precisely the independent finite capture boundary;
inside it, compatibility is exactly the original-head model, not a chosen
substitution replay or an assumed successful solver. -/
theorem run_satisfiable_exact (slots : Nat → α) (assignment : α → Comp Common.model)
    (old : List (Demand α)) (jobs : List Job) :
    (∃ state, run slots old jobs = some state ∧ All Common.model assignment state.atoms) ↔
      (∃ batches, Captured slots jobs batches) ∧
        ∃ values, SharedFits assignment values old ∧ HeadsFit slots assignment values jobs := by
  constructor
  · rintro ⟨state, result⟩
    obtain ⟨batches, captured, _, model⟩ := (run_exact slots assignment old jobs state).mp result
    exact ⟨⟨batches, captured⟩, model⟩
  · rintro ⟨⟨batches, captured⟩, model⟩
    exact ⟨_, (run_exact slots assignment old jobs _).mpr ⟨batches, captured, rfl, model⟩⟩

/-- This premise is only the actual executable return. Neither consistency,
a preselected source valuation nor a semantic invariant is a premise. -/
theorem returned_models_exact (slots : Nat → α) (assignment : α → Comp Common.model)
    (old : List (Demand α)) (jobs : List Job) (state : State α)
    (returned : run slots old jobs = some state) :
    All Common.model assignment state.atoms ↔
      ∃ values, SharedFits assignment values old ∧ HeadsFit slots assignment values jobs := by
  obtain ⟨batches, collected, same⟩ := Option.map_eq_some_iff.mp returned
  have captured := (collect_exact slots jobs batches).mp collected
  rw [← same]
  exact run_models_exact slots assignment old jobs batches captured

/-- Every original assignment has an extension to the existing graph compiler
exactly when every old atom, old source demand and original declaration head
has its independent shared model. Original type and row readback is literal. -/
theorem compile_returned_exact (slots : Nat → Fin n)
    (existing : List (Atom (Fin n))) (old : List (Demand (Fin n)))
    (jobs : List Job) (state : State (Fin n)) (returned : run slots old jobs = some state)
    (assignment : Fin n → Comp Common.model) :
    (All Common.model assignment existing ∧
      ∃ values, SharedFits assignment values old ∧ HeadsFit slots assignment values jobs) ↔
      ∃ graphValues : Fin (CommonPresenceConstraintGraph.compile (existing ++ state.atoms)).size → Common.Ty,
        (CommonPresenceConstraintGraph.compile (existing ++ state.atoms)).Models
          (fun index => (assignment index).2) graphValues ∧
        (CommonPresenceConstraintGraph.compile (existing ++ state.atoms)).readback
          (fun index => (assignment index).2) graphValues = assignment := by
  rw [← returned_models_exact slots assignment old jobs state returned,
    ← PresenceNormalForm.all_append]
  exact CommonPresenceConstraintGraph.compile_atoms_exact _ assignment

/-- Reflection quantifies all compiled graph models, not just the canonical
extension used to prove existence. Original roles and heads are retained. -/
theorem compiled_reflects (slots : Nat → Fin n)
    (existing : List (Atom (Fin n))) (old : List (Demand (Fin n)))
    (jobs : List Job) (state : State (Fin n)) (returned : run slots old jobs = some state)
    (rows : Fin n → Common.Row)
    (graphValues : Fin (CommonPresenceConstraintGraph.compile (existing ++ state.atoms)).size → Common.Ty)
    (model : (CommonPresenceConstraintGraph.compile (existing ++ state.atoms)).Models rows graphValues) :
    let assignment := (CommonPresenceConstraintGraph.compile (existing ++ state.atoms)).readback rows graphValues
    All Common.model assignment existing ∧
      ∃ values, SharedFits assignment values old ∧ HeadsFit slots assignment values jobs := by
  have reflected := CommonPresenceConstraintGraph.compile_atoms_reflects _ rows graphValues model
  exact ((PresenceNormalForm.all_append ..).mp reflected).imp_right
    (returned_models_exact slots _ old jobs state returned).mp

end Yulang.CommonRoleCaptureBatchModels
