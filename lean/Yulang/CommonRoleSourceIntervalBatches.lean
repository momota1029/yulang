import Yulang.CommonRoleIntervalGeneration

/-! Incremental ordinary constraints for arbitrary source-named intervals.
All existing endpoint constructors and original type/row slots are preserved.
Exactness concerns independent interval models, not general solver completion,
state-dependent materialization or final role classification. -/
namespace Yulang.CommonRoleSourceIntervalBatches
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (Atom All)
open CommonRoleIntervalGeneration (Argument eval)
open CommonRoleIntervals (Fits evaluate)

abbrev Demand (α : Type) := Nat × Argument α

def arguments (name : Nat) (requests : List (Demand α)) : List (Argument α) :=
  (requests.filter fun request => request.1 == name).map Prod.snd

theorem arguments_exact (name : Nat) (requests : List (Demand α)) (argument : Argument α) :
    argument ∈ arguments name requests ↔
      ∃ request ∈ requests, request.1 = name ∧ request.2 = argument := by
  simp only [arguments, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨request, ⟨member, same⟩, equal⟩
    exact ⟨request, member, same, equal⟩
  · rintro ⟨request, member, same, equal⟩
    exact ⟨request, ⟨member, same⟩, equal⟩

/-- No central type slot is allocated. Both directions are emitted for aliases. -/
def cross (first last : List (Demand α)) : List (Atom α) :=
  first.flatMap fun left => last.filterMap fun right =>
    if left.1 = right.1 then some (.tyLe left.2.1 right.2.2) else none

def generate (requests : List (Demand α)) : List (Atom α) := cross requests requests

/-- Independent original-source interpretation; witnesses are mathematical only. -/
def Models (assignment : α → Comp Common.model) (requests : List (Demand α)) : Prop :=
  ∀ name : Nat, ∃ actual : Common.Ty,
    ∀ request ∈ requests, request.1 = name →
      Fits (evaluate (eval assignment) request.2) actual

theorem cross_exact (assignment : α → Comp Common.model)
    (first last : List (Demand α)) :
    All Common.model assignment (cross first last) ↔
      ∀ left ∈ first, ∀ right ∈ last, left.1 = right.1 →
        Common.Subtype (eval assignment left.2.1) (eval assignment right.2.2) := by
  simp only [All, cross, List.forall_mem_flatMap, List.mem_filterMap]
  constructor
  · intro models left member right present same
    exact models left member (.tyLe left.2.1 right.2.2)
      ⟨right, present, by simp [same]⟩
  · intro models left member atom generated
    obtain ⟨right, present, returned⟩ := generated
    split at returned
    · rename_i same
      cases returned
      exact models left member right present same
    · cases returned

/-- Every finite source group has one common interval member exactly when all
its generated comparisons hold. No consistency premise or chosen witness. -/
theorem generate_exact (assignment : α → Comp Common.model) (requests : List (Demand α)) :
    All Common.model assignment (generate requests) ↔ Models assignment requests := by
  rw [generate, cross_exact]
  constructor
  · intro all name
    have valid : CommonRoleIntervals.Valid
        (CommonRoleIntervalGeneration.meaning assignment (arguments name requests)) := by
      rw [CommonRoleIntervalGeneration.meaning, CommonRoleIntervals.valid_coalesce]
      simp only [List.forall_mem_map]
      intro first hf last hl
      obtain ⟨left, member, sameLeft, rfl⟩ := (arguments_exact name requests first).mp hf
      obtain ⟨right, present, sameRight, rfl⟩ := (arguments_exact name requests last).mp hl
      exact all left member right present (sameLeft.trans sameRight.symm)
    obtain ⟨actual, fits⟩ := (CommonRoleIntervals.valid_iff_nonempty _).mp valid
    refine ⟨actual, ?_⟩
    intro request member same
    have found := (CommonRoleIntervals.fits_coalesce _ actual).mp fits
    exact found _ (List.mem_map.mpr ⟨request.2,
      (arguments_exact name requests request.2).mpr ⟨request, member, same, rfl⟩, rfl⟩)
  · intro models left member right present same
    obtain ⟨actual, fits⟩ := models left.1
    exact Common.subtype_trans (fits left member rfl).1 (fits right present same.symm).2

/-- Incremental reconciliation must add both old/new directions. -/
def delta (old fresh : List (Demand α)) : List (Atom α) :=
  cross old fresh ++ cross fresh old ++ generate fresh

theorem step_exact (assignment : α → Comp Common.model)
    (old fresh : List (Demand α)) :
    All Common.model assignment (generate old ++ delta old fresh) ↔
      Models assignment (old ++ fresh) := by
  rw [← generate_exact]
  simp only [delta, generate, PresenceNormalForm.all_append, cross_exact,
    List.mem_append, or_imp, forall_and]
  constructor
  · rintro ⟨a, ⟨b, c⟩, d⟩
    exact ⟨⟨a, c⟩, b, d⟩
  · rintro ⟨⟨a, c⟩, b, d⟩
    exact ⟨a, ⟨b, c⟩, d⟩

/-- State retains the original demand history and accumulates only delta atoms. -/
structure State (α : Type) where
  requests : List (Demand α)
  atoms : List (Atom α)

def start (requests : List (Demand α)) : State α := ⟨requests, generate requests⟩
def advance (state : State α) (fresh : List (Demand α)) : State α :=
  ⟨state.requests ++ fresh, state.atoms ++ delta state.requests fresh⟩
def run : State α → List (List (Demand α)) → State α
  | state, [] => state
  | state, fresh :: rest => run (advance state fresh) rest

theorem advance_exact (assignment : α → Comp Common.model) (state : State α)
    (invariant : All Common.model assignment state.atoms ↔ Models assignment state.requests)
    (fresh : List (Demand α)) :
    All Common.model assignment (advance state fresh).atoms ↔
      Models assignment (state.requests ++ fresh) := by
  change All Common.model assignment (state.atoms ++ delta state.requests fresh) ↔ _
  rw [PresenceNormalForm.all_append, invariant, ← generate_exact]
  rw [← PresenceNormalForm.all_append, step_exact]

theorem run_requests (state : State α) (batches : List (List (Demand α))) :
    (run state batches).requests = state.requests ++ batches.flatten := by
  induction batches generalizing state with
  | nil => simp [run]
  | cons fresh rest ih => simp [run, ih, advance, List.append_assoc]

/-- Arbitrary batch order, repeated source names and duplicates are retained;
all old and new comparisons are exact at the same original assignment. -/
theorem run_exact (assignment : α → Comp Common.model) (initial : List (Demand α))
    (batches : List (List (Demand α))) :
    All Common.model assignment (run (start initial) batches).atoms ↔
      Models assignment (initial ++ batches.flatten) := by
  have invariant : ∀ state : State α,
      (All Common.model assignment state.atoms ↔ Models assignment state.requests) →
      (All Common.model assignment (run state batches).atoms ↔
        Models assignment (run state batches).requests) := by
    induction batches with
    | nil => intro state same; exact same
    | cons fresh rest ih =>
        intro state same
        exact ih (advance state fresh) (advance_exact assignment state same fresh)
  have result := invariant (start initial) (generate_exact assignment initial)
  simpa only [run_requests, start] using result

/-- Reordering the history changes neither shared-source compatibility nor any
existing endpoint row. This is not final dictionary order independence. -/
theorem models_perm (assignment : α → Comp Common.model) (first last : List (Demand α))
    (reordered : first.Perm last) : Models assignment first ↔ Models assignment last := by
  simp only [Models, reordered.mem_iff]

/-- The executable delta driver is semantically independent of batch boundaries
and order whenever the complete original demand lists are permutations. -/
theorem run_order_independent (assignment : α → Comp Common.model)
    (first last : List (Demand α)) (firstBatches lastBatches : List (List (Demand α)))
    (reordered : (first ++ firstBatches.flatten).Perm (last ++ lastBatches.flatten)) :
    All Common.model assignment (run (start first) firstBatches).atoms ↔
      All Common.model assignment (run (start last) lastBatches).atoms := by
  rw [run_exact, run_exact]
  exact models_perm assignment _ _ reordered

/-- The existing graph compiler realizes every independent interval model and
reflects every model at literal readback, with all old constraints conjoined. -/
theorem compile_run_exact (existing : List (Atom (Fin n))) (initial : List (Demand (Fin n)))
    (batches : List (List (Demand (Fin n)))) (assignment : Fin n → Comp Common.model) :
    (All Common.model assignment existing ∧ Models assignment (initial ++ batches.flatten)) ↔
      ∃ values : Fin (CommonPresenceConstraintGraph.compile
        (existing ++ (run (start initial) batches).atoms)).size → Common.Ty,
      (CommonPresenceConstraintGraph.compile
        (existing ++ (run (start initial) batches).atoms)).Models
        (fun i => (assignment i).2) values ∧
      (CommonPresenceConstraintGraph.compile
        (existing ++ (run (start initial) batches).atoms)).readback
        (fun i => (assignment i).2) values = assignment := by
  rw [← run_exact, ← PresenceNormalForm.all_append]
  exact CommonPresenceConstraintGraph.compile_atoms_exact _ assignment

/-- Every compiled graph model, not only the compiler's constructed witness,
reflects old constraints and the entire original source-interval history. -/
theorem compiled_reflects (existing : List (Atom (Fin n))) (initial : List (Demand (Fin n)))
    (batches : List (List (Demand (Fin n)))) (rows : Fin n → Common.Row)
    (values : Fin (CommonPresenceConstraintGraph.compile
      (existing ++ (run (start initial) batches).atoms)).size → Common.Ty)
    (model : (CommonPresenceConstraintGraph.compile
      (existing ++ (run (start initial) batches).atoms)).Models rows values) :
    let assignment := (CommonPresenceConstraintGraph.compile
      (existing ++ (run (start initial) batches).atoms)).readback rows values
    All Common.model assignment existing ∧ Models assignment (initial ++ batches.flatten) := by
  have reflected := CommonPresenceConstraintGraph.compile_atoms_reflects _ rows values model
  exact ((PresenceNormalForm.all_append ..).mp reflected).imp_right
    (run_exact _ initial batches).mp

end Yulang.CommonRoleSourceIntervalBatches
