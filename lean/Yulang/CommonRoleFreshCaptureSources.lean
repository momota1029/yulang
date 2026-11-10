import Yulang.CommonRoleRecursiveSourceAllocation

/-! Computed fresh demand names for an independent local capture. Ambient
endpoint names and local binder names remain separate. Reusing an invocation
must retain its map; this utility does not decide when two invocations share
locals, and is not a saturation or language-classification algorithm. -/
namespace Yulang.CommonRoleFreshCaptureSources
open CommonRoleSourceIntervalBatches (Demand Models)
open CommonRoleStablePaterson (Declaration)
open CommonRoleIntervalPaterson (Goal)
open CommonRoleIntervalCapture (Bindings)
open CommonRoleIntervalCandidates (Accepts)
open CommonRoleCaptureBatchModels (SharedFits HeadFits)
open CommonRoleWhereSourceModels (Result WhereFits generatedState)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

/-- Strictly above every already used semantic demand name; endpoint slots are
not included because they inhabit a different namespace. -/
def boundary : List (Demand α) → Nat
  | [] => 0
  | request :: rest => max (request.1 + 1) (boundary rest)

def freshSource (old : List (Demand α)) (binder : Nat) : Nat := boundary old + binder

theorem old_below (old : List (Demand α)) (request : Demand α)
    (member : request ∈ old) : request.1 < boundary old := by
  induction old with
  | nil => simp at member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · have h := Nat.le_max_left (request.1 + 1) (boundary rest)
      simp only [boundary]
      omega
    · have h := ih member
      have bound := Nat.le_max_right (first.1 + 1) (boundary rest)
      simp only [boundary]
      omega

/-- A fresh local binder cannot collide with any actual prior demand. -/
theorem fresh_ne_old (old : List (Demand α)) (binder : Nat) (request : Demand α)
    (member : request ∈ old) : freshSource old binder ≠ request.1 := by
  have h := old_below old request member
  simp only [freshSource]
  omega

/-- Within one allocation, exactly equal local binders share a demand name. -/
theorem fresh_identity (old : List (Demand α)) (left right : Nat) :
    freshSource old left = freshSource old right ↔ left = right := by
  simp [freshSource]

/-- Proof witness only. The executable allocator never chooses semantic types. -/
def extend (old : List (Demand α)) (previous locals : Nat → Common.Ty) : Nat → Common.Ty :=
  fun name => if name < boundary old then previous name else locals (name - boundary old)

theorem extend_old (old : List (Demand α)) (previous locals : Nat → Common.Ty)
    (request : Demand α) (member : request ∈ old) :
    extend old previous locals request.1 = previous request.1 := by
  simp [extend, old_below old request member]

theorem extend_fresh (old : List (Demand α)) (previous locals : Nat → Common.Ty) :
    extend old previous locals ∘ freshSource old = locals := by
  funext binder
  change (if boundary old + binder < boundary old then previous (boundary old + binder)
    else locals (boundary old + binder - boundary old)) = locals binder
  have outside : ¬ boundary old + binder < boundary old := by omega
  simp [outside]

/-- Every old model and every independent local valuation coexist, rather than
assuming a single compatible valuation in the theorem's input. -/
theorem extend_shared (assignment : α → Comp Common.model) (old : List (Demand α))
    (previous locals : Nat → Common.Ty) (models : SharedFits assignment previous old) :
    SharedFits assignment (extend old previous locals) old := by
  intro request member
  rw [extend_old old previous locals request member]
  exact models request member

/-- Independent original-head and where-template models. This does not assert
that any of the where children has a dictionary. -/
def LocalModels (slots : Nat → α) (assignment : α → Comp Common.model)
    (declaration : Declaration) (goal : Goal) (bindings : Bindings) : Prop :=
  ∃ locals, HeadFits (fun n => (assignment (slots n)).1) locals
    declaration.head goal.arguments ∧
    WhereFits (fun n => (assignment (slots n)).1) locals declaration bindings

/-- Exact original models with a computed map, no caller source map or common
valuation premise. This is precisely the fresh independent-capture fragment. -/
theorem generated_models_exact (slots : Nat → α) (assignment : α → Comp Common.model)
    (old : List (Demand α)) (declaration : Declaration) (goal : Goal) (bindings : Bindings)
    (accepted : Accepts declaration goal bindings) :
    All Common.model assignment
      (generatedState slots old declaration goal (freshSource old) bindings).atoms ↔
      Models assignment old ∧ LocalModels slots assignment declaration goal bindings := by
  rw [CommonRoleWhereSourceModels.generated_models_exact slots assignment old
    declaration goal (freshSource old) bindings accepted,
    CommonRoleCaptureBatchModels.models_shared_exact]
  constructor
  · rintro ⟨values, previous, head, children⟩
    exact ⟨⟨values, previous⟩, values ∘ freshSource old, head, children⟩
  · rintro ⟨⟨previous, oldModels⟩, locals, head, children⟩
    refine ⟨extend old previous locals, extend_shared assignment old previous locals oldModels, ?_⟩
    rw [extend_fresh]
    exact ⟨head, children⟩

/-- The same candidate scanner and ordered children, now without a supplied
local binder map. All original outside/negative/positive results are retained. -/
def run (slots : Nat → α) (old : List (Demand α)) (declaration : Declaration) (goal : Goal) :
    Option (Option (Result α)) :=
  CommonRoleWhereSourceModels.run slots old declaration goal (freshSource old)

/-- Public exactness against independent accepted captures and local models.
The structural boundary remains explicit; no successful child is assumed. -/
theorem run_exact (slots : Nat → α) (assignment : α → Comp Common.model)
    (old : List (Demand α)) (declaration : Declaration) (goal : Goal) (result : Result α) :
    (run slots old declaration goal = some (some result) ∧
      All Common.model assignment result.state.atoms) ↔
    ∃ bindings, Accepts declaration goal bindings ∧
      result = ⟨bindings, generatedState slots old declaration goal (freshSource old) bindings,
        CommonRoleIntervalPaterson.expand declaration (CommonRoleIntervalCapture.total bindings)⟩ ∧
      Models assignment old ∧ LocalModels slots assignment declaration goal bindings := by
  constructor
  · rintro ⟨returned, models⟩
    obtain ⟨bindings, accepted, equal, _⟩ :=
      (CommonRoleWhereSourceModels.run_exact slots assignment old declaration goal
        (freshSource old) result).mp ⟨returned, models⟩
    refine ⟨bindings, accepted, equal, ?_⟩
    rw [equal] at models
    exact (generated_models_exact slots assignment old declaration goal bindings accepted).mp models
  · rintro ⟨bindings, accepted, rfl, models⟩
    refine ⟨?_, (generated_models_exact slots assignment old declaration goal bindings accepted).mpr models⟩
    simp [run, CommonRoleWhereSourceModels.run,
      (CommonRoleIntervalCandidates.inspect_accepts_exact ..).mpr accepted]

/-- Actual newly emitted demand names are disjoint from every old demand name,
while endpoint terms and the old request prefix remain unchanged. -/
theorem generated_fresh (slots : Nat → α) (old : List (Demand α))
    (declaration : Declaration) (goal : Goal) (bindings : Bindings)
    (request : Demand α)
    (member : request ∈ CommonRoleCaptureBatchModels.demands slots
      (CommonRoleWhereSourceModels.captureJob declaration goal (freshSource old)) bindings)
    (prior : Demand α) (present : prior ∈ old) : request.1 ≠ prior.1 := by
  obtain ⟨binding, _, rfl⟩ := List.mem_map.mp member
  exact fresh_ne_old old binding.1 prior present

/-- Root ownership is retained even after arbitrary real recapture history.
The fresh map is derived from the actual demand history, not from endpoint owners. -/
theorem history_owners (slots : Nat → α) (root goal : Goal)
    (history : CommonRoleRecursiveSourceAllocation.History slots root goal)
    (old : List (Demand α)) (declaration : Declaration) (result : Result α)
    (returned : run slots old declaration goal = some (some result)) :
    ∃ owners, CommonRoleWhereSourceAllocation.locate
        (CommonRoleWhereSourceAllocation.parentTable root)
        (CommonRoleRecursiveSourceAllocation.payloadTable result) = some owners ∧
      owners.map (CommonRoleSourceIdentity.source
        (CommonRoleWhereSourceAllocation.parentTable root)) =
          CommonRoleRecursiveSourceAllocation.payloadTable result ∧
      ∀ owner ∈ owners, CommonRoleCanonicalSourceGraph.canonical
        (CommonRoleWhereSourceAllocation.parentTable root) owner = owner :=
  CommonRoleRecursiveSourceAllocation.history_owners slots root goal history old
    declaration (freshSource old) result returned

/-- The original delta generator models exactly its retained request history. -/
theorem generated_requests_exact (slots : Nat → α) (assignment : α → Comp Common.model)
    (old : List (Demand α)) (declaration : Declaration) (goal : Goal) (bindings : Bindings) :
    All Common.model assignment
      (generatedState slots old declaration goal (freshSource old) bindings).atoms ↔
    Models assignment
      (generatedState slots old declaration goal (freshSource old) bindings).requests := by
  exact CommonRoleSourceIntervalBatches.step_exact assignment old _

/-- Selected path instruction: no binder-source map is supplied. -/
structure Instruction where
  declaration : Declaration
  childIndex : Nat

abbrev Cursor := CommonRoleRecursiveSourceAllocation.Cursor

def next (slots : Nat → α) (cursor : Cursor α) (instruction : Instruction) : Option (Cursor α) := do
  let answer ← run slots cursor.requests instruction.declaration cursor.goal
  let result ← answer
  let child ← result.children[instruction.childIndex]?
  pure ⟨child, result.state.requests⟩

def follow (slots : Nat → α) : Cursor α → List Instruction → Option (Cursor α)
  | cursor, [] => some cursor
  | cursor, instruction :: rest => do
    let after ← next slots cursor instruction
    follow slots after rest

/-- Independent finite-path judgment. It uses structural capture and original
head/where models, never the runner, generated ordinary atoms or allocator. Each
call has independent locals; every call uses the same ambient assignment. -/
def PathModels (slots : Nat → α) (assignment : α → Comp Common.model) :
    Goal → List Instruction → Prop
  | _, [] => True
  | goal, instruction :: rest => ∃ bindings child,
    Accepts instruction.declaration goal bindings ∧
    (CommonRoleIntervalPaterson.expand instruction.declaration
      (CommonRoleIntervalCapture.total bindings))[instruction.childIndex]? = some child ∧
    LocalModels slots assignment instruction.declaration goal bindings ∧
    PathModels slots assignment child rest

/-- One selected descent and its model, exact against the independent capture
boundary. A missing child or nonpositive candidate simply ends this path utility. -/
theorem next_exact (slots : Nat → α) (assignment : α → Comp Common.model)
    (cursor after : Cursor α) (instruction : Instruction) :
    (next slots cursor instruction = some after ∧ Models assignment after.requests) ↔
    ∃ bindings, Accepts instruction.declaration cursor.goal bindings ∧
      (CommonRoleIntervalPaterson.expand instruction.declaration
        (CommonRoleIntervalCapture.total bindings))[instruction.childIndex]? = some after.goal ∧
      after.requests = (generatedState slots cursor.requests instruction.declaration
        cursor.goal (freshSource cursor.requests) bindings).requests ∧
      Models assignment cursor.requests ∧
      LocalModels slots assignment instruction.declaration cursor.goal bindings := by
  constructor
  · rintro ⟨returned, models⟩
    cases original : run slots cursor.requests instruction.declaration cursor.goal with
    | none => simp [next, original] at returned
    | some answer =>
      cases answer with
      | none => simp [next, original] at returned
      | some result =>
        cases selected : result.children[instruction.childIndex]? with
        | none => simp [next, original, selected] at returned
        | some child =>
          have equal : (⟨child, result.state.requests⟩ : Cursor α) = after := by
            simpa [next, original, selected] using returned
          subst after
          cases inspected : CommonRoleIntervalCandidates.inspect instruction.declaration cursor.goal with
          | none => simp [run, CommonRoleWhereSourceModels.run, inspected] at original
          | some candidate =>
            cases candidate with
            | none => simp [run, CommonRoleWhereSourceModels.run, inspected] at original
            | some bindings =>
              have same : result = ⟨bindings, generatedState slots cursor.requests instruction.declaration
                  cursor.goal (freshSource cursor.requests) bindings,
                  CommonRoleIntervalPaterson.expand instruction.declaration
                    (CommonRoleIntervalCapture.total bindings)⟩ := by
                simpa [run, CommonRoleWhereSourceModels.run, inspected] using original.symm
              subst result
              have accepted := (CommonRoleIntervalCandidates.inspect_accepts_exact ..).mp inspected
              refine ⟨bindings, accepted, selected, rfl, ?_⟩
              exact (generated_models_exact slots assignment cursor.requests instruction.declaration
                cursor.goal bindings accepted).mp
                  ((generated_requests_exact slots assignment cursor.requests instruction.declaration
                    cursor.goal bindings).mpr models)
  · rintro ⟨bindings, accepted, selected, same, models⟩
    have atoms := (generated_models_exact slots assignment cursor.requests instruction.declaration
      cursor.goal bindings accepted).mpr models
    constructor
    · cases after with
      | mk goal requests =>
        simp only at same selected ⊢
        subst requests
        simp [next, run, CommonRoleWhereSourceModels.run,
          (CommonRoleIntervalCandidates.inspect_accepts_exact ..).mpr accepted, selected]
    · rw [same]
      exact (generated_requests_exact slots assignment cursor.requests instruction.declaration
        cursor.goal bindings).mp atoms

/-- Arbitrary finite actual recursion, with each binding map computed from its
real prior demands, is exact against independent original local models. No depth
bound, consistency, successful child dictionary or caller map is a premise.
This is a caller-selected positive path, not whole-resolver termination. -/
theorem follow_models_exact (slots : Nat → α) (assignment : α → Comp Common.model)
    (cursor : Cursor α) (instructions : List Instruction) :
    (∃ after, follow slots cursor instructions = some after ∧ Models assignment after.requests) ↔
      Models assignment cursor.requests ∧ PathModels slots assignment cursor.goal instructions := by
  induction instructions generalizing cursor with
  | nil => simp [follow, PathModels]
  | cons instruction rest ih =>
    constructor
    · rintro ⟨after, returned, models⟩
      cases advanced : next slots cursor instruction with
      | none => simp [follow, advanced] at returned
      | some middle =>
        have followed : follow slots middle rest = some after := by
          simpa [follow, advanced] using returned
        obtain ⟨middleModels, tail⟩ := (ih middle).mp ⟨after, followed, models⟩
        obtain ⟨bindings, accepted, child, _, previous, localModels⟩ :=
          (next_exact slots assignment cursor middle instruction).mp ⟨advanced, middleModels⟩
        exact ⟨previous, bindings, middle.goal, accepted, child, localModels, tail⟩
    · rintro ⟨previous, bindings, child, accepted, selected, localModels, tail⟩
      let middle : Cursor α := ⟨child,
        (generatedState slots cursor.requests instruction.declaration cursor.goal
          (freshSource cursor.requests) bindings).requests⟩
      have stepped := (next_exact slots assignment cursor middle instruction).mpr
        ⟨bindings, accepted, selected, rfl, previous, localModels⟩
      obtain ⟨after, followed, models⟩ := (ih middle).mpr ⟨stepped.2, tail⟩
      exact ⟨after, by simp [follow, stepped.1, followed], models⟩

/-- Executable fresh-map descent is an actual edge of the original history. -/
theorem next_history (slots : Nat → α) (root : Goal) (cursor after : Cursor α)
    (history : CommonRoleRecursiveSourceAllocation.History slots root cursor.goal)
    (instruction : Instruction) (returned : next slots cursor instruction = some after) :
    CommonRoleRecursiveSourceAllocation.History slots root after.goal :=
  CommonRoleRecursiveSourceAllocation.next_history slots root cursor after history
    ⟨instruction.declaration, freshSource cursor.requests, instruction.childIndex⟩ returned

theorem follow_history (slots : Nat → α) (root : Goal) (cursor after : Cursor α)
    (history : CommonRoleRecursiveSourceAllocation.History slots root cursor.goal)
    (instructions : List Instruction) (returned : follow slots cursor instructions = some after) :
    CommonRoleRecursiveSourceAllocation.History slots root after.goal := by
  induction instructions generalizing cursor with
  | nil =>
    have same : cursor = after := by simpa [follow] using returned
    subst after
    exact history
  | cons instruction rest ih =>
    cases advanced : next slots cursor instruction with
    | none => simp [follow, advanced] at returned
    | some middle =>
      exact ih middle (next_history slots root cursor middle history instruction advanced)
        (by simpa [follow, advanced] using returned)

end Yulang.CommonRoleFreshCaptureSources
