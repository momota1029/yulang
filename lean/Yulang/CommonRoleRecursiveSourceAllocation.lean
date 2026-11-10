import Yulang.CommonRoleWhereSourceAllocation

/-! Root-stable ownership for arbitrary finite actual where-capture histories.
Local binder labels and ambient endpoint identities remain separate. Each capture
can use a different demand state and binder map. This is not a termination theorem,
source-parser adequacy, or final role classification. -/
namespace Yulang.CommonRoleRecursiveSourceAllocation
open CommonRoleSourceIdentity (Table Slot source retain)
open CommonRoleCanonicalSourceGraph (canonical canonical_eq_iff)
open CommonRoleCanonicalSourceGrowth (newRoot)
open CommonRoleAllocatedGraph (allocate retainSnapshot)
open CommonRoleGraphInspection (inspectSnapshot VisibleHead)
open CommonRoleRegularGraph (Graph)
open CommonRoleIntervalPaterson (Goal)
open CommonRoleStablePaterson (Declaration)
open CommonRoleSourceIntervalBatches (Demand)
open CommonRoleWhereSourceModels (Result sources goalSources run)
open CommonRoleWhereSourceAllocation
  (Included parentTable childTable locate locate_exact locate_sources locate_canonical
   ownerAt ownerAt_source ownerAt_canonical)

/-- Each edge is an actual candidate return and an actual generated child.
The old state, declaration and binder map may vary at every edge. -/
inductive History (slots : Nat → α) (root : Goal) : Goal → Prop where
  | start : History slots root root
  | step {goal child : Goal} (previous : History slots root goal)
      (old : List (Demand α)) (declaration : Declaration) (bindingSource : Nat → Nat)
      (result : Result α)
      (returned : run slots old declaration goal bindingSource = some (some result))
      (member : child ∈ result.children) : History slots root child

/-- Arbitrarily deep actual recapture never escapes the original ambient domain.
No model, graph, alias, owner or finite-history-length bound is assumed. -/
theorem history_included (slots : Nat → α) (root goal : Goal)
    (history : History slots root goal) : Included (parentTable root) (parentTable goal) := by
  induction history with
  | start => exact fun _ present => present
  | step previous old declaration bindingSource result returned member ih =>
    intro name present
    exact ih name (CommonRoleWhereSourceModels.returned_sources slots old declaration _
      bindingSource result returned _ member name present)

/-- Keep every captured binder's endpoint occurrences, in binding order. This
registers the endpoint owners of a compound binding, not one invented center. -/
def capturedTable (result : Result α) : Table :=
  result.bindings.flatMap fun binding => sources binding.2

def payloadTable (result : Result α) : Table := capturedTable result ++ childTable result

/-- The real capture, not equality of local binder labels, determines provenance. -/
theorem captured_included (slots : Nat → α) (old : List (Demand α))
    (declaration : Declaration) (goal : Goal) (bindingSource : Nat → Nat)
    (result : Result α)
    (returned : run slots old declaration goal bindingSource = some (some result)) :
    Included (parentTable goal) (capturedTable result) := by
  cases inspected : CommonRoleIntervalCandidates.inspect declaration goal with
  | none => simp [run, inspected] at returned
  | some answer =>
    cases answer with
    | none => simp [run, inspected] at returned
    | some bindings =>
      have equal : result = ⟨bindings,
          CommonRoleWhereSourceModels.generatedState slots old declaration goal bindingSource bindings,
          CommonRoleIntervalPaterson.expand declaration (CommonRoleIntervalCapture.total bindings)⟩ := by
        simpa [run, inspected] using returned.symm
      subst result
      have accepted := (CommonRoleIntervalCandidates.inspect_accepts_exact ..).mp inspected
      intro name present
      obtain ⟨binding, member, used⟩ := List.mem_flatMap.mp present
      exact CommonRoleWhereSourceModels.normalized_goal_sources goal.arguments name
        (CommonRoleWhereSourceModels.capture_arguments_sources accepted.2.2.2.1
          binding member name used)

/-- Capture registration and all generated children share the same source domain. -/
theorem payload_included (slots : Nat → α) (old : List (Demand α))
    (declaration : Declaration) (goal : Goal) (bindingSource : Nat → Nat)
    (result : Result α)
    (returned : run slots old declaration goal bindingSource = some (some result)) :
    Included (parentTable goal) (payloadTable result) := by
  intro name present
  rcases List.mem_append.mp present with captured | child
  · exact captured_included slots old declaration goal bindingSource result returned name captured
  · exact CommonRoleWhereSourceAllocation.returned_included slots old declaration goal
      bindingSource result returned name child

structure Prepared (α : Type) (table : Table) where
  candidate : Result α
  owners : List (Slot table)

/-- Attach root owners to the original bindings, ordinary state and child list. -/
def prepareAt (table : Table) (slots : Nat → α) (old : List (Demand α))
    (declaration : Declaration) (goal : Goal) (bindingSource : Nat → Nat) :
    Option (Option (Prepared α table)) := do
  let answer ← run slots old declaration goal bindingSource
  match answer with
  | none => pure none
  | some candidate =>
    let owners ← locate table (payloadTable candidate)
    pure (some ⟨candidate, owners⟩)

/-- No new failure on an included goal. This is a domain premise, not a model
or successful-child premise; histories below discharge it for the root table. -/
theorem prepareAt_conservative (table : Table) (slots : Nat → α)
    (old : List (Demand α)) (declaration : Declaration) (goal : Goal)
    (bindingSource : Nat → Nat) (included : Included table (parentTable goal)) :
    (prepareAt table slots old declaration goal bindingSource).map
      (Option.map Prepared.candidate) = run slots old declaration goal bindingSource := by
  cases returned : run slots old declaration goal bindingSource with
  | none => simp [prepareAt, returned]
  | some answer =>
    cases answer with
    | none => simp [prepareAt, returned]
    | some candidate =>
      obtain ⟨owners, found⟩ := (locate_exact table (payloadTable candidate)).mpr
        (fun name present => included name
          (payload_included slots old declaration goal bindingSource candidate returned name present))
      simp [prepareAt, returned, found]

/-- The exact positive result, including the executable lookup, without a domain
premise. The conservative theorem separately establishes lookup totality. -/
theorem prepareAt_exact (table : Table) (slots : Nat → α) (old : List (Demand α))
    (declaration : Declaration) (goal : Goal) (bindingSource : Nat → Nat)
    (result : Prepared α table) :
    prepareAt table slots old declaration goal bindingSource = some (some result) ↔
      run slots old declaration goal bindingSource = some (some result.candidate) ∧
      locate table (payloadTable result.candidate) = some result.owners := by
  constructor
  · intro returned
    cases original : run slots old declaration goal bindingSource with
    | none => simp [prepareAt, original] at returned
    | some answer =>
      cases answer with
      | none => simp [prepareAt, original] at returned
      | some candidate =>
        cases found : locate table (payloadTable candidate) with
        | none => simp [prepareAt, original, found] at returned
        | some owners =>
          have equal : (⟨candidate, owners⟩ : Prepared α table) = result := by
            simpa [prepareAt, original, found] using returned
          subst result
          exact ⟨rfl, found⟩
  · rintro ⟨original, found⟩
    cases result
    simp_all [prepareAt]

/-- All three original outcomes survive after any finite actual history, using
one original root table, not a fresh parent-relative table at each step. -/
theorem history_conservative (slots : Nat → α) (root goal : Goal)
    (history : History slots root goal) (old : List (Demand α))
    (declaration : Declaration) (bindingSource : Nat → Nat) :
    (prepareAt (parentTable root) slots old declaration goal bindingSource).map
      (Option.map Prepared.candidate) = run slots old declaration goal bindingSource :=
  prepareAt_conservative _ slots old declaration goal bindingSource
    (history_included slots root goal history)

/-- Every payload after any actual finite history has computable original-root
owners, preserving all captured/child source occurrences in order. -/
theorem history_owners (slots : Nat → α) (root goal : Goal)
    (history : History slots root goal) (old : List (Demand α))
    (declaration : Declaration) (bindingSource : Nat → Nat) (result : Result α)
    (returned : run slots old declaration goal bindingSource = some (some result)) :
    ∃ owners, locate (parentTable root) (payloadTable result) = some owners ∧
      owners.map (source (parentTable root)) = payloadTable result ∧
      ∀ owner ∈ owners, canonical (parentTable root) owner = owner := by
  obtain ⟨owners, found⟩ := (locate_exact _ _).mpr
    (fun name present => history_included slots root goal history name
      (payload_included slots old declaration goal bindingSource result returned name present))
  exact ⟨owners, found, locate_sources _ _ _ found, locate_canonical _ _ _ found⟩

/-- Owners computed for two independent occurrence lists agree exactly on ambient
identity. This includes separate branches and different local binder spellings. -/
theorem owner_identity_exact (table first last : Table)
    (left : List (Slot table)) (right : List (Slot table))
    (foundLeft : locate table first = some left) (foundRight : locate table last = some right)
    (i : Slot first) (j : Slot last) :
    ownerAt table first left foundLeft i = ownerAt table last right foundRight j ↔
      source first i = source last j := by
  have equal := canonical_eq_iff table
    (ownerAt table first left foundLeft i) (ownerAt table last right foundRight j)
  simpa only [ownerAt_canonical, ownerAt_source] using equal

/-- Full graph inspection is retained at each root owner after arbitrary finite
actual recapture. Graph adequacy and mutation feedback remain separate obligations. -/
theorem history_allocation (slots : Nat → α) (root goal : Goal)
    (history : History slots root goal) (old : List (Demand α))
    (declaration : Declaration) (bindingSource : Nat → Nat) (result : Result α)
    (returned : run slots old declaration goal bindingSource = some (some result)) :
    ∃ owners, ∃ found : locate (parentTable root) (payloadTable result) = some owners,
      ∀ i : Slot (payloadTable result),
        newRoot (parentTable root) (payloadTable result) i =
          retain (parentTable root) (payloadTable result)
            (ownerAt (parentTable root) (payloadTable result) owners found i) ∧
        ∀ (graph : Graph (parentTable root).length) (role : Nat) (visible : List VisibleHead),
          inspectSnapshot (allocate (parentTable root) (payloadTable result) graph) role
            (newRoot (parentTable root) (payloadTable result) i) visible =
              retainSnapshot (parentTable root) (payloadTable result)
                (inspectSnapshot graph role
                  (ownerAt (parentTable root) (payloadTable result) owners found i) visible) := by
  obtain ⟨owners, found, _, _⟩ := history_owners slots root goal history old declaration
    bindingSource result returned
  exact ⟨owners, found, fun i =>
    ⟨CommonRoleWhereSourceAllocation.allocated_root _ _ _ found i,
      fun graph role visible => CommonRoleWhereSourceAllocation.allocated_snapshot
        _ _ _ found i graph role visible⟩⟩

/-- A caller-selected traversal step. Child positions preserve duplicate edges. -/
structure Instruction where
  declaration : Declaration
  bindingSource : Nat → Nat
  childIndex : Nat

/-- Actual old demand history is threaded into the next candidate computation. -/
structure Cursor (α : Type) where
  goal : Goal
  requests : List (Demand α)

/-- A positive-path utility, not a resolver verdict: an outside/no-candidate result
or a missing child position stops traversal. All original candidate outcomes are
preserved separately by `prepareAt`, rather than renamed here. -/
def next (slots : Nat → α) (cursor : Cursor α) (instruction : Instruction) :
    Option (Cursor α) := do
  let answer ← run slots cursor.requests instruction.declaration cursor.goal instruction.bindingSource
  let result ← answer
  let child ← result.children[instruction.childIndex]?
  pure ⟨child, result.state.requests⟩

def follow (slots : Nat → α) : Cursor α → List Instruction → Option (Cursor α)
  | cursor, [] => some cursor
  | cursor, instruction :: rest => do
    let after ← next slots cursor instruction
    follow slots after rest

/-- Every executable selected edge satisfies the independent actual-history
relation. The new ordinary demand history is the real result's request list. -/
theorem next_history (slots : Nat → α) (root : Goal) (cursor after : Cursor α)
    (history : History slots root cursor.goal) (instruction : Instruction)
    (returned : next slots cursor instruction = some after) : History slots root after.goal := by
  cases original : run slots cursor.requests instruction.declaration cursor.goal
      instruction.bindingSource with
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
        exact .step history cursor.requests instruction.declaration instruction.bindingSource
          result original (List.mem_of_getElem? selected)

/-- Arbitrarily many actual recursive calls preserve root provenance while
threading their real accumulated demand histories. No fixed depth is imposed. -/
theorem follow_history (slots : Nat → α) (root : Goal) (cursor after : Cursor α)
    (history : History slots root cursor.goal) (instructions : List Instruction)
    (returned : follow slots cursor instructions = some after) :
    History slots root after.goal := by
  induction instructions generalizing cursor with
  | nil =>
    have equal : cursor = after := by simpa [follow] using returned
    subst after
    exact history
  | cons instruction rest ih =>
    cases advanced : next slots cursor instruction with
    | none => simp [follow, advanced] at returned
    | some middle =>
      exact ih middle (next_history slots root cursor middle history instruction advanced)
        (by simpa [follow, advanced] using returned)

/-- Successful finite execution discharges the root-domain premise of allocation.
The following candidate may have any of the original three outcomes. -/
theorem follow_conservative (slots : Nat → α) (root : Goal) (initial : List (Demand α))
    (instructions : List Instruction) (after : Cursor α)
    (followed : follow slots ⟨root, initial⟩ instructions = some after)
    (declaration : Declaration) (bindingSource : Nat → Nat) :
    (prepareAt (parentTable root) slots after.requests declaration after.goal bindingSource).map
      (Option.map Prepared.candidate) =
        run slots after.requests declaration after.goal bindingSource :=
  history_conservative slots root after.goal
    (follow_history slots root ⟨root, initial⟩ after .start instructions followed)
    after.requests declaration bindingSource

/-- Root owners are computed after a real recursive traversal, not assumed as an
invariant supplied by a caller. Source occurrences and canonical roots are exact. -/
theorem follow_owners (slots : Nat → α) (root : Goal) (initial : List (Demand α))
    (instructions : List Instruction) (after : Cursor α)
    (followed : follow slots ⟨root, initial⟩ instructions = some after)
    (declaration : Declaration) (bindingSource : Nat → Nat) (result : Result α)
    (returned : run slots after.requests declaration after.goal bindingSource = some (some result)) :
    ∃ owners, locate (parentTable root) (payloadTable result) = some owners ∧
      owners.map (source (parentTable root)) = payloadTable result ∧
      ∀ owner ∈ owners, canonical (parentTable root) owner = owner :=
  history_owners slots root after.goal
    (follow_history slots root ⟨root, initial⟩ after .start instructions followed)
    after.requests declaration bindingSource result returned

/-- Every ambient endpoint of an actual local binding gets its original finite
root representative. Equal binder labels in different calls are not identified. -/
theorem registered_binding (slots : Nat → α) (root goal : Goal)
    (history : History slots root goal) (old : List (Demand α))
    (declaration : Declaration) (bindingSource : Nat → Nat) (result : Result α)
    (returned : run slots old declaration goal bindingSource = some (some result))
    (binding : Nat × CommonRoleIntervalPaterson.Argument) (member : binding ∈ result.bindings)
    (name : Nat) (used : name ∈ sources binding.2) :
    ∃ owner : Slot (parentTable root),
      CommonRoleSourceDescent.representative (parentTable root) name = some owner ∧
      source (parentTable root) owner = name ∧ canonical (parentTable root) owner = owner := by
  have present := history_included slots root goal history name
    (captured_included slots old declaration goal bindingSource result returned name
      (List.mem_flatMap.mpr ⟨binding, member, used⟩))
  obtain ⟨owner, found⟩ :=
    (CommonRoleWhereSourceAllocation.representative_present (parentTable root) name).mpr present
  exact ⟨owner, found, CommonRoleSourceDescent.representative_source _ _ _ found,
    CommonRoleWhereSourceAllocation.representative_canonical _ _ _ found⟩

end Yulang.CommonRoleRecursiveSourceAllocation
