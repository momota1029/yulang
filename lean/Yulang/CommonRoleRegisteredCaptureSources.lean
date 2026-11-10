import Yulang.CommonRoleFreshCaptureSources

/-! Persistent finite local-capture names, keyed by explicit invocation and
binder. The caller supplies invocation identity; equality of observations is
never used as identity. This local utility does not derive language invocation
keys, associated feedback, saturation or final dictionary classification. -/
namespace Yulang.CommonRoleRegisteredCaptureSources
open CommonRoleStablePaterson (Declaration)
open CommonRoleIntervalPaterson (Goal)
open CommonRoleIntervalCapture (Bindings Capture CaptureArguments variables argumentVariables)
open CommonRoleIntervalCandidates (Accepts)
open CommonRoleSourceIntervalBatches (Demand Models)
open CommonRoleCaptureBatchModels (SharedFits HeadFits)
open CommonRoleWhereSourceModels (WhereFits generatedState)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

abbrev Key := Nat × Nat
abbrev Table := List Key

/-- Only actual finite keys are assigned positions. Duplicate entries retain
first-occurrence identity; registering an already covered batch is a no-op. -/
def register (table keys : Table) : Table :=
  if keys.all table.contains then table else table ++ keys

def source (boundary : Nat) (table : Table) (key : Key) : Nat :=
  boundary + table.idxOf key

def bindingKeys (invocation : Nat) (bindings : Bindings) : Table :=
  bindings.map fun binding => (invocation, binding.1)

def bindingSource (boundary : Nat) (table : Table) (invocation binder : Nat) : Nat :=
  source boundary table (invocation, binder)

theorem register_old (table keys : Table) (key : Key) (member : key ∈ table) :
    key ∈ register table keys := by
  unfold register
  split
  · exact member
  · exact List.mem_append_left _ member

theorem register_new (table keys : Table) (key : Key) (member : key ∈ keys) :
    key ∈ register table keys := by
  unfold register
  split
  · rename_i covered
    exact List.contains_iff_mem.mp ((List.all_eq_true.mp covered) key member)
  · exact List.mem_append_right _ member

/-- A revisit cannot allocate a new position for an already present source. -/
theorem source_preserved (boundary : Nat) (table keys : Table) (key : Key)
    (member : key ∈ table) :
    source boundary (register table keys) key = source boundary table key := by
  unfold register
  split
  · rfl
  · simp [source, List.idxOf_append, member]

/-- No accidental aliasing, including between invocations with equal binder labels. -/
theorem source_identity (boundary : Nat) (table : Table) (left right : Key)
    (hl : left ∈ table) (hr : right ∈ table) :
    source boundary table left = source boundary table right ↔ left = right := by
  constructor
  · intro equal
    have indices : table.idxOf left = table.idxOf right := by
      simpa only [source, Nat.add_left_cancel_iff] using equal
    have a := List.getElem_idxOf (List.idxOf_lt_length_of_mem hl)
    have b := List.getElem_idxOf (List.idxOf_lt_length_of_mem hr)
    have same : table[table.idxOf left]'(List.idxOf_lt_length_of_mem hl) = table[table.idxOf right]'(List.idxOf_lt_length_of_mem hr) := by simp [indices]
    exact a.symm.trans (same.trans b)
  · rintro rfl
    rfl

theorem register_idempotent (table keys : Table) :
    register (register table keys) keys = register table keys := by
  have covered : keys.all (register table keys).contains = true := by
    apply List.all_eq_true.mpr
    intro key member
    exact List.contains_iff_mem.mpr (register_new table keys key member)
  change (if keys.all (register table keys).contains then register table keys
    else register table keys ++ keys) = register table keys
  rw [covered]
  rfl

/-- Scope separation from every preexisting demand is computed once at start. -/
theorem source_fresh (old : List (Demand α)) (table : Table) (key : Key)
    (request : Demand α) (member : request ∈ old) :
    source (CommonRoleFreshCaptureSources.boundary old) table key ≠ request.1 := by
  have below := CommonRoleFreshCaptureSources.old_below old request member
  simp only [source]
  omega

/-- Structural capture retains exactly the declaration's binder sequence. -/
theorem capture_keys (captured : Capture form argument bindings) :
    bindings.map Prod.fst = variables form := by
  induction captured with
  | var | int => rfl
  | pair _ _ first last => simp [List.map_append, first, last, variables]
  | tick _ ih => exact ih

theorem capture_arguments_keys (captured : CaptureArguments forms arguments bindings) :
    bindings.map Prod.fst = argumentVariables forms := by
  induction captured with
  | nil => rfl
  | cons first _ ih =>
    simp [List.map_append, capture_keys first, ih, argumentVariables]

/-- Endpoint refinement cannot change the local key domain of an accepted
capture of the same declaration, including captures with no local variables. -/
theorem accepted_keys (invocation : Nat) (declaration : Declaration) (goal : Goal)
    (bindings : Bindings) (accepted : Accepts declaration goal bindings) :
    bindingKeys invocation bindings =
      (argumentVariables declaration.head).map (fun binder => (invocation, binder)) := by
  rw [← capture_arguments_keys accepted.2.2.2.1]
  simp [bindingKeys, List.map_map]

structure State (α : Type) where
  boundary : Nat
  table : Table
  requests : List (Demand α)

/-- Start above all existing demand identities; endpoint names are unrelated. -/
def start (old : List (Demand α)) : State α :=
  ⟨CommonRoleFreshCaptureSources.boundary old, [], old⟩

def tableAfter (state : State α) (invocation : Nat) (bindings : Bindings) : Table :=
  register state.table (bindingKeys invocation bindings)

def sourceAfter (state : State α) (invocation : Nat) (bindings : Bindings) : Nat → Nat :=
  bindingSource state.boundary (tableAfter state invocation bindings) invocation

structure Result (α : Type) where
  registry : State α
  candidate : CommonRoleWhereSourceModels.Result α

def generated (slots : Nat → α) (state : State α) (invocation : Nat)
    (declaration : Declaration) (goal : Goal) (bindings : Bindings) : Result α :=
  let ordinary := generatedState slots state.requests declaration goal
    (sourceAfter state invocation bindings) bindings
  ⟨⟨state.boundary, tableAfter state invocation bindings, ordinary.requests⟩,
   ⟨bindings, ordinary,
    CommonRoleIntervalPaterson.expand declaration (CommonRoleIntervalCapture.total bindings)⟩⟩

/-- The original inspector determines all three candidate outcomes. Only an
accepted capture creates registry entries, and every emitted key is present. -/
def run (slots : Nat → α) (state : State α) (invocation : Nat)
    (declaration : Declaration) (goal : Goal) : Option (Option (Result α)) := do
  let answer ← CommonRoleIntervalCandidates.inspect declaration goal
  pure (answer.map (generated slots state invocation declaration goal))

/-- Exactness against original head and where models with intentional sharing.
The shared valuation is constructed existentially in the conclusion; it is not
an input consistency premise. Explicit invocation keys remain a local boundary. -/
theorem run_exact (slots : Nat → α) (assignment : α → Comp Common.model)
    (state : State α) (invocation : Nat) (declaration : Declaration) (goal : Goal)
    (result : Result α) :
    (run slots state invocation declaration goal = some (some result) ∧
      All Common.model assignment result.candidate.state.atoms) ↔
    ∃ bindings, Accepts declaration goal bindings ∧
      result = generated slots state invocation declaration goal bindings ∧
      ∃ values, SharedFits assignment values state.requests ∧
        HeadFits (fun n => (assignment (slots n)).1)
          (values ∘ sourceAfter state invocation bindings) declaration.head goal.arguments ∧
        WhereFits (fun n => (assignment (slots n)).1)
          (values ∘ sourceAfter state invocation bindings) declaration bindings := by
  constructor
  · rintro ⟨returned, models⟩
    cases inspected : CommonRoleIntervalCandidates.inspect declaration goal with
    | none => simp [run, inspected] at returned
    | some answer =>
      cases answer with
      | none => simp [run, inspected] at returned
      | some bindings =>
        have same : result = generated slots state invocation declaration goal bindings := by
          simpa [run, inspected] using returned.symm
        subst result
        have accepted := (CommonRoleIntervalCandidates.inspect_accepts_exact ..).mp inspected
        exact ⟨bindings, accepted, rfl,
          (CommonRoleWhereSourceModels.generated_models_exact slots assignment state.requests
            declaration goal (sourceAfter state invocation bindings) bindings accepted).mp models⟩
  · rintro ⟨bindings, accepted, rfl, models⟩
    exact ⟨by simp [run, (CommonRoleIntervalCandidates.inspect_accepts_exact ..).mpr accepted],
      (CommonRoleWhereSourceModels.generated_models_exact slots assignment state.requests
        declaration goal (sourceAfter state invocation bindings) bindings accepted).mpr models⟩

/-- Register every actual binder before any ordinary constraints are emitted. -/
theorem generated_key_present (state : State α) (invocation : Nat) (bindings : Bindings)
    (binding : Nat × CommonRoleIntervalPaterson.Argument) (member : binding ∈ bindings) :
    (invocation, binding.1) ∈ tableAfter state invocation bindings :=
  register_new _ _ _ (List.mem_map.mpr ⟨binding, member, rfl⟩)

/-- Two actual emitted local names alias exactly when their source pairs do. -/
theorem generated_identity (state : State α) (invocation : Nat) (bindings : Bindings)
    (left right : Nat × CommonRoleIntervalPaterson.Argument)
    (hl : left ∈ bindings) (hr : right ∈ bindings) :
    sourceAfter state invocation bindings left.1 = sourceAfter state invocation bindings right.1 ↔
      left.1 = right.1 := by
  exact (source_identity state.boundary (tableAfter state invocation bindings)
    (invocation, left.1) (invocation, right.1)
    (generated_key_present state invocation bindings left hl)
    (generated_key_present state invocation bindings right hr)).trans (by simp)

/-- Actual outputs retain all previous demand occurrences, not merely their models. -/
theorem generated_requests (slots : Nat → α) (state : State α) (invocation : Nat)
    (declaration : Declaration) (goal : Goal) (bindings : Bindings) :
    (generated slots state invocation declaration goal bindings).registry.requests =
      state.requests ++ CommonRoleCaptureBatchModels.demands slots
        (CommonRoleWhereSourceModels.captureJob declaration goal
          (sourceAfter state invocation bindings)) bindings := rfl

/-- A second accepted capture of the same declaration has exactly the same key
batch even when its actual goal endpoints have changed. Registration is a no-op. -/
theorem recapture_registry (state : State α) (invocation : Nat) (declaration : Declaration)
    (firstGoal nextGoal : Goal) (first next : Bindings)
    (firstAccepted : Accepts declaration firstGoal first)
    (nextAccepted : Accepts declaration nextGoal next) :
    register (tableAfter state invocation first) (bindingKeys invocation next) =
      tableAfter state invocation first := by
  have same : bindingKeys invocation next = bindingKeys invocation first :=
    (accepted_keys invocation declaration nextGoal next nextAccepted).trans
      (accepted_keys invocation declaration firstGoal first firstAccepted).symm
  rw [same]
  exact register_idempotent _ _

/-- Every positive execution preserves the old registry, all allocated names,
and the namespace boundary, regardless of its consistency or where success. -/
theorem run_preserves_sources (slots : Nat → α) (state : State α) (invocation : Nat)
    (declaration : Declaration) (goal : Goal) (result : Result α)
    (returned : run slots state invocation declaration goal = some (some result)) :
    result.registry.boundary = state.boundary ∧
      ∀ key ∈ state.table, key ∈ result.registry.table ∧
        source result.registry.boundary result.registry.table key =
          source state.boundary state.table key := by
  cases inspected : CommonRoleIntervalCandidates.inspect declaration goal with
  | none => simp [run, inspected] at returned
  | some answer =>
    cases answer with
    | none => simp [run, inspected] at returned
    | some bindings =>
      have same : result = generated slots state invocation declaration goal bindings := by
        simpa [run, inspected] using returned.symm
      subst result
      exact ⟨rfl, fun key member => ⟨register_old _ _ _ member,
        source_preserved _ _ _ _ member⟩⟩

/-- Caller-identified captures. This is not a candidate scheduler or a choice
of which goals constitute the same invocation. -/
structure Visit where
  invocation : Nat
  declaration : Declaration
  goal : Goal

def follow (slots : Nat → α) : State α → List Visit → Option (State α)
  | state, [] => some state
  | state, visit :: rest => do
    let answer ← run slots state visit.invocation visit.declaration visit.goal
    let result ← answer
    follow slots result.registry rest

/-- Arbitrarily many actual intervening captures cannot change an existing
binder's allocated identity, including captures with a reused invocation key. -/
theorem follow_preserves_sources (slots : Nat → α) (state after : State α)
    (visits : List Visit) (returned : follow slots state visits = some after) :
    after.boundary = state.boundary ∧
      ∀ key ∈ state.table, key ∈ after.table ∧
        source after.boundary after.table key = source state.boundary state.table key := by
  induction visits generalizing state with
  | nil =>
    have same : state = after := by simpa [follow] using returned
    subst after
    exact ⟨rfl, fun key member => ⟨member, rfl⟩⟩
  | cons visit rest ih =>
    cases stepped : run slots state visit.invocation visit.declaration visit.goal with
    | none => simp [follow, stepped] at returned
    | some answer =>
      cases answer with
      | none => simp [follow, stepped] at returned
      | some result =>
        have next := run_preserves_sources slots state visit.invocation
          visit.declaration visit.goal result stepped
        have tail := ih result.registry (by simpa [follow, stepped] using returned)
        exact ⟨tail.1.trans next.1, fun key member =>
          let first := next.2 key member
          let last := tail.2 key first.1
          ⟨last.1, last.2.trans first.2⟩⟩

/-- Actual generated atoms and retained requests carry the same model after
registration. No accepted-capture or consistency premise is required here. -/
theorem generated_requests_exact (slots : Nat → α) (assignment : α → Comp Common.model)
    (state : State α) (invocation : Nat) (declaration : Declaration) (goal : Goal)
    (bindings : Bindings) :
    All Common.model assignment
      (generated slots state invocation declaration goal bindings).candidate.state.atoms ↔
    Models assignment
      (generated slots state invocation declaration goal bindings).registry.requests :=
  CommonRoleSourceIntervalBatches.step_exact assignment state.requests _

/-- An independent original-model judgment for a finite sequence of explicitly
keyed invocations. Repeated keys use the same local valuation across visits.
Neither allocated names, ordinary atoms, the registry nor the runner occur here. -/
def VisitsFit (slots : Nat → α) (assignment : α → Comp Common.model)
    (locals : Key → Common.Ty) : List Visit → Prop
  | [] => True
  | visit :: rest => ∃ bindings,
    Accepts visit.declaration visit.goal bindings ∧
    HeadFits (fun n => (assignment (slots n)).1) (fun n => locals (visit.invocation, n))
      visit.declaration.head visit.goal.arguments ∧
    WhereFits (fun n => (assignment (slots n)).1) (fun n => locals (visit.invocation, n))
      visit.declaration bindings ∧
    VisitsFit slots assignment locals rest

private theorem generated_shared_exact (slots : Nat → α)
    (assignment : α → Comp Common.model) (values : Nat → Common.Ty)
    (locals : Key → Common.Ty) (state : State α) (invocation : Nat)
    (declaration : Declaration) (goal : Goal) (bindings : Bindings)
    (accepted : Accepts declaration goal bindings)
    (agrees : ∀ binding ∈ bindings,
      values (sourceAfter state invocation bindings binding.1) = locals (invocation, binding.1)) :
    SharedFits assignment values
      (generated slots state invocation declaration goal bindings).registry.requests ↔
    SharedFits assignment values state.requests ∧
      HeadFits (fun n => (assignment (slots n)).1) (fun n => locals (invocation,n))
        declaration.head goal.arguments ∧
      WhereFits (fun n => (assignment (slots n)).1) (fun n => locals (invocation,n))
        declaration bindings := by
  rw [generated_requests]
  simp only [SharedFits, List.forall_mem_append]
  change (SharedFits assignment values state.requests ∧
    SharedFits assignment values (CommonRoleCaptureBatchModels.demands slots
      (CommonRoleWhereSourceModels.captureJob declaration goal
        (sourceAfter state invocation bindings)) bindings)) ↔ _
  have batch : SharedFits assignment values (CommonRoleCaptureBatchModels.demands slots
      (CommonRoleWhereSourceModels.captureJob declaration goal
        (sourceAfter state invocation bindings)) bindings) ↔
      HeadFits (fun n => (assignment (slots n)).1) (fun n => locals (invocation,n))
        declaration.head goal.arguments := by
    rw [← CommonRoleWhereSourceModels.normalized_heads
      (fun n => (assignment (slots n)).1) (fun n => locals (invocation,n)) declaration.head goal.arguments,
      CommonRoleCaptureBatchModels.capture_arguments_fits
        (fun n => (assignment (slots n)).1) (fun n => locals (invocation,n)) accepted.2.2.2.1]
    simp only [SharedFits, CommonRoleCaptureBatchModels.demands, List.forall_mem_map,
      CommonRoleCaptureBatchModels.BindingFits, CommonRoleIntervals.evaluate,
      CommonRoleIntervalGeneration.eval, Core.PresenceGeneration.TyTerm.eval_rename,
      CommonRoleRepeatedCaptureChecks.term_eval,
      CommonRoleWhereSourceModels.captureJob, Function.comp_def]
    constructor <;> intro models binding member
    · simpa only [agrees binding member] using models binding member
    · simpa only [agrees binding member] using models binding member
  rw [batch]
  exact ⟨fun ⟨old, head⟩ => ⟨old, head,
    CommonRoleWhereSourceModels.accepted_where_fits _ _ _ _ _ accepted head⟩,
    fun ⟨old, head, _⟩ => ⟨old, head⟩⟩

/-- A structural/model witness produces an actual finite run; no success
hypothesis is required to obtain the execution. -/
theorem visits_fit_returns (slots : Nat → α) (assignment : α → Comp Common.model)
    (locals : Key → Common.Ty) (visits : List Visit)
    (fits : VisitsFit slots assignment locals visits) (state : State α) :
    ∃ after, follow slots state visits = some after := by
  induction visits generalizing state with
  | nil => exact ⟨state, rfl⟩
  | cons visit rest ih =>
    obtain ⟨bindings, accepted, _, _, tail⟩ := fits
    obtain ⟨after, followed⟩ := ih tail
      (generated slots state visit.invocation visit.declaration visit.goal bindings).registry
    exact ⟨after, by simp [follow, run,
      (CommonRoleIntervalCandidates.inspect_accepts_exact ..).mpr accepted, followed]⟩

/-- All visits share one original keyed model. Agreement is needed only for
actual finite registered keys, including every key emitted earlier in the run. -/
theorem follow_shared_exact (slots : Nat → α) (assignment : α → Comp Common.model)
    (values : Nat → Common.Ty) (locals : Key → Common.Ty)
    (state after : State α) (visits : List Visit)
    (returned : follow slots state visits = some after)
    (agrees : ∀ key ∈ after.table,
      values (source after.boundary after.table key) = locals key) :
    SharedFits assignment values after.requests ↔
      SharedFits assignment values state.requests ∧ VisitsFit slots assignment locals visits := by
  induction visits generalizing state with
  | nil =>
    have same : state = after := by simpa [follow] using returned
    subst state
    simp [VisitsFit]
  | cons visit rest ih =>
    cases inspected : CommonRoleIntervalCandidates.inspect visit.declaration visit.goal with
    | none => simp [follow, run, inspected] at returned
    | some answer =>
      cases answer with
      | none => simp [follow, run, inspected] at returned
      | some bindings =>
        let result := generated slots state visit.invocation visit.declaration visit.goal bindings
        have followed : follow slots result.registry rest = some after := by
          simpa [follow, run, inspected, result] using returned
        have preserved := follow_preserves_sources slots result.registry after rest followed
        have accepted := (CommonRoleIntervalCandidates.inspect_accepts_exact ..).mp inspected
        have step := generated_shared_exact slots assignment values locals state visit.invocation
          visit.declaration visit.goal bindings accepted (fun binding member => by
            have present := generated_key_present state visit.invocation bindings binding member
            have stable := preserved.2 (visit.invocation, binding.1) present
            exact (congrArg values stable.2.symm).trans (agrees _ stable.1))
        rw [ih result.registry followed, step]
        constructor
        · rintro ⟨⟨previous, head, children⟩, tail⟩
          exact ⟨previous, bindings, accepted, head, children, tail⟩
        · rintro ⟨previous, other, otherAccepted, head, children, tail⟩
          have same : other = bindings := by
            have otherReturned := (CommonRoleIntervalCandidates.inspect_accepts_exact ..).mpr otherAccepted
            rw [inspected] at otherReturned
            exact (Option.some.inj (Option.some.inj otherReturned)).symm
          subst other
          exact ⟨⟨previous, head, children⟩, tail⟩

/-- A mathematical extension, never evaluated by the candidate runner. -/
def extend (boundary : Nat) (table : Table) (previous : Nat → Common.Ty)
    (locals : Key → Common.Ty) (name : Nat) : Common.Ty :=
  if name < boundary then previous name else locals ((table[name - boundary]?).getD (0,0))

theorem extend_key (boundary : Nat) (table : Table) (previous : Nat → Common.Ty)
    (locals : Key → Common.Ty) (key : Key) (member : key ∈ table) :
    extend boundary table previous locals (source boundary table key) = locals key := by
  have bound := List.idxOf_lt_length_of_mem member
  have found : table[table.idxOf key]? = some key :=
    List.getElem?_eq_some_iff.mpr ⟨bound, List.getElem_idxOf bound⟩
  have outside : ¬ boundary + table.idxOf key < boundary := by omega
  simp [extend, source, outside, found]

/-- The complete finite explicit-key utility: actual success with a model iff
initial demands have a model and all original invocations have one shared keyed
model. No source map, successful-run, consistency, or child-dictionary premise.
This does not derive invocation keys or establish saturation of generated goals. -/
theorem follow_models_exact (slots : Nat → α) (assignment : α → Comp Common.model)
    (old : List (Demand α)) (visits : List Visit) :
    (∃ after, follow slots (start old) visits = some after ∧ Models assignment after.requests) ↔
      Models assignment old ∧ ∃ locals, VisitsFit slots assignment locals visits := by
  constructor
  · rintro ⟨after, returned, models⟩
    obtain ⟨values, shared⟩ := (CommonRoleCaptureBatchModels.models_shared_exact ..).mp models
    let locals : Key → Common.Ty := fun key => values (source after.boundary after.table key)
    have exactModels := follow_shared_exact slots assignment values locals (start old) after
      visits returned (fun _ _ => rfl)
    obtain ⟨previous, fits⟩ := exactModels.mp shared
    exact ⟨(CommonRoleCaptureBatchModels.models_shared_exact ..).mpr ⟨values, previous⟩,
      locals, fits⟩
  · rintro ⟨models, locals, fits⟩
    obtain ⟨previous, previousModels⟩ :=
      (CommonRoleCaptureBatchModels.models_shared_exact ..).mp models
    obtain ⟨after, returned⟩ := visits_fit_returns slots assignment locals visits fits (start old)
    have sameBoundary : after.boundary = CommonRoleFreshCaptureSources.boundary old :=
      (follow_preserves_sources slots (start old) after visits returned).1
    let values := extend after.boundary after.table previous locals
    have oldModels : SharedFits assignment values old := by
      intro request member
      have below := CommonRoleFreshCaptureSources.old_below old request member
      have equal : values request.1 = previous request.1 := by
        simp only [values, extend, sameBoundary, below, ite_true]
      rw [equal]
      exact previousModels request member
    have shared := (follow_shared_exact slots assignment values locals (start old) after
      visits returned (fun key member => extend_key _ _ _ _ key member)).mpr ⟨oldModels, fits⟩
    exact ⟨after, returned,
      (CommonRoleCaptureBatchModels.models_shared_exact ..).mpr ⟨values, shared⟩⟩

end Yulang.CommonRoleRegisteredCaptureSources
