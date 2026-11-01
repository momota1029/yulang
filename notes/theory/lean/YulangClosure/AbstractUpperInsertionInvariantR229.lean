import YulangClosure.AbstractBoundCycleNormalizationR223

/-!
R229: storage invariants for the exact successful R212 upper insertion only.
No accepted solver, source judgment, regular readout or production claim is
introduced. Build/cache ownership belongs to Luna; this leaf does not execute
Lean. The audit commands below are requested audits, not execution receipts.
-/
namespace YulangClosure.SimpleSub.UpperInsertionR229

open AbstractCore BoundCycleR223

/-- Finite histories of the actual partial operation, with no failed calls. -/
inductive History (problem : CoreProblem) : CoreState → Prop where
  | initial : History problem problem.initial
  | step {before after} : History problem before →
      before.insertPendingUpper = some after → History problem after

theorem lookup_lt {α : Type} {rows : List α} {identity : Nat} {row : α}
    (lookup : rows[identity]? = some row) : identity < rows.length := by
  rcases List.getElem?_eq_some_iff.mp lookup with ⟨inside, _⟩
  exact inside

/-- The exact row change, with its resulting queue supplied explicitly. -/
def update (state : CoreState) (kind : Kind) (identity : Nat)
    (row : CoreRow kind) (upper : Term kind) (pending : List CoreDemand) : CoreState :=
  { state.withRows kind ((state.rows kind).set identity
      { row with upperBounds := upper :: row.upperBounds }) with pending := pending }

@[simp] theorem update_rows_same (state : CoreState) (kind : Kind) (i : Nat)
    (row : CoreRow kind) (upper : Term kind) (pending : List CoreDemand) :
    (update state kind i row upper pending).rows kind =
      (state.rows kind).set i { row with upperBounds := upper :: row.upperBounds } := by
  cases kind <;> rfl

@[simp] theorem update_rows_other (state : CoreState) {kind other : Kind}
    (different : other ≠ kind) (i : Nat) (row : CoreRow kind)
    (upper : Term kind) (pending : List CoreDemand) :
    (update state kind i row upper pending).rows other = state.rows other := by
  cases kind <;> cases other <;> simp_all [update, CoreState.withRows, CoreState.rows]

@[simp] theorem update_representatives (state : CoreState) (kind other : Kind)
    (i : Nat) (row : CoreRow kind) (upper : Term kind) (pending : List CoreDemand) :
    (update state kind i row upper pending).representatives other =
      state.representatives other := by
  cases kind <;> cases other <;> rfl

@[simp] theorem update_pending (state : CoreState) (kind : Kind) (i : Nat)
    (row : CoreRow kind) (upper : Term kind) (pending : List CoreDemand) :
    (update state kind i row upper pending).pending = pending := by
  cases kind <;> rfl

/-- Inversion retains the real representative lookup and replay domain. -/
theorem successful_view {before after : CoreState}
    (call : before.insertPendingUpper = some after) :
    ∃ (demand : CoreDemand) (rest : List CoreDemand) (identity representative : Nat)
      (row : CoreRow demand.clause.kind),
      before.pending = demand :: rest ∧ demand.clause.lower = .var identity ∧
      (before.representatives demand.clause.kind)[identity]? = some representative ∧
      (before.rows demand.clause.kind)[representative]? = some row ∧
      (ScopedPublication.vars demand.clause.upper).all (fun dependency =>
        match (before.rows dependency.kind)[dependency.index]? with
        | none => false
        | some target => decide (target.level ≤ row.level)) = true ∧
      after = update before demand.clause.kind representative row demand.clause.upper
        (row.lowerBounds.map (fun lower =>
          { demand with clause := ⟨demand.clause.kind, lower, demand.clause.upper⟩ }) ++ rest) := by
  cases hp : before.pending with
  | nil => simp [CoreState.insertPendingUpper, hp] at call
  | cons demand rest =>
    rcases demand with ⟨⟨kind, lower, upper⟩, origin, receiver⟩
    cases lower <;>
      try simp [CoreState.insertPendingUpper, hp] at call
    all_goals
      rename_i identity
      cases hr : (before.representatives kind)[identity]? with
      | none => simp [CoreState.insertPendingUpper, hp, hr] at call
      | some representative =>
        cases hg : (before.rows kind)[representative]? with
        | none => simp [CoreState.insertPendingUpper, hp, hr, hg] at call
        | some row =>
          have decoded := call
          simp only [CoreState.insertPendingUpper, hp, hr, hg,
            Option.bind_some] at decoded
          split at decoded
          · simp at decoded
          · rename_i low
            simp only [Option.some.injEq] at decoded
            refine ⟨⟨⟨kind, .var identity, upper⟩, origin, receiver⟩, rest, identity, representative,
              row, rfl, rfl, hr, hg, ?_, ?_⟩
            · simp only [Bool.not_eq_true, Bool.not_eq_false', List.all_eq_true] at low ⊢
              intro dependency member
              cases hlookup : (before.rows dependency.kind)[dependency.index]? with
              | none =>
                exfalso
                exact low ⟨dependency, member, by simp [hlookup]⟩
              | some target =>
                by_cases okay : target.level ≤ row.level
                · simp [hlookup, okay]
                · exfalso
                  exact low ⟨dependency, member, by simp [hlookup, okay]⟩
            · exact decoded.symm

/-- This record contains conclusions proved by history induction, not inputs
or an alternative definition of successful inference. -/
structure Invariant (problem : CoreProblem) (state : CoreState) : Prop where
  lengths : ∀ kind, (state.rows kind).length = problem.allocated kind
  representatives : ∀ kind, state.representatives kind = List.range (problem.allocated kind)
  metadata : ∀ (kind : Kind) (identity : Nat) (row : CoreRow kind), (state.rows kind)[identity]? = some row →
    (problem.levels kind)[identity]? = some row.level ∧
      row.nonGeneric = false ∧ row.lowerBounds = []
  upperClosed : ∀ (kind : Kind) (identity : Nat) (row : CoreRow kind), (state.rows kind)[identity]? = some row →
    ∀ upper, upper ∈ row.upperBounds → ∀ dependency,
      dependency ∈ ScopedPublication.vars upper →
      ∃ target, (state.rows dependency.kind)[dependency.index]? = some target ∧
        target.level ≤ row.level
  conserved : List.Perm (state.pending.map CoreDemand.clause ++ physicalBounds state)
    problem.originalConstraints

/-- Indexed extraction with an arbitrary starting coordinate. -/
def rowsFrom {kind : Kind} (offset : Nat) (rows : List (CoreRow kind)) : Store :=
  (rows.zipIdx offset).flatMap (fun pair => rowClauses pair.2 pair.1)

@[simp] theorem rowsFrom_nil (offset : Nat) (kind : Kind) :
    rowsFrom offset ([] : List (CoreRow kind)) = [] := rfl

@[simp] theorem rowsFrom_cons {kind : Kind} (offset : Nat)
    (row : CoreRow kind) (rest : List (CoreRow kind)) :
    rowsFrom offset (row :: rest) = rowClauses offset row ++ rowsFrom (offset + 1) rest := by
  simp [rowsFrom, List.zipIdx_cons]

theorem rowsFrom_initial (kind : Kind) (levels : List Nat) (offset : Nat) :
    rowsFrom offset (levels.map (CoreRow.initial kind)) = [] := by
  induction levels generalizing offset with
  | nil => rfl
  | cons level rest ih => simp [rowClauses, CoreRow.initial, ih]

/-- One physical insertion adds exactly one clause, including duplicates. -/
theorem rowsFrom_insert {kind : Kind} (rows : List (CoreRow kind))
    (identity offset : Nat) (row : CoreRow kind) (upper : Term kind)
    (lookup : rows[identity]? = some row) (empty : row.lowerBounds = []) :
    List.Perm
      (rowsFrom offset (rows.set identity { row with upperBounds := upper :: row.upperBounds }))
      (⟨kind, .var (offset + identity), upper⟩ :: rowsFrom offset rows) := by
  induction rows generalizing identity offset with
  | nil => simp at lookup
  | cons first rest ih =>
    cases identity with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
      subst first
      simp [rowClauses, empty, Nat.add_zero]
    | succ identity =>
      simp only [List.getElem?_cons_succ] at lookup
      simpa only [List.set_cons_succ, rowsFrom_cons, Nat.add_succ,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_zero] using
        ((List.Perm.append_left (rowClauses offset first)
          (ih identity (offset + 1) lookup)).trans List.perm_middle)

/-- Physical extraction commutes with the actual selected-kind insertion. -/
theorem physical_insert (state : CoreState) (kind : Kind) (identity : Nat)
    (row : CoreRow kind) (upper : Term kind) (pending : List CoreDemand)
    (lookup : (state.rows kind)[identity]? = some row) (empty : row.lowerBounds = []) :
    List.Perm (physicalBounds (update state kind identity row upper pending))
      (⟨kind, .var identity, upper⟩ :: physicalBounds state) := by
  have added := rowsFrom_insert (state.rows kind) identity 0 row upper lookup empty
  cases kind with
  | value =>
    simpa [physicalBounds, physicalRows, rowsFrom, update, CoreState.withRows,
      CoreState.rows] using added.append_right (physicalRows state.effectRows)
  | effect =>
    simpa [physicalBounds, physicalRows, rowsFrom, update, CoreState.withRows,
      CoreState.rows] using
      (List.Perm.append_left (physicalRows state.valueRows) added).trans List.perm_middle

/-- The invariant has no assumption about solutions, typing or termination. -/
theorem initial_invariant (problem : CoreProblem) : Invariant problem problem.initial := by
  constructor
  · intro kind; cases kind <;> simp [CoreProblem.initial, CoreState.rows, CoreProblem.allocated,
      CoreProblem.levels]
  · intro kind; cases kind <;> rfl
  · intro kind identity row lookup
    have mapped : ((problem.levels kind).map (CoreRow.initial kind))[identity]? = some row := by
      cases kind <;> exact lookup
    rw [List.getElem?_map] at mapped
    cases h : (problem.levels kind)[identity]? with
    | none => simp [h] at mapped
    | some level =>
      simp only [h, Option.map_some, Option.some.injEq] at mapped
      subst row
      simp [CoreRow.initial, h]
  · intro kind identity row lookup upper member
    have mapped : ((problem.levels kind).map (CoreRow.initial kind))[identity]? = some row := by
      cases kind <;> exact lookup
    rw [List.getElem?_map] at mapped
    cases h : (problem.levels kind)[identity]? with
    | none => simp [h] at mapped
    | some level =>
      simp only [h, Option.map_some, Option.some.injEq] at mapped
      subst row
      cases member
  · have physical : physicalBounds problem.initial = [] := by
      change rowsFrom 0 (problem.valueLevels.map (CoreRow.initial .value)) ++
        rowsFrom 0 (problem.effectLevels.map (CoreRow.initial .effect)) = []
      rw [rowsFrom_initial, rowsFrom_initial]
      rfl
    change List.Perm (problem.originalConstraints ++ physicalBounds problem.initial)
      problem.originalConstraints
    rw [physical, List.append_nil]

/-- Updating an upper bound leaves all row levels unchanged, at every lookup. -/
theorem update_level {state : CoreState} {kind : Kind} {identity : Nat}
    {row : CoreRow kind} {upper : Term kind} {pending : List CoreDemand}
    (old : (state.rows kind)[identity]? = some row) (other : Kind) (index : Nat) :
    (((update state kind identity row upper pending).rows other)[index]?).map CoreRow.level =
      ((state.rows other)[index]?).map CoreRow.level := by
  by_cases same : other = kind
  · subst other
    rw [update_rows_same]
    by_cases hindex : identity = index
    · subst index
      simp [List.getElem?_set_self (lookup_lt old), old]
    · simp [List.getElem?_set_ne hindex]
  · rw [update_rows_other state same]

/-- A level-preserving update transports an existing lookup to a real row. -/
theorem update_target {state : CoreState} {kind : Kind} {identity : Nat}
    {row : CoreRow kind} {upper : Term kind} {pending : List CoreDemand}
    (old : (state.rows kind)[identity]? = some row) {other : Kind} {index : Nat}
    {target : CoreRow other} (lookup : (state.rows other)[index]? = some target) :
    ∃ target', ((update state kind identity row upper pending).rows other)[index]? = some target' ∧
      target'.level = target.level := by
  have levels := update_level (upper := upper) (pending := pending) old other index
  rw [lookup] at levels
  cases h : ((update state kind identity row upper pending).rows other)[index]? with
  | none => simp [h] at levels
  | some target' =>
    exact ⟨target', rfl, by simpa [h] using levels⟩

/-- Every successful call in the history has an empty replay list. -/
theorem step_invariant {problem : CoreProblem} {before after : CoreState}
    (inv : Invariant problem before) (call : before.insertPendingUpper = some after) :
    Invariant problem after := by
  rcases successful_view call with
    ⟨demand, rest, identity, representative, row, hp, hl, hr, hg, low, result⟩
  have empty := (inv.metadata _ _ _ hg).2.2
  have replay : row.lowerBounds.map (fun lower =>
      { demand with clause := ⟨demand.clause.kind, lower, demand.clause.upper⟩ }) = [] := by
    simp [empty]
  rw [replay, List.nil_append] at result
  subst after
  have sameRepresentative : representative = identity := by
    rw [inv.representatives] at hr
    rcases List.getElem?_eq_some_iff.mp hr with ⟨inside, found⟩
    simpa using found.symm
  subst representative
  constructor
  · intro kind
    by_cases same : kind = demand.clause.kind
    · subst kind; simp [inv.lengths]
    · rw [update_rows_other before same]; exact inv.lengths kind
  · intro kind
    rw [update_representatives]
    exact inv.representatives kind
  · intro kind index target lookup
    by_cases same : kind = demand.clause.kind
    · subst kind
      rw [update_rows_same] at lookup
      by_cases hindex : identity = index
      · subst index
        rw [List.getElem?_set_self (lookup_lt hg)] at lookup
        cases Option.some.inj lookup
        exact inv.metadata demand.clause.kind identity row hg
      · rw [List.getElem?_set_ne hindex] at lookup
        exact inv.metadata _ _ _ lookup
    · rw [update_rows_other before same] at lookup
      exact inv.metadata _ _ _ lookup
  · intro kind index target lookup upper member dependency hd
    have transport (oldTarget : CoreRow dependency.kind)
        (oldLookup : (before.rows dependency.kind)[dependency.index]? = some oldTarget)
        (le : oldTarget.level ≤ target.level) :
        ∃ target', ((update before demand.clause.kind identity row demand.clause.upper rest).rows
          dependency.kind)[dependency.index]? = some target' ∧ target'.level ≤ target.level := by
      rcases update_target (upper := demand.clause.upper) (pending := rest) hg oldLookup with
        ⟨target', lookup', level⟩
      exact ⟨target', lookup', by simpa only [level] using le⟩
    by_cases same : kind = demand.clause.kind
    · subst kind
      rw [update_rows_same] at lookup
      by_cases hindex : identity = index
      · subst index
        rw [List.getElem?_set_self (lookup_lt hg)] at lookup
        cases Option.some.inj lookup
        rcases List.mem_cons.mp member with rfl | oldMember
        · have checked := List.all_eq_true.mp low dependency hd
          cases ht : (before.rows dependency.kind)[dependency.index]? with
          | none => simp [ht] at checked
          | some oldTarget =>
            exact transport oldTarget ht (by simpa [ht] using checked)
        · rcases inv.upperClosed _ _ _ hg upper oldMember dependency hd with ⟨t, ht, le⟩
          exact transport t ht le
      · rw [List.getElem?_set_ne hindex] at lookup
        rcases inv.upperClosed _ _ _ lookup upper member dependency hd with ⟨t, ht, le⟩
        exact transport t ht le
    · rw [update_rows_other before same] at lookup
      rcases inv.upperClosed _ _ _ lookup upper member dependency hd with ⟨t, ht, le⟩
      exact transport t ht le
  · have clauseEq : (⟨demand.clause.kind, .var identity, demand.clause.upper⟩ : Constraint) =
        demand.clause := by
      cases demand with
      | mk clause origin receiver =>
        cases clause with
        | mk kind lower upper => simp only at hl ⊢; cases hl; rfl
    have physical : List.Perm
        (physicalBounds (update before demand.clause.kind identity row demand.clause.upper rest))
        (demand.clause :: physicalBounds before) := by
      simpa only [clauseEq] using
        physical_insert before demand.clause.kind identity row demand.clause.upper rest hg empty
    apply ((List.Perm.append_left (rest.map CoreDemand.clause) physical).trans
      List.perm_middle).trans
    simpa [hp] using inv.conserved

theorem history_invariant {problem : CoreProblem} {state : CoreState}
    (history : History problem state) : Invariant problem state := by
  induction history with
  | initial => exact initial_invariant _
  | step _ call ih => exact step_invariant ih call

/-- Replay is proved empty from history; it is not excluded by History's step. -/
theorem no_opposite_replay {problem : CoreProblem} {state : CoreState}
    (history : History problem state) (kind : Kind) (identity : Nat)
    (row : CoreRow kind) (lookup : (state.rows kind)[identity]? = some row)
    (demand : CoreDemand) :
    row.lowerBounds.map (fun lower =>
      { demand with clause := ⟨kind, lower, row.upperBounds.headD (.var identity)⟩ }) = [] := by
  rw [((history_invariant history).metadata kind identity row lookup).2.2]
  rfl

/-- R223's total identity fallback is harmless on this precise history domain. -/
theorem resolve_identity {problem : CoreProblem} {state : CoreState}
    (history : History problem state) : resolve state = fun _ i => i := by
  funext kind identity
  unfold resolve
  rw [(history_invariant history).representatives]
  by_cases inside : identity < problem.allocated kind
  · simp [List.getElem?_range inside]
  · have missing : (List.range (problem.allocated kind))[identity]? = none :=
      List.getElem?_eq_none (by simpa using Nat.le_of_not_gt inside)
    rw [missing]
    rfl

theorem resolved_eq_physical {problem : CoreProblem} {state : CoreState}
    (history : History problem state) : resolvedBounds state = physicalBounds state := by
  unfold resolvedBounds
  rw [resolve_identity history]
  apply List.map_id''
  intro clause
  cases clause with
  | mk kind lower upper =>
    simp [Constraint.rename, Term.rename, Term.subst_id]

/-- Terminal extraction conserves every original duplicate clause. -/
theorem terminal_store {problem : CoreProblem} {state : CoreState}
    (history : History problem state) (terminal : state.pending = []) :
    List.Perm (physicalBounds state) problem.originalConstraints ∧
      List.Perm (resolvedBounds state) problem.originalConstraints := by
  have physical := (history_invariant history).conserved
  simp only [terminal, List.map_nil, List.nil_append] at physical
  exact ⟨physical, by rw [resolved_eq_physical history]; exact physical⟩

/-- The R223 normalized-store theorem now applies to the actual terminal
extraction; no solution or shared valuation is silently constructed. -/
theorem terminal_normalized_iff {problem : CoreProblem} {state : CoreState}
    (history : History problem state) (terminal : state.pending = []) (ρ : Valuation) :
    (normalizedBounds state).Satisfied ρ ↔
      problem.originalConstraints.Satisfied (fun k i => ρ k (stateQuotient state k i)) := by
  rw [normalizedBounds, normalized_solution_iff]
  constructor
  · intro solved clause member
    exact solved clause ((terminal_store history terminal).2.mem_iff.mpr member)
  · intro solved clause member
    exact solved clause ((terminal_store history terminal).2.mem_iff.mp member)

/-- The same original valuation is shared across every structural term,
including future client coordinates and both effect ports of Function. -/
theorem terminal_all_terms {problem : CoreProblem} {state : CoreState}
    (history : History problem state) (terminal : state.pending = [])
    (ρ : Valuation) (solved : problem.originalConstraints.Satisfied ρ) :
    ∃ σ : Valuation, (normalizedBounds state).Satisfied σ ∧
      ∀ kind (term : Term kind), Equivalent (term.subst ρ)
        ((term.rename (physicalClass state)).subst σ) := by
  have physicalSolved : (resolvedBounds state).Satisfied ρ := by
    intro clause member
    exact solved clause ((terminal_store history terminal).2.mem_iff.mp member)
  have result := solutions_and_all_terms (scopeSize state) (resolvedBounds state) ρ physicalSolved
  rcases result with ⟨σ, normalized, terms⟩
  refine ⟨σ, normalized, ?_⟩
  intro kind term
  have classes : physicalClass state = quotient (scopeSize state) (resolvedBounds state) := by
    funext k i
    simp only [physicalClass, stateQuotient, resolve_identity history]
  rw [classes]
  exact terms kind term

/-- Per-kind allocation, preserving the exact structural occurrence traversal. -/
def AllocatedTerm (problem : CoreProblem) {kind} (term : Term kind) : Prop :=
  ∀ dependency, dependency ∈ ScopedPublication.vars term →
    dependency.index < problem.allocated dependency.kind

def AllocatedClause (problem : CoreProblem) (clause : Constraint) : Prop :=
  AllocatedTerm problem clause.lower ∧ AllocatedTerm problem clause.upper

theorem term_allocated_iff (problem : CoreProblem) {kind} (term : Term kind) :
    problem.termAllocated term = true ↔ AllocatedTerm problem term := by
  simp [CoreProblem.termAllocated, AllocatedTerm, List.all_eq_true]

theorem original_allocated {problem : CoreProblem} (valid : problem.inputValid = true)
    {clause : Constraint} (member : clause ∈ problem.originalConstraints) :
    AllocatedClause problem clause := by
  rcases List.mem_map.mp member with ⟨demand, hd, rfl⟩
  have demands : problem.demands.all problem.demandValid = true :=
    (Bool.and_eq_true_iff.mp valid).2
  have checked := List.all_eq_true.mp demands demand hd
  simp only [CoreProblem.demandValid, Bool.and_eq_true] at checked
  exact ⟨(term_allocated_iff problem _).mp checked.1.2,
    (term_allocated_iff problem _).mp checked.2⟩

/-- Allocation follows through multiset conservation, never a retained-store
assumption. This theorem also covers nonterminal histories. -/
theorem physical_allocated {problem : CoreProblem} {state : CoreState}
    (valid : problem.inputValid = true) (history : History problem state)
    {clause : Constraint} (member : clause ∈ physicalBounds state) :
    AllocatedClause problem clause := by
  apply original_allocated valid
  exact (history_invariant history).conserved.mem_iff.mp
    (List.mem_append_right _ member)

theorem resolved_allocated {problem : CoreProblem} {state : CoreState}
    (valid : problem.inputValid = true) (history : History problem state)
    {clause : Constraint} (member : clause ∈ resolvedBounds state) :
    AllocatedClause problem clause := by
  rw [resolved_eq_physical history] at member
  exact physical_allocated valid history member

theorem allocated_le_scope {problem : CoreProblem} {state : CoreState}
    (history : History problem state) (kind : Kind) :
    problem.allocated kind ≤ scopeSize state := by
  calc
    problem.allocated kind = (state.rows kind).length :=
      ((history_invariant history).lengths kind).symm
    _ ≤ scopeSize state := by
      cases kind
      · exact Nat.le_max_left _ _
      · exact Nat.le_max_right _ _

theorem allocated_bounded {problem : CoreProblem} {state : CoreState}
    (history : History problem state) {kind} {term : Term kind}
    (allocated : AllocatedTerm problem term) : Generalization.Bounded (scopeSize state) term := by
  have bound : ∀ dependency, dependency ∈ ScopedPublication.vars term →
      dependency.index < scopeSize state := fun dependency member =>
    Nat.lt_of_lt_of_le (allocated dependency member) (allocated_le_scope history dependency.kind)
  clear allocated
  induction term <;> simp_all [Generalization.Bounded, ScopedPublication.vars]

theorem resolved_bounded {problem : CoreProblem} {state : CoreState}
    (valid : problem.inputValid = true) (history : History problem state) :
    Generalization.StoreBounded (scopeSize state) (resolvedBounds state) := by
  intro clause member
  have allocated := resolved_allocated valid history member
  exact ⟨allocated_bounded history allocated.1, allocated_bounded history allocated.2⟩

/-- Edge endpoints are bounded by their own kind's allocation, not the maximum
allocation used by R223's finite enumeration. -/
theorem edge_allocated {problem : CoreProblem} {state : CoreState}
    (valid : problem.inputValid = true) (history : History problem state)
    {kind : Kind} {i j : Nat} (found : edge (resolvedBounds state) kind i j = true) :
    i < problem.allocated kind ∧ j < problem.allocated kind := by
  rcases List.any_eq_true.mp found with ⟨clause, member, found⟩
  have allocated := resolved_allocated valid history member
  cases clause with
  | mk ck lower upper =>
    cases lower <;> cases upper <;>
      simp_all [clauseEdge, AllocatedClause, AllocatedTerm, ScopedPublication.vars]

theorem reach_allocated {problem : CoreProblem} {state : CoreState}
    (valid : problem.inputValid = true) (history : History problem state)
    {kind : Kind} {i j : Nat}
    (path : BirthLevelSCC.Reach (fun a b => edge (resolvedBounds state) kind a b = true) i j)
    (start : i < problem.allocated kind) : j < problem.allocated kind := by
  revert start
  induction path with
  | refl => exact fun start => start
  | cons first _ ih => exact fun _ => ih (edge_allocated valid history first).2

/-- An allocated row cannot reach padding or a nonexistent same-kind row. -/
theorem connected_no_phantom {problem : CoreProblem} {state : CoreState}
    (valid : problem.inputValid = true) (history : History problem state)
    {kind : Kind} {i j : Nat} (allocated : i < problem.allocated kind)
    (same : connected (scopeSize state) (resolvedBounds state) kind i j = true) :
    j < problem.allocated kind := by
  have forward := (Bool.and_eq_true_iff.mp same).1
  exact reach_allocated valid history (BirthLevelSCC.finiteReach_sound _ forward) allocated

/-- Every physical class of an allocated row has only actual same-kind members,
even when the other kind has a larger allocation. -/
theorem class_no_phantom {problem : CoreProblem} {state : CoreState}
    (valid : problem.inputValid = true) (history : History problem state)
    {kind : Kind} {i j : Nat} (allocated : i < problem.allocated kind)
    (same : physicalClass state kind i = physicalClass state kind j) :
    j < problem.allocated kind := by
  have hi := Nat.lt_of_lt_of_le allocated (allocated_le_scope history kind)
  have sameQ : quotient (scopeSize state) (resolvedBounds state) kind i =
      quotient (scopeSize state) (resolvedBounds state) kind j := by
    simpa only [physicalClass, stateQuotient, resolve_identity history] using same
  by_cases hj : j < scopeSize state
  · exact connected_no_phantom valid history allocated ((quotient_eq_iff hi hj).mp sameQ)
  · rw [quotient_future (Nat.le_of_not_gt hj)] at sameQ
    exact sameQ ▸ Nat.lt_of_le_of_lt (quotient_le _ _ _ _) allocated

/-- The quotient representative itself is an allocated row. -/
theorem class_allocated {problem : CoreProblem} {state : CoreState}
    (history : History problem state) {kind : Kind} {i : Nat}
    (allocated : i < problem.allocated kind) :
    physicalClass state kind i < problem.allocated kind := by
  simpa only [physicalClass, stateQuotient, resolve_identity history] using
    Nat.lt_of_le_of_lt (quotient_le (scopeSize state) (resolvedBounds state) kind i) allocated

/-- R223's SCC theorem applies with its actual boundedness premise proved. -/
theorem exact_physical_scc {problem : CoreProblem} {state : CoreState}
    (valid : problem.inputValid = true) (history : History problem state)
    {kind : Kind} {i j : Nat} (hi : i < problem.allocated kind)
    (hj : j < problem.allocated kind) :
    physicalClass state kind i = physicalClass state kind j ↔
      BirthLevelSCC.Reach (fun a b => edge (resolvedBounds state) kind a b = true) i j ∧
      BirthLevelSCC.Reach (fun a b => edge (resolvedBounds state) kind a b = true) j i := by
  simpa only [physicalClass, stateQuotient, resolve_identity history] using
    quotient_exact_scc (resolved_bounded valid history)
      (Nat.lt_of_lt_of_le hi (allocated_le_scope history kind))
      (Nat.lt_of_lt_of_le hj (allocated_le_scope history kind))

/-- Class levels are R223's actual fiber minimum; the accompanying theorem
excludes every default-level padding coordinate from this fiber. -/
theorem class_minimum_real {problem : CoreProblem} {state : CoreState}
    (valid : problem.inputValid = true) (history : History problem state)
    {kind : Kind} {i : Nat} (allocated : i < problem.allocated kind) :
    Generalization.FiberMinimum (scopeSize state) (stateLevels state)
      (physicalClass state) kind (physicalClass state kind i)
      (classLevels state kind (physicalClass state kind i)) ∧
      (∀ j, physicalClass state kind j = physicalClass state kind i →
        j < problem.allocated kind) := by
  constructor
  · apply actual_class_minimum_at_fixed
    · exact Nat.lt_of_lt_of_le (class_allocated history allocated) (allocated_le_scope history kind)
    · simp only [physicalClass, stateQuotient, resolve_identity history]
      exact quotient_idempotent _ _ _ _
  · intro j same
    exact class_no_phantom valid history allocated same.symm

/-- Every stored upper dependency has a real row at no greater original level;
all lower lists and nonGeneric flags are still their initialized values. -/
theorem stored_upper_closed {problem : CoreProblem} {state : CoreState}
    (history : History problem state) {kind : Kind} {identity : Nat} {row : CoreRow kind}
    (lookup : (state.rows kind)[identity]? = some row) {upper : Term kind}
    (member : upper ∈ row.upperBounds) {dependency : ScopedPublication.Row}
    (occurs : dependency ∈ ScopedPublication.vars upper) :
    identity < problem.allocated kind ∧
      ∃ target, (state.rows dependency.kind)[dependency.index]? = some target ∧
        dependency.index < problem.allocated dependency.kind ∧ target.level ≤ row.level ∧
        (problem.levels dependency.kind)[dependency.index]? = some target.level := by
  have inv := history_invariant history
  have owner := (lookup_lt lookup)
  rw [inv.lengths] at owner
  rcases inv.upperClosed _ _ _ lookup upper member dependency occurs with ⟨target, ht, le⟩
  have allocated := (lookup_lt ht)
  rw [inv.lengths] at allocated
  exact ⟨owner, target, ht, allocated, le, (inv.metadata _ _ _ ht).1⟩

end YulangClosure.SimpleSub.UpperInsertionR229

/-! Complete authored-theorem audit surface; execution belongs to Luna. -/

#check @YulangClosure.SimpleSub.UpperInsertionR229.lookup_lt
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.lookup_lt

#check @YulangClosure.SimpleSub.UpperInsertionR229.update_rows_same
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.update_rows_same

#check @YulangClosure.SimpleSub.UpperInsertionR229.update_rows_other
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.update_rows_other

#check @YulangClosure.SimpleSub.UpperInsertionR229.update_representatives
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.update_representatives

#check @YulangClosure.SimpleSub.UpperInsertionR229.update_pending
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.update_pending

#check @YulangClosure.SimpleSub.UpperInsertionR229.successful_view
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.successful_view

#check @YulangClosure.SimpleSub.UpperInsertionR229.rowsFrom_nil
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.rowsFrom_nil

#check @YulangClosure.SimpleSub.UpperInsertionR229.rowsFrom_cons
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.rowsFrom_cons

#check @YulangClosure.SimpleSub.UpperInsertionR229.rowsFrom_initial
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.rowsFrom_initial

#check @YulangClosure.SimpleSub.UpperInsertionR229.rowsFrom_insert
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.rowsFrom_insert

#check @YulangClosure.SimpleSub.UpperInsertionR229.initial_invariant
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.initial_invariant

#check @YulangClosure.SimpleSub.UpperInsertionR229.update_level
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.update_level

#check @YulangClosure.SimpleSub.UpperInsertionR229.update_target
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.update_target

#check @YulangClosure.SimpleSub.UpperInsertionR229.step_invariant
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.step_invariant

#check @YulangClosure.SimpleSub.UpperInsertionR229.history_invariant
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.history_invariant

#check @YulangClosure.SimpleSub.UpperInsertionR229.no_opposite_replay
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.no_opposite_replay

#check @YulangClosure.SimpleSub.UpperInsertionR229.resolve_identity
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.resolve_identity

#check @YulangClosure.SimpleSub.UpperInsertionR229.resolved_eq_physical
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.resolved_eq_physical

#check @YulangClosure.SimpleSub.UpperInsertionR229.terminal_store
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.terminal_store

#check @YulangClosure.SimpleSub.UpperInsertionR229.terminal_normalized_iff
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.terminal_normalized_iff

#check @YulangClosure.SimpleSub.UpperInsertionR229.terminal_all_terms
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.terminal_all_terms

#check @YulangClosure.SimpleSub.UpperInsertionR229.term_allocated_iff
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.term_allocated_iff

#check @YulangClosure.SimpleSub.UpperInsertionR229.original_allocated
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.original_allocated

#check @YulangClosure.SimpleSub.UpperInsertionR229.physical_allocated
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.physical_allocated

#check @YulangClosure.SimpleSub.UpperInsertionR229.resolved_allocated
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.resolved_allocated

#check @YulangClosure.SimpleSub.UpperInsertionR229.allocated_le_scope
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.allocated_le_scope

#check @YulangClosure.SimpleSub.UpperInsertionR229.allocated_bounded
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.allocated_bounded

#check @YulangClosure.SimpleSub.UpperInsertionR229.resolved_bounded
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.resolved_bounded

#check @YulangClosure.SimpleSub.UpperInsertionR229.edge_allocated
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.edge_allocated

#check @YulangClosure.SimpleSub.UpperInsertionR229.reach_allocated
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.reach_allocated

#check @YulangClosure.SimpleSub.UpperInsertionR229.connected_no_phantom
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.connected_no_phantom

#check @YulangClosure.SimpleSub.UpperInsertionR229.class_no_phantom
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.class_no_phantom

#check @YulangClosure.SimpleSub.UpperInsertionR229.class_allocated
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.class_allocated

#check @YulangClosure.SimpleSub.UpperInsertionR229.exact_physical_scc
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.exact_physical_scc

#check @YulangClosure.SimpleSub.UpperInsertionR229.class_minimum_real
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.class_minimum_real

#check @YulangClosure.SimpleSub.UpperInsertionR229.stored_upper_closed
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.stored_upper_closed

#check @YulangClosure.SimpleSub.UpperInsertionR229.physical_insert
#print axioms YulangClosure.SimpleSub.UpperInsertionR229.physical_insert
