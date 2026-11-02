import YulangClosure.AbstractSimpleSubCore
import YulangClosure.BirthLevelSCC

/-!
R223 candidate constraint normalization, under the unchanged R223 theorem gate.
This module is a construction over the existing structural `Term`/`Sub` algebra.
It is not source typing, a complete CoreAccepted run, a regular-graph compiler,
or an equivalence theorem for the paper's Fig. 12 recursive syntax.

Only top-level variable/variable clauses form graph edges. Both kinds are
separate, and every retained clause is renamed before reflexive VARIABLE
clauses alone are removed. Free classes stay variables. No type is selected
for a free class. Physical row extraction below visits EVERY physical row.

Source: Parreaux, The Simple Essence of Algebraic Subtyping (2020), sections
3.5.1 and 5.3, Figs. 11--12; authoritative top-level inference principles;
birth-level correction (which concerns a different graph); R222 obstruction.
The paper and research drafts do not grant production semantic authority.

Execution ownership: Luna only. The leaf constructing this file does not run
Lean/Lake/checker or write any cache. The audit commands at the end are targets
for Luna, not claimed execution receipts. Luna reported that revision 1 failed
elaboration; revision 2 repairs the reported errors and awaits Luna's recheck.
-/
namespace YulangClosure.SimpleSub.BoundCycleR223

open YulangClosure.BirthLevelSCC (Reach finiteReach)

/-- A clause contributes an edge only when BOTH complete endpoints are vars. -/
def clauseEdge (k : Kind) (i j : Nat) (c : Constraint) : Bool :=
  match c.lower, c.upper with
  | .var a, .var b => decide (c.kind = k ∧ a = i ∧ b = j)
  | _, _ => false

def edge (store : Store) (k : Kind) (i j : Nat) : Bool :=
  store.any (clauseEdge k i j)

def connected (n : Nat) (store : Store) (k : Kind) (i j : Nat) : Bool :=
  finiteReach (edge store k) (List.range n) i j &&
    finiteReach (edge store k) (List.range n) j i

theorem connected_refl (n : Nat) (store : Store) (k : Kind) (i : Nat) :
    connected n store k i i = true := by
  simp [connected, BirthLevelSCC.finiteReach_refl]

theorem connected_symm {n store k i j} (h : connected n store k i j = true) :
    connected n store k j i = true := by
  simp only [connected, Bool.and_eq_true] at h ⊢
  exact ⟨h.2, h.1⟩

theorem connected_trans {n store k i j l}
    (hj : j < n) (ij : connected n store k i j = true)
    (jl : connected n store k j l = true) : connected n store k i l = true := by
  simp only [connected, Bool.and_eq_true] at ij jl ⊢
  exact ⟨BirthLevelSCC.finiteReach_join _ (List.mem_range.mpr hj) ij.1 jl.1,
    BirthLevelSCC.finiteReach_join _ (List.mem_range.mpr hj) jl.2 ij.2⟩

/-- Finite, executable minimum; the seed witnesses nonemptiness. -/
def lowerClass (select : Nat → Bool) (acc i : Nat) : Nat :=
  if select i then min acc i else acc

def classMinimum (select : Nat → Bool) (rows : List Nat) (seed : Nat) : Nat :=
  rows.foldl (lowerClass select) seed

theorem classMinimum_le (select : Nat → Bool) (rows : List Nat) (seed : Nat) :
    classMinimum select rows seed ≤ seed := by
  induction rows generalizing seed with
  | nil => exact Nat.le_refl _
  | cons i rest ih =>
    apply Nat.le_trans (ih _)
    simp only [lowerClass]
    split
    · exact Nat.min_le_left _ _
    · exact Nat.le_refl _

theorem classMinimum_member_le (select : Nat → Bool) {rows : List Nat} {i : Nat}
    (member : i ∈ rows) (selected : select i = true) (seed : Nat) :
    classMinimum select rows seed ≤ i := by
  induction rows generalizing seed with
  | nil => cases member
  | cons a rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_trans (classMinimum_le select rest _)
        (by simpa [lowerClass, selected] using Nat.min_le_right seed i)
    · exact ih member (lowerClass select seed a)

theorem classMinimum_selected (select : Nat → Bool) (rows : List Nat) (seed : Nat)
    (selected : select seed = true) :
    select (classMinimum select rows seed) = true := by
  induction rows generalizing seed with
  | nil => exact selected
  | cons a rest ih =>
    apply ih
    unfold lowerClass
    split
    · rename_i ha
      by_cases hs : seed ≤ a
      · simpa [Nat.min_eq_left hs] using selected
      · simpa [Nat.min_eq_right (Nat.le_of_not_ge hs)] using ha
    · exact selected

/-- Later client coordinates outside the original allocation remain fixed. -/
def quotient (n : Nat) (store : Store) : Renaming :=
  fun k i => if i < n then
    classMinimum (connected n store k i) (List.range n) i else i

theorem quotient_future {n store k i} (hi : n ≤ i) :
    quotient n store k i = i := by simp [quotient, Nat.not_lt.mpr hi]

theorem quotient_le (n : Nat) (store : Store) (k : Kind) (i : Nat) :
    quotient n store k i ≤ i := by
  unfold quotient
  split
  · exact classMinimum_le _ _ _
  · exact Nat.le_refl _

theorem quotient_in_scope {n store k i} (hi : i < n) :
    quotient n store k i < n := Nat.lt_of_le_of_lt (quotient_le _ _ _ _) hi

theorem quotient_connected (n : Nat) (store : Store) (k : Kind) (i : Nat) :
    connected n store k i (quotient n store k i) = true := by
  unfold quotient
  split
  · exact classMinimum_selected _ _ _ (connected_refl _ _ _ _)
  · exact connected_refl _ _ _ _

theorem quotient_eq_of_connected {n store k i j} (hi : i < n) (hj : j < n)
    (same : connected n store k i j = true) :
    quotient n store k i = quotient n store k j := by
  have iqj := connected_trans hj same (quotient_connected n store k j)
  have jqi := connected_trans hi (connected_symm same) (quotient_connected n store k i)
  apply Nat.le_antisymm
  · simpa only [quotient, if_pos hi] using
      (classMinimum_member_le (connected n store k i)
        (List.mem_range.mpr (quotient_in_scope hj)) iqj i)
  · simpa only [quotient, if_pos hj] using
      (classMinimum_member_le (connected n store k j)
        (List.mem_range.mpr (quotient_in_scope hi)) jqi j)

theorem quotient_idempotent (n : Nat) (store : Store) (k : Kind) (i : Nat) :
    quotient n store k (quotient n store k i) = quotient n store k i := by
  by_cases hi : i < n
  · exact (quotient_eq_of_connected hi (quotient_in_scope hi)
      (quotient_connected n store k i)).symm
  · simp [quotient, hi]

theorem quotient_canonical (n : Nat) (store : Store) :
    Generalization.Canonical n (quotient n store) :=
  ⟨fun _ _ hi => quotient_in_scope hi, fun k i _ => quotient_idempotent n store k i⟩

theorem quotient_eq_iff {n store k i j} (hi : i < n) (hj : j < n) :
    quotient n store k i = quotient n store k j ↔ connected n store k i j = true := by
  constructor
  · intro same
    have left := quotient_connected n store k i
    have right := connected_symm (quotient_connected n store k j)
    rw [← same] at right
    exact connected_trans (quotient_in_scope hi) left right
  · exact quotient_eq_of_connected hi hj

theorem edge_endpoint_bounds {n store k i j}
    (bounded : Generalization.StoreBounded n store) (h : edge store k i j = true) :
    i < n ∧ j < n := by
  rcases List.any_eq_true.mp h with ⟨c, member, found⟩
  have hc := bounded c member
  cases c with
  | mk kind lower upper =>
    cases lower <;> cases upper <;>
      simp_all [clauseEdge, Generalization.ConstraintBounded, Generalization.Bounded]

theorem reach_complete_in_scope {n store k i j}
    (bounded : Generalization.StoreBounded n store)
    (path : Reach (fun a b => edge store k a b = true) i j) :
    finiteReach (edge store k) (List.range n) i j = true := by
  induction path with
  | refl => exact BirthLevelSCC.finiteReach_refl _ _ _
  | cons h _ ih =>
    exact BirthLevelSCC.finiteReach_join _
      (List.mem_range.mpr (edge_endpoint_bounds bounded h).2)
      (BirthLevelSCC.finiteReach_edge _ h) ih

/-- For an allocated finite store this is the exact SCC, not a bounded-path
approximation. Boundedness concerns allocation only, never solution values. -/
theorem quotient_exact_scc {n store k i j}
    (bounded : Generalization.StoreBounded n store) (hi : i < n) (hj : j < n) :
    quotient n store k i = quotient n store k j ↔
      Reach (fun a b => edge store k a b = true) i j ∧
      Reach (fun a b => edge store k a b = true) j i := by
  rw [quotient_eq_iff hi hj]
  simp only [connected, Bool.and_eq_true]
  constructor
  · rintro ⟨left, right⟩
    exact ⟨BirthLevelSCC.finiteReach_sound _ left, BirthLevelSCC.finiteReach_sound _ right⟩
  · rintro ⟨left, right⟩
    exact ⟨reach_complete_in_scope bounded left, reach_complete_in_scope bounded right⟩

/-- Existing structural subtyping equivalence, with no new equality semantics. -/
def Equivalent {k} (a b : Term k) : Prop := Sub a b ∧ Sub b a

theorem Equivalent.refl {k} (t : Term k) : Equivalent t t := ⟨.refl _, .refl _⟩

theorem Equivalent.symm {k} {a b : Term k} (h : Equivalent a b) : Equivalent b a :=
  ⟨h.2, h.1⟩

theorem Equivalent.trans {k} {a b c : Term k} (ab : Equivalent a b)
    (bc : Equivalent b c) : Equivalent a c :=
  ⟨.trans ab.1 bc.1, .trans bc.2 ab.2⟩

/-- Both directions are essential at the contravariant Function ports. -/
theorem subst_equivalent (ρ σ : Valuation)
    (same : ∀ k i, Equivalent (ρ k i) (σ k i)) {k} (t : Term k) :
    Equivalent (t.subst ρ) (t.subst σ) := by
  induction t with
  | var i => exact same _ i
  | atom i => exact .refl _
  | bottom => exact .refl _
  | top => exact .refl _
  | union a b iha ihb =>
    exact ⟨.unionMono iha.1 ihb.1, .unionMono iha.2 ihb.2⟩
  | intersection a b iha ihb =>
    exact ⟨.intersectionMono iha.1 ihb.1, .intersectionMono iha.2 ihb.2⟩
  | function a ae re r iha ihae ihre ihr =>
    exact ⟨.function iha.2 ihae.2 ihre.1 ihr.1,
      .function iha.1 ihae.1 ihre.2 ihr.2⟩
  | recordNil => exact .refl _
  | recordCons label optional field tail ihf iht =>
    exact ⟨.recordCons label optional ihf.1 iht.1,
      .recordCons label optional ihf.2 iht.2⟩
  | tupleNil => exact .refl _
  | tupleCons head tail ihh iht => exact ⟨.tupleCons ihh.1 iht.1, .tupleCons ihh.2 iht.2⟩
  | variantNil => exact .refl _
  | variantCons tag payloads tail ihp iht =>
    exact ⟨.variantCons tag ihp.1 iht.1, .variantCons tag ihp.2 iht.2⟩

theorem clauseEdge_solution {store : Store} {ρ : Valuation} (solved : store.Satisfied ρ)
    {c : Constraint} (member : c ∈ store) {k i j}
    (h : clauseEdge k i j c = true) : Sub (ρ k i) (ρ k j) := by
  have hc := solved c member
  cases c with
  | mk kind lower upper =>
    cases lower <;> cases upper <;>
      simp only [clauseEdge, decide_eq_true_eq, Bool.false_eq_true] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    exact hc

theorem edge_solution {store : Store} {ρ : Valuation} (solved : store.Satisfied ρ)
    {k i j} (h : edge store k i j = true) : Sub (ρ k i) (ρ k j) := by
  rcases List.any_eq_true.mp h with ⟨c, member, found⟩
  exact clauseEdge_solution solved member found

theorem reach_solution {store : Store} {ρ : Valuation} (solved : store.Satisfied ρ)
    {k i j} (path : Reach (fun a b => edge store k a b = true) i j) :
    Sub (ρ k i) (ρ k j) := by
  induction path with
  | refl => exact .refl _
  | cons h _ ih => exact .trans (edge_solution solved h) ih

theorem connected_solution {n store k i j} {ρ : Valuation}
    (solved : store.Satisfied ρ) (h : connected n store k i j = true) :
    Equivalent (ρ k i) (ρ k j) := by
  simp only [connected, Bool.and_eq_true] at h
  exact ⟨reach_solution solved (BirthLevelSCC.finiteReach_sound _ h.1),
    reach_solution solved (BirthLevelSCC.finiteReach_sound _ h.2)⟩

/-- No bound on t: this includes ALL later client variables and constructors. -/
theorem all_term_factorization (n : Nat) (store : Store) (ρ : Valuation)
    (solved : store.Satisfied ρ) {k} (t : Term k) :
    Equivalent (t.subst ρ) ((t.rename (quotient n store)).subst ρ) := by
  rw [Term.rename_subst]
  exact subst_equivalent ρ _ (fun k i =>
    connected_solution solved (quotient_connected n store k i)) t

/-- Syntactically reflexive variables only; non-variable bounds always survive. -/
def trivialVariable (c : Constraint) : Bool :=
  match c.lower, c.upper with
  | .var i, .var j => decide (i = j)
  | _, _ => false

def normalize (n : Nat) (store : Store) : Store :=
  (store.map (Constraint.rename (quotient n store))).filter (fun c => !trivialVariable c)

theorem trivialVariable_solution (ρ : Valuation) (c : Constraint)
    (h : trivialVariable c = true) : c.Satisfied ρ := by
  cases c with
  | mk k lower upper =>
    cases lower <;> cases upper <;>
      simp_all [trivialVariable, Constraint.Satisfied, Term.subst, Sub.refl]

theorem filter_solution (store : Store) (ρ : Valuation) :
    Store.Satisfied ρ (store.filter (fun c => !trivialVariable c)) ↔
      store.Satisfied ρ := by
  constructor
  · intro h c hc
    by_cases ht : trivialVariable c = true
    · exact trivialVariable_solution ρ c ht
    · exact h c (List.mem_filter.mpr ⟨hc, by simp [ht]⟩)
  · intro h c hc
    exact h c (List.mem_filter.mp hc).1

theorem normalized_solution_iff (n : Nat) (store : Store) (ρ : Valuation) :
    (normalize n store).Satisfied ρ ↔
      store.Satisfied (fun k i => ρ k (quotient n store k i)) := by
  rw [normalize, filter_solution, Store.quotient_pullback]

/-- Constructive pullback, one valuation shared by the complete store. -/
theorem solution_pullback (n : Nat) (store : Store) (ρ : Valuation)
    (solved : (normalize n store).Satisfied ρ) :
    store.Satisfied (fun k i => ρ k (quotient n store k i)) :=
  (normalized_solution_iff n store ρ).mp solved

/-- The original valuation itself works on the normalized class coordinates. -/
theorem solution_pushforward (n : Nat) (store : Store) (ρ : Valuation)
    (solved : store.Satisfied ρ) : (normalize n store).Satisfied ρ := by
  apply (normalized_solution_iff n store ρ).mpr
  intro c hc
  have lower := all_term_factorization n store ρ solved c.lower
  have upper := all_term_factorization n store ρ solved c.upper
  have old := solved c hc
  simpa only [Constraint.Satisfied, Term.rename_subst] using
    (Sub.trans lower.2 (Sub.trans old upper.1))

theorem solutions_and_all_terms (n : Nat) (store : Store) (ρ : Valuation)
    (solved : store.Satisfied ρ) :
    ∃ σ : Valuation, (normalize n store).Satisfied σ ∧
      ∀ k (t : Term k), Equivalent (t.subst ρ)
        ((t.rename (quotient n store)).subst σ) :=
  ⟨ρ, solution_pushforward n store ρ solved, fun _ t =>
    all_term_factorization n store ρ solved t⟩

theorem retained_clause {n store} {c : Constraint} (member : c ∈ store)
    (nontrivial : trivialVariable (c.rename (quotient n store)) = false) :
    c.rename (quotient n store) ∈ normalize n store := by
  exact List.mem_filter.mpr ⟨List.mem_map.mpr ⟨c, member, rfl⟩, by simp [nontrivial]⟩

/-- Later substitution acts on class VALUES, including non-variable values. -/
theorem quotient_substitution (n : Nat) (store : Store) (σ τ : Valuation)
    {k} (t : Term k) :
    ((t.rename (quotient n store)).subst σ).subst τ =
      (t.rename (quotient n store)).subst (fun k i => (σ k i).subst τ) :=
  Term.subst_comp σ τ _

theorem factorization_after_substitution (n : Nat) (store : Store) (ρ τ : Valuation)
    (solved : store.Satisfied ρ) {k} (t : Term k) :
    Equivalent ((t.subst ρ).subst τ)
      (((t.rename (quotient n store)).subst ρ).subst τ) := by
  have h := all_term_factorization n store ρ solved t
  exact ⟨h.1.subst τ, h.2.subst τ⟩

/-! Actual physical-row extraction. It does not read just representative rows.
`resolvedBounds` is explicit; no equality with `retainedConstraints` is claimed.
Missing representative entries remain the same name. A future accepted-state
bridge must validate representative lookup and level/metadata coherence. -/
open AbstractCore

def rowClauses {k : Kind} (owner : Nat) (row : CoreRow k) : Store :=
  row.lowerBounds.map (fun t => ⟨k, t, .var owner⟩) ++
    row.upperBounds.map (fun t => ⟨k, .var owner, t⟩)

def physicalRows {k : Kind} (rows : List (CoreRow k)) : Store :=
  (rows.zipIdx).flatMap (fun pair => rowClauses pair.2 pair.1)

def physicalBounds (state : CoreState) : Store :=
  physicalRows state.valueRows ++ physicalRows state.effectRows

def resolve (state : CoreState) : Renaming :=
  fun k i => ((state.representatives k)[i]?).getD i

def resolvedBounds (state : CoreState) : Store :=
  (physicalBounds state).map (Constraint.rename (resolve state))

def scopeSize (state : CoreState) : Nat := max state.valueRows.length state.effectRows.length

def stateQuotient (state : CoreState) : Renaming :=
  quotient (scopeSize state) (resolvedBounds state)

/-- Actual physical membership includes the preexisting representative map.
The bound SCC map and this composite are deliberately distinct interfaces. -/
def physicalClass (state : CoreState) : Renaming :=
  fun k i => stateQuotient state k (resolve state k i)

def normalizedBounds (state : CoreState) : Store :=
  normalize (scopeSize state) (resolvedBounds state)

/-- All physical member rows contribute their lower AND upper bound clauses. -/
theorem physical_row_retained {k} {rows : List (CoreRow k)} {row : CoreRow k}
    {i : Nat} (member : (row, i) ∈ rows.zipIdx) {c : Constraint}
    (bound : c ∈ rowClauses i row) : c ∈ physicalRows rows :=
  List.mem_flatMap.mpr ⟨(row, i), member, bound⟩

def stateLevels (state : CoreState) : Generalization.Levels :=
  fun k i => (((state.rows k)[i]?).map CoreRow.level).getD 0

/-- Class level is the minimum of all actual allocated physical members. -/
def classLevels (state : CoreState) : Generalization.Levels :=
  Generalization.quotientLevels (scopeSize state) (stateLevels state) (physicalClass state)

theorem actual_class_level_le (state : CoreState) (k : Kind) (i : Nat)
    (hi : i < scopeSize state) :
    classLevels state k (physicalClass state k i) ≤ stateLevels state k i :=
  Generalization.quotientLevels_le hi

/-- The exact fiber minimum statement names its scope and fixed-point premises.
They are not alleged invariants of arbitrary R212 storage records. -/
theorem actual_class_minimum_at_fixed (state : CoreState) (k : Kind) (r : Nat)
    (inScope : r < scopeSize state) (fixed : physicalClass state k r = r) :
    Generalization.FiberMinimum (scopeSize state) (stateLevels state)
      (physicalClass state) k r (classLevels state k r) :=
  Generalization.quotientLevels_is_minimum inScope fixed

theorem actual_anchor_preserved (state : CoreState) (boundary : Nat) :
    Generalization.PreservesAnchors (scopeSize state) boundary (stateLevels state)
      (classLevels state) (physicalClass state) :=
  Generalization.quotientLevels_preserve_anchors _ _ _ _

/-- One common post-quotient valuation transports every separately freshened
use. This equation itself needs no store solution or accepted-run assumption.
The original term is allocated; arbitrary future terms are covered above. -/
theorem actual_fresh_use_transport (state : CoreState) (boundary count use : Nat)
    (hu : use < count) {k} {t : Term k}
    (bounded : Generalization.Bounded (scopeSize state) t) (ρ : Valuation) :
    (t.rename (Generalization.freshen (scopeSize state) boundary (stateLevels state) use)).subst
      (fun k i => ρ k (Generalization.transport (scopeSize state) count boundary
        (classLevels state) (physicalClass state) k i)) =
    ((t.rename (physicalClass state)).rename
      (Generalization.freshen (scopeSize state) boundary (classLevels state) use)).subst ρ :=
  Generalization.fresh_term_pullback (actual_anchor_preserved state boundary) hu bounded ρ

/-! Exact R212 one-step self-upper output, not a complete accepted run. -/
def selfUpperProblem : CoreProblem where
  demands := [⟨⟨.value, .var 0, .var 0⟩, 0, 0⟩]
  valueGraph := ⟨[0], []⟩
  valueLevels := [0]
  effectLevels := []
  publications := []
  uses := []

def selfUpperState : CoreState :=
  { selfUpperProblem.initial with
    pending := []
    valueRows := [⟨0, false, [], [.var 0]⟩] }

theorem self_upper_actual :
    selfUpperProblem.inputValid = true ∧
    selfUpperProblem.initial.insertPendingUpper = some selfUpperState := by
  exact ⟨rfl, rfl⟩

theorem self_upper_quotient_free :
    stateQuotient selfUpperState .value 0 = 0 ∧
    (Term.var 0 : Term .value).rename (stateQuotient selfUpperState) = .var 0 ∧
    normalizedBounds selfUpperState = [] := by
  exact ⟨rfl, rfl, rfl⟩

theorem self_upper_all_terms (ρ : Valuation) {k} (t : Term k) :
    Equivalent (t.subst ρ) ((t.rename (stateQuotient selfUpperState)).subst ρ) := by
  apply all_term_factorization
  intro c hc
  have same : c = ⟨.value, .var 0, .var 0⟩ := by
    simpa [resolvedBounds, physicalBounds, physicalRows, rowClauses,
      selfUpperState, selfUpperProblem, CoreProblem.initial, CoreRow.initial,
      resolve, CoreState.representatives, Constraint.rename, Term.rename, Term.subst] using hc
  subst c
  exact .refl _

/-- Actual R212 upper-only bound survives as a constraint on a free variable. -/
def upperOnlyState : CoreState :=
  { AbstractCore.upperOnlyProblem.initial with
    pending := []
    valueRows := [⟨0, false, [], [.atom 0]⟩] }

theorem upper_only_actual_and_preserved :
    AbstractCore.upperOnlyAfter = some upperOnlyState ∧
    normalizedBounds upperOnlyState = [⟨.value, .var 0, .atom 0⟩] := by
  exact ⟨rfl, rfl⟩

def twoCycleState : CoreState :=
  { selfUpperProblem.initial with
    pending := []
    valueRows := [⟨0, false, [], [.var 1]⟩, ⟨0, false, [], [.var 0, .atom 7]⟩]
    valueRepresentatives := [0, 1] }

theorem two_cycle_free_external_preserved :
    stateQuotient twoCycleState .value 0 = 0 ∧
    stateQuotient twoCycleState .value 1 = 0 ∧
    normalizedBounds twoCycleState = [⟨.value, .var 0, .atom 7⟩] := by
  exact ⟨rfl, rfl, rfl⟩

def duplicateRepresentativeState : CoreState :=
  { twoCycleState with
    valueRows := [⟨1, false, [], [.atom 9]⟩, ⟨0, false, [], [.atom 7]⟩]
    valueRepresentatives := [0, 0] }

theorem duplicate_physical_bounds_and_levels :
    normalizedBounds duplicateRepresentativeState =
      [⟨.value, .var 0, .atom 9⟩, ⟨.value, .var 0, .atom 7⟩] ∧
    physicalClass duplicateRepresentativeState .value 0 = 0 ∧
    physicalClass duplicateRepresentativeState .value 1 = 0 ∧
    classLevels duplicateRepresentativeState .value 0 = 0 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

def recursivePorts : Term .value := .function (.var 0) (.var 0) (.var 1) (.var 1)

def mixedKindState : CoreState :=
  { twoCycleState with
    valueRows := [⟨0, false, [], [.var 1, recursivePorts]⟩,
      ⟨0, false, [], [.var 0]⟩]
    effectRows := [⟨0, false, [], [.var 0]⟩, ⟨0, false, [], [.atom 8]⟩]
    effectRepresentatives := [0, 1] }

theorem recursive_function_all_ports_and_kinds :
    recursivePorts.rename (stateQuotient mixedKindState) =
      .function (.var 0) (.var 0) (.var 1) (.var 0) ∧
    normalizedBounds mixedKindState =
      [⟨.value, .var 0, .function (.var 0) (.var 0) (.var 1) (.var 0)⟩,
       ⟨.effect, .var 1, .atom 8⟩] := by
  exact ⟨rfl, rfl⟩

/-- Deliberately mixed actual row levels. This is a data discriminator, not
claimed reachable via same-level insertion. The class minimum captures both. -/
def mixedLevelState : CoreState :=
  { twoCycleState with
    valueRows := [⟨0, false, [], [.var 1]⟩, ⟨1, false, [], [.var 0]⟩] }

theorem mixed_level_shared_anchor :
    stateLevels mixedLevelState .value 0 = 0 ∧
    stateLevels mixedLevelState .value 1 = 1 ∧
    stateQuotient mixedLevelState .value 1 = 0 ∧
    classLevels mixedLevelState .value 0 = 0 ∧
    Generalization.freshen 2 0 (stateLevels mixedLevelState) 0 .value 1 = 3 ∧
    Generalization.freshen 2 0 (stateLevels mixedLevelState) 1 .value 1 = 5 ∧
    Generalization.transport 2 2 0 (classLevels mixedLevelState)
      (physicalClass mixedLevelState) .value 3 = 0 ∧
    Generalization.transport 2 2 0 (classLevels mixedLevelState)
      (physicalClass mixedLevelState) .value 5 = 0 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def mixedUseStore : Store :=
  Generalization.usesStore 2 0 (stateLevels mixedLevelState) [0, 1]
    (resolvedBounds mixedLevelState)

theorem mixed_use_store_exact : mixedUseStore =
    [⟨.value, .var 0, .var 1⟩, ⟨.value, .var 1, .var 0⟩,
     ⟨.value, .var 0, .var 3⟩, ⟨.value, .var 3, .var 0⟩,
     ⟨.value, .var 0, .var 5⟩, ⟨.value, .var 5, .var 0⟩] := rfl

theorem mixed_before_value (use i : Nat) :
    Generalization.freshen 2 0 (stateLevels mixedLevelState) use .value i =
      if i = 1 then Generalization.copyIndex 2 use 1 else i := by
  cases i with
  | zero => rfl
  | succ i => cases i <;> rfl

theorem mixed_before_effect (use i : Nat) :
    Generalization.freshen 2 0 (stateLevels mixedLevelState) use .effect i = i := rfl

theorem mixed_physical_value (i : Nat) :
    physicalClass mixedLevelState .value i = if i = 1 then 0 else i := by
  cases i with
  | zero => rfl
  | succ i => cases i <;> rfl

theorem mixed_physical_effect (i : Nat) :
    physicalClass mixedLevelState .effect i = i := by
  cases i with
  | zero => rfl
  | succ i => cases i <;> rfl

theorem mixed_after_fixed (use : Nat) (k : Kind) (i : Nat) :
    Generalization.freshen 2 0 (classLevels mixedLevelState) use k
      (physicalClass mixedLevelState k i) = physicalClass mixedLevelState k i := by
  cases k <;> cases i with
  | zero => rfl
  | succ i => cases i <;> rfl

/-- Reverse factorization on the mandatory mixed-level discriminator, for
both independent uses and every later Term under ONE valuation. Neither use
is assigned a new independent anchor. This is not the general reverse-use
theorem for arbitrary stores/publications. -/
theorem mixed_level_two_use_factorization (ρ : Valuation)
    (solved : mixedUseStore.Satisfied ρ) (use : Nat) (hu : use ∈ [0, 1])
    {k} (t : Term k) :
    Equivalent
      ((t.rename (Generalization.freshen 2 0 (stateLevels mixedLevelState) use)).subst ρ)
      (((t.rename (physicalClass mixedLevelState)).rename
        (Generalization.freshen 2 0 (classLevels mixedLevelState) use)).subst ρ) := by
  have copy : Equivalent (ρ .value (Generalization.copyIndex 2 use 1)) (ρ .value 0) := by
    have solved' := solved
    rw [mixed_use_store_exact] at solved'
    have casesUse : use = 0 ∨ use = 1 := by simpa using hu
    rcases casesUse with rfl | rfl
    · exact ⟨solved' ⟨.value, .var 3, .var 0⟩ (by simp),
        solved' ⟨.value, .var 0, .var 3⟩ (by simp)⟩
    · exact ⟨solved' ⟨.value, .var 5, .var 0⟩ (by simp),
        solved' ⟨.value, .var 0, .var 5⟩ (by simp)⟩
  simp only [Term.rename_subst]
  apply subst_equivalent
  intro kind i
  rw [mixed_after_fixed]
  cases kind with
  | value =>
    rw [mixed_before_value, mixed_physical_value]
    by_cases hi : i = 1
    · subst i
      change Equivalent (ρ .value (Generalization.copyIndex 2 use 1)) (ρ .value 0)
      exact copy
    · simp only [hi, ite_false]
      exact Equivalent.refl _
  | effect =>
    rw [mixed_before_effect, mixed_physical_effect]
    exact Equivalent.refl _

/-! The actual owner-local publication relation is DIFFERENT from usesStore.
The following is a counterexample to unconditional reverse factorization in
that relation. It is not source-qualified: its low-to-high bound violates
BoundLevelsClosed. No complete accepted run is asserted.

The witness uses rigid atoms as rigid atoms, and a union as the captured value;
it does not interpret atoms as substitution parameters or select an extremum
for a free class. The first missing native premise is level/bound closure at
the publication cut, together with actual representative/capture coherence.
-/

def lowToHigh : ScopedPublication.Bound := ⟨.value, 0, .negative, .var 1⟩
def highToLow : ScopedPublication.Bound := ⟨.value, 1, .negative, .var 0⟩
def mixedBounds : List ScopedPublication.Bound := [lowToHigh, highToLow]

def mixedCapture : ScopedPublication.Flags :=
  ScopedPublication.captureGuard 0 ⟨stateLevels mixedLevelState, fun _ _ => false⟩

def mixedAfterCapture : ScopedPublication.Flags :=
  ScopedPublication.captureGuard 0 ⟨classLevels mixedLevelState, fun _ _ => false⟩

def separatedUses : Valuation
  | .value, 0 => .union (.atom 0) (.atom 1)
  | .value, 1 => .union (.atom 0) (.atom 1)
  | .value, 3 => .atom 0
  | .value, 5 => .atom 1
  | .value, i => .var i
  | .effect, i => .var i

/-- A two-element Boolean observation refutes the required reverse Sub.
Structural constructors have constant observation, so this is a sound model
of every constructor of the EXISTING Sub, not a new subtype relation. -/
def observesOne {k} : Term k → Bool
  | .var _ => false
  | .atom i => decide (i = 1)
  | .bottom => false
  | .top => true
  | .union a b => observesOne a || observesOne b
  | .intersection a b => observesOne a && observesOne b
  | .function _ _ _ _ | .recordNil | .recordCons _ _ _ _ |
      .tupleNil | .tupleCons _ _ | .variantNil | .variantCons _ _ _ => false

theorem sub_observation {k} {a b : Term k} (h : Sub a b) :
    observesOne a = true → observesOne b = true := by
  induction h with
  | refl _ => exact fun h => h
  | trans _ _ ih₁ ih₂ => exact fun h => ih₂ (ih₁ h)
  | bottom _ => intro h; cases h
  | top _ => exact fun _ => rfl
  | unionLeft a b => intro h; simp [observesOne, h]
  | unionRight a b => intro h; simp [observesOne, h]
  | unionElim _ _ ih₁ ih₂ =>
    intro h
    simp only [observesOne, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ih₁ h
    · exact ih₂ h
  | intersectionLeft a b =>
    intro h
    simp only [observesOne, Bool.and_eq_true] at h
    exact h.1
  | intersectionRight a b =>
    intro h
    simp only [observesOne, Bool.and_eq_true] at h
    exact h.2
  | intersectionIntro _ _ ih₁ ih₂ =>
    intro h
    simp only [observesOne, Bool.and_eq_true]
    exact ⟨ih₁ h, ih₂ h⟩
  | unionMono _ _ ih₁ ih₂ =>
    intro h
    simp only [observesOne, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl (ih₁ h)
    · exact Or.inr (ih₂ h)
  | intersectionMono _ _ ih₁ ih₂ =>
    intro h
    simp only [observesOne, Bool.and_eq_true] at h ⊢
    exact ⟨ih₁ h.1, ih₂ h.2⟩
  | function _ _ _ _ _ _ _ _ => exact fun h => h
  | recordCons _ _ _ _ _ _ => exact fun h => h
  | tupleCons _ _ _ _ => exact fun h => h
  | variantCons _ _ _ _ _ => exact fun h => h

theorem union_not_left_atom :
    ¬ Sub (Term.union (.atom 0) (.atom 1) : Term .value) (.atom 0) := by
  intro h
  have impossible := sub_observation h (by rfl)
  cases impossible

theorem stopped_publication_separated_satisfies :
    ScopedPublication.Satisfied 2 mixedBounds mixedCapture mixedCapture
      [⟨.value, 1⟩] [0, 1] separatedUses := by
  intro c published
  cases published with
  | base b member =>
    have which : b = lowToHigh ∨ b = highToLow := by simpa [mixedBounds] using member
    rcases which with rfl | rfl
    · exact .refl _
    · exact .refl _
  | copy b member use hu _ active =>
    have which : b = lowToHigh ∨ b = highToLow := by simpa [mixedBounds] using member
    rcases which with rfl | rfl
    · have impossible : false = true := active
      cases impossible
    · have whichUse : use = 0 ∨ use = 1 := by simpa using hu
      rcases whichUse with rfl | rfl
      · exact .unionLeft (.atom 0) (.atom 1)
      · exact .unionRight (.atom 0) (.atom 1)

theorem mixed_bound_levels_not_closed :
    ¬ ScopedPublication.BoundLevelsClosed mixedBounds (stateLevels mixedLevelState) := by
  intro closed
  have bad := closed lowToHigh (by simp [mixedBounds]) ⟨.value, 1⟩
    (by simp [lowToHigh, ScopedPublication.vars])
  change 1 ≤ 0 at bad
  omega

/-- Even a SINGLE use cannot simultaneously factor its high copy and the
original captured anchor. The two-use fixture contains this minimal failure. -/
theorem stopped_publication_no_joint_factorization :
    ¬ ∃ σ : Valuation, ∀ use, use ∈ ([0, 1] : List Nat) → ∀ k (t : Term k),
      Equivalent
        ((t.rename (ScopedPublication.fresh 2 mixedCapture use)).subst separatedUses)
        (((t.rename (physicalClass mixedLevelState)).rename
          (ScopedPublication.fresh 2 mixedAfterCapture use)).subst σ) := by
  rintro ⟨σ, factor⟩
  have anchor := factor 0 (by simp) .value (.var 0)
  have copy := factor 0 (by simp) .value (.var 1)
  change Equivalent (.union (.atom 0) (.atom 1)) (σ .value 0) at anchor
  change Equivalent (.atom 0) (σ .value 0) at copy
  exact union_not_left_atom (.trans anchor.1 copy.2)

/-! A bound-closed mixed-level fixture stores BOTH directions at the high
owner. Its extracted constraints, quotient and levels agree with the previous
fixture, but actual owner-local publication now copies both directions.
This makes the lost ownership premise observable rather than excluding mixed
levels. This is still a CoreState data fixture, not an accepted solver run. -/
def closedMixedLevelState : CoreState :=
  { mixedLevelState with
    valueRows := [⟨0, false, [], []⟩, ⟨1, false, [.var 0], [.var 0]⟩] }

def highFromLow : ScopedPublication.Bound := ⟨.value, 1, .positive, .var 0⟩
def closedMixedBounds : List ScopedPublication.Bound := [highFromLow, highToLow]

theorem closed_mixed_same_constraints_and_levels :
    resolvedBounds closedMixedLevelState = resolvedBounds mixedLevelState ∧
    (Term.var 1 : Term .value).rename (physicalClass closedMixedLevelState) = .var 0 ∧
    classLevels closedMixedLevelState .value 0 = 0 :=
  ⟨rfl, rfl, rfl⟩

theorem closed_mixed_bound_levels :
    ScopedPublication.BoundLevelsClosed closedMixedBounds (stateLevels closedMixedLevelState) := by
  intro b hb r hr
  have which : b = highFromLow ∨ b = highToLow := by simpa [closedMixedBounds] using hb
  rcases which with rfl | rfl
  · have same : r = ⟨.value, 0⟩ := by
      simpa [highFromLow, ScopedPublication.vars] using hr
    subst r
    exact Nat.zero_le _
  · have same : r = ⟨.value, 0⟩ := by
      simpa [highToLow, ScopedPublication.vars] using hr
    subst r
    exact Nat.zero_le _

theorem fresh_capture_without_nonGeneric (n boundary use : Nat)
    (levels : Generalization.Levels) :
    ScopedPublication.fresh n
      (ScopedPublication.captureGuard boundary ⟨levels, fun _ _ => false⟩) use =
      Generalization.freshen n boundary levels use := by
  funext k i
  by_cases low : levels k i ≤ boundary
  · simp [ScopedPublication.fresh, ScopedPublication.guardLevels,
      ScopedPublication.captureGuard, Generalization.freshen, low, Nat.not_lt.mpr low]
  · have high := Nat.lt_of_not_ge low
    simp [ScopedPublication.fresh, ScopedPublication.guardLevels,
      ScopedPublication.captureGuard, Generalization.freshen, low, high]

/-- In this bound-closed fixture the actual published clauses provide exactly
the full-store discriminator's premises. No full-store copying is assumed. -/
theorem closed_publication_supplies_mixed_store (ρ : Valuation)
    (solved : ScopedPublication.Satisfied 2 closedMixedBounds mixedCapture mixedCapture
      [⟨.value, 1⟩] [0, 1] ρ) : mixedUseStore.Satisfied ρ := by
  have lower (use : Nat) (hu : use ∈ ([0, 1] : List Nat)) :=
    ScopedPublication.Published.copy (n := 2) (bounds := closedMixedBounds)
      (captured := mixedCapture) (allocation := mixedCapture)
      (roots := [⟨.value, 1⟩]) (uses := [0, 1])
      highFromLow (by simp [closedMixedBounds]) use hu
      (.root _ (by simp [highFromLow, ScopedPublication.Bound.row])) (by rfl)
  have upper (use : Nat) (hu : use ∈ ([0, 1] : List Nat)) :=
    ScopedPublication.Published.copy (n := 2) (bounds := closedMixedBounds)
      (captured := mixedCapture) (allocation := mixedCapture)
      (roots := [⟨.value, 1⟩]) (uses := [0, 1])
      highToLow (by simp [closedMixedBounds]) use hu
      (.root _ (by simp [highToLow, ScopedPublication.Bound.row])) (by rfl)
  intro c hc
  rw [mixed_use_store_exact] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact solved _ (.base highFromLow (by simp [closedMixedBounds]))
  · exact solved _ (.base highToLow (by simp [closedMixedBounds]))
  · exact solved _ (lower 0 (by simp))
  · exact solved _ (upper 0 (by simp))
  · exact solved _ (lower 1 (by simp))
  · exact solved _ (upper 1 (by simp))

/-- Both independent uses factor with their shared captured anchor, for every
Term, from the actual owner-local Published relation of the closed fixture. -/
theorem closed_publication_joint_factorization (ρ : Valuation)
    (solved : ScopedPublication.Satisfied 2 closedMixedBounds mixedCapture mixedCapture
      [⟨.value, 1⟩] [0, 1] ρ) (use : Nat) (hu : use ∈ ([0, 1] : List Nat))
    {k} (t : Term k) :
    Equivalent
      ((t.rename (ScopedPublication.fresh 2 mixedCapture use)).subst ρ)
      (((t.rename (physicalClass mixedLevelState)).rename
        (ScopedPublication.fresh 2 mixedAfterCapture use)).subst ρ) := by
  simpa only [mixedCapture, mixedAfterCapture, fresh_capture_without_nonGeneric] using
    (mixed_level_two_use_factorization ρ (closed_publication_supplies_mixed_store ρ solved)
      use hu t)

/-! Remaining obligations, deliberately not hidden inside an acceptance def:
1. Independently check this constructed module and every theorem's axioms.
2. Establish exact original-store / physical-row / representative coherence
   on real solver histories, with nonGeneric and captured-publication metadata.
3. Reverse owner-local publication factorization under one captured valuation:
   the explicit stopped-owner counterexample above blocks an unconditional
   theorem. `mixed_level_two_use_factorization` applies to FULL-store copying
   only. It cannot be relabeled actual owner-local publication. The missing
   native/source premise is level/bound closure and actual capture coherence.
4. Relate this structural all-term factorization to Fig.12 recursive syntax,
   guarded graph decoding, `sameScoped`, and the original `instanceOf`.
No original Contracts.SourceProblem root is closed by this file.
-/

end YulangClosure.SimpleSub.BoundCycleR223

/-! Complete authored-theorem audit surface. NOT_RUN by the proof leaf. -/

#check @YulangClosure.SimpleSub.BoundCycleR223.connected_refl
#print axioms YulangClosure.SimpleSub.BoundCycleR223.connected_refl

#check @YulangClosure.SimpleSub.BoundCycleR223.connected_symm
#print axioms YulangClosure.SimpleSub.BoundCycleR223.connected_symm

#check @YulangClosure.SimpleSub.BoundCycleR223.connected_trans
#print axioms YulangClosure.SimpleSub.BoundCycleR223.connected_trans

#check @YulangClosure.SimpleSub.BoundCycleR223.classMinimum_le
#print axioms YulangClosure.SimpleSub.BoundCycleR223.classMinimum_le

#check @YulangClosure.SimpleSub.BoundCycleR223.classMinimum_member_le
#print axioms YulangClosure.SimpleSub.BoundCycleR223.classMinimum_member_le

#check @YulangClosure.SimpleSub.BoundCycleR223.classMinimum_selected
#print axioms YulangClosure.SimpleSub.BoundCycleR223.classMinimum_selected

#check @YulangClosure.SimpleSub.BoundCycleR223.quotient_future
#print axioms YulangClosure.SimpleSub.BoundCycleR223.quotient_future

#check @YulangClosure.SimpleSub.BoundCycleR223.quotient_le
#print axioms YulangClosure.SimpleSub.BoundCycleR223.quotient_le

#check @YulangClosure.SimpleSub.BoundCycleR223.quotient_in_scope
#print axioms YulangClosure.SimpleSub.BoundCycleR223.quotient_in_scope

#check @YulangClosure.SimpleSub.BoundCycleR223.quotient_connected
#print axioms YulangClosure.SimpleSub.BoundCycleR223.quotient_connected

#check @YulangClosure.SimpleSub.BoundCycleR223.quotient_eq_of_connected
#print axioms YulangClosure.SimpleSub.BoundCycleR223.quotient_eq_of_connected

#check @YulangClosure.SimpleSub.BoundCycleR223.quotient_idempotent
#print axioms YulangClosure.SimpleSub.BoundCycleR223.quotient_idempotent

#check @YulangClosure.SimpleSub.BoundCycleR223.quotient_canonical
#print axioms YulangClosure.SimpleSub.BoundCycleR223.quotient_canonical

#check @YulangClosure.SimpleSub.BoundCycleR223.quotient_eq_iff
#print axioms YulangClosure.SimpleSub.BoundCycleR223.quotient_eq_iff

#check @YulangClosure.SimpleSub.BoundCycleR223.edge_endpoint_bounds
#print axioms YulangClosure.SimpleSub.BoundCycleR223.edge_endpoint_bounds

#check @YulangClosure.SimpleSub.BoundCycleR223.reach_complete_in_scope
#print axioms YulangClosure.SimpleSub.BoundCycleR223.reach_complete_in_scope

#check @YulangClosure.SimpleSub.BoundCycleR223.quotient_exact_scc
#print axioms YulangClosure.SimpleSub.BoundCycleR223.quotient_exact_scc

#check @YulangClosure.SimpleSub.BoundCycleR223.Equivalent.refl
#print axioms YulangClosure.SimpleSub.BoundCycleR223.Equivalent.refl

#check @YulangClosure.SimpleSub.BoundCycleR223.Equivalent.symm
#print axioms YulangClosure.SimpleSub.BoundCycleR223.Equivalent.symm

#check @YulangClosure.SimpleSub.BoundCycleR223.Equivalent.trans
#print axioms YulangClosure.SimpleSub.BoundCycleR223.Equivalent.trans

#check @YulangClosure.SimpleSub.BoundCycleR223.subst_equivalent
#print axioms YulangClosure.SimpleSub.BoundCycleR223.subst_equivalent

#check @YulangClosure.SimpleSub.BoundCycleR223.clauseEdge_solution
#print axioms YulangClosure.SimpleSub.BoundCycleR223.clauseEdge_solution

#check @YulangClosure.SimpleSub.BoundCycleR223.edge_solution
#print axioms YulangClosure.SimpleSub.BoundCycleR223.edge_solution

#check @YulangClosure.SimpleSub.BoundCycleR223.reach_solution
#print axioms YulangClosure.SimpleSub.BoundCycleR223.reach_solution

#check @YulangClosure.SimpleSub.BoundCycleR223.connected_solution
#print axioms YulangClosure.SimpleSub.BoundCycleR223.connected_solution

#check @YulangClosure.SimpleSub.BoundCycleR223.all_term_factorization
#print axioms YulangClosure.SimpleSub.BoundCycleR223.all_term_factorization

#check @YulangClosure.SimpleSub.BoundCycleR223.trivialVariable_solution
#print axioms YulangClosure.SimpleSub.BoundCycleR223.trivialVariable_solution

#check @YulangClosure.SimpleSub.BoundCycleR223.filter_solution
#print axioms YulangClosure.SimpleSub.BoundCycleR223.filter_solution

#check @YulangClosure.SimpleSub.BoundCycleR223.normalized_solution_iff
#print axioms YulangClosure.SimpleSub.BoundCycleR223.normalized_solution_iff

#check @YulangClosure.SimpleSub.BoundCycleR223.solution_pullback
#print axioms YulangClosure.SimpleSub.BoundCycleR223.solution_pullback

#check @YulangClosure.SimpleSub.BoundCycleR223.solution_pushforward
#print axioms YulangClosure.SimpleSub.BoundCycleR223.solution_pushforward

#check @YulangClosure.SimpleSub.BoundCycleR223.solutions_and_all_terms
#print axioms YulangClosure.SimpleSub.BoundCycleR223.solutions_and_all_terms

#check @YulangClosure.SimpleSub.BoundCycleR223.retained_clause
#print axioms YulangClosure.SimpleSub.BoundCycleR223.retained_clause

#check @YulangClosure.SimpleSub.BoundCycleR223.quotient_substitution
#print axioms YulangClosure.SimpleSub.BoundCycleR223.quotient_substitution

#check @YulangClosure.SimpleSub.BoundCycleR223.factorization_after_substitution
#print axioms YulangClosure.SimpleSub.BoundCycleR223.factorization_after_substitution

#check @YulangClosure.SimpleSub.BoundCycleR223.physical_row_retained
#print axioms YulangClosure.SimpleSub.BoundCycleR223.physical_row_retained

#check @YulangClosure.SimpleSub.BoundCycleR223.actual_class_level_le
#print axioms YulangClosure.SimpleSub.BoundCycleR223.actual_class_level_le

#check @YulangClosure.SimpleSub.BoundCycleR223.actual_class_minimum_at_fixed
#print axioms YulangClosure.SimpleSub.BoundCycleR223.actual_class_minimum_at_fixed

#check @YulangClosure.SimpleSub.BoundCycleR223.actual_anchor_preserved
#print axioms YulangClosure.SimpleSub.BoundCycleR223.actual_anchor_preserved

#check @YulangClosure.SimpleSub.BoundCycleR223.actual_fresh_use_transport
#print axioms YulangClosure.SimpleSub.BoundCycleR223.actual_fresh_use_transport

#check @YulangClosure.SimpleSub.BoundCycleR223.self_upper_actual
#print axioms YulangClosure.SimpleSub.BoundCycleR223.self_upper_actual

#check @YulangClosure.SimpleSub.BoundCycleR223.self_upper_quotient_free
#print axioms YulangClosure.SimpleSub.BoundCycleR223.self_upper_quotient_free

#check @YulangClosure.SimpleSub.BoundCycleR223.self_upper_all_terms
#print axioms YulangClosure.SimpleSub.BoundCycleR223.self_upper_all_terms

#check @YulangClosure.SimpleSub.BoundCycleR223.upper_only_actual_and_preserved
#print axioms YulangClosure.SimpleSub.BoundCycleR223.upper_only_actual_and_preserved

#check @YulangClosure.SimpleSub.BoundCycleR223.two_cycle_free_external_preserved
#print axioms YulangClosure.SimpleSub.BoundCycleR223.two_cycle_free_external_preserved

#check @YulangClosure.SimpleSub.BoundCycleR223.duplicate_physical_bounds_and_levels
#print axioms YulangClosure.SimpleSub.BoundCycleR223.duplicate_physical_bounds_and_levels

#check @YulangClosure.SimpleSub.BoundCycleR223.recursive_function_all_ports_and_kinds
#print axioms YulangClosure.SimpleSub.BoundCycleR223.recursive_function_all_ports_and_kinds

#check @YulangClosure.SimpleSub.BoundCycleR223.mixed_level_shared_anchor
#print axioms YulangClosure.SimpleSub.BoundCycleR223.mixed_level_shared_anchor

#check @YulangClosure.SimpleSub.BoundCycleR223.mixed_use_store_exact
#print axioms YulangClosure.SimpleSub.BoundCycleR223.mixed_use_store_exact

#check @YulangClosure.SimpleSub.BoundCycleR223.mixed_before_value
#print axioms YulangClosure.SimpleSub.BoundCycleR223.mixed_before_value

#check @YulangClosure.SimpleSub.BoundCycleR223.mixed_before_effect
#print axioms YulangClosure.SimpleSub.BoundCycleR223.mixed_before_effect

#check @YulangClosure.SimpleSub.BoundCycleR223.mixed_physical_value
#print axioms YulangClosure.SimpleSub.BoundCycleR223.mixed_physical_value

#check @YulangClosure.SimpleSub.BoundCycleR223.mixed_physical_effect
#print axioms YulangClosure.SimpleSub.BoundCycleR223.mixed_physical_effect

#check @YulangClosure.SimpleSub.BoundCycleR223.mixed_after_fixed
#print axioms YulangClosure.SimpleSub.BoundCycleR223.mixed_after_fixed

#check @YulangClosure.SimpleSub.BoundCycleR223.mixed_level_two_use_factorization
#print axioms YulangClosure.SimpleSub.BoundCycleR223.mixed_level_two_use_factorization

#check @YulangClosure.SimpleSub.BoundCycleR223.sub_observation
#print axioms YulangClosure.SimpleSub.BoundCycleR223.sub_observation

#check @YulangClosure.SimpleSub.BoundCycleR223.union_not_left_atom
#print axioms YulangClosure.SimpleSub.BoundCycleR223.union_not_left_atom

#check @YulangClosure.SimpleSub.BoundCycleR223.stopped_publication_separated_satisfies
#print axioms YulangClosure.SimpleSub.BoundCycleR223.stopped_publication_separated_satisfies

#check @YulangClosure.SimpleSub.BoundCycleR223.mixed_bound_levels_not_closed
#print axioms YulangClosure.SimpleSub.BoundCycleR223.mixed_bound_levels_not_closed

#check @YulangClosure.SimpleSub.BoundCycleR223.stopped_publication_no_joint_factorization
#print axioms YulangClosure.SimpleSub.BoundCycleR223.stopped_publication_no_joint_factorization

#check @YulangClosure.SimpleSub.BoundCycleR223.closed_mixed_same_constraints_and_levels
#print axioms YulangClosure.SimpleSub.BoundCycleR223.closed_mixed_same_constraints_and_levels

#check @YulangClosure.SimpleSub.BoundCycleR223.closed_mixed_bound_levels
#print axioms YulangClosure.SimpleSub.BoundCycleR223.closed_mixed_bound_levels

#check @YulangClosure.SimpleSub.BoundCycleR223.fresh_capture_without_nonGeneric
#print axioms YulangClosure.SimpleSub.BoundCycleR223.fresh_capture_without_nonGeneric

#check @YulangClosure.SimpleSub.BoundCycleR223.closed_publication_supplies_mixed_store
#print axioms YulangClosure.SimpleSub.BoundCycleR223.closed_publication_supplies_mixed_store

#check @YulangClosure.SimpleSub.BoundCycleR223.closed_publication_joint_factorization
#print axioms YulangClosure.SimpleSub.BoundCycleR223.closed_publication_joint_factorization
