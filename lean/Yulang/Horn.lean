import Std

/-!
# Finite Horn residual constraints

This is a total executable reference solver for a **finite** set of Boolean
facts. A clause has positive premises and either one positive conclusion or
`none`, which forbids its premises from holding together. Seeds and unary
inclusions are special cases. These facts can represent a resolved finite
row/variant constraint layer; this module does not solve Yulang structural
subtyping, recursive type equations, or unbounded effect stack constraints.

The reference algorithm enumerates all `2^n` valuations and intersects the
models. It is exponential, not a proposed production implementation. Its
structural recursion is total without a fuel assumption. `solve_principal`
and `solve_eq_none_iff` prove least-model correctness and exact rejection
against the independent declarative clause semantics `Models`.
-/

namespace Yulang.Horn

abbrev Valuation (n : Nat) := Fin n → Bool

structure Clause (n : Nat) where
  premises : List (Fin n)
  conclusion : Option (Fin n)
  deriving DecidableEq, Repr

abbrev Problem (n : Nat) := List (Clause n)

def Clause.seed (fact : Fin n) : Clause n := ⟨[], some fact⟩

def Clause.include (source target : Fin n) : Clause n :=
  ⟨[source], some target⟩

def Clause.forbid (facts : List (Fin n)) : Clause n := ⟨facts, none⟩

/-- Declarative Horn implication. `none` is a negative conclusion. -/
def ModelsClause (clause : Clause n) (value : Valuation n) : Prop :=
  (∀ fact ∈ clause.premises, value fact = true) →
    match clause.conclusion with
    | some fact => value fact = true
    | none => False

def Models (problem : Problem n) (value : Valuation n) : Prop :=
  ∀ clause ∈ problem, ModelsClause clause value

/-- Pointwise inclusion of the sets of true facts. -/
def Below (left right : Valuation n) : Prop :=
  ∀ fact, left fact = true → right fact = true

def IsLeastModel (problem : Problem n) (value : Valuation n) : Prop :=
  Models problem value ∧ ∀ other, Models problem other → Below value other

def checkClause (clause : Clause n) (value : Valuation n) : Bool :=
  if clause.premises.all value then
    match clause.conclusion with
    | some fact => value fact
    | none => false
  else true

def check (problem : Problem n) (value : Valuation n) : Bool :=
  problem.all (fun clause => checkClause clause value)

/-- Both choices for the first fact, followed by every assignment to the rest. -/
def valuations : (n : Nat) → List (Valuation n)
  | 0 => [fun fact => Fin.elim0 fact]
  | n + 1 =>
      (valuations n).map (fun rest => Fin.cases false rest) ++
      (valuations n).map (fun rest => Fin.cases true rest)

def allModels (problem : Problem n) : List (Valuation n) :=
  (valuations n).filter (check problem)

/-- Pointwise intersection; the empty intersection is the all-true valuation. -/
def intersection (values : List (Valuation n)) : Valuation n :=
  fun fact => values.all (fun value => value fact)

/-- `none` means unsatisfiable; a successful result is the unique least model. -/
def solve (problem : Problem n) : Option (Valuation n) :=
  match allModels problem with
  | [] => none
  | value :: values => some (intersection (value :: values))

@[simp] theorem checkClause_iff (clause : Clause n) (value : Valuation n) :
    checkClause clause value = true ↔ ModelsClause clause value := by
  cases hp : clause.premises.all value with
  | false =>
      have hnot : ¬ (∀ fact ∈ clause.premises, value fact = true) := by
        intro h
        have heq := List.all_eq_true.mpr h
        simp [hp] at heq
      simp [checkClause, ModelsClause, hp, hnot]
  | true =>
      have hyes := List.all_eq_true.mp hp
      constructor
      · intro hb _
        cases hc : clause.conclusion with
        | none => simp [checkClause, hp, hc] at hb
        | some fact => simpa [checkClause, hp, hc] using hb
      · intro hm
        have ht := hm hyes
        cases hc : clause.conclusion with
        | none => simp [hc] at ht
        | some fact => simpa [checkClause, hp, hc] using ht

@[simp] theorem check_iff (problem : Problem n) (value : Valuation n) :
    check problem value = true ↔ Models problem value := by
  simp only [check, List.all_eq_true, checkClause_iff, Models]

theorem mem_valuations (value : Valuation n) : value ∈ valuations n := by
  induction n with
  | zero =>
      have h : value = (fun fact : Fin 0 => Fin.elim0 fact) := by
        funext fact
        exact Fin.elim0 fact
      simp [valuations, h]
  | succ n ih =>
      let rest : Valuation n := fun fact => value fact.succ
      have hrest := ih rest
      have hcons : Fin.cases (value 0) rest = value := by
        funext fact
        refine Fin.cases ?_ (fun index => ?_) fact
        · rfl
        · rfl
      cases hzero : value 0 with
      | false =>
          apply List.mem_append.mpr
          left
          apply List.mem_map.mpr
          exact ⟨rest, hrest, by simpa [hzero] using hcons⟩
      | true =>
          apply List.mem_append.mpr
          right
          apply List.mem_map.mpr
          exact ⟨rest, hrest, by simpa [hzero] using hcons⟩

@[simp] theorem mem_allModels (problem : Problem n) (value : Valuation n) :
    value ∈ allModels problem ↔ Models problem value := by
  simp [allModels, mem_valuations]

theorem intersection_below (values : List (Valuation n)) (value : Valuation n)
    (hmem : value ∈ values) : Below (intersection values) value := by
  intro fact h
  exact List.all_eq_true.mp h value hmem

/-- Horn clauses are preserved by any nonempty finite intersection of models. -/
theorem intersection_models (problem : Problem n) (values : List (Valuation n))
    (hne : values ≠ []) (hmodels : ∀ value ∈ values, Models problem value) :
    Models problem (intersection values) := by
  intro clause hclause hpremises
  have hpremisesFor (value : Valuation n) (hmem : value ∈ values) :
      ∀ fact ∈ clause.premises, value fact = true := by
    intro fact hfact
    exact intersection_below values value hmem fact (hpremises fact hfact)
  cases hc : clause.conclusion with
  | some fact =>
      apply List.all_eq_true.mpr
      intro value hmem
      have h := hmodels value hmem clause hclause (hpremisesFor value hmem)
      simpa [hc] using h
  | none =>
      cases values with
      | nil => exact False.elim (hne rfl)
      | cons value values =>
          have h := hmodels value (by simp) clause hclause
            (hpremisesFor value (by simp))
          simp [hc] at h

/-- Every successful result is a model and is below every model, not only
the valuations encountered before a search cutoff. There is no cutoff. -/
theorem solve_principal (problem : Problem n) (value : Valuation n)
    (hsolve : solve problem = some value) : IsLeastModel problem value := by
  unfold solve at hsolve
  cases hmodels : allModels problem with
  | nil => simp [hmodels] at hsolve
  | cons first rest =>
      simp only [hmodels, Option.some.injEq] at hsolve
      subst value
      constructor
      · apply intersection_models problem (first :: rest) (by simp)
        intro value hmem
        exact (mem_allModels problem value).mp (by simpa [hmodels] using hmem)
      · intro other hother
        apply intersection_below
        have hmem := (mem_allModels problem other).mpr hother
        simpa [hmodels] using hmem

/-- Rejection is equivalent to the absence of any declarative model. -/
theorem solve_eq_none_iff (problem : Problem n) :
    solve problem = none ↔ ¬ ∃ value, Models problem value := by
  constructor
  · intro hsolve ⟨value, hmodel⟩
    have hmem := (mem_allModels problem value).mpr hmodel
    cases hmodels : allModels problem with
    | nil => simp [hmodels] at hmem
    | cons first rest => simp [solve, hmodels] at hsolve
  · intro hnone
    cases hmodels : allModels problem with
    | nil => simp [solve, hmodels]
    | cons first rest =>
        have hfirst : Models problem first :=
          (mem_allModels problem first).mp (by simp [hmodels])
        exact False.elim (hnone ⟨first, hfirst⟩)

theorem solve_complete (problem : Problem n) (model : Valuation n)
    (hmodel : Models problem model) :
    ∃ least, solve problem = some least ∧ IsLeastModel problem least ∧ Below least model := by
  cases hsolve : solve problem with
  | none => exact False.elim ((solve_eq_none_iff problem).mp hsolve ⟨model, hmodel⟩)
  | some least =>
      have hleast := solve_principal problem least hsolve
      exact ⟨least, rfl, hleast, hleast.2 model hmodel⟩

theorem below_antisymm (left right : Valuation n)
    (hlr : Below left right) (hrl : Below right left) : left = right := by
  funext fact
  cases hl : left fact <;> cases hr : right fact <;> try rfl
  · have := hrl fact hr
    simp [hl] at this
  · have := hlr fact hl
    simp [hr] at this

theorem least_unique (problem : Problem n) (left right : Valuation n)
    (hl : IsLeastModel problem left) (hr : IsLeastModel problem right) : left = right := by
  exact below_antisymm left right (hl.2 right hr.1) (hr.2 left hl.1)

/-- A valuation is returned exactly when it is the least declarative model. -/
theorem solve_eq_some_iff (problem : Problem n) (value : Valuation n) :
    solve problem = some value ↔ IsLeastModel problem value := by
  constructor
  · exact solve_principal problem value
  · intro hleast
    obtain ⟨other, hsolve, hother, _⟩ := solve_complete problem value hleast.1
    have heq := least_unique problem other value hother hleast
    simpa [heq] using hsolve

end Yulang.Horn
