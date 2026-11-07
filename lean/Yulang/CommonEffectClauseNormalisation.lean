import Yulang.CommonEffectClauses

/-! Actual finite existential clause normalization. A remaining type
universal or a signed-transformed upper expression returns none (unsupported),
never a falsely rejected/solved problem. All ordinary upper unions and
operation-local existential type binders are supported. -/
namespace Yulang.CommonEffectClauseNormalisation
open Core.PresenceGeneration (CompTerm RowTerm extend)
open CommonEffectRequestGeneration (Computation RowExpr localEnv)
open CommonEffectFormula (Formula)
open CommonEffectClauses (Atom Clause)

variable {scopes : Nat}

def Satisfiable (assignment : α → Computation) (clauses : List (Clause scopes α)) : Prop :=
  ∃ clause ∈ clauses, clause.Satisfiable assignment

@[simp] theorem satisfiable_empty (assignment : α → Computation) :
    Satisfiable assignment ([Clause.empty] : List (Clause scopes α)) := by
  exact ⟨.empty, by simp, Clause.empty_satisfiable assignment⟩

@[simp] theorem satisfiable_singleton (assignment : α → Computation) (atom : Atom scopes α) :
    Satisfiable assignment [.singleton atom] ↔ atom.Holds assignment := by
  simp [Satisfiable]

theorem append_exact (first last : List (Clause scopes α)) (assignment : α → Computation) :
    Satisfiable assignment (first ++ last) ↔ Satisfiable assignment first ∨ Satisfiable assignment last := by
  simp [Satisfiable, List.mem_append, or_and_right, exists_or]

def product (first last : List (Clause scopes α)) : List (Clause scopes α) :=
  first.flatMap (fun a => last.map a.combine)

theorem product_exact (first last : List (Clause scopes α)) (assignment : α → Computation) :
    Satisfiable assignment (product first last) ↔ Satisfiable assignment first ∧ Satisfiable assignment last := by
  simp only [Satisfiable, product, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨_, ⟨a, ma, b, mb, rfl⟩, held⟩
    obtain ⟨ha, hb⟩ := (Clause.combine_exact assignment a b).mp held
    exact ⟨⟨a, ma, ha⟩, ⟨b, mb, hb⟩⟩
  · rintro ⟨⟨a, ma, ha⟩, ⟨b, mb, hb⟩⟩
    exact ⟨a.combine b, ⟨a, ma, b, mb, rfl⟩, (Clause.combine_exact assignment a b).mpr ⟨ha, hb⟩⟩

theorem close_exact (clauses : List (Clause scopes (Option α))) (assignment : α → Computation) :
    Satisfiable assignment (clauses.map Clause.close) ↔ ∃ fresh, Satisfiable (extend assignment fresh) clauses := by
  simp only [Satisfiable, List.mem_map]
  constructor
  · rintro ⟨_, ⟨clause, member, rfl⟩, held⟩
    obtain ⟨fresh, held⟩ := (Clause.close_exact assignment clause).mp held
    exact ⟨fresh, clause, member, held⟩
  · rintro ⟨fresh, clause, member, held⟩
    exact ⟨clause.close, ⟨clause, member, rfl⟩, (Clause.close_exact assignment clause).mpr ⟨fresh, held⟩⟩

theorem closeTypes_exact (clauses : List (Clause scopes (α ⊕ Fin count))) (assignment : α → Computation) :
    Satisfiable assignment (clauses.map Clause.closeTypes) ↔ ∃ types, Satisfiable (localEnv assignment types) clauses := by
  simp only [Satisfiable, List.mem_map]
  constructor
  · rintro ⟨_, ⟨clause, member, rfl⟩, held⟩
    obtain ⟨types, held⟩ := (Clause.closeTypes_exact assignment clause).mp held
    exact ⟨types, clause, member, held⟩
  · rintro ⟨types, clause, member, held⟩
    exact ⟨clause.closeTypes, ⟨clause, member, rfl⟩, (Clause.closeTypes_exact assignment clause).mpr ⟨types, held⟩⟩

def normaliseCore : Core.PresenceGeneration.Formula α → List (Clause scopes α)
  | .top => [.empty]
  | .bot => []
  | .tyLe first last => [.singleton (.tyLe first last)]
  | .rowLe first last => [.singleton (.rowLe (.fromPresence first) last)]
  | .and first last => product (normaliseCore first) (normaliseCore last)
  | .or first last => normaliseCore first ++ normaliseCore last
  | .existsSlot body => (normaliseCore body).map Clause.close

theorem normaliseCore_exact (formula : Core.PresenceGeneration.Formula α) (assignment : α → Computation) :
    Satisfiable assignment (normaliseCore (scopes := scopes) formula) ↔ formula.Holds Common.model assignment := by
  induction formula with
  | top => exact ⟨fun _ => trivial, fun _ => satisfiable_empty assignment⟩
  | bot => simp [normaliseCore, Satisfiable, Core.PresenceGeneration.Formula.Holds]
  | tyLe first last => exact satisfiable_singleton assignment (.tyLe first last)
  | rowLe first last =>
    exact (satisfiable_singleton assignment (.rowLe (.fromPresence first) last)).trans
      (by simp only [Atom.Holds, RowExpr.eval_fromPresence]; rfl)
  | and first last ihf ihl => exact (product_exact _ _ assignment).trans (and_congr (ihf assignment) (ihl assignment))
  | or first last ihf ihl => exact (append_exact _ _ assignment).trans (or_congr (ihf assignment) (ihl assignment))
  | existsSlot body ih => exact (close_exact _ assignment).trans (exists_congr (fun fresh => ih _))

def ordinaryUpper : RowExpr scopes α → Option (RowTerm α)
  | .var name => some (.var name)
  | .empty => some .empty
  | .union first last => do return .join (← ordinaryUpper first) (← ordinaryUpper last)
  | _ => none

theorem ordinaryUpper_exact (expression : RowExpr scopes α) (row : RowTerm α)
    (computed : ordinaryUpper expression = some row) (assignment : α → Computation) :
    expression.eval assignment = row.eval Common.model assignment := by
  induction expression generalizing row with
  | var | empty => cases computed; rfl
  | head | protect | release | residual => cases computed
  | union first last ihf ihl =>
    cases fc : ordinaryUpper first with
    | none => simp [ordinaryUpper, fc] at computed
    | some fr =>
      cases lc : ordinaryUpper last with
      | none => simp [ordinaryUpper, fc, lc] at computed
      | some lr =>
        simp [ordinaryUpper, fc, lc] at computed
        subst row
        change Common.rowJoin _ _ = Common.rowJoin _ _
        rw [ihf fr fc, ihl lr lc]

@[simp] theorem ordinaryUpper_fromPresence (row : RowTerm α) : ordinaryUpper (RowExpr.fromPresence (scopes := scopes) row) = some row := by
  induction row <;> simp_all [ordinaryUpper, RowExpr.fromPresence]

def normalise : Formula scopes α → Option (List (Clause scopes α))
  | .core body => some (normaliseCore body)
  | .rowLe first last => (ordinaryUpper last).map (fun row => [.singleton (.rowLe first row)])
  | .and first last => do return product (← normalise first) (← normalise last)
  | .or first last => do return (← normalise first) ++ (← normalise last)
  | .existsSlot body => (normalise body).map (List.map Clause.close)
  | .existsTypes _ body => (normalise body).map (List.map Clause.closeTypes)
  | .forallTypes _ _ => none

/-- Any finite formula, actual successful finite normalization, every captured
computation assignment. Unsupported universals are not interpreted as false. -/
theorem normalise_exact (formula : Formula scopes α) (clauses : List (Clause scopes α))
    (computed : normalise formula = some clauses) (assignment : α → Computation) :
    Satisfiable assignment clauses ↔ formula.Holds assignment := by
  induction formula with
  | core body =>
    have same : normaliseCore body = clauses := Option.some.inj computed
    subst clauses
    exact normaliseCore_exact body assignment
  | rowLe first last =>
    cases found : ordinaryUpper last with
    | none => simp [normalise, found] at computed
    | some row =>
      simp [normalise, found] at computed
      subst clauses
      rw [satisfiable_singleton]
      exact Iff.rfl.trans (show Common.rowLe (first.eval assignment) (row.eval Common.model assignment) ↔
        Common.rowLe (first.eval assignment) (last.eval assignment) by rw [ordinaryUpper_exact last row found assignment])
  | and first last ihf ihl =>
    cases fc : normalise first with
    | none => simp [normalise, fc] at computed
    | some fs =>
      cases lc : normalise last with
      | none => simp [normalise, fc, lc] at computed
      | some ls =>
        simp [normalise, fc, lc] at computed
        subst clauses
        exact (product_exact fs ls assignment).trans (and_congr (ihf fs fc assignment) (ihl ls lc assignment))
  | or first last ihf ihl =>
    cases fc : normalise first with
    | none => simp [normalise, fc] at computed
    | some fs =>
      cases lc : normalise last with
      | none => simp [normalise, fc, lc] at computed
      | some ls =>
        simp [normalise, fc, lc] at computed
        subst clauses
        exact (append_exact fs ls assignment).trans (or_congr (ihf fs fc assignment) (ihl ls lc assignment))
  | existsSlot body ih =>
    cases found : normalise body with
    | none => simp [normalise, found] at computed
    | some cs =>
      simp [normalise, found] at computed
      subst clauses
      exact (close_exact cs assignment).trans (exists_congr (fun fresh => ih cs found _))
  | existsTypes count body ih =>
    cases found : normalise body with
    | none => simp [normalise, found] at computed
    | some cs =>
      simp [normalise, found] at computed
      subst clauses
      exact (closeTypes_exact cs assignment).trans (exists_congr (fun types => ih cs found _))
  | forallTypes => cases computed
end Yulang.CommonEffectClauseNormalisation
