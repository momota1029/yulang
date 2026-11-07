import Yulang.CommonEffectFormula
import Yulang.PresenceNormalForm

/-! Finite signed clauses with paired computation slots. Conjunction and
both kinds of existential binders share the actual original names. Local
type slots are projected through pure terms, retaining their empty row
meaning without restricting arbitrary computation parameters elsewhere. -/
namespace Yulang.CommonEffectClauses
open Core.PresenceGeneration (Comp CompTerm TyTerm RowTerm extend)
open CommonEffectRequestGeneration (Computation RowExpr localEnv)
open CommonEffectFormula (rowSubst rowSubst_eval)
open PresenceNormalForm (leftName rightName closeName resultName)

variable {scopes : Nat}

inductive Atom (scopes : Nat) (α : Type) where
  | tyLe : TyTerm α → TyTerm α → Atom scopes α
  | rowLe : RowExpr scopes α → RowTerm α → Atom scopes α

def Atom.Holds (assignment : α → Computation) : Atom scopes α → Prop
  | .tyLe first last => Common.Subtype (first.eval Common.model assignment) (last.eval Common.model assignment)
  | .rowLe first last => Common.rowLe (first.eval assignment) (last.eval Common.model assignment)

def Atom.subst (substitution : α → CompTerm β) : Atom scopes α → Atom scopes β
  | .tyLe first last => .tyLe (first.subst substitution) (last.subst substitution)
  | .rowLe first last => .rowLe (rowSubst substitution first) (last.subst substitution)

@[simp] theorem Atom.holds_subst (assignment : β → Computation) (substitution : α → CompTerm β) (atom : Atom scopes α) :
    (atom.subst substitution).Holds assignment ↔ atom.Holds (fun name => (substitution name).eval Common.model assignment) := by
  cases atom <;> simp only [Atom.subst, Atom.Holds, TyTerm.eval_subst, RowTerm.eval_subst, rowSubst_eval]

def Atom.rename (names : α → β) (atom : Atom scopes α) : Atom scopes β := atom.subst (CompTerm.var ∘ names)

@[simp] theorem Atom.holds_rename (assignment : β → Computation) (names : α → β) (atom : Atom scopes α) :
    (atom.rename names).Holds assignment ↔ atom.Holds (assignment ∘ names) := by
  simp only [Atom.rename, Atom.holds_subst, Function.comp_apply, CompTerm.eval_var]
  rfl

def All (assignment : α → Computation) (atoms : List (Atom scopes α)) : Prop := ∀ atom ∈ atoms, atom.Holds assignment

@[simp] theorem all_append (assignment : α → Computation) (first last : List (Atom scopes α)) :
    All assignment (first ++ last) ↔ All assignment first ∧ All assignment last := by
  simp only [All, List.mem_append, or_imp, forall_and]

@[simp] theorem all_subst (assignment : β → Computation) (substitution : α → CompTerm β) (atoms : List (Atom scopes α)) :
    All assignment (atoms.map (Atom.subst substitution)) ↔
      All (fun name => (substitution name).eval Common.model assignment) atoms := by
  simp only [All, List.forall_mem_map, Atom.holds_subst]

@[simp] theorem all_rename (assignment : β → Computation) (names : α → β) (atoms : List (Atom scopes α)) :
    All assignment (atoms.map (Atom.rename names)) ↔ All (assignment ∘ names) atoms := by
  simp only [All, List.forall_mem_map, Atom.holds_rename]

structure Clause (scopes : Nat) (α : Type) where
  locals : Nat
  atoms : List (Atom scopes (Fin locals ⊕ α))

def Clause.Holds (assignment : α → Computation) (clause : Clause scopes α) (values : Fin clause.locals → Computation) : Prop :=
  All (Sum.elim values assignment) clause.atoms

def Clause.Satisfiable (assignment : α → Computation) (clause : Clause scopes α) : Prop := ∃ values, clause.Holds assignment values

def Clause.empty : Clause scopes α := ⟨0, []⟩
def Clause.singleton (atom : Atom scopes α) : Clause scopes α := ⟨0, [atom.rename Sum.inr]⟩

@[simp] theorem Clause.empty_satisfiable (assignment : α → Computation) :
    (Clause.empty : Clause scopes α).Satisfiable assignment := ⟨Fin.elim0, by intro atom member; cases member⟩

@[simp] theorem Clause.singleton_exact (assignment : α → Computation) (atom : Atom scopes α) :
    (Clause.singleton atom).Satisfiable assignment ↔ atom.Holds assignment := by
  constructor
  · rintro ⟨values, held⟩
    exact (Atom.holds_rename (Sum.elim values assignment) Sum.inr atom).mp
      (held (atom.rename Sum.inr) (List.mem_singleton_self _))
  · intro held
    refine ⟨Fin.elim0, ?_⟩
    intro actual member
    have same : actual = atom.rename Sum.inr := List.mem_singleton.mp member
    subst actual
    exact (Atom.holds_rename (Sum.elim Fin.elim0 assignment) Sum.inr atom).mpr held

def Clause.combine (first last : Clause scopes α) : Clause scopes α :=
  ⟨first.locals + last.locals,
    first.atoms.map (Atom.rename (leftName first.locals last.locals)) ++
    last.atoms.map (Atom.rename (rightName first.locals last.locals))⟩

private theorem combine_left (assignment : α → Computation) (first : Fin a → Computation) (last : Fin b → Computation) :
    Sum.elim (Fin.addCases first last) assignment ∘ leftName a b = Sum.elim first assignment := by
  funext name
  cases name <;> simp [leftName]

private theorem combine_right (assignment : α → Computation) (first : Fin a → Computation) (last : Fin b → Computation) :
    Sum.elim (Fin.addCases first last) assignment ∘ rightName a b = Sum.elim last assignment := by
  funext name
  cases name <;> simp [rightName]

private theorem restrict_left (assignment : α → Computation) (values : Fin (a + b) → Computation) :
    Sum.elim values assignment ∘ leftName a b = Sum.elim (fun index => values (Fin.castAdd b index)) assignment := by
  funext name
  cases name <;> rfl

private theorem restrict_right (assignment : α → Computation) (values : Fin (a + b) → Computation) :
    Sum.elim values assignment ∘ rightName a b = Sum.elim (fun index => values (Fin.natAdd a index)) assignment := by
  funext name
  cases name <;> rfl

@[simp] theorem Clause.combine_exact (assignment : α → Computation) (first last : Clause scopes α) :
    (first.combine last).Satisfiable assignment ↔ first.Satisfiable assignment ∧ last.Satisfiable assignment := by
  simp only [Clause.combine, Clause.Satisfiable, Clause.Holds, all_append, all_rename]
  constructor
  · rintro ⟨values, hf, hl⟩
    exact ⟨⟨fun index => values (Fin.castAdd last.locals index), by simpa only [restrict_left] using hf⟩,
      ⟨fun index => values (Fin.natAdd first.locals index), by simpa only [restrict_right] using hl⟩⟩
  · rintro ⟨⟨fv, hf⟩, ⟨lv, hl⟩⟩
    exact ⟨Fin.addCases fv lv, by simpa only [combine_left] using hf, by simpa only [combine_right] using hl⟩

def Clause.close (clause : Clause scopes (Option α)) : Clause scopes α :=
  ⟨clause.locals + 1, clause.atoms.map (Atom.rename (closeName clause.locals))⟩

private theorem close_values (assignment : α → Computation) (values : Fin n → Computation) (fresh : Computation) :
    Sum.elim (Fin.lastCases fresh values) assignment ∘ closeName n = Sum.elim values (extend assignment fresh) := by
  funext name
  cases name with
  | inl index => simp [closeName]
  | inr index => cases index <;> simp [closeName, Core.PresenceGeneration.extend]

private theorem restrict_close (assignment : α → Computation) (values : Fin (n + 1) → Computation) :
    Sum.elim values assignment ∘ closeName n =
      Sum.elim (fun index => values index.castSucc) (extend assignment (values (Fin.last n))) := by
  funext name
  cases name with
  | inl => rfl
  | inr index => cases index <;> rfl

@[simp] theorem Clause.close_exact (assignment : α → Computation) (clause : Clause scopes (Option α)) :
    clause.close.Satisfiable assignment ↔ ∃ fresh, clause.Satisfiable (extend assignment fresh) := by
  simp only [Clause.close, Clause.Satisfiable, Clause.Holds, all_rename]
  constructor
  · rintro ⟨values, held⟩
    exact ⟨values (Fin.last clause.locals), (fun index => values index.castSucc), by simpa only [restrict_close] using held⟩
  · rintro ⟨fresh, values, held⟩
    exact ⟨Fin.lastCases fresh values, by simpa only [close_values] using held⟩

def typeSubstitution (locals count : Nat) : Fin locals ⊕ (α ⊕ Fin count) → CompTerm (Fin (locals + count) ⊕ α)
  | .inl index => CompTerm.var (.inl (Fin.castAdd count index))
  | .inr (.inl name) => CompTerm.var (.inr name)
  | .inr (.inr index) => CompTerm.pure (.var (.inl (Fin.natAdd locals index)))

def Clause.closeTypes (clause : Clause scopes (α ⊕ Fin count)) : Clause scopes α :=
  ⟨clause.locals + count, clause.atoms.map (Atom.subst (typeSubstitution clause.locals count))⟩

private theorem type_values (assignment : α → Computation) (values : Fin n → Computation) (types : Fin count → Common.Ty) :
    (fun name => (typeSubstitution n count name).eval Common.model
      (Sum.elim (Fin.addCases values (fun index => Comp.pure Common.model (types index))) assignment)) =
      Sum.elim values (localEnv assignment types) := by
  funext name
  cases name with
  | inl index => simp [typeSubstitution]
  | inr name =>
    cases name with
    | inl index => rfl
    | inr index => simp [typeSubstitution, CompTerm.eval_pure, TyTerm.eval, localEnv, Comp.pure]

private theorem restrict_types (assignment : α → Computation) (values : Fin (n + count) → Computation) :
    (fun name => (typeSubstitution n count name).eval Common.model (Sum.elim values assignment)) =
      Sum.elim (fun index => values (Fin.castAdd count index))
        (localEnv assignment (fun index => (values (Fin.natAdd n index)).1)) := by
  funext name
  cases name with
  | inl index => rfl
  | inr name => cases name <;> rfl

@[simp] theorem Clause.closeTypes_exact (assignment : α → Computation) (clause : Clause scopes (α ⊕ Fin count)) :
    clause.closeTypes.Satisfiable assignment ↔ ∃ types, clause.Satisfiable (localEnv assignment types) := by
  simp only [Clause.closeTypes, Clause.Satisfiable, Clause.Holds, all_subst]
  constructor
  · rintro ⟨values, held⟩
    exact ⟨(fun index => (values (Fin.natAdd clause.locals index)).1),
      (fun index => values (Fin.castAdd count index)), by simpa only [restrict_types] using held⟩
  · rintro ⟨types, values, held⟩
    exact ⟨Fin.addCases values (fun index => Comp.pure Common.model (types index)), by simpa only [type_values] using held⟩
end Yulang.CommonEffectClauses
