import Yulang.CommonNominalFieldGeneration
import Yulang.PresenceNormalForm

/-!
# Finite atomic clauses for actual nominal field generation

The binder allocation/combine/close construction follows PresenceNormalForm,
with atoms extended to full regular field-template applications. Ordinary
source formulas are normalized by the existing actual normalizer and embedded
atom by atom. The result has no source-typing atoms or nested logical binders.

This is a solver interface: it does not declare atomic comparisons solved.
-/

namespace Yulang.CommonNominalFieldNormalForm

open CommonNominalCarrier
open Core.PresenceGeneration (Comp RowTerm extend)
open CommonNominalFieldTemplates (Term Formula)

inductive Atom (α : Type) where
  | tyLe : Term α → Term α → Atom α
  | rowLe : RowTerm α → RowTerm α → Atom α

def Atom.Models (assignment : α → Comp model) : Atom α → Prop
  | .tyLe first last => CommonNominalCarrier.Subtype (first.eval assignment) (last.eval assignment)
  | .rowLe first last => Common.rowLe (first.eval model assignment) (last.eval model assignment)

def Atom.rename (rename : α → β) : Atom α → Atom β
  | .tyLe first last => .tyLe (first.rename rename) (last.rename rename)
  | .rowLe first last => .rowLe (first.rename rename) (last.rename rename)

@[simp] theorem Atom.holds_rename (assignment : β → Comp model) (rename : α → β) (atom : Atom α) :
    (atom.rename rename).Models assignment ↔ atom.Models (assignment ∘ rename) := by
  cases atom <;> simp only [Atom.rename, Atom.Models, Term.eval_rename, RowTerm.eval_rename]

def All (assignment : α → Comp model) (atoms : List (Atom α)) : Prop :=
  ∀ atom ∈ atoms, atom.Models assignment

@[simp] theorem all_nil (assignment : α → Comp model) :
    All assignment [] := by intro atom member; cases member

@[simp] theorem all_append (assignment : α → Comp model)
    (left right : List (Atom α)) :
    All assignment (left ++ right) ↔ All assignment left ∧ All assignment right := by
  simp only [All, List.mem_append, or_imp, forall_and]

@[simp] theorem all_rename (assignment : β → Comp model)
    (rename : α → β) (atoms : List (Atom α)) :
    All assignment (atoms.map (Atom.rename rename)) ↔
      All (assignment ∘ rename) atoms := by
  simp only [All, List.forall_mem_map, Atom.holds_rename]

structure Clause (α : Type) where
  locals : Nat
  atoms : List (Atom (Fin locals ⊕ α))

/-- A clause is a conjunction at a supplied local computation assignment.
No logical binders remain in its atoms, and each local retains both its value
and its row component. -/
def Clause.Models (assignment : α → Comp model) (clause : Clause α)
    (localValues : Fin clause.locals → Comp model) : Prop :=
  All (Sum.elim localValues assignment) clause.atoms

def Clause.Satisfiable (assignment : α → Comp model) (clause : Clause α) : Prop :=
  ∃ localValues : Fin clause.locals → Comp model, clause.Models assignment localValues

def Clause.empty : Clause α := ⟨0, []⟩

def Clause.singleton (atom : Atom α) : Clause α := ⟨0, [atom.rename Sum.inr]⟩

@[simp] theorem Clause.holds_empty (assignment : α → Comp model) :
    Clause.empty.Satisfiable assignment :=
  ⟨Fin.elim0, all_nil _⟩

@[simp] theorem Clause.holds_singleton (assignment : α → Comp model)
    (atom : Atom α) :
    (Clause.singleton atom).Satisfiable assignment ↔ atom.Models assignment := by
  constructor
  · rintro ⟨values, held⟩
    have single := held (atom.rename Sum.inr) (List.mem_singleton_self _)
    exact (Atom.holds_rename (Sum.elim values assignment) Sum.inr atom).mp single
  · intro held
    refine ⟨Fin.elim0, ?_⟩
    intro actual member
    have same : actual = atom.rename Sum.inr := List.mem_singleton.mp member
    subst actual
    exact (Atom.holds_rename (Sum.elim Fin.elim0 assignment) Sum.inr atom).mpr held

def leftName (left right : Nat) : Fin left ⊕ α → Fin (left + right) ⊕ α
  | .inl index => .inl (Fin.castAdd right index)
  | .inr name => .inr name

def rightName (left right : Nat) : Fin right ⊕ α → Fin (left + right) ⊕ α
  | .inl index => .inl (Fin.natAdd left index)
  | .inr name => .inr name

def Clause.combine (left right : Clause α) : Clause α :=
  ⟨left.locals + right.locals,
    left.atoms.map (Atom.rename (leftName left.locals right.locals)) ++
    right.atoms.map (Atom.rename (rightName left.locals right.locals))⟩

private theorem combine_left (assignment : α → Comp model)
    (left : Fin a → Comp model) (right : Fin b → Comp model) :
    Sum.elim (Fin.addCases left right) assignment ∘ leftName a b = Sum.elim left assignment := by
  funext index
  cases index <;> simp [leftName]

private theorem combine_right (assignment : α → Comp model)
    (left : Fin a → Comp model) (right : Fin b → Comp model) :
    Sum.elim (Fin.addCases left right) assignment ∘ rightName a b = Sum.elim right assignment := by
  funext index
  cases index <;> simp [rightName]

private theorem restrict_left (assignment : α → Comp model)
    (values : Fin (a + b) → Comp model) :
    Sum.elim values assignment ∘ leftName a b =
      Sum.elim (fun index => values (Fin.castAdd b index)) assignment := by
  funext index
  cases index <;> rfl

private theorem restrict_right (assignment : α → Comp model)
    (values : Fin (a + b) → Comp model) :
    Sum.elim values assignment ∘ rightName a b =
      Sum.elim (fun index => values (Fin.natAdd a index)) assignment := by
  funext index
  cases index <;> rfl

@[simp] theorem Clause.holds_combine (assignment : α → Comp model)
    (left right : Clause α) :
    (left.combine right).Satisfiable assignment ↔
      left.Satisfiable assignment ∧ right.Satisfiable assignment := by
  simp only [Clause.combine, Clause.Satisfiable, Clause.Models, all_append, all_rename]
  constructor
  · rintro ⟨values, leftHeld, rightHeld⟩
    exact ⟨⟨fun index => values (Fin.castAdd right.locals index),
      by simpa only [restrict_left] using leftHeld⟩,
      ⟨fun index => values (Fin.natAdd left.locals index),
      by simpa only [restrict_right] using rightHeld⟩⟩
  · rintro ⟨⟨leftValues, leftHeld⟩, ⟨rightValues, rightHeld⟩⟩
    exact ⟨Fin.addCases leftValues rightValues,
      by simpa only [combine_left] using leftHeld,
      by simpa only [combine_right] using rightHeld⟩

def closeName (locals : Nat) : Fin locals ⊕ Option α → Fin (locals + 1) ⊕ α
  | .inl index => .inl index.castSucc
  | .inr none => .inl (Fin.last locals)
  | .inr (some name) => .inr name

/-- A fresh binder becomes a new local slot. Captured names are unchanged. -/
def Clause.close (clause : Clause (Option α)) : Clause α :=
  ⟨clause.locals + 1, clause.atoms.map (Atom.rename (closeName clause.locals))⟩

private theorem close_values (assignment : α → Comp model)
    (values : Fin n → Comp model) (fresh : Comp model) :
    Sum.elim (Fin.lastCases fresh values) assignment ∘ closeName n =
      Sum.elim values (extend assignment fresh) := by
  funext index
  cases index with
  | inl index => simp [closeName]
  | inr index => cases index <;> simp [closeName, extend]

private theorem restrict_close (assignment : α → Comp model)
    (values : Fin (n + 1) → Comp model) :
    Sum.elim values assignment ∘ closeName n =
      Sum.elim (fun index => values index.castSucc)
        (extend assignment (values (Fin.last n))) := by
  funext index
  cases index with
  | inl => rfl
  | inr index => cases index <;> rfl

@[simp] theorem Clause.holds_close (assignment : α → Comp model)
    (clause : Clause (Option α)) :
    clause.close.Satisfiable assignment ↔
      ∃ fresh, clause.Satisfiable (extend assignment fresh) := by
  simp only [Clause.close, Clause.Satisfiable, Clause.Models, all_rename]
  constructor
  · rintro ⟨values, held⟩
    exact ⟨values (Fin.last clause.locals), (fun index => values index.castSucc),
      by simpa only [restrict_close] using held⟩
  · rintro ⟨fresh, values, held⟩
    exact ⟨Fin.lastCases fresh values, by simpa only [close_values] using held⟩


def Atom.ofPresence : PresenceNormalForm.Atom α → Atom α
  | .tyLe first last => .tyLe (.ordinary first) (.ordinary last)
  | .rowLe first last => .rowLe first last

@[simp] theorem Atom.models_ofPresence (assignment : α → Comp model) (atom : PresenceNormalForm.Atom α) :
    (Atom.ofPresence atom).Models assignment ↔ atom.Holds model assignment := by
  cases atom <;> rfl

def Clause.ofPresence (clause : PresenceNormalForm.Clause α) : Clause α :=
  ⟨clause.locals, clause.atoms.map Atom.ofPresence⟩

@[simp] theorem Clause.models_ofPresence (assignment : α → Comp model)
    (clause : PresenceNormalForm.Clause α) (values : Fin clause.locals → Comp model) :
    (Clause.ofPresence clause).Models assignment values ↔ clause.Holds model assignment values := by
  constructor
  · intro held atom member
    exact (Atom.models_ofPresence _ atom).mp (held _ (List.mem_map.mpr ⟨atom, member, rfl⟩))
  · intro held atom member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact (Atom.models_ofPresence _ original).mpr (held original present)

@[simp] theorem Clause.satisfiable_ofPresence (assignment : α → Comp model)
    (clause : PresenceNormalForm.Clause α) :
    (Clause.ofPresence clause).Satisfiable assignment ↔ clause.Satisfiable model assignment := by
  apply exists_congr
  intro values
  exact Clause.models_ofPresence assignment clause values

def normalise : Formula α → List (Clause α)
  | .ordinary formula => (PresenceNormalForm.normalise formula).map Clause.ofPresence
  | .tyLe first last => [.singleton (.tyLe first last)]
  | .and first last => (normalise first).flatMap fun a => (normalise last).map a.combine
  | .or first last => normalise first ++ normalise last
  | .existsSlot body => (normalise body).map Clause.close

/-- Every original existential, alternative, ambient type/row and whole
regular template is retained by actual finite atomic normalization. -/
theorem normalise_exact (assignment : α → Comp model) (formula : Formula α) :
    (∃ clause ∈ normalise formula, clause.Satisfiable assignment) ↔ formula.Models assignment := by
  induction formula with
  | ordinary formula =>
      simp only [normalise, List.mem_map]
      constructor
      · rintro ⟨_, ⟨clause, member, rfl⟩, held⟩
        exact (PresenceNormalForm.normalise_exact model assignment formula).mp
          ⟨clause, member, (Clause.satisfiable_ofPresence assignment clause).mp held⟩
      · intro held
        obtain ⟨clause, member, held⟩ := (PresenceNormalForm.normalise_exact model assignment formula).mpr held
        exact ⟨Clause.ofPresence clause, ⟨clause, member, rfl⟩,
          (Clause.satisfiable_ofPresence assignment clause).mpr held⟩
  | tyLe first last => simp [normalise, Formula.Models, Atom.Models]
  | and left right ihLeft ihRight =>
      simp only [normalise, List.mem_flatMap, List.mem_map, Formula.Models]
      constructor
      · rintro ⟨_, ⟨a, ma, b, mb, rfl⟩, held⟩
        obtain ⟨ha, hb⟩ := (Clause.holds_combine assignment a b).mp held
        exact ⟨(ihLeft assignment).mp ⟨a, ma, ha⟩, (ihRight assignment).mp ⟨b, mb, hb⟩⟩
      · rintro ⟨ha, hb⟩
        obtain ⟨a, ma, ha⟩ := (ihLeft assignment).mpr ha
        obtain ⟨b, mb, hb⟩ := (ihRight assignment).mpr hb
        exact ⟨a.combine b, ⟨a, ma, b, mb, rfl⟩,
          (Clause.holds_combine assignment a b).mpr ⟨ha, hb⟩⟩
  | or left right ihLeft ihRight =>
      simp only [normalise, List.mem_append, Formula.Models]
      constructor
      · rintro ⟨clause, member, held⟩
        rcases member with member | member
        · exact .inl ((ihLeft assignment).mp ⟨clause, member, held⟩)
        · exact .inr ((ihRight assignment).mp ⟨clause, member, held⟩)
      · rintro (held | held)
        · obtain ⟨clause, member, held⟩ := (ihLeft assignment).mpr held
          exact ⟨clause, .inl member, held⟩
        · obtain ⟨clause, member, held⟩ := (ihRight assignment).mpr held
          exact ⟨clause, .inr member, held⟩
  | existsSlot formula ih =>
      simp only [normalise, List.mem_map, Formula.Models]
      constructor
      · rintro ⟨_, ⟨clause, member, rfl⟩, held⟩
        obtain ⟨fresh, held⟩ := (Clause.holds_close assignment clause).mp held
        exact ⟨fresh, (ih _).mp ⟨clause, member, held⟩⟩
      · rintro ⟨fresh, held⟩
        obtain ⟨clause, member, held⟩ := (ih _).mpr held
        exact ⟨clause.close, ⟨clause, member, rfl⟩,
          (Clause.holds_close assignment clause).mpr ⟨fresh, held⟩⟩


def packName (locals ambient : Nat) : Fin locals ⊕ Fin ambient → Fin (locals + ambient) :=
  Sum.elim (Fin.castAdd ambient) (Fin.natAdd locals)

def Clause.pack (clause : Clause (Fin ambient)) : List (Atom (Fin (clause.locals + ambient))) :=
  clause.atoms.map (Atom.rename (packName clause.locals ambient))

/-- The entire original ambient computation vector is fixed literally.
Fresh slots from all source bodies/sites remain distinct finite IDs. -/
theorem Clause.pack_exact (clause : Clause (Fin ambient)) (assignment : Fin ambient → Comp model) :
    clause.Satisfiable assignment ↔
      ∃ values : Fin (clause.locals + ambient) → Comp model,
        (∀ index, values (Fin.natAdd clause.locals index) = assignment index) ∧ All values clause.pack := by
  constructor
  · rintro ⟨locals, held⟩
    refine ⟨Fin.addCases locals assignment, ?_, ?_⟩
    · intro index
      exact Fin.addCases_right _
    · rw [Clause.pack, all_rename]
      have same : Fin.addCases locals assignment ∘ packName clause.locals ambient = Sum.elim locals assignment := by
        funext index
        cases index <;> simp [packName]
      rw [same]
      exact held
  · rintro ⟨values, ambientSame, held⟩
    refine ⟨fun index => values (Fin.castAdd ambient index), ?_⟩
    rw [Clause.pack, all_rename] at held
    have same : values ∘ packName clause.locals ambient =
        Sum.elim (fun index => values (Fin.castAdd ambient index)) assignment := by
      funext index
      cases index with
      | inl index => rfl
      | inr index => exact ambientSame index
    rw [same] at held
    exact held

/-- This is the exact finite constraint-set interface for the original
resolved construction generator, before solving atomic type/row bounds. -/
theorem construction_atomic_exact
    (registry : CommonNominalSourceRegistry.Registry vertices (Fin ambient))
    (symbolic : Core.PresenceGeneration.SchemeEnv (Fin ambient))
    (environment : List (Core.PresenceGeneration.Binding model)) (assignment : Fin ambient → Comp model)
    (declaration : CommonNominalFieldGeneration.Declaration types rows)
    (sources : List CommonNominalFieldGeneration.SourceSite)
    (arguments : Fin types → Core.PresenceGeneration.TyTerm (Fin ambient))
    (rowArguments : Fin rows → RowTerm (Fin ambient)) (output : Core.PresenceGeneration.CompTerm (Fin ambient))
    (related : Core.PresenceGeneration.EnvRel model assignment symbolic environment) :
    CommonNominalFieldGeneration.ConstructionTyping registry assignment environment declaration sources
      (fun index => (arguments index).eval model assignment)
      (fun index => (rowArguments index).eval model assignment) (output.eval model assignment) ↔
      ∃ clause ∈ normalise (CommonNominalFieldGeneration.generate registry symbolic declaration sources arguments rowArguments output),
        ∃ values : Fin (clause.locals + ambient) → Comp model,
          (∀ index, values (Fin.natAdd clause.locals index) = assignment index) ∧ All values clause.pack := by
  rw [← CommonNominalFieldGeneration.generate_fields_exact registry symbolic environment assignment
    declaration sources arguments rowArguments output related]
  exact (normalise_exact assignment _).symm.trans (by
    apply exists_congr
    intro clause
    exact and_congr Iff.rfl (clause.pack_exact assignment))

end Yulang.CommonNominalFieldNormalForm
