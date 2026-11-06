import Yulang.CorePresenceGenerationCore

/-!
# Finite existential clauses for presence-aware principal formulas

This normalization consumes the actual `Core.PresenceGeneration.Formula`,
including exact empty records, required fields, whole-record defaults, both
branches of a value-restricted let, and its captured environment. A clause has finitely
many fresh computation slots and a conjunction of value/row inequalities.
The result is a finite list of alternative clauses; it contains no nested
logical binders. Fresh slots from distinct conjuncts are kept disjoint.

Correctness holds for every inference model, before choosing a subtype or row
solver. This is a solver interface, not a decision procedure for the atoms.
The explicit disjunctive normal form can grow exponentially; no efficiency
claim or replacement of the production generator is made here.
-/

namespace Yulang.PresenceNormalForm

open Core.PresenceGeneration
open Inference (Expr)

inductive Atom (α : Type) where
  | tyLe : TyTerm α → TyTerm α → Atom α
  | rowLe : RowTerm α → RowTerm α → Atom α

def Atom.Holds (model : Model) (assignment : α → Comp model) : Atom α → Prop
  | .tyLe left right => model.subTy (left.eval model assignment) (right.eval model assignment)
  | .rowLe left right => model.subRow (left.eval model assignment) (right.eval model assignment)

def Atom.rename (rename : α → β) : Atom α → Atom β
  | .tyLe left right => .tyLe (left.rename rename) (right.rename rename)
  | .rowLe left right => .rowLe (left.rename rename) (right.rename rename)

@[simp] theorem Atom.holds_rename (model : Model) (assignment : β → Comp model)
    (rename : α → β) (atom : Atom α) :
    (atom.rename rename).Holds model assignment ↔ atom.Holds model (assignment ∘ rename) := by
  cases atom <;> simp [Atom.rename, Atom.Holds]

def All (model : Model) (assignment : α → Comp model) (atoms : List (Atom α)) : Prop :=
  ∀ atom ∈ atoms, atom.Holds model assignment

@[simp] theorem all_nil (model : Model) (assignment : α → Comp model) :
    All model assignment [] := by intro atom member; cases member

@[simp] theorem all_append (model : Model) (assignment : α → Comp model)
    (left right : List (Atom α)) :
    All model assignment (left ++ right) ↔ All model assignment left ∧ All model assignment right := by
  simp only [All, List.mem_append, or_imp, forall_and]

@[simp] theorem all_rename (model : Model) (assignment : β → Comp model)
    (rename : α → β) (atoms : List (Atom α)) :
    All model assignment (atoms.map (Atom.rename rename)) ↔
      All model (assignment ∘ rename) atoms := by
  simp only [All, List.forall_mem_map, Atom.holds_rename]

structure Clause (α : Type) where
  locals : Nat
  atoms : List (Atom (Fin locals ⊕ α))

/-- A clause is a conjunction at a supplied local computation assignment.
No logical binders remain in its atoms, and each local retains both its value
and its row component. -/
def Clause.Holds (model : Model) (assignment : α → Comp model) (clause : Clause α)
    (localValues : Fin clause.locals → Comp model) : Prop :=
  All model (Sum.elim localValues assignment) clause.atoms

def Clause.Satisfiable (model : Model) (assignment : α → Comp model) (clause : Clause α) : Prop :=
  ∃ localValues : Fin clause.locals → Comp model, clause.Holds model assignment localValues

def Clause.empty : Clause α := ⟨0, []⟩

def Clause.singleton (atom : Atom α) : Clause α := ⟨0, [atom.rename Sum.inr]⟩

@[simp] theorem Clause.holds_empty (model : Model) (assignment : α → Comp model) :
    Clause.empty.Satisfiable model assignment :=
  ⟨Fin.elim0, all_nil _ _⟩

@[simp] theorem Clause.holds_singleton (model : Model) (assignment : α → Comp model)
    (atom : Atom α) :
    (Clause.singleton atom).Satisfiable model assignment ↔ atom.Holds model assignment := by
  constructor
  · rintro ⟨values, held⟩
    have single := held (atom.rename Sum.inr) (List.mem_singleton_self _)
    exact (Atom.holds_rename model (Sum.elim values assignment) Sum.inr atom).mp single
  · intro held
    refine ⟨Fin.elim0, ?_⟩
    intro actual member
    have same : actual = atom.rename Sum.inr := List.mem_singleton.mp member
    subst actual
    exact (Atom.holds_rename model (Sum.elim Fin.elim0 assignment) Sum.inr atom).mpr held

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

private theorem combine_left (model : Model) (assignment : α → Comp model)
    (left : Fin a → Comp model) (right : Fin b → Comp model) :
    Sum.elim (Fin.addCases left right) assignment ∘ leftName a b = Sum.elim left assignment := by
  funext index
  cases index <;> simp [leftName]

private theorem combine_right (model : Model) (assignment : α → Comp model)
    (left : Fin a → Comp model) (right : Fin b → Comp model) :
    Sum.elim (Fin.addCases left right) assignment ∘ rightName a b = Sum.elim right assignment := by
  funext index
  cases index <;> simp [rightName]

private theorem restrict_left (model : Model) (assignment : α → Comp model)
    (values : Fin (a + b) → Comp model) :
    Sum.elim values assignment ∘ leftName a b =
      Sum.elim (fun index => values (Fin.castAdd b index)) assignment := by
  funext index
  cases index <;> rfl

private theorem restrict_right (model : Model) (assignment : α → Comp model)
    (values : Fin (a + b) → Comp model) :
    Sum.elim values assignment ∘ rightName a b =
      Sum.elim (fun index => values (Fin.natAdd a index)) assignment := by
  funext index
  cases index <;> rfl

@[simp] theorem Clause.holds_combine (model : Model) (assignment : α → Comp model)
    (left right : Clause α) :
    (left.combine right).Satisfiable model assignment ↔
      left.Satisfiable model assignment ∧ right.Satisfiable model assignment := by
  simp only [Clause.combine, Clause.Satisfiable, Clause.Holds, all_append, all_rename]
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

private theorem close_values (model : Model) (assignment : α → Comp model)
    (values : Fin n → Comp model) (fresh : Comp model) :
    Sum.elim (Fin.lastCases fresh values) assignment ∘ closeName n =
      Sum.elim values (extend assignment fresh) := by
  funext index
  cases index with
  | inl index => simp [closeName]
  | inr index => cases index <;> simp [closeName, extend]

private theorem restrict_close (model : Model) (assignment : α → Comp model)
    (values : Fin (n + 1) → Comp model) :
    Sum.elim values assignment ∘ closeName n =
      Sum.elim (fun index => values index.castSucc)
        (extend assignment (values (Fin.last n))) := by
  funext index
  cases index with
  | inl => rfl
  | inr index => cases index <;> rfl

@[simp] theorem Clause.holds_close (model : Model) (assignment : α → Comp model)
    (clause : Clause (Option α)) :
    clause.close.Satisfiable model assignment ↔
      ∃ fresh, clause.Satisfiable model (extend assignment fresh) := by
  simp only [Clause.close, Clause.Satisfiable, Clause.Holds, all_rename]
  constructor
  · rintro ⟨values, held⟩
    exact ⟨values (Fin.last clause.locals), (fun index => values index.castSucc),
      by simpa only [restrict_close] using held⟩
  · rintro ⟨fresh, values, held⟩
    exact ⟨Fin.lastCases fresh values, by simpa only [close_values] using held⟩

/-- Structural recursion constructs the finite alternatives. No type or row
assignment is consulted by this normalization. -/
def normalise : Formula α → List (Clause α)
  | .top => [.empty]
  | .bot => []
  | .and left right =>
      (normalise left).flatMap fun a => (normalise right).map a.combine
  | .or left right => normalise left ++ normalise right
  | .tyLe left right => [.singleton (.tyLe left right)]
  | .rowLe left right => [.singleton (.rowLe left right)]
  | .existsSlot formula => (normalise formula).map Clause.close

/-- Exactness includes all original existentials, disjunctions, and rows. -/
theorem normalise_exact (model : Model) (assignment : α → Comp model) (formula : Formula α) :
    (∃ clause ∈ normalise formula, clause.Satisfiable model assignment) ↔
      formula.Holds model assignment := by
  induction formula with
  | top => simp [normalise, Formula.Holds]
  | bot => simp [normalise, Formula.Holds]
  | tyLe left right => simp [normalise, Formula.Holds, Atom.Holds]
  | rowLe left right => simp [normalise, Formula.Holds, Atom.Holds]
  | and left right ihLeft ihRight =>
      simp only [normalise, List.mem_flatMap, List.mem_map, Formula.Holds]
      constructor
      · rintro ⟨_, ⟨a, ma, b, mb, rfl⟩, held⟩
        obtain ⟨ha, hb⟩ := (Clause.holds_combine model assignment a b).mp held
        exact ⟨(ihLeft assignment).mp ⟨a, ma, ha⟩, (ihRight assignment).mp ⟨b, mb, hb⟩⟩
      · rintro ⟨ha, hb⟩
        obtain ⟨a, ma, ha⟩ := (ihLeft assignment).mpr ha
        obtain ⟨b, mb, hb⟩ := (ihRight assignment).mpr hb
        exact ⟨a.combine b, ⟨a, ma, b, mb, rfl⟩,
          (Clause.holds_combine model assignment a b).mpr ⟨ha, hb⟩⟩
  | or left right ihLeft ihRight =>
      simp only [normalise, List.mem_append, Formula.Holds]
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
      simp only [normalise, List.mem_map, Formula.Holds]
      constructor
      · rintro ⟨_, ⟨clause, member, rfl⟩, held⟩
        obtain ⟨fresh, held⟩ := (Clause.holds_close model assignment clause).mp held
        exact ⟨fresh, (ih _).mp ⟨clause, member, held⟩⟩
      · rintro ⟨fresh, held⟩
        obtain ⟨clause, member, held⟩ := (ih _).mpr held
        exact ⟨clause.close, ⟨clause, member, rfl⟩,
          (Clause.holds_close model assignment clause).mpr ⟨fresh, held⟩⟩

/-- Every presence formula and every free computation environment, in every
extended model. Quantifiers remain only in this semantic theorem: the computed
clauses contain finite atomic constraints. This is exact normalization, not
elimination of the atoms by a solver. -/
theorem presence_normalise_exact (model : Model) (formula : Formula α)
    (assignment : α → Comp model) :
    formula.Holds model assignment ↔
      ∃ clause ∈ normalise formula,
        ∃ localValues : Fin clause.locals → Comp model,
          clause.Holds model assignment localValues :=
  (normalise_exact model assignment formula).symm

/-- Every existing source expression, including lambdas, applications, and
value-restricted lets, has exactly the computed finite clause semantics. -/
theorem principal_clauses_exact (model : Model) (expression : Expr)
    (schemes : SchemeEnv α) (bindings : List (Binding model))
    (assignment : α → Comp model) (environment : EnvRel model assignment schemes bindings)
    (result : Comp model) :
    (∃ clause ∈ normalise (principal schemes expression),
      clause.Satisfiable model (extend assignment result)) ↔ Typing model bindings expression result :=
  (normalise_exact model (extend assignment result) (principal schemes expression)).trans
    (principal_exact model expression schemes bindings assignment environment result)

def resultName (locals : Nat) : Fin locals ⊕ Option Empty → Fin (locals + 1)
  | .inl index => index.castSucc
  | .inr none => Fin.last locals
  | .inr (some impossible) => nomatch impossible

/-- A closed source clause uses only finite numeric slots. Its final slot
is the observed result; its earlier slots are the original existentials. -/
def Clause.pack (clause : Clause (Option Empty)) : List (Atom (Fin (clause.locals + 1))) :=
  clause.atoms.map (Atom.rename (resultName clause.locals))

theorem Clause.pack_exact (model : Model) (clause : Clause (Option Empty))
    (result : Comp model) :
    clause.Satisfiable model (extend Empty.elim result) ↔
      ∃ assignment : Fin (clause.locals + 1) → Comp model,
        assignment (Fin.last clause.locals) = result ∧ All model assignment clause.pack := by
  constructor
  · rintro ⟨localValues, held⟩
    refine ⟨Fin.lastCases result localValues, Fin.lastCases_last, ?_⟩
    rw [Clause.pack, all_rename]
    have same : Fin.lastCases result localValues ∘ resultName clause.locals =
        Sum.elim localValues (extend Empty.elim result) := by
      funext name
      cases name with
      | inl index => simp [resultName]
      | inr name =>
          cases name with
          | none => simp [resultName, extend]
          | some impossible => exact impossible.elim
    rw [same]
    exact held
  · rintro ⟨assignment, resultEqual, held⟩
    refine ⟨fun index => assignment index.castSucc, ?_⟩
    rw [Clause.pack, all_rename] at held
    have same : assignment ∘ resultName clause.locals =
        Sum.elim (fun index => assignment index.castSucc) (extend Empty.elim result) := by
      funext name
      cases name with
      | inl => rfl
      | inr name =>
          cases name with
          | none => exact resultEqual
          | some impossible => exact impossible.elim
    rw [same] at held
    exact held

/-- The original closed source judgment is exactly a finite alternative of
conjunctive graph-facing obligations. Value and row slots remain paired. -/
theorem closed_source_exact (model : Model) (expression : Expr) (result : Comp model) :
    Typing model [] expression result ↔
      ∃ clause ∈ normalise (principal ([] : SchemeEnv Empty) expression),
        ∃ assignment : Fin (clause.locals + 1) → Comp model,
          assignment (Fin.last clause.locals) = result ∧ All model assignment clause.pack := by
  rw [← principal_clauses_exact model expression ([] : SchemeEnv Empty) [] Empty.elim
    (by intro index value; simp [SchemeLookup, BindingLookup]) result]
  exact exists_congr fun clause => and_congr_right fun _ => clause.pack_exact model result

/-- Normalization also preserves the actual Core lowering and its captured
environment. Terms outside the declared fragment generate false rather than
being replaced by the decoder's default literal. -/
theorem principalCore_clauses_exact (model : Model) (expression : Core.Required.Term)
    (schemes : SchemeEnv α) (bindings : List (Binding model))
    (assignment : α → Comp model) (environment : EnvRel model assignment schemes bindings)
    (result : Comp model) :
    (∃ clause ∈ normalise (CoreRules.principalCore schemes expression),
      clause.Satisfiable model (extend assignment result)) ↔
        Core.Typing (CoreRules.model model) (bindings.map CoreRules.binding) expression result :=
  (normalise_exact model (extend assignment result) (CoreRules.principalCore schemes expression)).trans
    (CoreRules.principalCore_exact model expression schemes bindings assignment environment result)

/-- Every closed Core term and every result computation, without a support
check or inference-success premise. The result is an exact finite clause
interface; its atomic constraints have not been solved by this theorem. -/
theorem closed_core_exact (model : Model) (expression : Core.Required.Term) (result : Comp model) :
    Core.Typing (CoreRules.model model) [] expression result ↔
      ∃ clause ∈ normalise (CoreRules.principalCore ([] : SchemeEnv Empty) expression),
        ∃ assignment : Fin (clause.locals + 1) → Comp model,
          assignment (Fin.last clause.locals) = result ∧ All model assignment clause.pack := by
  have normalized := principalCore_clauses_exact model expression ([] : SchemeEnv Empty) [] Empty.elim
    (EnvRel.nil model Empty.elim) result
  simp only [List.map_nil] at normalized
  exact normalized.symm.trans
    (exists_congr fun clause => and_congr_right fun _ => clause.pack_exact model result)

end Yulang.PresenceNormalForm
