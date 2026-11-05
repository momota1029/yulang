import Yulang.Inference

/-!
# Finite simultaneous recursive constraint checking

This layer checks a resolved finite recursive block. All members see the same
assumption context: an unannotated member has one shared monotype, while a full
annotation supplies a value-polymorphic signature to every member. A definition
with an annotation is checked for every assignment of its annotation variables.
Rows written inside the annotation refer to captured slots, never those local
value variables. The generated constraint is finite data; no solver success or
body typability is assumed by its exactness theorem.

The input interface distinguishes local slots from captured environment/weak
slots. This is not a solver computing free-variable sets, a parser elaboration,
an SCC discovery algorithm, or an evaluation-order check. Evaluation dependencies
and computed-value cycles are checked separately.

Source: spec/04-types.md §4.7, decisions 12–13 in
notes/handoff/2026-11-05-lean-proof-handoff.md.
-/

namespace Yulang.RecursiveInference

open Inference

def manyEnv (ρ : α → Comp m) (locals : Fin n → Comp m) : Fin n ⊕ α → Comp m :=
  Sum.elim locals ρ

def typeEnv (m : Model) (ρ : α → Comp m) (locals : Fin n → m.Ty) : Fin n ⊕ α → Comp m :=
  manyEnv ρ (fun i => Comp.pure m (locals i))

@[simp] theorem manyEnv_inl (ρ : α → Comp m) (locals : Fin n → Comp m) (i : Fin n) :
    manyEnv ρ locals (.inl i) = locals i := rfl

@[simp] theorem manyEnv_inr (ρ : α → Comp m) (locals : Fin n → Comp m) (a : α) :
    manyEnv ρ locals (.inr a) = ρ a := rfl

@[simp] theorem typeEnv_inr (m : Model) (ρ : α → Comp m) (locals : Fin n → m.Ty) (a : α) :
    typeEnv m ρ locals (.inr a) = ρ a := rfl

def popSlot : Fin (n + 1) ⊕ α → Fin n ⊕ Option α
  | .inl i => Fin.cases (.inr none) (fun j => .inl j) i
  | .inr a => .inr (some a)

theorem manyEnv_popSlot (ρ : α → Comp m) (first : Comp m) (rest : Fin n → Comp m) :
    manyEnv (extend ρ first) rest ∘ popSlot = manyEnv ρ (Fin.cases first rest) := by
  funext x
  cases x with
  | inl i => cases i using Fin.cases <;> rfl
  | inr a => rfl

/-- Close a finite group of computation slots with the existing first-order
existential binder. These slots are allocated once for the whole block. -/
def existsMany : (n : Nat) → Formula (Fin n ⊕ α) → Formula α
  | 0, p => p.rename (Sum.elim (fun i => Fin.elim0 i) id)
  | n + 1, p => .existsSlot (existsMany n (p.rename popSlot))

theorem existsMany_holds (m : Model) (n : Nat) (p : Formula (Fin n ⊕ α))
    (ρ : α → Comp m) :
    (existsMany n p).Holds m ρ ↔ ∃ locals, p.Holds m (manyEnv ρ locals) := by
  induction n generalizing α with
  | zero =>
    simp only [existsMany, Formula.holds_rename]
    constructor
    · intro h
      refine ⟨(fun i => Fin.elim0 i), ?_⟩
      have he : manyEnv ρ (fun i : Fin 0 => Fin.elim0 i) =
          ρ ∘ Sum.elim (fun i => Fin.elim0 i) id := by
        funext x
        cases x with
        | inl i => exact Fin.elim0 i
        | inr a => rfl
      rw [he]
      exact h
    · rintro ⟨locals, h⟩
      have he : manyEnv ρ locals = ρ ∘ Sum.elim (fun i => Fin.elim0 i) id := by
        funext x
        cases x with
        | inl i => exact Fin.elim0 i
        | inr a => rfl
      rw [← he]
      exact h
  | succ n ih =>
    simp only [existsMany, Formula.Holds, ih, Formula.holds_rename, manyEnv_popSlot]
    constructor
    · rintro ⟨first, rest, h⟩
      exact ⟨Fin.cases first rest, h⟩
    · rintro ⟨locals, h⟩
      refine ⟨locals 0, (fun i => locals i.succ), ?_⟩
      have he : Fin.cases (locals 0) (fun i => locals i.succ) = locals := by
        funext i
        cases i using Fin.cases <;> rfl
      simpa only [he] using h

/-- Local annotation variables have value kind. A row variable must name a
captured slot, including the shared rows inferred for the recursive block. -/
def rowCaptured : RowTerm (Fin n ⊕ α) → Bool
  | .var (.inl _) => false
  | .var (.inr _) => true
  | .empty => true
  | .join a b => rowCaptured a && rowCaptured b

def rowsCaptured : TyTerm (Fin n ⊕ α) → Bool
  | .var _ | .base _ | .bottom | .emptyRecord => true
  | .union a b | .inter a b | .pair a b => rowsCaptured a && rowsCaptured b
  | .record _ a b => rowsCaptured a && rowsCaptured b
  | .variant _ a => rowsCaptured a
  | .arrow a ea b eb => rowsCaptured a && rowCaptured ea && rowsCaptured b && rowCaptured eb

theorem captured_row_ignores_local_rows (m : Model) (ρ : α → Comp m)
    (locals : Fin n → Comp m) (r : RowTerm (Fin n ⊕ α)) (captured : rowCaptured r = true) :
    r.eval m (manyEnv ρ locals) = r.eval m (typeEnv m ρ (fun i => (locals i).1)) := by
  induction r with
  | var x =>
    cases x with
    | inl i => simp [rowCaptured] at captured
    | inr a => rfl
  | empty => rfl
  | join a b iha ihb =>
    simp only [rowCaptured, Bool.and_eq_true] at captured
    simp only [RowTerm.eval, iha captured.1, ihb captured.2]

theorem captured_type_ignores_local_rows (m : Model) (ρ : α → Comp m)
    (locals : Fin n → Comp m) (t : TyTerm (Fin n ⊕ α)) (captured : rowsCaptured t = true) :
    t.eval m (manyEnv ρ locals) = t.eval m (typeEnv m ρ (fun i => (locals i).1)) := by
  induction t with
  | var x => cases x <;> rfl
  | base _ | bottom | emptyRecord => rfl
  | union a b iha ihb | inter a b iha ihb | pair a b iha ihb | record _ a b iha ihb =>
    simp only [rowsCaptured, Bool.and_eq_true] at captured
    simp only [TyTerm.eval, iha captured.1, ihb captured.2]
  | variant l a ih => exact congrArg (m.variant l) (ih captured)
  | arrow a ea b eb iha ihb =>
    simp only [rowsCaptured, Bool.and_eq_true] at captured
    rcases captured with ⟨⟨⟨ha, hea⟩, hb⟩, heb⟩
    simp only [TyTerm.eval, iha ha, ihb hb,
      captured_row_ignores_local_rows m ρ locals ea hea,
      captured_row_ignores_local_rows m ρ locals eb heb]

def functionShape : TyTerm α → Bool
  | .arrow _ _ _ _ => true
  | _ => false

/-- A resolved, complete function value-type annotation. There is no hole
constructor. Its finite local names are declared value-type parameters; every
standalone effect-row slot is captured. Recognizing source annotation coverage
and resolving nominal types are outside this core representation. -/
structure FullAnnotation (α : Type) (n : Nat) where
  type : TyTerm (Fin n ⊕ α)
  function : functionShape type = true
  captured : rowsCaptured type = true

def FullAnnotation.eval (annotation : FullAnnotation α n) (m : Model)
    (ρ : α → Comp m) (locals : Fin n → m.Ty) : m.Ty :=
  annotation.type.eval m (typeEnv m ρ locals)

def FullAnnotation.scheme (annotation : FullAnnotation α n) : Scheme α :=
  existsMany n (Formula.compLe
    (CompTerm.pure (annotation.type.rename (Sum.map id some)))
    (CompTerm.var (.inr none)))

theorem manyEnv_skip_result (ρ : α → Comp m) (c : Comp m) (locals : Fin n → Comp m) :
    manyEnv (extend ρ c) locals ∘ Sum.map id some = manyEnv ρ locals := by
  funext x
  cases x <;> rfl

theorem FullAnnotation.scheme_instances (annotation : FullAnnotation α n)
    (m : Model) (ρ : α → Comp m) (c : Comp m) :
    annotation.scheme.Holds m (extend ρ c) ↔
      ∃ locals, Comp.le m (Comp.pure m (annotation.eval m ρ locals)) c := by
  simp only [scheme, existsMany_holds, Formula.holds_compLe, CompTerm.eval_pure,
    TyTerm.eval_rename, manyEnv_skip_result, CompTerm.eval_var, manyEnv_inr, extend_none]
  constructor
  · rintro ⟨locals, h⟩
    refine ⟨(fun i => (locals i).1), ?_⟩
    simpa only [eval, captured_type_ignores_local_rows m ρ locals annotation.type annotation.captured]
      using h
  · rintro ⟨locals, h⟩
    exact ⟨(fun i => Comp.pure m (locals i)), h⟩

theorem FullAnnotation.scheme_related (annotation : FullAnnotation α n)
    (m : Model) (ρ : α → Comp m) (c : Comp m) :
    annotation.scheme.Holds m (extend ρ c) ↔
      BindingTyping m (.signature n (fun locals => Comp.pure m (annotation.eval m ρ locals))) c := by
  rw [annotation.scheme_instances, BindingTyping.signature_iff]

/-- A slot belongs to the entire recursive block, not to a use of its member.
The annotated alternative carries all value-type information of the function. -/
inductive Declaration (α : Type) where
  | inferred (slot : α) (body : Expr)
  | annotated (parameters : Nat) (annotation : FullAnnotation α parameters) (body : Expr)

def Declaration.body : Declaration α → Expr
  | .inferred _ body | .annotated _ _ body => body

def Declaration.assumption : Declaration α → Scheme α
  | .inferred slot _ => Scheme.mono (CompTerm.pure (.var slot))
  | .annotated _ annotation _ => annotation.scheme

def Declaration.binding (m : Model) (ρ : α → Comp m) : Declaration α → Binding m
  | .inferred slot _ => .mono (Comp.pure m (ρ slot).1)
  | .annotated n annotation _ =>
      .signature n (fun locals => Comp.pure m (annotation.eval m ρ locals))

theorem Declaration.assumption_related (declaration : Declaration α) (m : Model)
    (ρ : α → Comp m) (c : Comp m) :
    declaration.assumption.Holds m (extend ρ c) ↔
      BindingTyping m (declaration.binding m ρ) c := by
  cases declaration with
  | inferred slot body => simp [assumption, binding, CompTerm.pure, CompTerm.eval,
      TyTerm.eval, RowTerm.eval, Comp.pure]
  | annotated n annotation body => exact annotation.scheme_related m ρ c

def assumptions (members : List (Declaration α)) (Γ : SchemeEnv α) : SchemeEnv α :=
  members.map Declaration.assumption ++ Γ

def bindings (m : Model) (ρ : α → Comp m) (members : List (Declaration α))
    (Γ : List (Binding m)) : List (Binding m) :=
  members.map (Declaration.binding m ρ) ++ Γ

theorem assumptions_related (m : Model) (ρ : α → Comp m) (members : List (Declaration α))
    (sΓ : SchemeEnv α) (Γ : List (Binding m)) (henv : EnvRel m ρ sΓ Γ) :
    EnvRel m ρ (assumptions members sΓ) (bindings m ρ members Γ) := by
  induction members with
  | nil => exact henv
  | cons declaration rest ih =>
    exact ih.cons (declaration.assumption_related m ρ)

/-- Universal annotation checks and existential block slots are kept separate.
Calls use the finite existential scheme above; a definition is checked at every
annotation instance rather than at a convenient chosen instance. -/
inductive Constraint : Type → Type 1 where
  | core : Formula α → Constraint α
  | and : Constraint α → Constraint α → Constraint α
  | forallTypes (n : Nat) : Constraint (Fin n ⊕ α) → Constraint α
  | existsSlots (n : Nat) : Constraint (Fin n ⊕ α) → Constraint α

def Constraint.Holds (m : Model) : {α : Type} → (α → Comp m) → Constraint α → Prop
  | _, ρ, .core p => p.Holds m ρ
  | _, ρ, .and p q => p.Holds m ρ ∧ q.Holds m ρ
  | _, ρ, .forallTypes _ p => ∀ locals, p.Holds m (typeEnv m ρ locals)
  | _, ρ, .existsSlots _ p => ∃ locals, p.Holds m (manyEnv ρ locals)

def checkDeclaration (Γ : SchemeEnv α) : Declaration α → Constraint α
  | .inferred slot body => .core (generate Γ body (CompTerm.var slot))
  | .annotated n annotation body => .forallTypes n
      (.core (generate (Γ.rename Sum.inr) body (CompTerm.pure annotation.type)))

/-- Independent simultaneous declaration checking. Its recursive assumptions
are supplied by the caller; this judgement never mentions generated formulas. -/
inductive DefinitionTyping (m : Model) (Γ : List (Binding m)) (ρ : α → Comp m) :
    Declaration α → Prop where
  | inferred : Typing m Γ body (ρ slot) → DefinitionTyping m Γ ρ (.inferred slot body)
  | annotated : (∀ locals, Typing m Γ body (Comp.pure m (annotation.eval m ρ locals))) →
      DefinitionTyping m Γ ρ (.annotated n annotation body)

@[simp] theorem DefinitionTyping.inferred_iff (m : Model) (Γ : List (Binding m))
    (ρ : α → Comp m) (slot : α) (body : Expr) :
    DefinitionTyping m Γ ρ (.inferred slot body) ↔ Typing m Γ body (ρ slot) := by
  constructor
  · intro h; cases h with | inferred ht => exact ht
  · exact DefinitionTyping.inferred

@[simp] theorem DefinitionTyping.annotated_iff (m : Model) (Γ : List (Binding m))
    (ρ : α → Comp m) (n : Nat) (annotation : FullAnnotation α n) (body : Expr) :
    DefinitionTyping m Γ ρ (.annotated n annotation body) ↔
      ∀ locals, Typing m Γ body (Comp.pure m (annotation.eval m ρ locals)) := by
  constructor
  · intro h; cases h with | annotated ht => exact ht
  · exact DefinitionTyping.annotated

theorem checkDeclaration_exact (m : Model) (ρ : α → Comp m) (sΓ : SchemeEnv α)
    (Γ : List (Binding m)) (henv : EnvRel m ρ sΓ Γ) (declaration : Declaration α) :
    (checkDeclaration sΓ declaration).Holds m ρ ↔ DefinitionTyping m Γ ρ declaration := by
  cases declaration with
  | inferred slot body =>
    simpa only [checkDeclaration, Constraint.Holds, DefinitionTyping.inferred_iff,
      CompTerm.eval_var] using generate_models_iff_typing m body sΓ Γ ρ (CompTerm.var slot) henv
  | annotated n annotation body =>
    simp only [checkDeclaration, Constraint.Holds, DefinitionTyping.annotated_iff]
    apply forall_congr'
    intro locals
    simpa only [CompTerm.eval_pure, FullAnnotation.eval] using
      generate_models_iff_typing m body (sΓ.rename Sum.inr) Γ (typeEnv m ρ locals)
        (CompTerm.pure annotation.type) (henv.rename Sum.inr _ rfl)

def checkBodies (Γ : SchemeEnv α) : List (Declaration α) → Constraint α
  | [] => .core .top
  | member :: rest => .and (checkDeclaration Γ member) (checkBodies Γ rest)

theorem checkBodies_exact (m : Model) (ρ : α → Comp m) (sΓ : SchemeEnv α)
    (Γ : List (Binding m)) (henv : EnvRel m ρ sΓ Γ) (members : List (Declaration α)) :
    (checkBodies sΓ members).Holds m ρ ↔ ∀ member ∈ members, DefinitionTyping m Γ ρ member := by
  induction members with
  | nil => simp [checkBodies, Constraint.Holds, Formula.Holds]
  | cons member rest ih =>
    simp only [checkBodies, Constraint.Holds, checkDeclaration_exact m ρ sΓ Γ henv, ih]
    simp

/-- Each body is checked against the SAME recursive assumption context. -/
def generateSCC (Γ : SchemeEnv α) (members : List (Declaration α)) : Constraint α :=
  checkBodies (assumptions members Γ) members

def SCCTyping (m : Model) (Γ : List (Binding m)) (ρ : α → Comp m)
    (members : List (Declaration α)) : Prop :=
  ∀ member ∈ members, DefinitionTyping m (bindings m ρ members Γ) ρ member

/-- Exactness for every finite resolved block and arbitrary model. No premise
assumes a block body typable, or assumes that a constraint solver succeeds. -/
theorem generateSCC_exact (m : Model) (ρ : α → Comp m) (sΓ : SchemeEnv α)
    (Γ : List (Binding m)) (henv : EnvRel m ρ sΓ Γ) (members : List (Declaration α)) :
    (generateSCC sΓ members).Holds m ρ ↔ SCCTyping m Γ ρ members :=
  checkBodies_exact m ρ (assumptions members sΓ) (bindings m ρ members Γ)
    (assumptions_related m ρ members sΓ Γ henv) members

/-- Allocate all local slots outside the body checks, so they are shared
throughout the SCC and chosen only once for each solution of the block. -/
def closeSCC (Γ : SchemeEnv α) (members : List (Declaration (Fin n ⊕ α))) : Constraint α :=
  .existsSlots n (generateSCC (Γ.rename Sum.inr) members)

theorem closeSCC_exact (m : Model) (ρ : α → Comp m) (sΓ : SchemeEnv α)
    (Γ : List (Binding m)) (henv : EnvRel m ρ sΓ Γ)
    (members : List (Declaration (Fin n ⊕ α))) :
    (closeSCC sΓ members).Holds m ρ ↔
      ∃ slots, SCCTyping m Γ (manyEnv ρ slots) members := by
  simp only [closeSCC, Constraint.Holds]
  apply exists_congr
  intro slots
  exact generateSCC_exact m (manyEnv ρ slots) (sΓ.rename Sum.inr) Γ
    (henv.rename Sum.inr _ rfl) members

/-- The standard unannotated allocation gives every member its own slot.
Different uses still refer to that one slot, rather than freshening it. -/
def unannotatedMembers (bodies : Fin n → Expr) : List (Declaration (Fin n ⊕ α)) :=
  List.ofFn (fun i => .inferred (.inl i) (bodies i))

def inferUnannotatedSCC (Γ : SchemeEnv α) (bodies : Fin n → Expr) : Constraint α :=
  closeSCC Γ (unannotatedMembers bodies)

theorem inferUnannotatedSCC_exact (m : Model) (ρ : α → Comp m) (sΓ : SchemeEnv α)
    (Γ : List (Binding m)) (henv : EnvRel m ρ sΓ Γ) (bodies : Fin n → Expr) :
    (inferUnannotatedSCC sΓ bodies).Holds m ρ ↔
      ∃ slots, SCCTyping m Γ (manyEnv ρ slots) (unannotatedMembers bodies) :=
  closeSCC_exact m ρ sΓ Γ henv (unannotatedMembers bodies)

end Yulang.RecursiveInference
