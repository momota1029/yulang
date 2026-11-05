import Yulang.QualifiedInference

/-!
# Checked qualified generalization with shared ambient slots

The finite local interface is explicit. Raw method obligations are partitioned
automatically: a predicate mentioning a local slot is lifted into the scheme;
captured-only and concrete predicates stay pending in the enclosing module.
Mixed predicates may mention ambient slots, but those slots are never quantified.

The RHS is checked under abstract dictionaries, universally over local types.
No global impl is required merely to define a qualified value. Instantiation
requires real evidence. Inferring the finite interface from an unsolved subtype
graph, nested source elaboration and an all-language solver remain separate.
-/

namespace Yulang.QualifiedInference

open Inference RoleConstraints
open EffectInference (localEnv localEnv_comp_inl localEnv_map)

def rowUsesLocal : RowTerm (α ⊕ β) → Bool
  | .var (.inl _) | .empty => false
  | .var (.inr _) => true
  | .join a b => rowUsesLocal a || rowUsesLocal b

def typeUsesLocal : TyTerm (α ⊕ β) → Bool
  | .var (.inl _) | .base _ | .bottom | .emptyRecord => false
  | .var (.inr _) => true
  | .union a b | .inter a b | .pair a b | .record _ a b =>
      typeUsesLocal a || typeUsesLocal b
  | .variant _ a => typeUsesLocal a
  | .arrow a ea b eb =>
      typeUsesLocal a || rowUsesLocal ea || typeUsesLocal b || rowUsesLocal eb

def goalUsesLocal (goal : Goal (α ⊕ β)) : Bool := goal.args.any typeUsesLocal

theorem row_eval_capture (m : Model) (ρ η : α ⊕ β → Comp m)
    (agree : ∀ a, ρ (.inl a) = η (.inl a)) (r : RowTerm (α ⊕ β))
    (absent : rowUsesLocal r = false) : r.eval m ρ = r.eval m η := by
  induction r with
  | var x =>
      cases x with
      | inl a => exact congrArg Prod.snd (agree a)
      | inr b => simp [rowUsesLocal] at absent
  | empty => rfl
  | join a b iha ihb =>
      simp only [rowUsesLocal, Bool.or_eq_false_iff] at absent
      simp [RowTerm.eval, iha absent.1, ihb absent.2]

theorem type_eval_capture (m : Model) (ρ η : α ⊕ β → Comp m)
    (agree : ∀ a, ρ (.inl a) = η (.inl a)) (t : TyTerm (α ⊕ β))
    (absent : typeUsesLocal t = false) : t.eval m ρ = t.eval m η := by
  induction t with
  | var x =>
      cases x with
      | inl a => exact congrArg Prod.fst (agree a)
      | inr b => simp [typeUsesLocal] at absent
  | base _ | bottom | emptyRecord => rfl
  | union a b iha ihb | inter a b iha ihb | pair a b iha ihb | record _ a b iha ihb =>
      simp only [typeUsesLocal, Bool.or_eq_false_iff] at absent
      simp [TyTerm.eval, iha absent.1, ihb absent.2]
  | variant _ a ih => exact congrArg _ (ih absent)
  | arrow a ea b eb iha ihb =>
      simp only [typeUsesLocal, Bool.or_eq_false_iff] at absent
      rcases absent with ⟨⟨⟨ha, hea⟩, hb⟩, heb⟩
      simp [TyTerm.eval, iha ha, ihb hb, row_eval_capture m ρ η agree ea hea,
        row_eval_capture m ρ η agree eb heb]

/-- The fallback for a local variable is unobservable on a residual goal. -/
def dropLocal : α ⊕ β → CompTerm α
  | .inl a => CompTerm.var a
  | .inr _ => CompTerm.pure .bottom

def lowerGoal (goal : Goal (α ⊕ β)) : Goal α := goal.subst dropLocal

theorem lowerGoal_exact (m : Model) (ρ : α → Comp m) (ι : Fin n → m.Ty)
    (goal : Goal (α ⊕ Fin n)) (absent : goalUsesLocal goal = false) :
    (lowerGoal goal).eval m ρ = goal.eval m (localEnv m ρ ι) := by
  rw [lowerGoal, Goal.eval_subst]
  apply congrArg (Predicate.mk goal.role)
  apply List.map_congr_left
  intro t ht
  apply type_eval_capture m (fun x => (dropLocal x).eval m ρ) (localEnv m ρ ι)
    (fun _ => rfl) t
  simpa using (List.any_eq_false.mp absent) t ht

def qualifiers (goals : List (Goal (α ⊕ Fin n))) : List (Goal (α ⊕ Fin n)) :=
  goals.filter goalUsesLocal

def pending (goals : List (Goal (α ⊕ Fin n))) : List (Goal α) :=
  (goals.filter (fun goal => !goalUsesLocal goal)).map lowerGoal

/-- The partition preserves every role obligation at every substitution. -/
theorem partition_exact (m : Model) (theory : Theory m) (ρ : α → Comp m)
    (ι : Fin n → m.Ty) (goals : List (Goal (α ⊕ Fin n))) :
    Satisfies theory (goals.map (Goal.eval m (localEnv m ρ ι))) ↔
      Satisfies theory ((pending goals).map (Goal.eval m ρ)) ∧
      Satisfies theory ((qualifiers goals).map (Goal.eval m (localEnv m ρ ι))) := by
  constructor
  · intro all
    constructor
    · intro goal member
      obtain ⟨lowered, hl, rfl⟩ := List.mem_map.mp member
      obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hl
      have hm := List.mem_filter.mp ho
      have absent : goalUsesLocal original = false := by simpa using hm.2
      rw [lowerGoal_exact m ρ ι original absent]
      exact all _ (List.mem_map.mpr ⟨original, hm.1, rfl⟩)
    · intro goal member
      obtain ⟨original, ho, rfl⟩ := List.mem_map.mp member
      exact all _ (List.mem_map.mpr ⟨original, (List.mem_filter.mp ho).1, rfl⟩)
  · rintro ⟨shared, lifted⟩ goal member
    obtain ⟨original, ho, rfl⟩ := List.mem_map.mp member
    cases h : goalUsesLocal original with
    | true => exact lifted _ (List.mem_map.mpr ⟨original, List.mem_filter.mpr ⟨ho, h⟩, rfl⟩)
    | false =>
        rw [← lowerGoal_exact m ρ ι original h]
        exact shared _ (List.mem_map.mpr ⟨lowerGoal original,
          List.mem_map.mpr ⟨original, List.mem_filter.mpr ⟨ho, by simp [h]⟩, rfl⟩, rfl⟩)

theorem captured_obligation_retained (goals : List (Goal (α ⊕ Fin n)))
    (goal : Goal (α ⊕ Fin n)) (member : goal ∈ goals) (absent : goalUsesLocal goal = false) :
    lowerGoal goal ∈ pending goals :=
  List.mem_map.mpr ⟨goal, List.mem_filter.mpr ⟨member, by simp [absent]⟩, rfl⟩

/-- The input is a resolved finite inference interface, not a public source
annotation. Raw obligations are split by `qualifiers` and `pending`. -/
structure Interface (α : Type) (n : Nat) where
  value : TyTerm (α ⊕ Fin n)
  obligations : List (Goal (α ⊕ Fin n))

def Interface.scheme (interface : Interface α n) : Scheme α :=
  .existsTypes n (
    .and (Formula.roles ((qualifiers interface.obligations).map (Goal.rename (Sum.map some id))))
      (Formula.compLe (CompTerm.pure (interface.value.rename (Sum.map some id)))
        (CompTerm.var (.inl none))))

def Interface.binding (m : Model) (ρ : α → Comp m) (interface : Interface α n) : Binding m :=
  .qualified n
    (fun ι => (qualifiers interface.obligations).map (Goal.eval m (localEnv m ρ ι)))
    (fun ι => Comp.pure m (interface.value.eval m (localEnv m ρ ι)))

@[simp] theorem BindingTyping.qualified_iff (m : Model) (theory : Theory m)
    (requirements : (Fin n → m.Ty) → List (Predicate m.Ty))
    (result : (Fin n → m.Ty) → Comp m) (c : Comp m) :
    BindingTyping m theory (.qualified n requirements result) c ↔
      ∃ ι, Satisfies theory (requirements ι) ∧ Comp.le m (result ι) c := by
  constructor
  · intro h; cases h with | qualified ι hr ht => exact ⟨ι, hr, ht⟩
  · rintro ⟨ι, hr, ht⟩; exact .qualified ι hr ht

theorem Interface.scheme_exact (m : Model) (theory : Theory m) (ρ : α → Comp m)
    (interface : Interface α n) (c : Comp m) :
    interface.scheme.Holds m theory (extend ρ c) ↔
      BindingTyping m theory (interface.binding m ρ) c := by
  simp only [scheme, Formula.Holds, Formula.holds_roles, Formula.holds_compLe,
    binding, BindingTyping.qualified_iff]
  apply exists_congr; intro ι
  have he : (fun x => localEnv m (extend ρ c) ι (Sum.map some id x)) = localEnv m ρ ι := by
    funext x; cases x <;> rfl
  simp only [List.map_map, Function.comp_def, Goal.eval_rename, CompTerm.eval_pure,
    TyTerm.eval_rename, CompTerm.eval_var]
  simp only [he]
  rfl

/-- Captured slots stay shared under every independent local instantiation. -/
theorem ambient_not_quantified (m : Model) (ρ : α → Comp m)
    (ι κ : Fin n → m.Ty) (a : α) :
    localEnv m ρ ι (.inl a) = ρ a ∧ localEnv m ρ κ (.inl a) = ρ a := ⟨rfl, rfl⟩

theorem captured_scheme_shared (m : Model) (theory : Theory m) (ρ : α → Comp m)
    (ι : Fin n → m.Ty) (scheme : Scheme α) (c : Comp m) :
    (scheme.rename (Option.map Sum.inl)).Holds m theory (extend (localEnv m ρ ι) c) ↔
      scheme.Holds m theory (extend ρ c) := by
  rw [Formula.holds_rename]
  have he : extend (localEnv m ρ ι) c ∘ Option.map Sum.inl = extend ρ c := by
    funext x; cases x <;> rfl
  rw [he]

def qualifiedLetConstraints (methods : MethodTable) (Γ : SchemeEnv α)
    (interface : Interface α n) (rhs body : Expr) (out : CompTerm α) : Formula α :=
  if rhs.isValue then
    .and (Formula.roles (pending interface.obligations))
      (.and (.forallTypes n (.given (qualifiers interface.obligations)
        (generate methods (Γ.rename Sum.inl) rhs (CompTerm.pure interface.value))))
        (generate methods (interface.scheme :: Γ) body out))
  else .bot

/-- This independent rule checks the definition under its dictionaries, while
uses of the stored signature must supply evidence in the caller's theory. -/
inductive QualifiedLetTyping (m : Model) (methods : MethodTable) (theory : Theory m)
    (Γ : List (Binding m)) (shared : List (Predicate m.Ty))
    (requirements : (Fin n → m.Ty) → List (Predicate m.Ty))
    (value : (Fin n → m.Ty) → m.Ty) (rhs body : Expr) (out : Comp m) : Prop where
  | intro : rhs.isValue = true → Satisfies theory shared →
      (∀ ι, Typing m methods (WithEvidence theory (requirements ι)) Γ rhs (Comp.pure m (value ι))) →
      Typing m methods theory (.qualified n requirements (fun ι => Comp.pure m (value ι)) :: Γ) body out →
      QualifiedLetTyping m methods theory Γ shared requirements value rhs body out

@[simp] theorem qualifiedLetTyping_iff (m : Model) (methods : MethodTable) (theory : Theory m)
    (Γ : List (Binding m)) (shared : List (Predicate m.Ty))
    (requirements : (Fin n → m.Ty) → List (Predicate m.Ty))
    (value : (Fin n → m.Ty) → m.Ty) (rhs body : Expr) (out : Comp m) :
    QualifiedLetTyping m methods theory Γ shared requirements value rhs body out ↔
      rhs.isValue = true ∧ Satisfies theory shared ∧
      (∀ ι, Typing m methods (WithEvidence theory (requirements ι)) Γ rhs (Comp.pure m (value ι))) ∧
      Typing m methods theory (.qualified n requirements (fun ι => Comp.pure m (value ι)) :: Γ) body out := by
  constructor
  · intro h; cases h with | intro hv hs hr hb => exact ⟨hv, hs, hr, hb⟩
  · rintro ⟨hv, hs, hr, hb⟩; exact .intro hv hs hr hb

theorem qualified_let_exact (m : Model) (methods : MethodTable) (theory : Theory m)
    (sΓ : SchemeEnv α) (Γ : List (Binding m)) (ρ : α → Comp m)
    (henv : ∀ evidence, EnvRel m evidence ρ sΓ Γ) (interface : Interface α n)
    (rhs body : Expr) (out : CompTerm α) :
    (qualifiedLetConstraints methods sΓ interface rhs body out).Holds m theory ρ ↔
      QualifiedLetTyping m methods theory Γ
        ((pending interface.obligations).map (Goal.eval m ρ))
        (fun ι => (qualifiers interface.obligations).map (Goal.eval m (localEnv m ρ ι)))
        (fun ι => interface.value.eval m (localEnv m ρ ι)) rhs body (out.eval m ρ) := by
  have hr (ι : Fin n → m.Ty) :
      (generate methods (sΓ.rename Sum.inl) rhs (CompTerm.pure interface.value)).Holds m
        (WithEvidence theory ((qualifiers interface.obligations).map (Goal.eval m (localEnv m ρ ι))))
        (localEnv m ρ ι) ↔
      Typing m methods
        (WithEvidence theory ((qualifiers interface.obligations).map (Goal.eval m (localEnv m ρ ι))))
        Γ rhs (Comp.pure m (interface.value.eval m (localEnv m ρ ι))) := by
    simpa using generate_models_iff_typing m methods _ rhs _ Γ (localEnv m ρ ι)
      (CompTerm.pure interface.value) ((henv _).rename Sum.inl _ rfl)
  have hb :
      (generate methods (interface.scheme :: sΓ) body out).Holds m theory ρ ↔
      Typing m methods theory (interface.binding m ρ :: Γ) body (out.eval m ρ) :=
    generate_models_iff_typing m methods theory body _ _ ρ out
      ((henv theory).cons (interface.scheme_exact m theory ρ))
  cases hv : rhs.isValue <;>
    simp [qualifiedLetConstraints, hv, Formula.Holds, qualifiedLetTyping_iff,
      Formula.holds_roles, hr, hb, Interface.binding]

end Yulang.QualifiedInference
