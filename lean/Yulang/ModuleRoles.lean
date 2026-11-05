import Yulang.QualifiedGeneralization

/-!
# EOF discharge and closed qualified exports

The module boundary receives the partial assignment produced by inference.
It checks every ambient slot occurring in the exported type or its obligations,
then runs the real terminating role resolver on residual predicates. Failure
never turns an unresolved weak slot into a new polymorphic parameter.

An accepted export is interpreted over its explicit generalized slots only.
The preservation theorem quantifies over every total extension of the assignment
assignment, so a default used outside the checked support cannot affect it.
This gate does not compute a structural-subtyping solution or a source module
schedule; it validates the assignment available at EOF.
-/

namespace Yulang.QualifiedInference

open Inference RoleConstraints

def rowVariables : RowTerm α → List α
  | .var a => [a]
  | .empty => []
  | .join a b => rowVariables a ++ rowVariables b

def typeVariables : TyTerm α → List α
  | .var a => [a]
  | .base _ | .bottom | .emptyRecord => []
  | .union a b | .inter a b | .pair a b | .record _ a b => typeVariables a ++ typeVariables b
  | .variant _ a => typeVariables a
  | .arrow a ea b eb => typeVariables a ++ rowVariables ea ++ typeVariables b ++ rowVariables eb

def goalVariables (goal : Goal α) : List α := goal.args.flatMap typeVariables

theorem row_eval_on_support (m : Model) (ρ η : α → Comp m) (r : RowTerm α)
    (agree : ∀ a ∈ rowVariables r, ρ a = η a) : r.eval m ρ = r.eval m η := by
  induction r with
  | var a => exact congrArg Prod.snd (agree a (by simp [rowVariables]))
  | empty => rfl
  | join a b iha ihb =>
      simp only [rowVariables, List.mem_append, or_imp, forall_and] at agree
      simp [RowTerm.eval, iha agree.1, ihb agree.2]

theorem type_eval_on_support (m : Model) (ρ η : α → Comp m) (t : TyTerm α)
    (agree : ∀ a ∈ typeVariables t, ρ a = η a) : t.eval m ρ = t.eval m η := by
  induction t with
  | var a => exact congrArg Prod.fst (agree a (by simp [typeVariables]))
  | base _ | bottom | emptyRecord => rfl
  | union a b iha ihb | inter a b iha ihb | pair a b iha ihb | record _ a b iha ihb =>
      simp only [typeVariables, List.mem_append, or_imp, forall_and] at agree
      simp [TyTerm.eval, iha agree.1, ihb agree.2]
  | variant _ a ih => exact congrArg _ (ih agree)
  | arrow a ea b eb iha ihb =>
      simp only [typeVariables, List.mem_append, or_imp, forall_and] at agree
      rcases agree with ⟨⟨⟨ha, hea⟩, hb⟩, heb⟩
      simp [TyTerm.eval, iha ha, ihb hb, row_eval_on_support m ρ η ea hea,
        row_eval_on_support m ρ η eb heb]

theorem goal_eval_on_support (m : Model) (ρ η : α → Comp m) (goal : Goal α)
    (agree : ∀ a ∈ goalVariables goal, ρ a = η a) : goal.eval m ρ = goal.eval m η := by
  apply congrArg (Predicate.mk goal.role)
  apply List.map_congr_left
  intro t ht
  exact type_eval_on_support m ρ η t (fun a ha => agree a (List.mem_flatMap.mpr ⟨t, ht, ha⟩))

def ambientVariables (variables : List (α ⊕ β)) : List α :=
  variables.filterMap (fun | .inl a => some a | .inr _ => none)

@[simp] theorem mem_ambientVariables (a : α) (variables : List (α ⊕ β)) :
    a ∈ ambientVariables variables ↔ Sum.inl a ∈ variables := by
  rw [ambientVariables, List.mem_filterMap]
  constructor
  · rintro ⟨x, member, equal⟩
    cases x with
    | inl b => simp only [Option.some.injEq] at equal; cases equal; exact member
    | inr b => cases equal
  · intro member
    exact ⟨.inl a, member, rfl⟩

def Interface.support (interface : Interface α n) : List α :=
  ambientVariables (typeVariables interface.value ++ interface.obligations.flatMap goalVariables)

def completeAssignment (m : Model) (assignment : α → Option (Comp m)) : α → Comp m :=
  fun a => (assignment a).getD (m.bottom, m.empty)

def Interface.known (interface : Interface α n) (assignment : α → Option (Comp m)) : Bool :=
  interface.support.all (fun a => (assignment a).isSome)

structure ClosedInterface (m : Model) (n : Nat) where
  value : (Fin n → Comp m) → m.Ty
  requirements : (Fin n → Comp m) → List (Predicate m.Ty)

def Interface.closeAt (m : Model) (ρ : α → Comp m) (interface : Interface α n) : ClosedInterface m n :=
  ⟨fun ι => interface.value.eval m (slotEnv ρ ι),
    fun ι => (qualifiers interface.obligations).map (Goal.eval m (slotEnv ρ ι))⟩

def pendingCheck (m : Model) (decode : m.Ty → Roles.Term) (impls : List Roles.Impl)
    (wf : Roles.WellFormed impls) (ρ : α → Comp m) (interface : Interface α n) : Bool :=
  (pending interface.obligations).all fun goal =>
    decide (Roles.resolve impls wf ((goal.eval m ρ).map decode).toGoal = .resolved)

theorem pendingCheck_exact (m : Model) (decode : m.Ty → Roles.Term) (impls : List Roles.Impl)
    (wf : Roles.WellFormed impls) (ρ : α → Comp m) (interface : Interface α n) :
    pendingCheck m decode impls wf ρ interface = true ↔
      Satisfies (resolvingTheory decode impls)
        ((pending interface.obligations).map (Goal.eval m ρ)) := by
  simp [pendingCheck, List.all_eq_true, Satisfies, resolvingTheory_iff decode impls wf]

def finishModule (m : Model) (decode : m.Ty → Roles.Term) (impls : List Roles.Impl)
    (wf : Roles.WellFormed impls) (assignment : α → Option (Comp m)) (interface : Interface α n) :
    Option (ClosedInterface m n) :=
  if interface.known assignment && pendingCheck m decode impls wf (completeAssignment m assignment) interface
  then some (interface.closeAt m (completeAssignment m assignment)) else none

theorem finishModule_exact (m : Model) (decode : m.Ty → Roles.Term) (impls : List Roles.Impl)
    (wf : Roles.WellFormed impls) (assignment : α → Option (Comp m)) (interface : Interface α n)
    (closed : ClosedInterface m n) :
    finishModule m decode impls wf assignment interface = some closed ↔
      interface.known assignment = true ∧
      Satisfies (resolvingTheory decode impls)
        ((pending interface.obligations).map (Goal.eval m (completeAssignment m assignment))) ∧
      interface.closeAt m (completeAssignment m assignment) = closed := by
  simp [finishModule, pendingCheck_exact, and_assoc]

theorem known_has_value (interface : Interface α n) (assignment : α → Option (Comp m))
    (known : interface.known assignment = true) (a : α) (member : a ∈ interface.support) :
    ∃ value, assignment a = some value :=
  Option.isSome_iff_exists.mp ((List.all_eq_true.mp known) a member)

/-- A missing ambient slot actually used in the export is an EOF error. -/
theorem finishModule_missing (m : Model) (decode : m.Ty → Roles.Term) (impls : List Roles.Impl)
    (wf : Roles.WellFormed impls) (assignment : α → Option (Comp m)) (interface : Interface α n)
    (a : α) (member : a ∈ interface.support) (missing : assignment a = none) :
    finishModule m decode impls wf assignment interface = none := by
  have notKnown : interface.known assignment = false := by
    cases h : interface.known assignment with
    | false => rfl
    | true =>
      obtain ⟨value, hv⟩ := known_has_value interface assignment h a member
      rw [missing] at hv
      cases hv
  simp [finishModule, notKnown]

theorem complete_agrees_on_support (m : Model) (assignment : α → Option (Comp m))
    (interface : Interface α n) (known : interface.known assignment = true)
    (ρ : α → Comp m) (agrees : ∀ a value, assignment a = some value → ρ a = value)
    (a : α) (member : a ∈ interface.support) : completeAssignment m assignment a = ρ a := by
  obtain ⟨value, hv⟩ := known_has_value interface assignment known a member
  rw [agrees a value hv]
  simp [completeAssignment, hv]

/-- No later choice for a missing slot can affect an accepted public scheme. -/
theorem closeAt_extension_independent (m : Model) (assignment : α → Option (Comp m))
    (interface : Interface α n) (known : interface.known assignment = true)
    (ρ : α → Comp m) (agrees : ∀ a value, assignment a = some value → ρ a = value) :
    interface.closeAt m (completeAssignment m assignment) = interface.closeAt m ρ := by
  have agree (x : α ⊕ Fin n) (ι : Fin n → Comp m)
      (member : x ∈ typeVariables interface.value ++ interface.obligations.flatMap goalVariables) :
      slotEnv (completeAssignment m assignment) ι x = slotEnv ρ ι x := by
    cases x with
    | inr _ => rfl
    | inl a =>
      exact complete_agrees_on_support m assignment interface known ρ agrees a
        ((mem_ambientVariables a _).mpr member)
  unfold Interface.closeAt
  congr 1
  · funext ι
    exact type_eval_on_support m _ _ interface.value
      (fun x hx => agree x ι (List.mem_append.mpr (Or.inl hx)))
  · funext ι
    apply List.map_congr_left
    intro goal member
    apply goal_eval_on_support m _ _ goal
    intro x hx
    exact agree x ι (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
      ⟨goal, (List.mem_filter.mp member).1, hx⟩)))

theorem finishModule_no_unresolved_exports (m : Model) (decode : m.Ty → Roles.Term)
    (impls : List Roles.Impl) (wf : Roles.WellFormed impls) (assignment : α → Option (Comp m))
    (interface : Interface α n) (closed : ClosedInterface m n)
    (accepted : finishModule m decode impls wf assignment interface = some closed) :
    (∀ a ∈ interface.support, ∃ value, assignment a = some value) ∧
      ∀ ρ, (∀ a value, assignment a = some value → ρ a = value) → closed = interface.closeAt m ρ := by
  obtain ⟨known, _, hc⟩ := (finishModule_exact m decode impls wf assignment interface closed).mp accepted
  exact ⟨known_has_value interface assignment known,
    fun ρ agrees => hc.symm.trans (closeAt_extension_independent m assignment interface known ρ agrees)⟩

/-- Closure preserves the meaning of the actual stored inference scheme. -/
theorem finalized_scheme_exact (m : Model) (decode : m.Ty → Roles.Term)
    (impls : List Roles.Impl) (wf : Roles.WellFormed impls) (assignment : α → Option (Comp m))
    (interface : Interface α n) (closed : ClosedInterface m n)
    (accepted : finishModule m decode impls wf assignment interface = some closed)
    (theory : Theory m) (ρ : α → Comp m)
    (agrees : ∀ a value, assignment a = some value → ρ a = value) (c : Comp m) :
    interface.scheme.Holds m theory (extend ρ c) ↔
      BindingTyping m theory (.qualified n closed.requirements (fun ι => Comp.pure m (closed.value ι))) c := by
  rw [Interface.scheme_exact]
  rw [(finishModule_no_unresolved_exports m decode impls wf assignment interface closed accepted).2 ρ agrees]
  rfl

end Yulang.QualifiedInference
