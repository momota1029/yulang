import Yulang.CommonRecursiveNominalIntervalContextExact

/-!
# Admission and public compilation with inherited invariant context

Every nested node is validated, including unused payloads. An open bound at
a used position is admitted when either its declaration or an enclosing
argument makes the position invariant. The same context is used by admission
and by the comparison compiler; root covariance is preserved.
-/

namespace Yulang.CommonRecursiveNominalIntervals

open Core.PresenceGeneration (TyTerm RowTerm Comp)
open CommonDeclaredNominalInspection (Kind Parameter Declaration Registry)
open CommonDeclaredNominalVariance (Variance)
open PresenceNormalForm (Atom)

mutual
inductive ContextWellFormed (registry : Registry) : Bool → Endpoint α → Prop where
  | ordinary (context : Bool) (term : TyTerm α) : ContextWellFormed registry context (.ordinary term)
  | nominal {context name arguments declaration} :
      registry[name]? = some declaration → ContextArgumentsWellFormed registry context declaration arguments →
      ContextWellFormed registry context (.nominal name arguments)

inductive ContextArgumentsWellFormed (registry : Registry) :
    Bool → Declaration → List (Argument α) → Prop where
  | nil (context : Bool) : ContextArgumentsWellFormed registry context [] []
  | cons {context parameter rest argument tail} :
      ContextArgumentWellFormed registry (childContext context parameter)
        (effectiveParameter context parameter) argument →
      ContextArgumentsWellFormed registry context rest tail →
      ContextArgumentsWellFormed registry context (parameter :: rest) (argument :: tail)

inductive ContextArgumentWellFormed (registry : Registry) : Bool → Parameter → Argument α → Prop where
  | valuePoint {context mode term} : ContextWellFormed registry context term →
      ContextArgumentWellFormed registry context ⟨.value, mode⟩ (.inl (.point term))
  | valueInterval {context lower upper} :
      ContextWellFormed registry context lower → ContextWellFormed registry context upper →
      ContextArgumentWellFormed registry context ⟨.value, .invariant⟩ (.inl (.interval lower upper))
  | rowPoint (context) (mode : Variance) (term : RowTerm α) :
      ContextArgumentWellFormed registry context ⟨.row, mode⟩ (.inr (.point term))
  | rowInterval (context) (lower upper : RowTerm α) :
      ContextArgumentWellFormed registry context ⟨.row, .invariant⟩ (.inr (.interval lower upper))
end

mutual
def admitContext (registry : Registry) (context : Bool) (endpoint : Endpoint α) : Bool :=
  match endpoint with
  | .ordinary _ => true
  | .nominal name arguments =>
      match registry[name]? with
      | none => false
      | some declaration => admitContextArguments registry context declaration arguments
termination_by sizeOf endpoint
decreasing_by
  all_goals simp_wf
  all_goals omega

def admitContextArguments (registry : Registry) (context : Bool) (declaration : Declaration)
    (arguments : List (Argument α)) : Bool :=
  match declaration, arguments with
  | [], [] => true
  | parameter :: rest, argument :: tail =>
      admitContextArgument registry (childContext context parameter)
        (effectiveParameter context parameter) argument &&
        admitContextArguments registry context rest tail
  | _, _ => false
termination_by sizeOf arguments
decreasing_by
  all_goals simp_wf
  all_goals omega

def admitContextArgument (registry : Registry) (context : Bool)
    (parameter : Parameter) (argument : Argument α) : Bool :=
  match parameter.kind, argument with
  | .value, .inl (.point term) => admitContext registry context term
  | .value, .inl (.interval lower upper) =>
      decide (parameter.variance = .invariant) &&
        admitContext registry context lower && admitContext registry context upper
  | .row, .inr (.point _) => true
  | .row, .inr (.interval _ _) => decide (parameter.variance = .invariant)
  | _, _ => false
termination_by sizeOf argument
decreasing_by
  all_goals simp_wf
  all_goals try simp only [wfParam]
  all_goals omega
end

theorem context_argument_wellFormed_exact (registry : Registry) (context : Bool)
    (parameter : Parameter) (argument : Argument α) :
    ContextArgumentWellFormed registry context parameter argument ↔
      match parameter.kind, argument with
      | .value, .inl (.point term) => ContextWellFormed registry context term
      | .value, .inl (.interval lower upper) => parameter.variance = .invariant ∧
          ContextWellFormed registry context lower ∧ ContextWellFormed registry context upper
      | .row, .inr (.point _) => True
      | .row, .inr (.interval _ _) => parameter.variance = .invariant
      | _, _ => False := by
  rcases parameter with ⟨kind, mode⟩
  cases kind <;> cases mode <;> cases argument <;> rename_i bounds
  all_goals cases bounds <;> simp only [reduceCtorEq, false_and, true_and]
  all_goals constructor <;> intro proof
  all_goals solve
    | cases proof <;> simp_all
    | exact .valuePoint proof
    | exact .valueInterval proof.1 proof.2
    | exact .rowPoint _ _ _
    | exact .rowInterval _ _ _

mutual
theorem admit_context_exact (registry : Registry) (context : Bool) (endpoint : Endpoint α) :
    admitContext registry context endpoint = true ↔ ContextWellFormed registry context endpoint := by
  cases endpoint with
  | ordinary term =>
      constructor
      · intro _; exact .ordinary context term
      · intro _; simp only [admitContext]
  | nominal name arguments =>
      cases declared : registry[name]? with
      | none =>
          simp only [admitContext, declared, Bool.false_eq_true]
          constructor
          · exact False.elim
          · intro proof
            cases proof with
            | nominal found _ => simp [declared] at found
      | some declaration =>
          simp only [admitContext, declared]
          rw [admit_context_arguments_exact]
          constructor
          · intro proof; exact .nominal declared proof
          · intro proof
            cases proof with
            | @nominal _ _ _ actual found arguments =>
                have same : actual = declaration := Option.some.inj (found.symm.trans declared)
                subst actual
                exact arguments
termination_by sizeOf endpoint
decreasing_by
  all_goals simp_wf
  all_goals omega

theorem admit_context_arguments_exact (registry : Registry) (context : Bool)
    (declaration : Declaration) (arguments : List (Argument α)) :
    admitContextArguments registry context declaration arguments = true ↔
      ContextArgumentsWellFormed registry context declaration arguments := by
  cases declaration with
  | nil =>
      cases arguments with
      | nil =>
          constructor
          · intro _; exact .nil context
          · intro _; simp only [admitContextArguments]
      | cons head tail =>
          simp only [admitContextArguments, Bool.false_eq_true]
          constructor <;> intro impossible <;> cases impossible
  | cons parameter rest =>
      cases arguments with
      | nil =>
          simp only [admitContextArguments, Bool.false_eq_true]
          constructor <;> intro impossible <;> cases impossible
      | cons argument tail =>
          simp only [admitContextArguments, Bool.and_eq_true]
          rw [admit_context_argument_exact, admit_context_arguments_exact]
          constructor
          · rintro ⟨head, rest⟩; exact .cons head rest
          · intro proof; cases proof; exact ⟨by assumption, by assumption⟩
termination_by sizeOf arguments
decreasing_by
  all_goals simp_wf
  all_goals omega

theorem admit_context_argument_exact (registry : Registry) (context : Bool)
    (parameter : Parameter) (argument : Argument α) :
    admitContextArgument registry context parameter argument = true ↔
      ContextArgumentWellFormed registry context parameter argument := by
  rw [context_argument_wellFormed_exact]
  rcases parameter with ⟨kind, mode⟩
  cases kind with
  | value =>
      cases argument with
      | inl bounds =>
          cases bounds with
          | point term => simpa only [admitContextArgument] using admit_context_exact registry context term
          | interval lower upper =>
              simp only [admitContextArgument, Bool.and_eq_true, decide_eq_true_eq]
              rw [admit_context_exact registry context lower, admit_context_exact registry context upper]
              exact and_assoc
      | inr bounds => cases bounds <;> simp [admitContextArgument]
  | row =>
      cases argument with
      | inl bounds => cases bounds <;> simp [admitContextArgument]
      | inr bounds => cases bounds <;> simp [admitContextArgument]
termination_by sizeOf argument
decreasing_by
  all_goals simp_wf
  all_goals omega
end

/-- The starting context is explicit: a check already generated by an
invariant role-argument merge can start inside invariance. -/
def compileInContext (registry : Registry) (context : Bool) (first last : Endpoint α) :
    Option (List (Atom α)) :=
  if admitContext registry context first && admitContext registry context last then
    inspectContext registry context first last
  else none

/-- An ordinary outer subtype comparison starts outside invariant context. -/
def compileContext (registry : Registry) (first last : Endpoint α) : Option (List (Atom α)) :=
  compileInContext registry false first last

theorem compile_in_context_exact (registry : Registry) (assignment : α → Comp Common.model)
    (context : Bool) (first last : Endpoint α) :
    ResultHolds (fun atom => atom.Holds Common.model assignment)
      (compileInContext registry context first last) ↔
        ContextWellFormed registry context first ∧ ContextWellFormed registry context last ∧
          ContextDerives registry assignment context first last := by
  unfold compileInContext
  by_cases admitted : (admitContext registry context first && admitContext registry context last) = true
  · simp only [admitted, ↓reduceIte, inspect_context_exact]
    obtain ⟨left, right⟩ := Bool.and_eq_true_iff.mp admitted
    simp only [(admit_context_exact registry context first).mp left,
      (admit_context_exact registry context last).mp right, true_and]
  · simp only [admitted, Bool.false_eq_true, ↓reduceIte, result_none, false_iff]
    rintro ⟨left, right, _⟩
    exact admitted (Bool.and_eq_true_iff.mpr
      ⟨(admit_context_exact registry context first).mpr left,
        (admit_context_exact registry context last).mpr right⟩)

theorem compile_context_exact (registry : Registry) (assignment : α → Comp Common.model)
    (first last : Endpoint α) :
    ResultHolds (fun atom => atom.Holds Common.model assignment) (compileContext registry first last) ↔
      ContextWellFormed registry false first ∧ ContextWellFormed registry false last ∧
        ContextDerives registry assignment false first last :=
  compile_in_context_exact registry assignment false first last

end Yulang.CommonRecursiveNominalIntervals
