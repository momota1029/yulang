import Yulang.CommonRecursiveNominalIntervalExact

/-!
# Recursive admission of every nested nominal description

Variance can make an argument unobserved by subtyping, but it does not make
malformed syntax well formed. The public entry checks every nested nominal
identity, arity and ordered kind, including payloads in unused positions.
Open bound descriptions are admitted only at invariant positions.

Admission is a total structural check, independent of the ordinary Common
assignment and of endpoint consistency. The public compiler is exact for
admitted finite structural derivations; it is not the full nominal source
solver. The recursive inspector remains a reference expansion: repeated
endpoint pairs are not memoized here.
-/

namespace Yulang.CommonRecursiveNominalIntervals

open Core.PresenceGeneration (TyTerm RowTerm Comp)
open CommonDeclaredNominalInspection (Kind Parameter Declaration Registry)
open CommonDeclaredNominalVariance (Variance)
open PresenceNormalForm (Atom All)

mutual
inductive WellFormed (registry : Registry) : Endpoint α → Prop where
  | ordinary (term : TyTerm α) : WellFormed registry (.ordinary term)
  | nominal {name : Nat} {arguments : List (Argument α)} {declaration : Declaration} :
      registry[name]? = some declaration → ArgumentsWellFormed registry declaration arguments →
      WellFormed registry (.nominal name arguments)

inductive ArgumentsWellFormed (registry : Registry) : Declaration → List (Argument α) → Prop where
  | nil : ArgumentsWellFormed registry [] []
  | cons {parameter rest argument tail} :
      ArgumentWellFormed registry parameter argument → ArgumentsWellFormed registry rest tail →
      ArgumentsWellFormed registry (parameter :: rest) (argument :: tail)

inductive ArgumentWellFormed (registry : Registry) : Parameter → Argument α → Prop where
  | valuePoint {mode : Variance} {term : Endpoint α} : WellFormed registry term →
      ArgumentWellFormed registry ⟨.value, mode⟩ (.inl (.point term))
  | valueInterval {lower upper : Endpoint α} :
      WellFormed registry lower → WellFormed registry upper →
      ArgumentWellFormed registry ⟨.value, .invariant⟩ (.inl (.interval lower upper))
  | rowPoint (mode : Variance) (term : RowTerm α) :
      ArgumentWellFormed registry ⟨.row, mode⟩ (.inr (.point term))
  | rowInterval (lower upper : RowTerm α) :
      ArgumentWellFormed registry ⟨.row, .invariant⟩ (.inr (.interval lower upper))
end

mutual
def admit (registry : Registry) (endpoint : Endpoint α) : Bool :=
  match endpoint with
  | .ordinary _ => true
  | .nominal name arguments =>
      match registry[name]? with
      | none => false
      | some declaration => admitArguments registry declaration arguments
termination_by sizeOf endpoint
decreasing_by
  all_goals simp_wf
  all_goals try simp only [wfParam]
  all_goals omega

def admitArguments (registry : Registry) (declaration : Declaration)
    (arguments : List (Argument α)) : Bool :=
  match declaration, arguments with
  | [], [] => true
  | parameter :: rest, argument :: tail =>
      admitArgument registry parameter argument && admitArguments registry rest tail
  | _, _ => false
termination_by sizeOf arguments
decreasing_by
  all_goals simp_wf
  all_goals try simp only [wfParam]
  all_goals omega

def admitArgument (registry : Registry) (parameter : Parameter) (argument : Argument α) : Bool :=
  match parameter.kind, argument with
  | .value, .inl (.point term) => admit registry term
  | .value, .inl (.interval lower upper) =>
      decide (parameter.variance = .invariant) && admit registry lower && admit registry upper
  | .row, .inr (.point _) => true
  | .row, .inr (.interval _ _) => decide (parameter.variance = .invariant)
  | _, _ => false
termination_by sizeOf argument
decreasing_by
  all_goals simp_wf
  all_goals try simp only [wfParam]
  all_goals omega
end

theorem argument_wellFormed_exact (registry : Registry) (parameter : Parameter) (argument : Argument α) :
    ArgumentWellFormed registry parameter argument ↔
      match parameter.kind, argument with
      | .value, .inl (.point term) => WellFormed registry term
      | .value, .inl (.interval lower upper) =>
          parameter.variance = .invariant ∧ WellFormed registry lower ∧ WellFormed registry upper
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
    | exact .rowPoint _ _
    | exact .rowInterval _ _

mutual
theorem admit_exact (registry : Registry) (endpoint : Endpoint α) :
    admit registry endpoint = true ↔ WellFormed registry endpoint := by
  cases endpoint with
  | ordinary term =>
      constructor
      · intro _; exact .ordinary term
      · intro _; simp only [admit]
  | nominal name arguments =>
      cases declared : registry[name]? with
      | none =>
          simp only [admit, declared, Bool.false_eq_true]
          constructor
          · exact False.elim
          · intro proof
            cases proof with
            | nominal found _ => simp [declared] at found
      | some declaration =>
          simp only [admit, declared]
          rw [admit_arguments_exact]
          constructor
          · intro proof; exact .nominal declared proof
          · intro proof
            cases proof with
            | @nominal _ _ actual found arguments =>
                have same : actual = declaration := Option.some.inj (found.symm.trans declared)
                subst actual
                exact arguments
termination_by sizeOf endpoint
decreasing_by
  all_goals simp_wf
  all_goals try simp only [wfParam]
  all_goals omega

theorem admit_arguments_exact (registry : Registry) (declaration : Declaration)
    (arguments : List (Argument α)) :
    admitArguments registry declaration arguments = true ↔
      ArgumentsWellFormed registry declaration arguments := by
  cases declaration with
  | nil =>
      cases arguments with
      | nil =>
          constructor
          · intro _; exact .nil
          · intro _; simp only [admitArguments]
      | cons head tail =>
          simp only [admitArguments, Bool.false_eq_true]
          constructor <;> intro impossible <;> cases impossible
  | cons parameter rest =>
      cases arguments with
      | nil =>
          simp only [admitArguments, Bool.false_eq_true]
          constructor <;> intro impossible <;> cases impossible
      | cons argument tail =>
          simp only [admitArguments, Bool.and_eq_true]
          rw [admit_argument_exact, admit_arguments_exact]
          constructor
          · rintro ⟨head, rest⟩; exact .cons head rest
          · intro proof; cases proof; exact ⟨by assumption, by assumption⟩
termination_by sizeOf arguments
decreasing_by
  all_goals simp_wf
  all_goals try simp only [wfParam]
  all_goals omega

theorem admit_argument_exact (registry : Registry) (parameter : Parameter) (argument : Argument α) :
    admitArgument registry parameter argument = true ↔ ArgumentWellFormed registry parameter argument := by
  rw [argument_wellFormed_exact]
  rcases parameter with ⟨kind, mode⟩
  cases kind with
  | value =>
      cases argument with
      | inl bounds =>
          cases bounds with
          | point term => simpa only [admitArgument] using admit_exact registry term
          | interval lower upper =>
              simp only [admitArgument, Bool.and_eq_true, decide_eq_true_eq]
              rw [admit_exact registry lower, admit_exact registry upper]
              exact and_assoc
      | inr bounds => cases bounds <;> simp [admitArgument]
  | row =>
      cases argument with
      | inl bounds => cases bounds <;> simp [admitArgument]
      | inr bounds => cases bounds <;> simp [admitArgument]

termination_by sizeOf argument
decreasing_by
  all_goals simp_wf
  all_goals try simp only [wfParam]
  all_goals omega
end

/-- Full syntactic admission precedes the reference constraint expansion. -/
def compile (registry : Registry) (first last : Endpoint α) : Option (List (Atom α)) :=
  if admit registry first && admit registry last then inspect registry first last else none

/-- Every table, both complete original descriptions and every independent
Common assignment. No success/shape premise is shifted to the caller. -/
theorem compile_exact (registry : Registry) (assignment : α → Comp Common.model)
    (first last : Endpoint α) :
    ResultHolds (fun atom => atom.Holds Common.model assignment) (compile registry first last) ↔
      WellFormed registry first ∧ WellFormed registry last ∧ Derives registry assignment first last := by
  unfold compile
  by_cases admitted : (admit registry first && admit registry last) = true
  · simp only [admitted, ↓reduceIte, inspect_exact]
    obtain ⟨left, right⟩ := Bool.and_eq_true_iff.mp admitted
    simp only [(admit_exact registry first).mp left, (admit_exact registry last).mp right, true_and]
  · simp only [admitted, Bool.false_eq_true, ↓reduceIte, result_none, false_iff]
    rintro ⟨left, right, _⟩
    exact admitted (Bool.and_eq_true_iff.mpr
      ⟨(admit_exact registry first).mpr left, (admit_exact registry last).mpr right⟩)

end Yulang.CommonRecursiveNominalIntervals
