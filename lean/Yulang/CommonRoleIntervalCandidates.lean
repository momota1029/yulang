import Yulang.CommonRoleIntervalCapture

/-!
# A finite candidate scan for the supported interval expansion kernel

Both endpoints are normalized by the existing local pass before structural
capture. Every original head/where variable is checked bound. A successful
capture is replayed against those same endpoint pairs before recursion.

`none` means outside this local grammar, never a pending language role or
a proof of absence of a general candidate. A definite rigid constructor
mismatch (or different role/arity) is distinct from that outside result.
Repeated-variable and join heads are outside even if a literal equality
test could happen to succeed. No interval reconciliation is replaced here.
-/

namespace Yulang.CommonRoleIntervalCandidates

open CommonRoleCaptureNormalization (Form)
open CommonRoleStablePaterson (Declaration)
open CommonRoleIntervalPaterson (Argument Goal head child size)
open CommonRoleIntervalCapture (Bindings CaptureArguments captureArguments supported bound total)

def normalizeArguments (arguments : List Argument) : List Argument :=
  arguments.map fun argument => (argument.1.normalize, argument.2.normalize)

def normalizeGoal (goal : Goal) : Goal := ⟨goal.role, normalizeArguments goal.arguments⟩

theorem normalized_size_le (arguments : List Argument) : size (normalizeArguments arguments) ≤ size arguments := by
  induction arguments with
  | nil => exact Nat.le_refl _
  | cons argument rest ih =>
      have low := CommonRoleStablePaterson.normalize_size_le argument.1
      have up := CommonRoleStablePaterson.normalize_size_le argument.2
      simp only [normalizeArguments, List.map_cons, size, CommonRoleIntervalPaterson.lower,
        CommonRoleIntervalPaterson.upper, Roles.argsSize] at *
      omega

/-- This test reports only rigid aligned constructor clashes. At rigid head
positions, a union, free endpoint, or differing endpoint shapes remains
outside, not rejected. Variable head positions retain any endpoint pair. -/
def mismatch : Form → Argument → Bool
  | .var _, _ | .join _ _, _ => false
  | .int, (.pair _ _, .pair _ _) | .int, (.tick _, .tick _) => true
  | .pair _ _, (.int, .int) | .pair _ _, (.tick _, .tick _) => true
  | .tick _, (.int, .int) | .tick _, (.pair _ _, .pair _ _) => true
  | .pair first last, (.pair lowFirst lowLast, .pair upFirst upLast) =>
      mismatch first (lowFirst, upFirst) || mismatch last (lowLast, upLast)
  | .tick payload, (.tick low, .tick up) => mismatch payload (low, up)
  | _, _ => false

def mismatchArguments : List Form → List Argument → Bool
  | [], [] => false
  | form :: forms, argument :: arguments => mismatch form argument || mismatchArguments forms arguments
  | _, _ => true

def namesBound (declaration : Declaration) (bindings : Bindings) : Bool :=
  bound bindings declaration.head && declaration.requirements.all (fun requirement => bound bindings requirement.2)

def Accepts (declaration : Declaration) (goal : Goal) (bindings : Bindings) : Prop :=
  supported declaration = true ∧ declaration.role = goal.role ∧
    mismatchArguments declaration.head (normalizeArguments goal.arguments) = false ∧
    CaptureArguments declaration.head (normalizeArguments goal.arguments) bindings ∧
    namesBound declaration bindings = true ∧ head declaration (total bindings) = normalizeGoal goal

def Rejects (declaration : Declaration) (goal : Goal) : Prop :=
  supported declaration = true ∧
    (declaration.role ≠ goal.role ∨ mismatchArguments declaration.head (normalizeArguments goal.arguments) = true)

def inspect (declaration : Declaration) (goal : Goal) : Option (Option Bindings) :=
  if supported declaration then
    if declaration.role = goal.role then
      if mismatchArguments declaration.head (normalizeArguments goal.arguments) then some none
      else do
        let bindings ← captureArguments declaration.head (normalizeArguments goal.arguments)
        if namesBound declaration bindings && decide (head declaration (total bindings) = normalizeGoal goal)
          then some (some bindings) else none
    else some none
  else none

theorem inspect_accepts_exact (declaration : Declaration) (goal : Goal) (bindings : Bindings) :
    inspect declaration goal = some (some bindings) ↔ Accepts declaration goal bindings := by
  simp only [Accepts, ← CommonRoleIntervalCapture.capture_arguments_exact]
  cases supportedEq : supported declaration with
  | false => simp [inspect, supportedEq]
  | true =>
      by_cases same : declaration.role = goal.role
      · cases mismatchEq : mismatchArguments declaration.head (normalizeArguments goal.arguments) with
        | true => simp [inspect, supportedEq, same, mismatchEq]
        | false =>
            cases captured : captureArguments declaration.head (normalizeArguments goal.arguments) with
            | none => simp [inspect, supportedEq, same, mismatchEq, captured]
            | some actual =>
                simp only [inspect, supportedEq, same, mismatchEq, captured]
                dsimp
                split <;> simp_all [Bool.and_eq_true]
                all_goals rintro rfl; assumption
      · simp [inspect, supportedEq, same]

theorem inspect_rejects_exact (declaration : Declaration) (goal : Goal) :
    inspect declaration goal = some none ↔ Rejects declaration goal := by
  cases supportedEq : supported declaration with
  | false => simp [inspect, Rejects, supportedEq]
  | true =>
      by_cases same : declaration.role = goal.role
      · cases mismatchEq : mismatchArguments declaration.head (normalizeArguments goal.arguments) with
        | true => simp [inspect, Rejects, supportedEq, same, mismatchEq]
        | false =>
            cases captured : captureArguments declaration.head (normalizeArguments goal.arguments) with
            | none => simp [inspect, Rejects, supportedEq, same, mismatchEq, captured]
            | some actual =>
                simp only [inspect, Rejects, supportedEq, same, mismatchEq, captured]
                dsimp
                split <;> simp
      · simp [inspect, Rejects, supportedEq, same]

structure Candidate where
  declaration : Declaration
  bindings : Bindings
  deriving DecidableEq, Repr

def scan (goal : Goal) : List Declaration → Option (List Candidate)
  | [] => some []
  | declaration :: rest => do
      let inspected ← inspect declaration goal
      let later ← scan goal rest
      pure (match inspected with | none => later | some bindings => ⟨declaration, bindings⟩ :: later)

inductive Selection (goal : Goal) : List Declaration → List Candidate → Prop where
  | nil : Selection goal [] []
  | reject : Rejects declaration goal → Selection goal rest selected → Selection goal (declaration :: rest) selected
  | accept : Accepts declaration goal bindings → Selection goal rest selected →
      Selection goal (declaration :: rest) (⟨declaration, bindings⟩ :: selected)

theorem scan_exact (goal : Goal) (declarations : List Declaration) (selected : List Candidate) :
    scan goal declarations = some selected ↔ Selection goal declarations selected := by
  constructor
  · intro returned
    induction declarations generalizing selected with
    | nil =>
        simp [scan] at returned
        subst selected
        exact .nil
    | cons declaration rest ih =>
        cases inspected : inspect declaration goal with
        | none => simp [scan, inspected] at returned
        | some result =>
            cases later : scan goal rest with
            | none => simp [scan, later] at returned
            | some laterCandidates =>
                cases result with
                | none =>
                    have same : laterCandidates = selected := by simpa [scan, inspected, later] using returned
                    subst selected
                    exact .reject ((inspect_rejects_exact _ _).mp inspected) (ih _ later)
                | some bindings =>
                    have same : (⟨declaration, bindings⟩ : Candidate) :: laterCandidates = selected := by
                      simpa [scan, inspected, later] using returned
                    subst selected
                    exact .accept ((inspect_accepts_exact _ _ _).mp inspected) (ih _ later)
  · intro derivation
    induction derivation with
    | nil => rfl
    | reject rejected _ ih => simp [scan, (inspect_rejects_exact _ _).mpr rejected, ih]
    | accept accepted _ ih => simp [scan, (inspect_accepts_exact _ _ _).mpr accepted, ih]

theorem Selection.member (selected : Selection goal declarations candidates)
    (candidate : Candidate) (member : candidate ∈ candidates) :
    candidate.declaration ∈ declarations ∧ Accepts candidate.declaration goal candidate.bindings := by
  induction selected with
  | nil => cases member
  | reject _ _ ih =>
      obtain ⟨included, accepted⟩ := ih member
      exact ⟨List.mem_cons_of_mem _ included, accepted⟩
  | accept accepted _ ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨List.mem_cons_self, accepted⟩
      · obtain ⟨included, accepted⟩ := ih later
        exact ⟨List.mem_cons_of_mem _ included, accepted⟩

/-- Every original variable in every original where-template is read from
the finite captured table. The total extension's fallback is unobservable. -/
theorem all_where_bindings_exist (declaration : Declaration) (goal : Goal) (bindings : Bindings)
    (accepted : Accepts declaration goal bindings) (requirement : Nat × List Form)
    (member : requirement ∈ declaration.requirements) (name : Nat)
    (used : name ∈ CommonRoleIntervalCapture.argumentVariables requirement.2) :
    ∃ argument, CommonRoleIntervalCapture.lookup bindings name = some argument ∧ total bindings name = argument := by
  have allNames := (Bool.and_eq_true_iff.mp accepted.2.2.2.2.1).2
  have bounded := (List.all_eq_true.mp allNames) requirement member
  obtain ⟨argument, present⟩ := (CommonRoleIntervalCapture.bound_exact bindings requirement.2).mp bounded name used
  exact ⟨argument, present, by simp [total, present]⟩

theorem accepted_child_decreases (declaration : Declaration)
    (checked : CommonRoleStablePaterson.check declaration = true) (goal : Goal) (bindings : Bindings)
    (accepted : Accepts declaration goal bindings) (requirement : Nat × List Form)
    (member : requirement ∈ declaration.requirements) :
    size (child requirement (total bindings)).arguments < size goal.arguments := by
  have smaller := CommonRoleIntervalPaterson.every_where_decreases declaration checked (total bindings) requirement member
  rw [accepted.2.2.2.2.2] at smaller
  exact Nat.lt_of_lt_of_le smaller (normalized_size_le goal.arguments)

end Yulang.CommonRoleIntervalCandidates
