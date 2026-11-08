import Yulang.CommonRoleIntervalPaterson

/-!
# Finite structural capture of original endpoint pairs

This local expansion kernel admits linear constructor heads (int, pair,
tick and plain variables). A variable captures the two original endpoint
subtrees together. Repeated head variables and join heads are outside this
grammar: their interval reconciliation must not be replaced by equality.

All bindings are finite syntax. Every variable used by the head or any
where template is checked present before substitution. The total lookup
extension below is only accessed after that finite bound-name check.
-/

namespace Yulang.CommonRoleIntervalCapture

open CommonRoleCaptureNormalization (Form)
open CommonRoleStablePaterson (Declaration)
open CommonRoleIntervalPaterson (Argument Goal Substitution)

abbrev Bindings := List (Nat × Argument)

def variables : Form → List Nat
  | .var name => [name]
  | .int => []
  | .pair first last | .join first last => variables first ++ variables last
  | .tick payload => variables payload

def argumentVariables (forms : List Form) : List Nat := forms.flatMap variables

def structural : Form → Bool
  | .var _ | .int => true
  | .pair first last => structural first && structural last
  | .tick payload => structural payload
  | .join _ _ => false

def supported (declaration : Declaration) : Bool :=
  declaration.head.all structural && decide (argumentVariables declaration.head).Nodup

def lookup (bindings : Bindings) (name : Nat) : Option Argument :=
  match bindings with
  | [] => none
  | (key, argument) :: rest => if key = name then some argument else lookup rest name

/-- The fallback cannot be observed by a checked application: `bound`
checks every occurring source variable before any template is applied. -/
def total (bindings : Bindings) : Substitution :=
  fun name => (lookup bindings name).getD (.var name, .var name)

def bound (bindings : Bindings) (forms : List Form) : Bool :=
  (argumentVariables forms).all (fun name => (lookup bindings name).isSome)

theorem bound_exact (bindings : Bindings) (forms : List Form) :
    bound bindings forms = true ↔
      ∀ name ∈ argumentVariables forms, ∃ argument, lookup bindings name = some argument := by
  simp only [bound, List.all_eq_true, Option.isSome_iff_exists]

def append (first last : Option Bindings) : Option Bindings := do
  let first ← first
  let last ← last
  pure (first ++ last)

def capture : Form → Argument → Option Bindings
  | .var name, argument => some [(name, argument)]
  | .int, (.int, .int) => some []
  | .pair first last, (.pair lowFirst lowLast, .pair upFirst upLast) =>
      append (capture first (lowFirst, upFirst)) (capture last (lowLast, upLast))
  | .tick payload, (.tick low, .tick up) => capture payload (low, up)
  | _, _ => none

inductive Capture : Form → Argument → Bindings → Prop where
  | var (name) (argument) : Capture (.var name) argument [(name, argument)]
  | int : Capture .int (.int, .int) []
  | pair : Capture first (lowFirst, upFirst) before → Capture last (lowLast, upLast) after →
      Capture (.pair first last) (.pair lowFirst lowLast, .pair upFirst upLast) (before ++ after)
  | tick : Capture payload (low, up) bindings → Capture (.tick payload) (.tick low, .tick up) bindings

theorem capture_exact (form : Form) (argument : Argument) (bindings : Bindings) :
    capture form argument = some bindings ↔ Capture form argument bindings := by
  constructor
  · intro returned
    induction form generalizing argument bindings with
    | var name =>
        simp only [capture, Option.some.injEq] at returned
        subst bindings
        exact .var name argument
    | int =>
        rcases argument with ⟨low, up⟩
        cases low <;> cases up <;> simp [capture] at returned
        subst bindings
        exact .int
    | pair first last ihFirst ihLast =>
        rcases argument with ⟨low, up⟩
        cases low <;> cases up <;> simp only [capture] at returned
        all_goals try cases returned
        rename_i lowFirst lowLast upFirst upLast
        cases before : capture first (lowFirst, upFirst) with
        | none => simp [append, before] at returned
        | some beforeBindings =>
            cases after : capture last (lowLast, upLast) with
            | none => simp [append, after] at returned
            | some afterBindings =>
                have combined : beforeBindings ++ afterBindings = bindings := by
                  simpa [append, before, after] using returned
                subst bindings
                exact .pair (ihFirst _ _ before) (ihLast _ _ after)
    | tick payload ih =>
        rcases argument with ⟨low, up⟩
        cases low <;> cases up <;> simp only [capture] at returned
        all_goals try cases returned
        exact .tick (ih _ _ returned)
    | join => cases returned
  · intro derivation
    induction derivation with
    | var | int => rfl
    | pair _ _ first last => simp [capture, append, first, last]
    | tick _ ih => exact ih

def captureArguments : List Form → List Argument → Option Bindings
  | [], [] => some []
  | form :: forms, argument :: arguments => append (capture form argument) (captureArguments forms arguments)
  | _, _ => none

inductive CaptureArguments : List Form → List Argument → Bindings → Prop where
  | nil : CaptureArguments [] [] []
  | cons : Capture form argument before → CaptureArguments forms arguments after →
      CaptureArguments (form :: forms) (argument :: arguments) (before ++ after)

theorem capture_arguments_exact (forms : List Form) (arguments : List Argument) (bindings : Bindings) :
    captureArguments forms arguments = some bindings ↔ CaptureArguments forms arguments bindings := by
  constructor
  · intro returned
    induction forms generalizing arguments bindings with
    | nil =>
        cases arguments <;> simp [captureArguments] at returned
        subst bindings
        exact .nil
    | cons form forms ih =>
        cases arguments with
        | nil => cases returned
        | cons argument arguments =>
            cases before : capture form argument with
            | none => simp [captureArguments, append, before] at returned
            | some beforeBindings =>
                cases after : captureArguments forms arguments with
                | none => simp [captureArguments, append, after] at returned
                | some afterBindings =>
                    have combined : beforeBindings ++ afterBindings = bindings := by
                      simpa [captureArguments, append, before, after] using returned
                    subst bindings
                    exact .cons ((capture_exact _ _ _).mp before) (ih _ _ after)
  · intro derivation
    induction derivation with
    | nil => rfl
    | cons first _ ih =>
        simp [captureArguments, append, (capture_exact _ _ _).mpr first, ih]

end Yulang.CommonRoleIntervalCapture
