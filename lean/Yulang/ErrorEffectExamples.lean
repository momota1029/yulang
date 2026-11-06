import Yulang.ErrorEffects

/-!
# Executable error-declaration examples

These structural declaration models have several genuinely different payload
types, empty error responses, and an unrelated operation that returns `Unit`.
They instantiate the helper contracts without assuming an inference result or
choosing a nominal source-language representation.
-/

namespace Yulang.ErrorEffectExamples

open Directed SignatureRequests ErrorEffects

inductive Operation where
  | missing | denied | parse | appPath | appParse | appOther | trace
  deriving DecidableEq, Repr

inductive PathError where
  | missing : String → PathError
  | denied : String → PathError
  deriving DecidableEq, Repr

inductive AppError where
  | path : PathError → AppError
  | parse : Nat → AppError
  | other : AppError
  deriving DecidableEq, Repr

def signature : Signature Operation where
  Payload
    | .missing | .denied | .trace => String
    | .parse | .appParse => Nat
    | .appPath => PathError
    | .appOther => Unit
  Response
    | .trace => Unit
    | _ => Empty

def pathCases : Cases signature PathError where
  keys := [.missing, .denied]
  decode := fun operation member payload => by
    cases operation with
    | missing => exact .missing payload
    | denied => exact .denied payload
    | _ => simp at member
  noResponse := fun operation member response => by
    cases operation with
    | trace => simp at member
    | _ => exact response

def pathEncoding : Encoding pathCases where
  operation
    | .missing _ => .missing
    | .denied _ => .denied
  payload
    | .missing path => path
    | .denied path => path
  declared := by intro error; cases error <;> simp [pathCases]
  decoded := by intro error; cases error <;> rfl

def parseCases : Cases signature Nat where
  keys := [.parse]
  decode := fun operation member payload => by
    cases operation with
    | parse => exact payload
    | _ => simp at member
  noResponse := fun operation member response => by
    cases operation with
    | trace => simp at member
    | _ => exact response

def parseEncoding : Encoding parseCases where
  operation := fun _ => .parse
  payload := id
  declared := by intro _; simp [parseCases]
  decoded := by intro _; rfl

def appCases : Cases signature AppError where
  keys := [.appPath, .appParse, .appOther]
  decode := fun operation member payload => by
    cases operation with
    | appPath => exact .path payload
    | appParse => exact .parse payload
    | appOther => exact .other
    | _ => simp at member
  noResponse := fun operation member response => by
    cases operation with
    | trace => simp at member
    | _ => exact response

def appEncoding : Encoding appCases where
  operation
    | .path _ => .appPath
    | .parse _ => .appParse
    | .other => .appOther
  payload
    | .path error => error
    | .parse position => position
    | .other => ()
  declared := by intro error; cases error <;> simp [appCases]
  decoded := by intro error; cases error <;> rfl

/-- Two declared `from` sources share one result-error type. -/
def inclusiveCases : Cases signature AppError :=
  (appCases.append (pathCases.map AppError.path)).append (parseCases.map AppError.parse)

theorem wrap_path_error (error : PathError) :
    wrap pathCases (raise (n := 1) (Value := Nat) pathEncoding error) = .pure (.error error) :=
  wrap_raise _ _ _

theorem up_path_error (error : PathError) :
    up pathCases appEncoding AppError.path (raise (n := 1) (Value := Nat) pathEncoding error) =
      raise appEncoding (.path error) := up_raise _ _ _ _ _

theorem wrap_after_up_all_actions (action : Tree 1 signature Nat) :
    wrap appCases (up pathCases appEncoding AppError.path action) =
      wrapFrom appCases pathCases AppError.path action := by
  apply wrap_up_exact
  intro operation target source
  cases operation <;> simp [appCases, pathCases] at target source

theorem inclusive_path :
    wrap inclusiveCases (raise (n := 1) (Value := Nat) pathEncoding (.missing "sample")) =
      .pure (.error (.path (.missing "sample"))) := by rfl

theorem inclusive_parse :
    wrap inclusiveCases (raise (n := 1) (Value := Nat) parseEncoding 9) =
      .pure (.error (.parse 9)) := by rfl

theorem inclusive_own :
    wrap inclusiveCases (raise (n := 1) (Value := Nat) appEncoding .other) =
      .pure (.error .other) := by rfl

theorem unrelated_request_is_preserved :
    wrap inclusiveCases
        (.request (raw .trace) "before" (fun _ =>
          raise (n := 1) (Value := Nat) pathEncoding (.denied "sample"))) =
      .request (raw .trace) "before"
        (fun _ => .pure (.error (.path (.denied "sample")))) := by rfl

/-- A signed old debt remains on the request; error wrapping cannot cancel it. -/
theorem old_debt_is_not_captured :
    wrap pathCases
        (.request (release (0 : Fin 1) allowNone (raw .missing)) "sample"
          (fun response => (response : Empty).elim) : Tree 1 signature Nat) =
      .request (release (0 : Fin 1) allowNone (raw .missing)) "sample"
        (fun response => (response : Empty).elim) := by
  refine (wrap_nonzero (Value := Nat) pathCases
    (release (0 : Fin 1) allowNone (raw .missing)) "sample"
    (fun response => (response : Empty).elim) 0 (by decide)).trans ?_
  apply congrArg (Tree.request (signature := signature)
    (release (0 : Fin 1) allowNone (raw .missing)) "sample")
  funext response
  exact response.elim

theorem code_after_error_is_unreachable (next : Nat → Tree 1 signature Unit) :
    wrap pathCases ((raise pathEncoding (.missing "sample")).bind next) =
      .pure (.error (.missing "sample")) := by
  rw [raise_bind, wrap_raise]

end Yulang.ErrorEffectExamples
