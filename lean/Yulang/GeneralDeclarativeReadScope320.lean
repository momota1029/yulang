import Yulang.GeneralDeclarativePoint320

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 14000
set_option maxHeartbeats 3300000
namespace Yulang.GeneralDeclarativeReadScope320
open GeneralDeclarationPatterns (Constructors Pattern normalize normalizeArgs variablesArgs)
open GeneralDeclarations (Declaration Clause DeclarationChecked)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadMatExpressions (Expr translate translateMany application)
open GeneralNominalExpressionIntervals237 (reads readsMany)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeBounds319 (Tracks)

theorem application_reads {catalogue : Constructors} {interp : Interpretation}
    {name : Nat} {args : List Expr} {result : Expr}
    (compiled : application catalogue interp name args = some result) :
    reads result ⊆ readsMany args := by
  intro n used
  cases declared : catalogue name with
  | none => simp [application,declared] at compiled
  | some declaration =>
    by_cases arity : declaration.parameters.length = args.length
    · simp [application,declared,arity] at compiled
      cases primitive : interp.primitives name with
      | none =>
        simp only [primitive] at compiled
        split at compiled
        · cases Option.some.inj compiled; cases used
        · cases compiled
      | some op =>
        simp only [primitive] at compiled
        split at compiled
        · cases Option.some.inj compiled; exact used
        · cases compiled
    · simp [application,declared,arity] at compiled

mutual
 theorem compiled_reads {catalogue : Constructors} {interp : Interpretation}
    (pattern : Pattern) {exp : Expr}
    (compiled : translate catalogue interp pattern = some exp) :
    reads exp ⊆ pattern.variables := by
  intro key used
  cases pattern with
  | var name =>
    cases Option.some.inj compiled
    exact used
  | app name patterns =>
    cases inside : translateMany catalogue interp patterns with
    | none => simp [translate,inside] at compiled
    | some es =>
      simp only [translate,inside] at compiled
      exact compiled_reads_many patterns inside (application_reads compiled used)
  | record label payload tail =>
    cases left : translate catalogue interp payload <;>
      simp only [translate,left] at compiled
    · cases compiled
    · cases right : translate catalogue interp tail <;>
        simp only [right,Option.pure_def] at compiled
      · cases compiled
      · cases Option.some.inj compiled
        rcases List.mem_append.mp used with h|h
        · exact List.mem_append_left _ (compiled_reads payload left h)
        · exact List.mem_append_right _ (compiled_reads tail right h)
  | variant label payload =>
    cases body : translate catalogue interp payload <;>
      simp only [translate,body,Option.pure_def] at compiled
    · cases compiled
    · cases Option.some.inj compiled
      exact compiled_reads payload body used
  | join first last =>
    cases left : translate catalogue interp first <;>
      simp only [translate,left] at compiled
    · cases compiled
    · cases right : translate catalogue interp last <;>
        simp only [right,Option.pure_def] at compiled
      · cases compiled
      · cases Option.some.inj compiled
        rcases List.mem_append.mp used with h|h
        · exact List.mem_append_left _ (compiled_reads first left h)
        · exact List.mem_append_right _ (compiled_reads last right h)
 termination_by sizeOf pattern
 theorem compiled_reads_many {catalogue : Constructors} {interp : Interpretation}
    (patterns : List Pattern) {exps : List Expr}
    (compiled : translateMany catalogue interp patterns = some exps) :
    readsMany exps ⊆ variablesArgs patterns := by
  intro key used
  cases patterns with
  | nil => cases Option.some.inj compiled; cases used
  | cons head tail =>
    cases first : translate catalogue interp head <;>
      simp only [translateMany,first] at compiled
    · cases compiled
    · cases rest : translateMany catalogue interp tail <;>
        simp only [rest,Option.pure_def] at compiled
      · cases compiled
      · cases Option.some.inj compiled
        rcases List.mem_append.mp used with h|h
        · exact List.mem_append_left _ (compiled_reads head first h)
        · exact List.mem_append_right _ (compiled_reads_many tail rest h)
 termination_by sizeOf patterns
end

theorem normalize_member {p : Pattern} {ps : List Pattern} (found : p ∈ ps) :
    normalize p ∈ normalizeArgs ps := by
  induction ps with
  | nil => cases found
  | cons one rest ih =>
    rcases List.mem_cons.mp found with rfl|later
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih later)

theorem variable_of_member {p : Pattern} {ps : List Pattern} {n : Nat}
    (found : p ∈ ps) (used : n ∈ p.variables) : n ∈ variablesArgs ps := by
  induction ps with
  | nil => cases found
  | cons one rest ih =>
    rcases List.mem_cons.mp found with rfl|later
    · exact List.mem_append_left _ used
    · exact List.mem_append_right _ (ih later)

theorem tracked_from_declared_inputs {s : State} {catalogue : Constructors}
    {interp : Interpretation} {capture : Nat → Capture} {declaration : Declaration}
    {clause : Clause} {pattern : Pattern} {exp : Expr}
    (checked : DeclarationChecked catalogue roles declaration)
    (clauseIn : clause ∈ declaration.requirements)
    (argument : pattern ∈ clause.arguments)
    (compiled : translate catalogue interp (normalize pattern) = some exp)
    (bounds : ∀ name ∈ declaration.inputNames, Bounds s (capture name)) :
    Tracks s.normal capture exp := by
  intro name used
  apply bounds name
  exact checked.scope.1 clause clauseIn name
    (variable_of_member (normalize_member argument) (compiled_reads _ compiled used))

end Yulang.GeneralDeclarativeReadScope320
