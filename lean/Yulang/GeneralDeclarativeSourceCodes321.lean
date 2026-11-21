import Yulang.GeneralDeclarativeFreshForest321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeSourceCodes321
open GeneralDeclarativeFreshCalls321 (SourceCodes)
open GeneralDeclarativeFreshForest321 (ClauseCode all_children_extension)
open GeneralDeclarations (Registry Clause Equation)
open GeneralDeclarationPatterns (Constructors Pattern normalize normalizeArgs)
open GeneralNominalCenteredHeadMatExpressions (Expr translate translateMany)
open GeneralNominalInspection (Interpretation)
open CommonRoleOutermostResolver (All₂)

def outputCodes (c : Constructors) (interp : Interpretation) : List Equation → Option (List (Nat × Expr))
  | [] => some []
  | eqn :: tail => do
    let code ← translate c interp eqn.rhs
    let more ← outputCodes c interp tail
    pure ((eqn.name,code) :: more)

def clauseCode (r : Registry) (interp : Interpretation) (clause : Clause) : Option ClauseCode := do
  let args ← translateMany r.constructors interp (normalizeArgs clause.arguments)
  let out ← outputCodes r.constructors interp clause.outputs
  pure ⟨args,out⟩

def clauseCodes (r : Registry) (interp : Interpretation) : List Clause → Option (List ClauseCode)
  | [] => some []
  | clause::more => do
    let first ← clauseCode r interp clause
    let rest ← clauseCodes r interp more
    pure (first::rest)

theorem args_exact {c interp} {args : List Pattern} {es : List Expr}
    (compiled : translateMany c interp (normalizeArgs args) = some es) :
    All₂ (fun pat e => translate c interp (normalize pat) = some e) args es := by
  induction args generalizing es with
  | nil => cases compiled; exact .nil
  | cons x xs ih =>
    cases head : translate c interp (normalize x) with
    | none => simp [normalizeArgs,translateMany,head] at compiled
    | some e =>
      cases tail : translateMany c interp (normalizeArgs xs) with
      | none => simp [normalizeArgs,translateMany,head,tail] at compiled
      | some rest =>
        have equal : e :: rest = es := by simpa [normalizeArgs,translateMany,head,tail] using compiled
        subst es
        exact .cons head (ih tail)

theorem output_exact {c interp} {source : List Equation} {es : List (Nat × Expr)}
    (compiled : outputCodes c interp source = some es) :
    All₂ (fun eqn pr => pr.1 = eqn.name ∧ translate c interp eqn.rhs = some pr.2) source es := by
  induction source generalizing es with
  | nil => cases compiled; exact .nil
  | cons x xs ih =>
    cases head : translate c interp x.rhs with
    | none => simp [outputCodes,head] at compiled
    | some e =>
      cases tail : outputCodes c interp xs with
      | none => simp [outputCodes,head,tail] at compiled
      | some rest =>
        have equal : (x.name,e) :: rest = es := by simpa [outputCodes,head,tail] using compiled
        subst es
        exact .cons ⟨rfl,head⟩ (ih tail)

theorem clause_exact {r interp clause table} (compiled : clauseCode r interp clause = some table) :
    SourceCodes r interp clause table.args table.outputs := by
  cases args : translateMany r.constructors interp (normalizeArgs clause.arguments) with
  | none => simp [clauseCode,args] at compiled
  | some a =>
    cases out : outputCodes r.constructors interp clause.outputs with
    | none => simp [clauseCode,args,out] at compiled
    | some o =>
      have shape : ClauseCode.mk a o = table := by simpa [clauseCode,args,out] using compiled
      subst table
      exact ⟨args_exact args,output_exact out⟩

theorem forest_exact {r interp} {clauses : List Clause} {ts : List ClauseCode}
    (compiled : clauseCodes r interp clauses = some ts) :
    All₂ (fun c t => SourceCodes r interp c t.args t.outputs) clauses ts := by
  induction clauses generalizing ts with
  | nil => cases compiled; exact .nil
  | cons c cs ih =>
    cases head : clauseCode r interp c with
    | none => simp [clauseCodes,head] at compiled
    | some start =>
      cases tail : clauseCodes r interp cs with
      | none => simp [clauseCodes,head,tail] at compiled
      | some rest =>
        have shape : start :: rest = ts := by simpa [clauseCodes,head,tail] using compiled
        subst ts
        exact .cons (clause_exact head) (ih tail)

end Yulang.GeneralDeclarativeSourceCodes321
