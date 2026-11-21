import Yulang.GeneralDeclarativeSourceCodes321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeFreshExact321
open GeneralDeclarativeFreshCalls321 (SourceCodes arguments results codes argCode demand from_append length_argCode)
open GeneralDeclarativeFreshForest321 (ClauseCode allCodes children)
open GeneralDeclarativeSourceCodes321 (clauseCodes forest_exact)
open GeneralDeclarativeNewNames321 (numbered)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarativeBatch320 (zipFacts)
open GeneralDeclarativeArgumentFacts320 (whereFacts)
open GeneralDeclarativeOutputFacts320 (childFact)
open GeneralDeclarativeNodeFacts320 (clauseFacts)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarations (Clause)
open CommonRoleOutermostResolver (All₂)

theorem input_exact {patterns : List Pattern} {exps : List Expr}
    (compiled : All₂ (fun p e => translate c interp (normalize p) = some e) patterns exps)
    (capture : Nat → Capture) (start : Nat) :
    zipFacts (whereFacts c interp capture) (arguments start exps) patterns =
      some (numbered start (exps.flatMap (argCode capture))) := by
  induction compiled generalizing start with
  | nil => rfl
  | cons one rest ih =>
    simp [arguments,zipFacts,whereFacts,one,ih,numbered,argCode]

theorem output_exact {out : List GeneralDeclarations.Equation} {exps : List (Nat × Expr)}
    (compiled : All₂ (fun eqn p => p.1 = eqn.name ∧ translate c interp eqn.rhs = some p.2) out exps)
    (capture : Nat → Capture) (start : Nat) :
    zipFacts (childFact c interp capture) out (results start exps) =
      some (numbered start (exps.map (fun p => logical capture .actual p.2))) := by
  induction compiled generalizing start with
  | nil => rfl
  | @cons eqn one outs es freshly tail ih =>
    rcases one with ⟨name,code⟩
    have same : name = eqn.name := freshly.1
    have emitted : translate c interp eqn.rhs = some code := freshly.2
    simp [results,zipFacts,childFact,same,emitted,ih,numbered]

theorem exact_clause (proof : SourceCodes r interp clause args out)
    (capture : Nat → Capture) (start : Nat) :
    clauseFacts r interp capture clause (demand clause.role start args out) =
      some (numbered start (codes capture args out)) := by
  simp only [clauseFacts,demand]
  rw [input_exact proof.arguments,output_exact proof.outputs,codes,from_append,length_argCode]
  rfl

/-- Byte-for-byte formal equation list equality: no item is silently lost
or coalesced when the source uses the same binder or name more than once. -/
theorem exact_forest {clauses : List Clause} {ts : List ClauseCode}
    (compiled : clauseCodes r interp clauses = some ts) (capture : Nat → Capture) (start : Nat) :
    zipFacts (clauseFacts r interp capture) clauses (children capture start clauses ts) =
      some (numbered start (allCodes capture ts)) := by
  have source := forest_exact compiled
  clear compiled
  induction source generalizing start with
  | nil => rfl
  | cons first tail ih =>
    simp only [children,allCodes,List.flatMap_cons,zipFacts,exact_clause first,ih,from_append]
    rfl

end Yulang.GeneralDeclarativeFreshExact321
