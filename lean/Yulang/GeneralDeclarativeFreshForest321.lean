import Yulang.GeneralDeclarativeFreshChild321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeFreshForest321
open GeneralDeclarativeFreshCalls321 (SourceCodes codes seed demand from_append)
open GeneralDeclarativeFreshChild321 (compile_child)
open GeneralDeclarativeNewNames321 (numbered supply old_plus_extra)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralDeclarativeWhereProducer321 (Child)
open GeneralDeclarativeFresh321 (extend)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Clause Registry)
open CommonRoleOutermostResolver (All₂)

structure ClauseCode where
  args : List Expr
  outputs : List (Nat × Expr)

def allCodes (capture : Nat → Capture) (tables : List ClauseCode) : List Expr :=
  tables.flatMap fun code => codes capture code.args code.outputs

def children (capture : Nat → Capture) (first : Nat) : List Clause → List ClauseCode → List Demand
  | c :: clauses, row :: rows =>
    demand c.role first row.args row.outputs ::
      children capture (first+(codes capture row.args row.outputs).length) clauses rows
  | _,_ => []


theorem ordered_children {s : State} {capture : Nat → Capture}
    (source : All₂ (fun (c : Clause) (t : ClauseCode) => SourceCodes r interp c t.args t.outputs) clauses tables)
    (first : Nat) (stored : numbered first (allCodes capture tables) ⊆ s.equations) :
    All₂ (Child s r interp capture) clauses (children capture first clauses tables) := by
  induction source generalizing first with
  | nil => exact .nil
  | @cons clause table clauses tables head tail ih =>
    have both : numbered first (allCodes capture (table :: tables)) =
        numbered first (codes capture table.args table.outputs) ++
          numbered (first+(codes capture table.args table.outputs).length) (allCodes capture tables) := by
      exact from_append _ _ _
    have here : numbered first (codes capture table.args table.outputs) ⊆ s.equations := by
      intro row member
      exact stored (both.symm ▸ List.mem_append_left _ member)
    have later : numbered (first+(codes capture table.args table.outputs).length) (allCodes capture tables)
        ⊆ s.equations := by
      intro row member
      exact stored (both.symm ▸ List.mem_append_right _ member)
    exact .cons (compile_child head first here) (ih _ later)

/-- Generate all where children and all their named outputs, in order,
using a single ordinary assignment extension. No child is claimed to
select; the requested equalities do not settle its own dictionary. -/
theorem all_children_extension {s : State} {capture : Nat → Capture} {extra : List Nat}
    (source : All₂ (fun (c : Clause) (t : ClauseCode) => SourceCodes r interp c t.args t.outputs) clauses tables)
    (m) (valid : Models s m) :
    let expr := allCodes capture tables
    let defs := supply s extra expr
    let s' := appendFacts s defs
    Models s' (extend m defs) ∧
    (∀ name ∈ stateNames s ++ extra, extend m defs name = m name) ∧
    All₂ (Child s' r interp capture) clauses (children capture (seed s extra expr) clauses tables) := by
  dsimp only
  have equiv := old_plus_extra s extra (allCodes capture tables) m valid
  exact ⟨equiv.1,equiv.2,ordered_children source _ (fun _ there => List.mem_append_right _ there)⟩

end Yulang.GeneralDeclarativeFreshForest321
