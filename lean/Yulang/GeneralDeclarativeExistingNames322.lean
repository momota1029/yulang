import Yulang.GeneralDeclarativeNameFill322
import Yulang.GeneralDeclarativeSourceCodes321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeExistingNames322
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeExistingClause322 (Existing Refers NamedRefers)
open GeneralDeclarativeNameFill322 (Pool CoversArg Covered input associated zipNames zip_build input_build output_build)
open GeneralDeclarativeFreshCalls321 (SourceCodes)
open GeneralDeclarativeFreshForest321 (ClauseCode)
open GeneralDeclarativeSourceCodes321 (clauseCodes forest_exact)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarations (Clause)
open CommonRoleOutermostResolver (All₂)

structure Pools where
  arguments : List Pool
  outputTargets : List (List Nat)

def Covers (s : State) (capture : Nat → Capture) (code : ClauseCode) (pools : Pools) : Prop :=
  All₂ (CoversArg s capture) code.args pools.arguments ∧
  All₂ (fun entry pool => Covered s pool (logical capture .actual entry.2))
    code.outputs pools.outputTargets

noncomputable def recover (s : State) (capture : Nat → Capture) (role : Nat)
    (code : ClauseCode) (pools : Pools) : Option Demand := do
  let args ← zipNames (input s capture) code.args pools.arguments
  let names ← zipNames (associated s capture) code.outputs pools.outputTargets
  pure ⟨role,args,names⟩

theorem recovered {s : State} {capture : Nat → Capture}
    (source : SourceCodes r interp clause code.args code.outputs)
    (covers : Covers s capture code pools) :
    ∃ request, recover s capture clause.role code pools = some request ∧
      Existing s r interp capture clause request := by
  have one := zip_build
    (f := input s capture)
    (facts := fun code pool arg => Refers s capture code arg ∧
      arg.lower ∈ pool.lower ∧ arg.center ∈ pool.actual ∧ arg.upper ∈ pool.upper)
    (fun _ _ h => input_build h) covers.1
  have two := zip_build
    (f := associated s capture)
    (facts := fun code pool out => NamedRefers s capture code out ∧ out.target ∈ pool)
    (fun _ _ h => output_build h) covers.2
  obtain ⟨args,foundArgs,readArgs⟩ := one
  obtain ⟨outs,foundOut,readOut⟩ := two
  exact ⟨⟨clause.role,args,outs⟩,by simp [recover,foundArgs,foundOut],rfl,_,_,source,
    GeneralDeclarativeNormalized320.ordered_map readArgs (fun _ _ _ _ ⟨_,h⟩ => h.1),
    GeneralDeclarativeNormalized320.ordered_map readOut (fun _ _ _ _ ⟨_,h⟩ => h.1)⟩

noncomputable def recoverForest (s : State) (capture : Nat → Capture) :
    List Clause → List (ClauseCode × Pools) → Option (List Demand) :=
  zipNames fun clause data => recover s capture clause.role data.1 data.2

/-- The existing children are obtained by the actual ordered source
compiler and pools of already-existing names. Fields which were supplied
by the caller are preserved by using their singleton pools. -/
theorem recovered_forest {s : State} {capture : Nat → Capture}
    {clauses : List Clause} {tables : List (ClauseCode × Pools)}
    (compiled : clauseCodes r interp clauses = some (tables.map Prod.fst))
    (covers : ∀ table ∈ tables, Covers s capture table.1 table.2) :
    ∃ kids, recoverForest s capture clauses tables = some kids ∧
      All₂ (Existing s r interp capture) clauses kids := by
  have source := forest_exact compiled
  have aux {clauses : List Clause} {tables : List (ClauseCode × Pools)}
      (source : All₂ (fun c t => SourceCodes r interp c t.args t.outputs) clauses (tables.map Prod.fst))
      (covered : ∀ table ∈ tables, Covers s capture table.1 table.2) :
      All₂ (fun c t => SourceCodes r interp c t.1.args t.1.outputs ∧ Covers s capture t.1 t.2) clauses tables := by
    induction tables generalizing clauses with
    | nil => cases source; exact .nil
    | cons first more ih =>
      cases source with
      | cons head tail =>
        exact .cons ⟨head,covered first List.mem_cons_self⟩
          (ih tail (fun row there => covered row (List.mem_cons_of_mem _ there)))
  have built := zip_build
    (f := fun c t => recover s capture c.role t.1 t.2)
    (facts := fun c _ d => Existing s r interp capture c d)
    (fun _ _ h => recovered h.1 h.2) (aux source covers)
  obtain ⟨kids,selection,criteria⟩ := built
  exact ⟨kids,selection,
    GeneralDeclarativeNormalized320.ordered_map criteria (fun _ _ _ _ ⟨_,h⟩ => h)⟩

end Yulang.GeneralDeclarativeExistingNames322
