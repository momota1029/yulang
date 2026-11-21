import Yulang.GeneralDeclarativeNFWhere324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNFEmit324
open GeneralDeclarations (Clause Declaration Registry)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeSourceEmission322 (Names useOutput demand)
open GeneralDeclarativeEmissionForest322 (Placement children)
open GeneralDeclarativeEmissionOutputs322 (Direct Agree output_operand)
open GeneralDeclarativeEmissionOperands322 (Compound ordered_inputs)
open GeneralDeclarativeExistingClause322 (Refers input_results)
open GeneralDeclarativeEmissionClause322 (Ready)
open GeneralDeclarativeCompileLists321 (Result zip_result)
open GeneralDeclarativeArgumentFacts320 (whereFacts)
open GeneralDeclarativeNFWhere324 (namedFact clauseFacts)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarativeEqualities322 (Derives entails)
open GeneralDeclarativeBatch320 (zipFacts)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarationPatterns (normalize)
open CommonRoleOutermostResolver (All₂)

/-- Independent source readback at the normalized actual clause.
In particular, this structure makes no demand on the interpretation
of a hidden constructor inside a named RHS. -/
structure Read (s : State) (r : Registry) (interp : Interpretation) (decl : Declaration)
    (clause : Clause) (names : Names) (compound : Nat → GeneralDeclarativeWhere319.Capture)
    (targets : Nat → Nat) : Prop where
  args : ∃ codes : List Expr,
    All₂ (fun p e => translate r.constructors interp (normalize p) = some e) clause.arguments codes ∧
    (∀ (i : Nat) p e, clause.arguments[i]? = some p → codes[i]? = some e →
      Compound p → Refers s names.input e (compound i))
  outputs : ∀ eqn ∈ clause.outputs, ∃ norm,
    translate r.constructors interp (normalize eqn.rhs) = some norm ∧
    (¬Direct decl eqn → Derives s (.variable (useOutput decl names targets eqn).target)
      (logical names.input .actual norm))

theorem old_implies {s : State} (old : Ready s r interp decl clause names compound targets) :
    Read s r interp decl clause names compound targets :=
  ⟨old.args,fun row used => by
    obtain ⟨_,nf,_,written,needed⟩ := old.outputs row used
    exact ⟨nf,written,needed⟩⟩

theorem ordered_named {s : State} {names : Names} {decl : Declaration} {targets : Nat → Nat}
    {source : List GeneralDeclarations.Equation} (coherent : Agree decl names)
    (ordinary : ∀ eqn ∈ source, ∃ nf,
      translate c interp (normalize eqn.rhs) = some nf ∧
      (¬Direct decl eqn → Derives s (.variable (useOutput decl names targets eqn).target)
        (logical names.input .actual nf))) :
    All₂ (fun eqn request => Result s (namedFact c interp names.input eqn request))
      source (source.map (useOutput decl names targets)) := by
  induction source with
  | nil => exact .nil
  | cons first rest ih =>
    obtain ⟨nf,printed,ordinaryEq⟩ := ordinary first List.mem_cons_self
    refine .cons ⟨[⟨(useOutput decl names targets first).target,logical names.input .actual nf⟩],
      by simp [namedFact,useOutput,printed],?_⟩
      (ih (fun e present => ordinary e (List.mem_cons_of_mem _ present)))
    intro row used
    cases List.mem_singleton.mp used
    exact entails (output_operand coherent printed ordinaryEq)

theorem ordinary_clause {s : State}
    (agree : Agree decl names) (read : Read s r interp decl clause names compound targets) :
    Result s (clauseFacts r interp names.input clause (demand decl clause names compound targets)) := by
  obtain ⟨codes,ordered,compoundReads⟩ := read.args
  have args := ordered_inputs (s := s) ordered 0 compound (by simpa using compoundReads)
  obtain ⟨a,ha,ea⟩ := zip_result (f := whereFacts r.constructors interp names.input) (input_results ordered args)
  obtain ⟨b,hb,eb⟩ := zip_result (f := namedFact r.constructors interp names.input)
    (ordered_named agree read.outputs)
  refine ⟨a++b,by simp [clauseFacts,demand,ha,hb],?_⟩
  intro row present
  exact (List.mem_append.mp present).elim (ea row) (eb row)

theorem ordinary_forest {s : State} {place : Placement}
    (agree : Agree decl names)
    (read : ∀ clause ∈ decl.requirements, Read s r interp decl clause names (place.compound clause) (place.targets clause)) :
    Result s (zipFacts (clauseFacts r interp names.input) decl.requirements (children decl names place)) := by
  have aux (clauses : List Clause)
      (next : ∀ cl ∈ clauses, Read s r interp decl cl names (place.compound cl) (place.targets cl)) :
      All₂ (fun c d => Result s (clauseFacts r interp names.input c d))
      clauses (clauses.map fun c => demand decl c names (place.compound c) (place.targets c)) := by
    induction clauses with
    | nil => exact .nil
    | cons first rest ih =>
      exact .cons (ordinary_clause agree (next first List.mem_cons_self))
        (ih (fun c found => next c (List.mem_cons_of_mem _ found)))
  exact zip_result (aux decl.requirements read)

end Yulang.GeneralDeclarativeNFEmit324
