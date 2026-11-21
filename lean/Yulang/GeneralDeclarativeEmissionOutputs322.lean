import Yulang.GeneralDeclarativeSourceEmission322
import Yulang.GeneralDeclarativeExistingReturn322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeEmissionOutputs322
open GeneralDeclarativeSourceEmission322 (Names useOutput)
open GeneralDeclarativeEqualities322 (Derives entails)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeWhere319 (variables)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeSubstitution320 (logical logical_value)
open GeneralDeclarativeOutputFacts320 (childFact)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarations (Declaration Equation)
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarationDemands (outputTarget)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralNominalCenteredHeadMatCompilerSemantics (compiled_normalized translate_value)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)
open CommonRoleOutermostResolver (All₂)

def Direct (decl : Declaration) (eqn : Equation) : Prop :=
  ∃ binder, normalize eqn.rhs = .var binder ∧ binder ∈ decl.outputNames

def Agree (decl : Declaration) (names : Names) : Prop :=
  ∀ binder ∈ decl.outputNames, (names.input binder).center = names.output binder

theorem output_operand {s : State} {decl : Declaration} {names : Names}
    {eqn : Equation} {allocate : Nat → Nat}
    (coherent : Agree decl names)
    (normal : translate c interp (normalize eqn.rhs) = some norm)
    (derived : ¬Direct decl eqn →
      Derives s (.variable (useOutput decl names allocate eqn).target) (logical names.input .actual norm)) :
    Derives s (.variable (useOutput decl names allocate eqn).target) (logical names.input .actual norm) := by
  classical
  by_cases existing : Direct decl eqn
  · obtain ⟨binder,shape,outOnly⟩ := existing
    have e : norm = .variable binder := Option.some.inj (normal.symm.trans (by rw [shape]; rfl))
    subst norm
    have target : (useOutput decl names allocate eqn).target = names.output binder := by
      simp [useOutput,outputTarget,shape,outOnly,Names.old]
    rw [target,← coherent binder outOnly]
    exact .refl _
  · exact derived existing

/-- Output targets selected by the source emitter are retained. The
normalized where RHS can be read even when raw spelling differs. -/
theorem output_result {s : State} {names : Names}
    (original : translate c interp eqn.rhs = some raw)
    (normalized : translate c interp (normalize eqn.rhs) = some norm)
    (proof : Derives s (.variable (useOutput decl names allocate eqn).target) (logical names.input .actual norm)) :
    Result s (childFact c interp names.input eqn (useOutput decl names allocate eqn)) := by
  refine ⟨[⟨(useOutput decl names allocate eqn).target,logical names.input .actual raw⟩],
    by simp [childFact,useOutput,original],?_⟩
  intro row included m valid
  cases List.mem_singleton.mp included
  simp only [Holds,logical_value]
  have read := entails proof m valid
  simp only [Holds,logical_value] at read
  rw [translate_value (normalize eqn.rhs) normalized] at read
  exact eqv_trans read (eqv_symm (compiled_normalized (variables := variables names.input m) original))

theorem ordered_outputs {s : State} {decl : Declaration} {names : Names}
    {source : List Equation} (coherent : Agree decl names)
    (evidence : ∀ eqn ∈ source, ∃ raw norm, translate c interp eqn.rhs = some raw ∧
      translate c interp (normalize eqn.rhs) = some norm ∧
      (¬Direct decl eqn → Derives s (.variable (useOutput decl names allocate eqn).target)
        (logical names.input .actual norm))) :
    All₂ (fun eqn request => Result s (childFact c interp names.input eqn request))
      source (source.map (useOutput decl names allocate)) := by
  induction source with
  | nil => exact .nil
  | cons first more ih =>
    obtain ⟨raw,norm,one,two,proof⟩ := evidence first List.mem_cons_self
    exact .cons (output_result one two (output_operand coherent two proof))
      (ih (fun eqn member => evidence eqn (List.mem_cons_of_mem _ member)))

end Yulang.GeneralDeclarativeEmissionOutputs322
