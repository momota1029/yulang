import Yulang.GeneralDeclarativeDemand320
import Yulang.GeneralDictionaryAssociatedProvenance

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 3000000
namespace Yulang.GeneralDeclarativeOutputs320
open CommonNominalFullCarrier (Equivalent)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeHead320 (State Models Read source_head)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand sourceValue)
open GeneralNominalCenteredHeadMatExpressions (Expr translate translateMany translateDefault translateDefaults)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarationPatterns (Constructors Pattern)
open GeneralDeclarations (Clause Declaration Equation)
open GeneralDictionaryAssociatedProvenance (Body Supplies lookup_exact)
open GeneralSourceState (Output)
open CommonRoleOutermostResolver (All₂)

mutual
 def termPattern : Roles.Term → Pattern
  | .var n => .var n
  | .app k ts => .app k (termPatterns ts)
 def termPatterns : List Roles.Term → List Pattern
  | [] => []
  | first :: rest => termPattern first :: termPatterns rest
end

mutual
 theorem default_translation (catalogue : Constructors) (interp : Interpretation) (term : Roles.Term) :
    translate catalogue interp (termPattern term) = translateDefault catalogue interp term := by
  cases term with
  | var => rfl
  | app key args =>
    simp only [termPattern,translate,translateDefault,defaults_translation catalogue interp args]
 termination_by sizeOf term
 theorem defaults_translation (catalogue : Constructors) (interp : Interpretation) (terms : List Roles.Term) :
    translateMany catalogue interp (termPatterns terms) = translateDefaults catalogue interp terms := by
  cases terms with
  | nil => rfl
  | cons first rest =>
    simp only [termPatterns,translateMany,translateDefaults,default_translation catalogue interp first,
      defaults_translation catalogue interp rest]
 termination_by sizeOf terms
end

def positional (d : Demand) (index : Nat) : Capture :=
  let center := (d.arguments[index]?.map Capture.center).getD 0
  ⟨center,center,center⟩

theorem positional_exact (d : Demand) {index : Nat} {argument : Capture}
    (there : d.arguments[index]? = some argument) : positional d index = ⟨argument.center,argument.center,argument.center⟩ := by
  simp [positional,there]

def bodyPattern : Body → Pattern
  | .explicit equation => equation.rhs
  | .default _ _ term => termPattern term

def bodyCapture (d : Demand) (capture : Nat → Capture) : Body → Nat → Capture
  | .explicit _ => capture
  | .default _ _ _ => positional d

def compile (catalogue : Constructors) (interp : Interpretation) : Body → Option Expr
  | .explicit equation => translate catalogue interp equation.rhs
  | .default _ _ term => translateDefault catalogue interp term

theorem compile_exact (catalogue : Constructors) (interp : Interpretation) (body : Body) :
    translate catalogue interp (bodyPattern body) = compile catalogue interp body := by
  cases body with
  | explicit => rfl
  | default _ _ term => exact default_translation catalogue interp term

/-- A named where requirement retains actual source RHS and target. The
equation is in the declarative state; this does not assume a child has selected
an implementation which proves the named result. -/
def ChildOutput (s : State) (catalogue : Constructors) (interp : Interpretation)
    (capture : Nat → Capture) (equation : Equation) (request : Output) : Prop :=
  request.name = equation.name ∧
  ∃ code, translate catalogue interp equation.rhs = some code ∧
    Read s capture .actual request.target code

def ChildOutputMeaning (catalogue : Constructors) (interp : Interpretation)
    (capture : Nat → Capture) (m : Assignment) (equation : Equation) (request : Output) : Prop :=
  request.name = equation.name ∧
  Equivalent (m request.target).1 (sourceValue catalogue interp capture m equation.rhs)

theorem child_output {s catalogue interp capture equation request}
    (proof : ChildOutput s catalogue interp capture equation request) (m : Assignment) (valid : Models s m) :
    ChildOutputMeaning catalogue interp capture m equation request := by
  obtain ⟨named,code,comp,read⟩ := proof
  exact ⟨named,source_head comp read m valid⟩

theorem child_outputs {s catalogue interp capture equations requests}
    (proof : All₂ (ChildOutput s catalogue interp capture) equations requests)
    (m : Assignment) (valid : Models s m) :
    All₂ (ChildOutputMeaning catalogue interp capture m) equations requests := by
  induction proof with
  | nil => exact .nil
  | cons h _ ih => exact .cons (child_output h m valid) ih

def RootOutput (s : State) (roles : Roles.RoleDecls) (catalogue : Constructors) (interp : Interpretation)
    (declaration : Declaration) (d : Demand) (capture : Nat → Capture) (out : Output) : Prop :=
  ∃ body code, GeneralDictionaryAssociatedProvenance.lookup roles declaration out.name = some body ∧
    compile catalogue interp body = some code ∧
    Read s (bodyCapture d capture body) .actual out.target code

def OutputMeaning (roles : Roles.RoleDecls) (catalogue : Constructors) (interp : Interpretation)
    (declaration : Declaration) (d : Demand) (capture : Nat → Capture) (m : Assignment) (out : Output) : Prop :=
  ∃ body, Supplies roles declaration out.name body ∧
    Equivalent (m out.target).1
      (sourceValue catalogue interp (bodyCapture d capture body) m (bodyPattern body))

theorem root_output {s roles catalogue interp declaration d capture out}
    (unique : (declaration.associated.map Equation.name).Nodup)
    (proof : RootOutput s roles catalogue interp declaration d capture out)
    (m : Assignment) (valid : Models s m) :
    OutputMeaning roles catalogue interp declaration d capture m out := by
  obtain ⟨body,code,lookup,comp,read⟩ := proof
  refine ⟨body,(lookup_exact roles declaration unique _ _).mp lookup,?_⟩
  exact source_head ((compile_exact catalogue interp body).trans comp) read m valid

end Yulang.GeneralDeclarativeOutputs320
