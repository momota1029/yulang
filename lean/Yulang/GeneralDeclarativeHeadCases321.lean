import Yulang.GeneralDeclarativeNominalHead321
import Yulang.GeneralDeclarativeNormalizedLocal321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeHeadCases321
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeTrace321 (Trace Links Occurrence)
open GeneralDeclarativeTraceHead321 (Read)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeArgumentFacts320 (headFact)
open GeneralDeclarativeWhereProducer321 (Child)
open GeneralDeclarativeNodeProducer321 (ReturnRead attach_head)
open GeneralDeclarativeNormalizedCompiler321 (normalized_result)
open GeneralDeclarativeNominalHead321 (supported_nominal_head)
open GeneralDeclarativeEntailment320 (BatchRecipe)
open GeneralDeclarativePriority321 (Local selected_generated)
open GeneralDeclarativeCompilerTree320 (Compiles compile_classify)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarationPatterns (Constructors Pattern normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarations (Declaration Registry Checked)
open CommonRoleOutermostResolver (All₂ Classify)

inductive Derived {s : State} (p : Supported s completed) (capture : Nat → Capture) (arg : Capture)
    (code : Expr) : List Occurrence → Prop where
  | walked : Read (restriction p) capture arg code uses → Derived p capture arg code uses
  | invariant :
    Bounds s arg →
    (⟨arg.lower,.nominal lo xs⟩ : Equation) ∈ (restriction p).equations →
    (⟨arg.upper,.nominal hi ys⟩ : Equation) ∈ s.equations →
    Trace (restriction p) .actual arg.lower code uses →
    Derived p capture arg code uses

theorem derived_row (p : Supported s completed)
    (raw : translate c interp pattern = some original)
    (normal : translate c interp (normalize pattern) = some code)
    (derived : Derived p capture arg code uses)
    (links : Links (restriction p) capture uses) : Result s (headFact c interp capture arg pattern) := by
  cases derived with
  | walked observation => exact normalized_result p raw normal observation links
  | invariant span lower upper proof =>
    exact supported_nominal_head p span lower upper raw normal proof links

structure Head (s : State) (p : Supported s completed) (r : Registry) (interp : Interpretation)
    (d : Demand) (decl : Declaration) (capture : Nat → Capture) (read : List Occurrence) : Prop where
  occurrences : All₂ (fun arg pattern => ∃ original code uses,
    translate r.constructors interp pattern = some original ∧
    translate r.constructors interp (normalize pattern) = some code ∧
    Derived p capture arg code uses ∧ uses ⊆ read) d.arguments decl.head
  same : Links (restriction p) capture read

def Generates (s : State) (p : Supported s completed) (r : Registry) (interp : Interpretation)
    (d : Demand) (decl : Declaration) (kids : List Demand) : Prop :=
  ∃ capture seen, Head s p r interp d decl capture seen ∧
    (∀ name ∈ decl.inputNames, Bounds s (capture name)) ∧
    (∀ arg ∈ d.arguments, Bounds s arg) ∧
    All₂ (Child s r interp capture) decl.requirements kids ∧
    (∀ out ∈ d.outputs, ReturnRead s r interp decl d capture out)

theorem compiles {s : State} {p : Supported s completed} (checked : Checked r) :
    Compiles s r interp (Local s r interp p tests (Generates s p r interp)) := by
  intro d key kids picked
  obtain ⟨decl,rfl,⟨⟨vis,role⟩,_⟩,cap,occ,head,caps,bounds,child,outs⟩ := selected_generated picked
  refine .inr (attach_head checked vis role caps bounds ?_ child outs)
  apply GeneralDeclarativeNormalized320.ordered_map head.occurrences
  rintro arg _ pattern _ ⟨original,code,uses,raw,norm,present,used⟩
  exact derived_row p raw norm present (fun o h => head.same o (used h))

theorem sound {s : State} {p : Supported s completed} (checked : Checked r) (m : Assignment)
    (fits : Models s m) (picked : Classify (Local s r interp p tests (Generates s p r interp)) d (.selected dict)) :
    Evidence r interp m d dict :=
  compile_classify checked (compiles checked) m fits picked

end Yulang.GeneralDeclarativeHeadCases321
