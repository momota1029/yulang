import Yulang.GeneralDeclarativeNormalizedCompiler321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNormalizedLocal321
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeNormalizedCompiler321 (HeadWalk normalized_batch)
open GeneralDeclarativeWhereProducer321 (Child)
open GeneralDeclarativeNodeProducer321 (ReturnRead)
open GeneralDeclarativePriority321 (Local selected_generated)
open GeneralDeclarativeCompilerTree320 (Compiles compile_classify)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarations (Declaration Registry Checked)
open CommonRoleOutermostResolver (Classify All₂)

def Generates (s : State) (p : Supported s completed) (r : Registry) (interp : Interpretation)
    (d : Demand) (decl : Declaration) (kids : List Demand) : Prop :=
  ∃ capture seen, HeadWalk s p r interp d decl capture seen ∧
    (∀ binder ∈ decl.inputNames, Bounds s (capture binder)) ∧
    (∀ arg ∈ d.arguments, Bounds s arg) ∧
    All₂ (Child s r interp capture) decl.requirements kids ∧
    (∀ out ∈ d.outputs, ReturnRead s r interp decl d capture out)

theorem normalized_compiles {s : State} {p : Supported s completed} (checked : Checked r) :
    Compiles s r interp (Local s r interp p tests (Generates s p r interp)) := by
  intro d key kids selected
  obtain ⟨decl,rfl,⟨⟨visible,role⟩,_⟩,capture,seen,head,capBounds,bounds,children,output⟩ :=
    selected_generated selected
  exact .inr (normalized_batch checked visible role capBounds bounds head children output)

theorem normalized_classify_sound {s : State} {p : Supported s completed} (checked : Checked r)
    (m : Assignment) (valid : Models s m)
    (classification : Classify (Local s r interp p tests (Generates s p r interp)) d (.selected dict)) :
    Evidence r interp m d dict :=
  compile_classify checked (normalized_compiles checked) m valid classification

end Yulang.GeneralDeclarativeNormalizedLocal321
