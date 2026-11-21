import Yulang.GeneralDeclarativeExistingReturn322
import Yulang.GeneralDeclarativeTermHead322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeExistingLocal322
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeHeadCases321 (Head derived_row)
open GeneralDeclarativeTermHead322 (Actual actual_result)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarationPatterns (normalize)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralDeclarativeExistingClause322 (Existing existing_result)
open GeneralDeclarativeExistingReturn322 (Settled settled_result)
open GeneralDeclarativeCompileLists321 (Result zip_result collect_result)
open GeneralDeclarativeArgumentFacts320 (headFact)
open GeneralDeclarativeOutputFacts320 (rootFact)
open GeneralDeclarativeNodeFacts320 (nodeFacts clauseFacts)
open GeneralDeclarativeEntailment320 (BatchRecipe)
open GeneralDeclarativeCompilerTree320 (Compiles compile_classify)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativePriority321 (Local selected_generated)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarations (Declaration Registry Checked)
open CommonRoleOutermostResolver (All₂ Classify)

def Heads (s : State) (p : Supported s completed) (r : Registry) (interp : Interpretation)
    (d : Demand) (decl : Declaration) (capture : Nat → Capture) : Prop :=
  (∃ seen, Head s p r interp d decl capture seen) ∨
    All₂ (fun arg pat => ∃ raw norm, translate r.constructors interp pat = some raw ∧
      translate r.constructors interp (normalize pat) = some norm ∧ Actual s capture arg norm)
      d.arguments decl.head

theorem head_results {s : State} {p : Supported s completed}
    (proof : Heads s p r interp d decl capture) :
    All₂ (fun arg pat => Result s (headFact r.constructors interp capture arg pat)) d.arguments decl.head := by
  rcases proof with ⟨seen,head⟩|term
  · apply GeneralDeclarativeNormalized320.ordered_map head.occurrences
    rintro arg _ pat _ ⟨raw,code,uses,translated,norm,observed,subset⟩
    exact derived_row p translated norm observed (fun o h => head.same o (subset h))
  · apply GeneralDeclarativeNormalized320.ordered_map term
    rintro arg _ pat _ ⟨raw,norm,one,two,read⟩
    exact actual_result one two read

def Proven (s : State) (p : Supported s completed) (r : Registry) (interp : Interpretation)
    (d : Demand) (decl : Declaration) (kids : List Demand) : Prop :=
  ∃ capture, Heads s p r interp d decl capture ∧
    (∀ n ∈ decl.inputNames, Bounds s (capture n)) ∧
    (∀ arg ∈ d.arguments, Bounds s arg) ∧
    All₂ (Existing s r interp capture) decl.requirements kids ∧
    ∀ out ∈ d.outputs, Settled s r interp decl d capture out

/-- The chosen logical names and the same state are retained. No
conservative extension is used to make an existing output equality true. -/
theorem actual_batch {s : State} {p : Supported s completed}
    (checked : Checked r) (visible : decl ∈ r.declarations) (role : decl.role = d.role)
    (source : Proven s p r interp d decl kids) :
    BatchRecipe s r interp d decl.id kids := by
  obtain ⟨capture,head,capBounds,argBounds,results,outputs⟩ := source
  obtain ⟨a,ha,ea⟩ := zip_result (head_results head)
  obtain ⟨b,hb,eb⟩ := zip_result (f := clauseFacts r interp capture)
    (GeneralDeclarativeNormalized320.ordered_map results (fun _ _ _ _ read => existing_result read))
  obtain ⟨c,hc,ec⟩ := collect_result (f := rootFact r interp decl d capture)
    (fun out used => settled_result checked visible (outputs out used))
  refine ⟨decl,capture,a ++ b ++ c,rfl,visible,capBounds,argBounds,by simp [nodeFacts,role,ha,hb,hc],?_⟩
  intro row there
  rcases List.mem_append.mp there with before|after
  · exact (List.mem_append.mp before).elim (ea row) (eb row)
  · exact ec row after

theorem local_compiles {s : State} {p : Supported s completed} (checked : Checked r) :
    Compiles s r interp (Local s r interp p tests (Proven s p r interp)) := by
  intro d key kids selected
  obtain ⟨decl,rfl,⟨⟨visible,role⟩,_⟩,derivation⟩ := selected_generated selected
  exact .inr (actual_batch checked visible role derivation)

theorem sound {s : State} {p : Supported s completed}
    (checked : Checked r) (m : Assignment) (valid : Models s m)
    (accepted : Classify (Local s r interp p tests (Proven s p r interp)) d (.selected dict)) :
    Evidence r interp m d dict :=
  compile_classify checked (local_compiles checked) m valid accepted

end Yulang.GeneralDeclarativeExistingLocal322
