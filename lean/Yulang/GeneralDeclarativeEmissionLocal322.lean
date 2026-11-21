import Yulang.GeneralDeclarativeEmissionForest322
import Yulang.GeneralDeclarativeExistingLocal322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeEmissionLocal322
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeSourceEmission322 (Names)
open GeneralDeclarativeEmissionForest322 (Placement children all_clauses)
open GeneralDeclarativeEmissionClause322 (Ready)
open GeneralDeclarativeEmissionOutputs322 (Agree)
open GeneralDeclarativeExistingLocal322 (Heads head_results)
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

structure Data (s : State) (p : Supported s completed) (r : Registry) (interp : Interpretation)
    (d : Demand) (decl : Declaration) (names : Names) (placement : Placement) : Prop where
  head : Heads s p r interp d decl names.input
  binderBounds : ∀ binder ∈ decl.inputNames, Bounds s (names.input binder)
  argumentBounds : ∀ arg ∈ d.arguments, Bounds s arg
  binders : Agree decl names
  whereReady : ∀ clause ∈ decl.requirements,
    Ready s r interp decl clause names (placement.compound clause) (placement.targets clause)
  actualOutput : ∀ out ∈ d.outputs, Settled s r interp decl d names.input out

/-- The actual child names are the source emitter's names, rather than a
hypothesis that arbitrary equivalent names were emitted. -/
theorem source_batch {s : State} {p : Supported s completed} (checked : Checked r)
    (visible : decl ∈ r.declarations) (role : decl.role = d.role)
    (data : Data s p r interp d decl names placement) :
    BatchRecipe s r interp d decl.id (children decl names placement) := by
  obtain ⟨a,ha,ea⟩ := zip_result (head_results data.head)
  obtain ⟨b,hb,eb⟩ := all_clauses data.binders data.whereReady
  obtain ⟨c,hc,ec⟩ := collect_result (f := rootFact r interp decl d names.input)
    (fun out there => settled_result checked visible (data.actualOutput out there))
  refine ⟨decl,names.input,a++b++c,rfl,visible,data.binderBounds,data.argumentBounds,
    by simp [nodeFacts,role,ha,hb,hc],?_⟩
  intro row listed
  rcases List.mem_append.mp listed with left|right
  · exact (List.mem_append.mp left).elim (ea row) (eb row)
  · exact ec row right

def Generates (s : State) (p : Supported s completed) (r : Registry) (interp : Interpretation)
    (d : Demand) (decl : Declaration) (kids : List Demand) : Prop :=
  ∃ names place, kids = children decl names place ∧ Data s p r interp d decl names place

theorem compiles {s : State} {p : Supported s completed} (checked : Checked r) :
    Compiles s r interp (Local s r interp p tests (Generates s p r interp)) := by
  intro d key kids picked
  obtain ⟨decl,rfl,⟨⟨visible,role⟩,_⟩,names,place,rfl,data⟩ := selected_generated picked
  exact .inr (source_batch checked visible role data)

theorem source_sound {s : State} {p : Supported s completed} (checked : Checked r)
    (m : Assignment) (valid : Models s m)
    (choice : Classify (Local s r interp p tests (Generates s p r interp)) d (.selected dict)) :
    Evidence r interp m d dict :=
  compile_classify checked (compiles checked) m valid choice

end Yulang.GeneralDeclarativeEmissionLocal322
