import Yulang.GeneralDeclarativeEvidenceFold325
import Yulang.GeneralDeclarativeSourceAdvance325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeDerivedSource325
open GeneralDeclarations (Checked Declaration Registry)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativePriority321 (Local selected_generated)
open GeneralDeclarativeFrameReadback325 (Frame Recorded observed sourceNames)
open GeneralDeclarativeAppliedSource325 (output_read_and_exact)
open GeneralDeclarativeNormalizeAssoc324 (one)
open GeneralDeclarativeBatch320 (collect)
open GeneralDeclarativeEqualities322 (Derives entails)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeOutputRequests323 (child_declared)
open GeneralDeclarativeEmissionForest322 (children)
open GeneralDeclarativeNFComplete324 (local_sound produces)
open GeneralDeclarativeModelStable324 (stable_exact)
open GeneralDeclarativeEvidenceFold325 (LocalWitness same_model)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralNominalInspection (Interpretation)
open CommonRoleOutermostResolver (Classify)

structure Current (s : State) (r : Registry) (i : Interpretation)
    {completed : Nat → Prop} (p : Supported s completed) (d : Demand)
    (impl : Declaration) (base : Nat → GeneralDeclarativeWhere319.Capture)
    (place : GeneralDeclarativeEmissionForest322.Placement) : Prop where
  frame : Frame s r i p d impl base place
  ordinary : ∃ rows, collect (one r i impl d (sourceNames impl place base).input) d.outputs = some rows ∧
    ∀ row ∈ rows, Derives s (.variable row.left) row.right

def Source (s : State) (r : Registry) (i : Interpretation)
    {completed : Nat → Prop} (p : Supported s completed) (d : Demand)
    (impl : Declaration) (kids : List Demand) : Prop :=
  ∃ base place, Current s r i p d impl base place ∧
    children impl (sourceNames impl place base) place = kids

abbrev Rule (s : State) (r : Registry) (i : Interpretation)
    {completed : Nat → Prop} (p : Supported s completed)
    (tests : GeneralDeclarativePriority321.Candidates) := Local s r i p tests (Source s r i p)

theorem recorded_to_current {s : State} {p : Supported s completed}
    (old : Recorded s r i p d impl base place) : Current s r i p d impl base place := by
  obtain ⟨rows,built,occupied⟩ := old.written
  exact ⟨old.frame,rows,built,fun row present => .row (occupied present)⟩

theorem ordinary_rules {s : State} {p : Supported s completed} (checked : Checked r)
    (visible : impl ∈ r.declarations) (current : Current s r i p d impl base place) :
    GeneralDeclarativeNFNode324.BodyCoverage r i d impl ∧
      GeneralDeclarativeModelStable324.StableUnder s
        (GeneralDeclarativeAssocRule323.SourceEquation r i d impl (sourceNames impl place base).input) := by
  obtain ⟨rows,built,written⟩ := current.ordinary
  obtain ⟨cover,exact⟩ := output_read_and_exact checked visible built
  exact ⟨cover,stable_exact.mpr (fun row h => entails (written row ((exact row).mpr h)))⟩

theorem local_witness {s : State} {p : Supported s completed} (checked : Checked r) :
    LocalWitness r i s (Rule s r i p tests) := by
  intro m valid d declared key kids chosen
  obtain ⟨impl,rfl,⟨⟨visible,role⟩,_⟩,base,place,frame,rfl⟩ := selected_generated chosen
  obtain ⟨cover,stable⟩ := ordinary_rules checked visible frame
  exact ⟨⟨impl,(sourceNames impl place base).input,rfl,
    local_sound checked visible role declared cover (observed checked visible frame.frame) stable m valid⟩,
    fun _ present => child_declared checked visible present⟩

theorem sound {s : State} {p : Supported s completed} (checked : Checked r)
    (declared : Declared r d) (model : Models s m)
    (outcome : Classify (Rule s r i p tests) d (.selected dict)) : Evidence r i m d dict :=
  same_model (local_witness checked) model declared outcome

end Yulang.GeneralDeclarativeDerivedSource325
