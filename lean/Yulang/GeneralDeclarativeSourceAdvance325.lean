import Yulang.GeneralDeclarativeFrameIncrease325
import Yulang.GeneralDeclarativeSourceSelection325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeSourceAdvance325
open GeneralDeclarations (Checked)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativePriority321 (Local selected_generated)
open GeneralDeclarativeFrameReadback325 (Frame Recorded sourceNames)
open GeneralDeclarativeFrameIncrease325 (after_emit)
open GeneralDeclarativeNormalizeAssoc324 (one)
open GeneralDeclarativeAppliedSource325 (exact_effect)
open GeneralDeclarativeOutputOrigins323 (emit)
open GeneralDeclarativeAssocRule323 (SourceEquation)
open GeneralDeclarativeEntailment320 (appendFacts Holds)
open GeneralDeclarativeBatch320 (collect)
open GeneralDeclarativeEmissionForest322 (children)
open CommonRoleOutermostResolver (Frontier)

def PreSource (s : State) (r : GeneralDeclarations.Registry)
    (i : GeneralNominalInspection.Interpretation) {complete : Nat → Prop}
    (p : Supported s complete) (d : Demand) (decl : GeneralDeclarations.Declaration) (kids : List Demand) : Prop :=
  ∃ base place, Frame s r i p d decl base place ∧
    children decl (sourceNames decl place base) place = kids ∧
    ∃ rows, collect (one r i decl d (sourceNames decl place base).input) d.outputs = some rows

abbrev Rule (s : State) (r : GeneralDeclarations.Registry)
    (i : GeneralNominalInspection.Interpretation) {complete : Nat → Prop}
    (p : Supported s complete) (tests : GeneralDeclarativePriority321.Candidates) :=
  Local s r i p tests (PreSource s r i p)

theorem after_ordinary {s : State} {p : Supported s complete}
    (frame : Frame s r i p d impl base place)
    (printed : collect (one r i impl d (sourceNames impl place base).input) d.outputs = some rows)
    (owner : Nat) :
    Recorded (appendFacts s rows) r i (emit p owner rows) d impl base place :=
  ⟨after_emit frame rows owner,rows,printed,fun _ there => List.mem_append_right _ there⟩

/-- One independently selected source application has a genuine ordinary
model effect and a recorded frame afterward. It need not leave any of
the candidate priority/uniqueness/K2 decisions unchanged. -/
theorem selected_application {s : State} {p : Supported s complete} (checked : Checked r)
    (chose : Rule s r i p tests d (.selected key kids)) (owner : Nat) :
    ∃ decl base place rows,
      decl.id = key ∧ decl ∈ r.declarations ∧ children decl (sourceNames decl place base) place = kids ∧
      collect (one r i decl d (sourceNames decl place base).input) d.outputs = some rows ∧
      Recorded (appendFacts s rows) r i (emit p owner rows) d decl base place ∧
      ∀ m, Models (appendFacts s rows) m ↔ Models s m ∧
        ∀ row, SourceEquation r i d decl (sourceNames decl place base).input row → Holds m row := by
  obtain ⟨impl,rfl,⟨⟨visible,_⟩,_⟩,base,place,frame,fixed,rows,printed⟩ := selected_generated chose
  exact ⟨impl,base,place,rows,rfl,visible,fixed,printed,after_ordinary frame printed owner,
    exact_effect checked visible printed⟩

theorem recorded_is_pre {s : State} {support : Supported s complete}
    (source : GeneralDeclarativeSourceSelection325.Rule s r i support tests d result) :
    Rule s r i support tests d result := by
  apply GeneralDeclarativeSourceSelection325.map_generated ?_ source
  rintro asked impl _ kids ⟨base,place,stored,fixed⟩
  obtain ⟨rows,printed,_⟩ := stored.written
  exact ⟨base,place,stored.frame,fixed,rows,printed⟩

end Yulang.GeneralDeclarativeSourceAdvance325
