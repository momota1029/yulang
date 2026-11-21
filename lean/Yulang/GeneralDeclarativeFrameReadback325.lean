import Yulang.GeneralDeclarativeHeadFrame325
import Yulang.GeneralDeclarativeProducedNames325
import Yulang.GeneralDeclarativeAppliedSource325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeFrameReadback325
open GeneralDeclarations (Checked Declaration Clause Registry)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeHeadFrame325 (FromSource ordered)
open GeneralDeclarativeNFComplete324 (ReadBack)
open GeneralDeclarativeNFNode324 (BodyCoverage)
open GeneralDeclarativeNFEmit324 (Read)
open GeneralDeclarativeProducedNames325 (table coherent exact_input)
open GeneralDeclarativeClauseOrigins325 (Origin from_ordinary_rows)
open GeneralDeclarativeEmissionForest322 (Placement children)
open GeneralDeclarativeEmissionOperands322 (Compound)
open GeneralDeclarativeEmissionOutputs322 (Direct)
open GeneralDeclarativeSourceEmission322 (Names useOutput)
open GeneralDeclarativeAppliedSource325 (stable_after_written)
open GeneralDeclarativeNormalizeAssoc324 (one)
open GeneralDeclarativeBatch320 (collect)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarativeAssocRule323 (SourceEquation)
open GeneralDeclarativeModelStable324 (StableUnder)
open GeneralNominalCenteredHeadMatExpressions (Expr translate translateMany)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarationPatterns (Pattern normalize)
open CommonRoleOutermostResolver (All₂)

structure ClauseFrame (s : State) (r : Registry) (i : Interpretation)
    (impl : Declaration) (cl : Clause) (names : Names) (place : Placement) : Prop where
  input : ∃ codes, translateMany r.constructors i (cl.arguments.map normalize) = some codes ∧
    ∀ (pos : Nat) (p : Pattern) (e : Expr),
      cl.arguments[pos]? = some p → codes[pos]? = some e → Compound p →
      Origin s (place.compound cl pos).lower (logical names.input .lower e) ∧
      Origin s (place.compound cl pos).center (logical names.input .actual e) ∧
      Origin s (place.compound cl pos).upper (logical names.input .upper e)
  output : ∀ eq ∈ cl.outputs, ∃ e, translate r.constructors i (normalize eq.rhs) = some e ∧
    (¬Direct impl eq → Origin s (useOutput impl names (place.targets cl) eq).target
      (logical names.input .actual e))

theorem clause {s : State} (source : ClauseFrame s r i impl cl names place) :
    Read s r i impl cl names (place.compound cl) (place.targets cl) := by
  obtain ⟨_,compiled,registered⟩ := source.input
  exact from_ordinary_rows compiled registered source.output

def placeById (impl : Declaration) (place : Placement) (key eq : Nat) : Nat :=
  ((impl.requirements.find? fun cl => cl.id == key).map fun cl => place.targets cl eq).getD 0

def sourceNames (impl : Declaration) (place : Placement) (base : Nat → Capture) : Names :=
  table impl (placeById impl place) base

structure Frame (s : State) (r : Registry) (i : Interpretation)
    {complete : Nat → Prop} (support : Supported s complete) (d : Demand) (impl : Declaration)
    (base : Nat → Capture) (place : Placement) : Prop where
  head : All₂
    (fun a p => Bounds s a ∧ FromSource s r.constructors i support
      (sourceNames impl place base).input a p)
    d.arguments impl.head
  ranges : ∀ binder ∈ impl.inputNames, Bounds s (base binder)
  clauses : ∀ cl ∈ impl.requirements, ClauseFrame s r i impl cl
    (sourceNames impl place base) place

theorem observed {s : State} {support : Supported s complete} (checked : Checked r)
    (visible : impl ∈ r.declarations) (frame : Frame s r i support d impl base place) :
    ReadBack s r i d impl (sourceNames impl place base) place := by
  refine ⟨ordered frame.head,?_,coherent _ _ _,fun c used => clause (frame.clauses c used)⟩
  intro binder used
  unfold sourceNames
  rw [exact_input (checked.2 impl visible) used]
  exact frame.ranges binder used

structure Recorded (s : State) (r : Registry) (i : Interpretation)
    {complete : Nat → Prop} (support : Supported s complete)
    (d : Demand) (impl : Declaration) (base : Nat → Capture) (place : Placement) : Prop where
  frame : Frame s r i support d impl base place
  written : ∃ rows, collect (one r i impl d (sourceNames impl place base).input) d.outputs = some rows ∧
    rows ⊆ s.equations

/-- Positive source frames whose actual associated equations were
retained give both local readback and ordinary stability. Nothing is
assumed about a recursively selected child or a chosen model. -/
theorem complete_read {s : State} {support : Supported s complete} (checked : Checked r)
    (visible : impl ∈ r.declarations) (source : Recorded s r i support d impl base place) :
    ReadBack s r i d impl (sourceNames impl place base) place ∧
      BodyCoverage r i d impl ∧ StableUnder s (SourceEquation r i d impl (sourceNames impl place base).input) := by
  obtain ⟨_,built,occupied⟩ := source.written
  exact ⟨observed checked visible source.frame,stable_after_written checked visible built occupied⟩

end Yulang.GeneralDeclarativeFrameReadback325
