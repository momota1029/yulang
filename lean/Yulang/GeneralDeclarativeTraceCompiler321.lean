import Yulang.GeneralDeclarativeNodeProducer321
import Yulang.GeneralDeclarativeTraceHead321
import Yulang.GeneralDeclarativePriority321
import Yulang.GeneralDeclarativeCompilerTree320

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeTraceCompiler321
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeTrace321 (Occurrence Links)
open GeneralDeclarativeTraceHead321 (Read head_result)
open GeneralDeclarativeRepresentatives321 (captureOf chosen_reads)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeLowerKnown321 (Alias)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeWhereProducer321 (Child)
open GeneralDeclarativeNodeProducer321 (ReturnRead attach_head)
open GeneralDeclarativeEntailment320 (BatchRecipe)
open GeneralDeclarativePriority321 (Local selected_generated)
open GeneralDeclarativeCompilerTree320 (Compiles compile_classify)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarations (Registry Declaration Checked)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (All₂ Classify)

/-- Finite source constructor occurrences are shared across all arguments.
The selected actual name is read from the common occurrence list. For
non-actual endpoints the general theorem deliberately takes the already
merged logical capture names, not an arbitrary first interval. -/
structure HeadTrace (s : State) (p : Supported s completed) (r : Registry) (interp : Interpretation)
    (d : Demand) (decl : Declaration) (capture : Nat → Capture) (seen : List Occurrence) : Prop where
  all : All₂ (fun arg pattern => ∃ code used, translate r.constructors interp pattern = some code ∧
      Read (restriction p) capture arg code used ∧ used ⊆ seen) d.arguments decl.head
  shared : Links (restriction p) capture seen

theorem trace_batch (checked : Checked r) (declared : decl ∈ r.declarations)
    (role : decl.role = d.role)
    (captureBounds : ∀ binder ∈ decl.inputNames, Bounds s (capture binder))
    (bounds : ∀ argument ∈ d.arguments, Bounds s argument)
    (head : HeadTrace s p r interp d decl capture seen)
    (children : All₂ (Child s r interp capture) decl.requirements kids)
    (results : ∀ out ∈ d.outputs, ReturnRead s r interp decl d capture out) :
    BatchRecipe s r interp d decl.id kids := by
  refine attach_head checked declared role captureBounds bounds ?_ children results
  apply GeneralDeclarativeNormalized320.ordered_map head.all
  rintro arg _ pat _ ⟨code,used,translated,trace,sub⟩
  exact head_result p translated trace (fun field one => head.shared field (sub one))

/-- Syntactic exact frontiers for the supported fragment. The rule does not
stipulate equality to a compiler or any evidence in a model. Completeness of
the source normalizer, propagation, and this child derivation remain open. -/
def Generated (s : State) (p : Supported s completed) (r : Registry) (interp : Interpretation)
    (d : Demand) (decl : Declaration) (kids : List Demand) : Prop :=
  ∃ capture seen, HeadTrace s p r interp d decl capture seen ∧
    (∀ binder ∈ decl.inputNames, Bounds s (capture binder)) ∧
    (∀ arg ∈ d.arguments, Bounds s arg) ∧
    All₂ (Child s r interp capture) decl.requirements kids ∧
    (∀ out ∈ d.outputs, ReturnRead s r interp decl d capture out)

theorem local_compiles {s : State} {p : Supported s completed}
    (checked : Checked r) :
    Compiles s r interp (Local s r interp p tests (Generated s p r interp)) := by
  intro d key kids selected
  obtain ⟨decl,rfl,⟨⟨visible,role⟩,_⟩,capture,seen,head,capBounds,bounds,children,output⟩ :=
    selected_generated selected
  exact .inr (trace_batch checked visible role capBounds bounds head children output)

theorem classify_evidence {s : State} {p : Supported s completed} (checked : Checked r)
    (m : Assignment) (valid : Models s m)
    (classification : Classify (Local s r interp p tests (Generated s p r interp)) d (.selected dict)) :
    Evidence r interp m d dict :=
  compile_classify checked (local_compiles checked) m valid classification

end Yulang.GeneralDeclarativeTraceCompiler321
