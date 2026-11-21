import Yulang.GeneralDeclarativeOutputSource323
import Yulang.GeneralDeclarativeEmissionLocal322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOutputSplit323
open GeneralDeclarations (Checked Registry Declaration)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarativeSourceEmission322 (Names)
open GeneralDeclarativeEmissionForest322 (Placement children all_clauses)
open GeneralDeclarativeEmissionClause322 (Ready)
open GeneralDeclarativeEmissionOutputs322 (Agree)
open GeneralDeclarativeExistingLocal322 (Heads head_results)
open GeneralDeclarativeArgumentFacts320 (headFact)
open GeneralDeclarativeOutputFacts320 (rootFact)
open GeneralDeclarativeOutputSource323 (Declared generated)
open GeneralDeclarativeNodeFacts320 (nodeFacts clauseFacts)
open GeneralDeclarativeEntailment320 (Entails literal appendFacts BatchRecipe model_append)
open GeneralDeclarativeCompileLists321 (Result zip_result)
open GeneralDeclarativeBatch320 (collect)
open GeneralNominalCenteredHeadWFSource (Coverage)

/-- Independent ordinary realization of the source head and where
syntax; it specifically does not require the parent output row. -/
structure NonOutputs (s : State) (p : Supported s completed) (r : Registry)
    (interp : Interpretation) (d : Demand) (decl : Declaration) (names : Names) (place : Placement) : Prop where
  head : Heads s p r interp d decl names.input
  binderBounds : ∀ n ∈ decl.inputNames, Bounds s (names.input n)
  argumentBounds : ∀ arg ∈ d.arguments, Bounds s arg
  binders : Agree decl names
  clauses : ∀ w ∈ decl.requirements,
    Ready s r interp decl w names (place.compound w) (place.targets w)

theorem lift_entails {s : State} {rows : List Equation} (was : Entails s e) :
    Entails (appendFacts s rows) e :=
  fun m now => was m ((model_append m).mp now).1

theorem local_batch_iff_rows {s : State} {p : Supported s completed}
    (role : decl.role = d.role)
    (ready : NonOutputs s p r interp d decl names place)
    (outputRows : collect (rootFact r interp decl d names.input) d.outputs = some os) :
    ∃ hs ws, nodeFacts r interp names.input decl d (children decl names place) = some (hs ++ ws ++ os) ∧
      ∀ row ∈ hs ++ ws, Entails s row := by
  obtain ⟨hs,headRead,hed⟩ := zip_result (head_results ready.head)
  obtain ⟨ws,whereRead,wed⟩ := all_clauses ready.binders ready.clauses
  exact ⟨hs,ws,by simp [nodeFacts,role,headRead,whereRead,outputRows],
    fun row found => (List.mem_append.mp found).elim (hed row) (wed row)⟩

/-- General finite narrowing result. Once genuine source head and where
reads are supplied, all remaining *root-output* equations can be added by
their specified ordinary rule. Old models survive exactly when they
satisfy those rows; this is not a conservative freshness extension. -/
theorem batch_after_outputs {s : State} {p : Supported s completed}
    (checked : Checked r) (coverage : Coverage r interp) (vis : decl ∈ r.declarations)
    (role : decl.role = d.role) (requests : Declared r d)
    (ready : NonOutputs s p r interp d decl names place) :
    ∃ os, collect (rootFact r interp decl d names.input) d.outputs = some os ∧
      BatchRecipe (appendFacts s os) r interp d decl.id (children decl names place) := by
  obtain ⟨os,emits⟩ := generated checked coverage vis role requests
  obtain ⟨hs,ws,batch,other⟩ := local_batch_iff_rows role ready emits
  refine ⟨os,emits,decl,names.input,hs ++ ws ++ os,rfl,vis,ready.binderBounds,ready.argumentBounds,batch,?_⟩
  intro row found
  rcases List.mem_append.mp found with previous|output
  · exact lift_entails (other row previous)
  · exact literal (List.mem_append_right _ output)

theorem batch_when_closed {s : State} {p : Supported s completed}
    (vis : decl ∈ r.declarations) (role : decl.role = d.role)
    (ready : NonOutputs s p r interp d decl names place)
    (outputRows : collect (rootFact r interp decl d names.input) d.outputs = some os)
    (closed : ∀ row ∈ os, Entails s row) :
    BatchRecipe s r interp d decl.id (children decl names place) := by
  obtain ⟨hs,ws,batch,other⟩ := local_batch_iff_rows role ready outputRows
  exact ⟨decl,names.input,hs ++ ws ++ os,rfl,vis,ready.binderBounds,ready.argumentBounds,batch,
    fun row found => (List.mem_append.mp found).elim (other row) (closed row)⟩

end Yulang.GeneralDeclarativeOutputSplit323
