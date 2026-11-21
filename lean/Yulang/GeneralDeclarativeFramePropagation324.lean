import Yulang.GeneralDeclarativeNormalizeAssoc324
import Yulang.GeneralDeclarativeRigidLocal323

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeFramePropagation324
open GeneralDeclarations (Checked)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeRigidLocal323 (RigidReads RootClosed)
open GeneralDeclarativeRuleExact323 (exact)
open GeneralDeclarativeSemanticSharing323 (exact_shared)
open GeneralDeclarativeRigidSource323 (compiled_results)
open GeneralDeclarativeEmissionForest322 (children all_clauses)
open GeneralDeclarativeOutputSource323 (Declared declared_rows generated)
open GeneralDeclarativeOutputFacts320 (rootFact)
open GeneralDeclarativeNodeFacts320 (nodeFacts)
open GeneralDeclarativeRootClosure323 (exact_rows)
open GeneralDeclarativeEntailment320 (Entails appendFacts BatchRecipe literal)
open GeneralDeclarativeOutputSplit323 (lift_entails)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralDeclarativeAssocRule323 (SourceEquation)
open GeneralDeclarativeNormalizeAssoc324 (one complete)
open GeneralDeclarativeBatch320 (collect)

/-- Actual head/where observations are justified independently before
the ordinary parsed output rules update the state. Capture and children
are held fixed for this comparison; it is not a reselection theorem. -/
theorem after_rules {s : State} {written : List Equation}
    (checked : Checked r) (metaOK : Coverage r interp)
    (visible : impl ∈ r.declarations) (role : impl.role = d.role) (wanted : Declared r d)
    (read : RigidReads s r interp d impl names place)
    (applied : ∀ row, SourceEquation r interp d impl names.input row → row ∈ written) :
    BatchRecipe (appendFacts s written) r interp d impl.id (children impl names place) := by
  obtain ⟨uses,scanned,first,shared⟩ := read.seen
  obtain ⟨h,hr,he⟩ := compiled_results scanned ((exact_shared scanned first).mpr shared)
  obtain ⟨k,kr,ke⟩ := all_clauses read.coherent read.clauseReads
  obtain ⟨o,orows⟩ := generated (capture := names.input) checked metaOK visible role wanted
  have strengthened : RootClosed (appendFacts s written) r interp d impl names.input :=
    (exact checked metaOK visible role wanted).mpr
      (fun row rule => literal (List.mem_append_right _ (applied row rule)))
  refine ⟨impl,names.input,h++k++o,rfl,visible,read.boundCaptured,read.boundArguments,
    by simp [nodeFacts,role,hr,kr,orows],?_⟩
  intro row there
  rcases List.mem_append.mp there with old|new
  · exact lift_entails ((List.mem_append.mp old).elim (he row) (ke row))
  · obtain ⟨out,requested,printed⟩ :=
      (exact_rows (declared_rows checked metaOK visible role wanted) orows).mp new
    exact strengthened out requested row printed

theorem produces_finite {s : State} (checked : Checked r) (metaOK : Coverage r interp)
    (visible : impl ∈ r.declarations) (role : impl.role = d.role) (wanted : Declared r d)
    (read : RigidReads s r interp d impl names place) :
    ∃ written, collect (one r interp impl d names.input) d.outputs = some written ∧
      (∀ row, row ∈ written ↔ SourceEquation r interp d impl names.input row) ∧
      BatchRecipe (appendFacts s written) r interp d impl.id (children impl names place) := by
  obtain ⟨written,generated,contains⟩ := complete (capture := names.input) checked metaOK visible role wanted
  exact ⟨written,generated,contains,after_rules checked metaOK visible role wanted read
    (fun row source => (contains row).mpr source)⟩

end Yulang.GeneralDeclarativeFramePropagation324
