import Yulang.GeneralDeclarativeStableAssemble329

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNestedBody332
open GeneralDeclarations (Registry Declaration Clause Checked)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarativeStableTies329 (Consequence pairOf rows used_after present_entails repeated_shares)
open GeneralDeclarativeStableReads329 (Heads weakened names_all)
open GeneralDeclarativeStableCanonical329 (EqualUses exact uses_existing)
open GeneralDeclarativeOpaqueCapture328 (choose)
open GeneralDeclarativeOpaqueShared328 (Chosen build built)
open GeneralDeclarativeOpaqueConserve328 (Retains)
open GeneralDeclarativeEntailment320 (appendFacts model_append)
open GeneralDeclarativeGrowth327 (Extends facts trans fits derives)
open GeneralDeclarativeStableCompiler329 (Frame read)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeAppliedClause327 (prepared_exists targetsOnly compiler_projection compiled_frames)
open GeneralDeclarativeClauseBatch327 (Port prepare)
open GeneralDeclarativeClausePlacement327 (placement)
open GeneralDeclarativeFrameReadback325 (sourceNames)
open GeneralDeclarativeWhereOutputBatch327 (whole)
open GeneralDeclarativeBatch320 (collect)
open GeneralDeclarativeNormalizeAssoc324 (one)
open GeneralDeclarativeEmissionForest322 (children)

open GeneralDeclarativeStableAssemble329 (merged tieState assemble prepare_grows)

open GeneralDeclarativeFootprint321 (stateNames)

def compileBody (r : Registry) (i : Interpretation) (d : Demand) (impl : Declaration)
    (s : State) (spans : List (Nat × Capture)) (keep : List Nat)
    (fallback : Nat → Capture) (targets : Clause → Nat → Nat) : Option (State × List Demand) := do
  let initial := merged s keep spans fallback
  let inputs := (sourceNames impl (targetsOnly targets) initial.captures).input
  let (prepared,ports) ← prepare r.constructors i (stateNames initial.state ++ keep)
    inputs initial.state impl.requirements
  let place := placement impl.requirements ports targets
  let chosen := sourceNames impl place initial.captures
  let whereRows ← whole r i impl chosen targets
  let rootRows ← collect (one r i impl d chosen.input) d.outputs
  pure (appendFacts (appendFacts prepared whereRows) rootRows,children impl chosen place)

/-- Compile and replay the exact approved ordinary selection writes.
Naming the repeated captures comes *after* the equality, so only the
post-equality part is conservative. The exact association rows may
narrow the state again. A resulting frame is a source compilation
fact; by itself it is not an election or a proof of model existence. The targeting
function and exact two write append stages are exposed as equations. -/
theorem compiler_exact {s : State} {d : Demand} (checked : Checked r) (covered : Coverage r i)
    (visible : impl ∈ r.declarations) (role : impl.role = d.role) (demand : Declared r d)
    (keep : List Nat) (fallback : Nat → Capture) (targets : Clause → Nat → Nat)
    (walks : Heads s r.constructors i d.arguments impl.head spans)
    (fit : ∀ a ∈ spans, Bounds s a.2) :
    ∃ (current : State) (kids : List Demand) (frame : Frame current r i d impl kids),
      let input := merged s keep spans fallback
      compileBody r i d impl s spans keep fallback targets = some (current,kids) ∧
      frame.base = input.captures ∧ frame.spans = spans ∧ frame.targets = targets ∧
      current = appendFacts (appendFacts frame.prepared frame.whereRows) frame.rootRows ∧
      Extends (tieState s spans fallback) current ∧
      (∀ m, Models current m ↔ Models frame.prepared m ∧
        ∀ e ∈ frame.whereRows ++ frame.rootRows, GeneralDeclarativeEntailment320.Holds m e) := by
  let input := merged s keep spans fallback
  have built := assemble keep spans fallback fit
  obtain ⟨prep,ports,ready⟩ := prepared_exists (s := input.state) covered visible targets input.captures keep
  let place := placement impl.requirements ports targets
  let named := sourceNames impl place input.captures
  obtain ⟨ws,rs,atWhere,atRoot,_,_,_,_,models⟩ :=
    compiled_frames checked covered visible role demand targets input.captures keep ready
  let afterWhere := appendFacts prep ws
  let current := appendFacts afterWhere rs
  let kids := children impl named place
  have appended : Extends prep current := trans (facts _ _) (facts _ _)
  have prepGrows : Extends input.state prep :=
    prepare_grows ready
  have headGrows : Extends s current :=
    trans (facts _ _) (trans built.preserve.grows (trans prepGrows appended))
  have has : ∀ v ∈ impl.inputNames, Bounds current (input.captures v) := by
    intro v listed
    change v ∈ _ at listed
    rw [GeneralDeclarations.Declaration.inputNames,← names_all walks] at listed
    obtain ⟨span,found,same⟩ := List.mem_map.mp listed
    rw [← same]
    exact fits (trans prepGrows appended) (built.ranges span found)
  have ties : Consequence current input.captures (spans.map pairOf) := by
    intro e member m fit
    exact built.written e member m (GeneralDeclarativeGrowth327.restrict (trans prepGrows appended) m fit)
  let frame : Frame current r i d impl kids :=
    ⟨input.captures,spans,weakened headGrows walks,ties,has,targets,
      GeneralDeclarativeFootprint321.stateNames input.state ++ keep,input.state,prep,ports,
      ready,appended,ws,atWhere,fun _ h => List.mem_append_left _ (List.mem_append_right _ h),
      rs,atRoot,fun _ h => List.mem_append_right _ h,GeneralDeclarativeOpaqueBatch328.check_exact.mpr rfl⟩
  refine ⟨current,kids,frame,?_,rfl,rfl,rfl,rfl,trans built.preserve.grows (trans prepGrows appended),models⟩

  unfold compileBody
  change (do
    let (prepared,ports) ← prepare r.constructors i (stateNames input.state ++ keep)
      (sourceNames impl (targetsOnly targets) input.captures).input input.state impl.requirements
    let place := placement impl.requirements ports targets
    let chosen := sourceNames impl place input.captures
    let whereRows ← whole r i impl chosen targets
    let rootRows ← collect (one r i impl d chosen.input) d.outputs
    pure (appendFacts (appendFacts prepared whereRows) rootRows,children impl chosen place)) = some (current,kids)
  simp [ready,atWhere,atRoot,place,named,current,afterWhere,kids]

end Yulang.GeneralDeclarativeNestedBody332
