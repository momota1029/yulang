import Yulang.GeneralDeclarativeWhereOutputBatch327

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAppliedClause327
open GeneralDeclarations (Clause Declaration Registry Checked)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeEmissionForest322 (Placement children)
open GeneralDeclarativeFrameReadback325 (sourceNames placeById ClauseFrame)
open GeneralDeclarativeClauseBatch327 (prepare all_read exact_projection past_origin)
open GeneralDeclarativeClausePlacement327 (placement checked_inputs)
open GeneralDeclarativeWhereOutputBatch327 (whole compiled origin_after)
open GeneralDeclarativeEntailment320 (appendFacts model_append Holds)
open GeneralDeclarativeGrowth327 (facts)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeOutputRequests323 (child_declared)
open GeneralDeclarativeProducedNames325 (exact_input)
open GeneralDeclarativeNormalizeAssoc324 (one complete)
open GeneralDeclarativeBatch320 (collect)
open GeneralDeclarativeNFNode324 (BodyCoverage)
open GeneralDeclarativeAssocRule323 (SourceEquation)
open GeneralDeclarativeModelStable324 (StableUnder)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralNominalCenteredHeadMatExpressions (translateMany_complete)
open GeneralDeclarativeNormalizeCovered322 (normalize_args_covered)

def targetsOnly (targets : Clause → Nat → Nat) : Placement :=
  ⟨fun _ _ => ⟨0,0,0⟩,targets⟩

theorem prepared_exists {s : State} (covered : Coverage r i) (visible : impl ∈ r.declarations)
    (targets : Clause → Nat → Nat) (base : Nat → Capture) (protect : List Nat) :
    let names := sourceNames impl (targetsOnly targets) base
    ∃ t ports, prepare r.constructors i (stateNames s ++ protect) names.input s impl.requirements = some (t,ports) := by
  apply all_read
  intro cl given
  obtain ⟨codes,built,_⟩ := translateMany_complete (normalize_args_covered ((covered.1 impl visible).2.1 cl given).1)
  exact ⟨codes,by simpa only [GeneralNominalChildAssembly.normalize_map] using built⟩

theorem compiler_projection {s t : State} (checked : Checked r) (visible : impl ∈ r.declarations)
    (targets : Clause → Nat → Nat) (base : Nat → Capture) (protect : List Nat)
    (known : ∀ name ∈ impl.inputNames, Bounds s (base name))
    (actual : prepare r.constructors i (stateNames s ++ protect)
      (sourceNames impl (targetsOnly targets) base).input s impl.requirements = some (t,ports)) (m) :
    Models s m ↔ ∃ next, Models t next ∧ ∀ n ∈ stateNames s ++ protect, next n = m n := by
  apply exact_projection (checked.2 impl visible) (fun _ h => h) ?_ actual m
  intro n present
  unfold sourceNames
  rw [exact_input (checked.2 impl visible) present]
  exact known n present

theorem compiled_frames {s t : State} (checked : Checked r) (covered : Coverage r i)
    (visible : impl ∈ r.declarations) (must : impl.role = d.role) (declared : Declared r d)
    (targets : Clause → Nat → Nat) (base : Nat → Capture) (protect : List Nat)
    (portTable : prepare r.constructors i (stateNames s ++ protect)
      (sourceNames impl (targetsOnly targets) base).input s impl.requirements = some (t,ports)) :
    let place := placement impl.requirements ports targets
    let names := sourceNames impl place base
    ∃ whereRows rootRows,
      whole r i impl names targets = some whereRows ∧
      collect (one r i impl d names.input) d.outputs = some rootRows ∧
      let applied := appendFacts (appendFacts t whereRows) rootRows
      (∀ cl ∈ impl.requirements, ClauseFrame applied r i impl cl names place) ∧
      BodyCoverage r i d impl ∧ StableUnder applied (SourceEquation r i d impl names.input) ∧
      (∀ child ∈ children impl names place, Declared r child) ∧
      ∀ m, Models applied m ↔ Models t m ∧ (∀ row ∈ whereRows ++ rootRows, Holds m row) := by
  dsimp
  let place := placement impl.requirements ports targets
  let names := sourceNames impl place base
  have actual : prepare r.constructors i (stateNames s ++ protect) names.input s impl.requirements = some (t,ports) := portTable
  obtain ⟨ws,written⟩ := compiled (names := names) (targets := targets) covered visible
  obtain ⟨rs,rootApplied,_⟩ := complete (capture := names.input) checked covered visible must declared
  let before := appendFacts t ws
  let now := appendFacts before rs
  have growth := GeneralDeclarativeGrowth327.trans (facts t ws) (facts before rs)
  have registered : rs ⊆ now.equations := fun _ row => List.mem_append_right _ row
  obtain ⟨coveredBodies,stable⟩ := GeneralDeclarativeAppliedSource325.stable_after_written checked visible rootApplied registered
  refine ⟨ws,rs,written,rootApplied,?_,coveredBodies,stable,fun _ member => child_declared checked visible member,?_⟩
  · intro cl listed
    obtain ⟨port,_,stored,chosen⟩ := checked_inputs (targets := targets) (checked.2 impl visible) actual listed
    constructor
    · refine ⟨port.code,stored.1,?_⟩
      intro j p e source print notDirect
      rw [chosen]
      obtain ⟨_,lo,mid,hi⟩ := stored.2 j p e source print notDirect
      exact ⟨past_origin growth lo,past_origin growth mid,past_origin growth hi⟩
    · intro eq member
      obtain ⟨code,printed,after⟩ := origin_after (s := t) covered visible written listed member
      exact ⟨code,printed,fun guard => past_origin (facts before rs) (after guard)⟩
  · intro m
    rw [model_append,model_append]
    constructor
    · rintro ⟨⟨before,found⟩,output⟩
      exact ⟨before,fun row h => (List.mem_append.mp h).elim (found row) (output row)⟩
    · rintro ⟨before,found⟩
      exact ⟨⟨before,fun row h => found row (List.mem_append_left _ h)⟩,
        fun row h => found row (List.mem_append_right _ h)⟩

end Yulang.GeneralDeclarativeAppliedClause327
