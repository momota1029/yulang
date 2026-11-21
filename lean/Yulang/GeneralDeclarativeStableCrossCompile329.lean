import Yulang.GeneralDeclarativeStableCrossSource329
import Yulang.GeneralDeclarativeNestedModels328

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 17000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralDeclarativeStableCrossCompile329
open GeneralDeclarativeRepeatedSource323 (registry parent child goal whereClause nominalCode checked well_covered)
open GeneralDeclarativeExampleSource320 (interp point)
open GeneralDeclarativeStableCrossSource329 (actual spans keep real_heads real_ranges assignment actual_model)
open GeneralDeclarativeStableAssemble329 (merged tieState assemble witness_projection firsts)
open GeneralDeclarativeStableCanonical329 (EqualUses)
open GeneralDeclarativeStableTies329 (rows pairOf model_batch)
open GeneralDeclarativeStableReads329 (weakened)
open GeneralDeclarativeStableCompiler329 (Frame read)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeGrowth327 (Extends facts trans)
open GeneralDeclarativeFrameReadback325 (sourceNames)
open GeneralDeclarativeAppliedClause327 (targetsOnly)
open GeneralDeclarativeClauseBatch327 (prepare make)
open GeneralDeclarativeClausePlacement327 (placement)
open GeneralDeclarativeEmissionForest322 (children)
open GeneralDeclarativeOpaqueBatch328 (check)
open GeneralDeclarativeNFComplete324 (facts)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeAssembly320 (Meaning)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeRepeat320 (int)
open GeneralDeclarativeNestedModels328 (boolType payload_gt_int)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open CommonNominalFullCarrier (Equivalent Subtype subtype_refl common_union_is_join)

abbrev fallback (_ : Nat) := point 0
abbrev chosen := merged actual.state keep spans fallback
abbrev final := chosen.state
abbrev targets (_ : GeneralDeclarations.Clause) (_ : Nat) : Nat := 18
abbrev ports := [make final keep (sourceNames parent (targetsOnly targets) chosen.captures).input whereClause [.variable 0]]
abbrev place := placement parent.requirements ports targets
abbrev requested : Demand := ⟨0,[⟨13,3,14⟩],[]⟩

theorem write : rows (firsts spans fallback) (spans.map pairOf) = [⟨3,.variable 7⟩] := rfl
theorem exact_capture : chosen.captures 0 = ⟨13,3,14⟩ := rfl
theorem exact_child : children parent (sourceNames parent place chosen.captures) place = [requested] := rfl
theorem rejects_wrong_center :
    check (children parent (sourceNames parent place chosen.captures) place) [⟨0,[⟨13,7,14⟩],[]⟩] = false :=
  rfl

theorem declared : Declared registry goal := by intro _ h; cases h
def frame : Frame final registry interp goal parent [requested] := by
  have h := assemble keep spans fallback real_ranges
  have first : Extends actual.state final := trans (GeneralDeclarativeGrowth327.facts _ _) h.preserve.grows
  refine ⟨chosen.captures,spans,weakened first real_heads,h.written,?_,targets,keep,final,final,ports,
    rfl,GeneralDeclarativeClauseBatch327.reflexive _,[],rfl,(fun _ p => False.elim (List.not_mem_nil p)),
    [],rfl,(fun _ p => False.elim (List.not_mem_nil p)),rfl⟩
  intro key found
  change key ∈ [0,0] at found
  have zero : key = 0 := by simpa using found
  subst key
  exact h.ranges (0,point 3) List.mem_cons_self

theorem typed : Result final (facts registry interp (sourceNames parent place chosen.captures).input parent goal [requested]) ∧
    (∀ m, Models final m → Meaning registry interp m goal parent (sourceNames parent place chosen.captures).input [requested]) := by
  have done := read checked well_covered List.mem_cons_self rfl declared frame
  exact ⟨done.1,done.2.1⟩

theorem untied_model : Models actual.state (assignment boolType) ∧
    ¬Models (tieState actual.state spans fallback) (assignment boolType) := by
  refine ⟨actual_model _,?_⟩
  intro narrow
  have eq := ((model_batch (s := actual.state) (firsts spans fallback) (spans.map pairOf) _).mp narrow).2
    (0,7) (List.mem_cons_of_mem _ List.mem_cons_self)
  have wrong : Subtype boolType int := eq.1
  exact payload_gt_int ((common_union_is_join ..).mpr ⟨subtype_refl _,wrong⟩)

theorem compatible (m : GeneralNominalCommonBridge.Assignment)
    (fit : Models final m) : Equivalent (m 3).1 (m 7).1 := by
  have h := assemble keep spans fallback real_ranges
  have matched := GeneralDeclarativeGrowth327.restrict h.preserve.grows m fit
  have eq := ((model_batch (s := actual.state) (firsts spans fallback) (spans.map pairOf) m).mp matched).2
    (0,7) (List.mem_cons_of_mem _ List.mem_cons_self)
  exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_symm eq

theorem inhabitance : ∃ m, Models final m := by
  have a : Models (tieState actual.state spans fallback) (assignment int) := by
    apply (model_batch (s := actual.state) (firsts spans fallback) (spans.map pairOf) _).mpr
    refine ⟨actual_model _,?_⟩
    intro u here
    change u ∈ [(0,3),(0,7)] at here
    rcases List.mem_cons.mp here with rfl|later
    · exact eqv_refl _
    · cases List.mem_singleton.mp later
      exact eqv_refl _
  obtain ⟨m,fit,_⟩ := (assemble keep spans fallback real_ranges).preserve.lifts _ a
  exact ⟨m,fit⟩

end Yulang.GeneralDeclarativeStableCrossCompile329
