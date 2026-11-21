import Yulang.GeneralDeclarativeAggregatePoint324
import Yulang.GeneralDeclarativeRepeatedResolve323
import Yulang.GeneralDeclarativeNFComplete324
import Yulang.GeneralDeclarativeHiddenProbe324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAggregateFixture324
open GeneralDeclarativeRepeatedSource323 (state a b eqs nominalCode scalar pat goal parent child registry whereClause model fits checked)
open GeneralDeclarativeRepeatedReads323 (scanned observed parentNames place parent_reads)
open GeneralDeclarativeExampleSource320 (interp point)
open GeneralDeclarativeAggregate324 (span aggregates ready allNames kept aggregate_model now_bounds)
open GeneralDeclarativeAggregatePoint324 (observable Points observable_models)
open GeneralDeclarativeMergeCenters324 (Linked)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeDemand320 (Bounds Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeEntailment320 (literal model_append)
open GeneralDeclarativeSourceEmission322 (Names)
open GeneralDeclarativeEmissionForest322 (children)
open GeneralDeclarativeNFNode324 (Reads)
open GeneralDeclarativeNFHead324 (fact)
open GeneralDeclarativeRigidSource323 (ordered_results)
open GeneralDeclarativeSemanticSharing323 (exact_shared)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeLowerKnown321 (Ready knows_row alias_refl knows_alias)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (All₂)

abbrev seed : Capture := point 3
abbrev more : List Capture := [point 7]
abbrev keepNames : List Nat := [32]
abbrev merged : Capture := span state keepNames seed more
abbrev newState : State := observable state keepNames seed more

theorem computed : merged = ⟨33,3,34⟩ := rfl

theorem points : Points seed more := by
  intro other used
  simp only [List.mem_cons,List.not_mem_nil,or_false] at used
  rcases used with rfl|rfl <;> exact ⟨rfl,rfl⟩

theorem each : ∀ other ∈ seed :: more, Bounds state other := by
  intro other used
  simp only [List.mem_cons,List.not_mem_nil,or_false] at used
  rcases used with rfl|rfl <;> exact ⟨.refl _,.refl _⟩

theorem shares : Linked state seed more := by
  intro m valid other used
  simp only [List.mem_cons,List.not_mem_nil,or_false] at used
  rcases used with rfl|rfl
  · exact eqv_refl _
  · exact valid.2 ⟨7,.variable 3⟩ (by change _ ∈ eqs; simp [eqs])

theorem every_old_model (m : Assignment) (valid : Models state m) :
    ∃ newer, Models newState newer ∧
      ∀ n ∈ GeneralDeclarativeFootprint321.stateNames state ++ kept keepNames seed more, newer n = m n := by
  obtain ⟨new,good,fixed⟩ := aggregate_model (extra := keepNames) each shares m valid
  exact ⟨new,(observable_models each points new).mpr good,fixed⟩

theorem inhabited : ∃ e, Models newState e := by
  obtain ⟨e,good,_⟩ := every_old_model model fits
  exact ⟨e,good⟩

theorem current_old (m : Assignment) (valid : Models newState m) : Models state m := by
  have r : Models (ready state keepNames seed more) m := ((model_append m).mp valid).1
  have agg : Models (aggregates state keepNames seed more) m := (GeneralDeclarativeAggregate324.ready_iff each m).mp r
  have a : Models (GeneralDeclarativeAggregate324.aligned state seed more) m :=
    ((GeneralDeclarativeCaptureClosure320.ordinary_models m).mp agg).1
  exact (GeneralDeclarativeMergeCenters324.conservative shares m).mp a

abbrev actualNames : Names := ⟨fun _ => merged,fun _ => 3⟩
abbrev emitted : Demand := ⟨0,[merged],[]⟩

theorem exact_child : children parent actualNames place = [emitted] := rfl

theorem bounds : Bounds newState merged :=
  now_bounds state keepNames seed more

def support (completed : Nat → Prop) : Supported newState completed :=
  ⟨fun row origin => row ∈ newState.equations ∧ origin = .source,fun h => h.1⟩

theorem old_rows {row : Equation} (written : row ∈ eqs) : row ∈ newState.equations :=
  List.mem_append_left _ written

theorem lower_alias : (⟨merged.lower,.variable merged.center⟩ : Equation) ∈ newState.equations :=
  List.mem_append_right _ List.mem_cons_self

theorem supported_row (completed : Nat → Prop) {row : Equation} (ordinary : row ∈ newState.equations) :
    row ∈ (restriction (support completed)).equations :=
  from_source (support completed) ⟨ordinary,rfl⟩

/-- The freshly defined lower aggregate can legitimately start the
actual emitted child's probe: its alias was derived from ordinary
source points, not from an unsettled associated result. -/
theorem child_ready (completed : Nat → Prop) : Ready (support completed) emitted := by
  intro a known
  cases List.mem_singleton.mp known
  have known : (⟨3,scalar⟩ : Equation) ∈ (restriction (support completed)).equations :=
    supported_row completed (old_rows (by simp [eqs]))
  exact ⟨_,knows_alias (.forward (supported_row completed lower_alias)) (knows_row known rfl)⟩

end Yulang.GeneralDeclarativeAggregateFixture324
