import Yulang.GeneralDeclarativeExampleRead320
import Yulang.GeneralDeclarativeEndpointProbe321
import Yulang.GeneralDeclarativeTraceHead321

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 14000
namespace Yulang.GeneralDeclarativeFixtureSupport321
open GeneralDeclarativeExampleSource320
open GeneralDeclarativeExampleRead320 (headExpr childCapture)
open GeneralDeclarationExamples (wrap)
open GeneralDeclarativeOrigins321 (Supported Origin restriction from_source)
open GeneralDeclarativeLowerKnown321 (Ready alias_refl knows_row)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeTrace321 (Trace TraceArgs Occurrence Links)
open GeneralDeclarativeTraceHead321 (Read)
open GeneralDeclarativeEndpointProbe321 (Matches HeadMatches)
open GeneralDeclarativePoint320 (frozen_nominal)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalMaterialization (Mode)
open CommonRoleOutermostResolver (All₂)

def support : Supported state (fun _ => False) :=
  ⟨fun row origin => row.left ∈ [0,2,3] ∧ row ∈ state.equations ∧ origin = .source,
    fun h => h.2.1⟩

theorem nomLo : (⟨0,nApp 3⟩ : Equation) ∈ (restriction support).equations :=
  from_source support ⟨List.mem_cons_self,List.mem_cons_self,rfl⟩

theorem nomHi : (⟨2,nApp 3⟩ : Equation) ∈ (restriction support).equations :=
  from_source support ⟨List.mem_cons_of_mem _ List.mem_cons_self,
    List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩

theorem scalar : (⟨3,.primitive (.scalar .int) []⟩ : Equation) ∈ (restriction support).equations :=
  from_source support ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),rfl⟩

theorem root_ready : Ready support root := by
  intro arg present
  cases List.mem_singleton.mp present
  exact ⟨_,knows_row nomLo rfl⟩

theorem leaf_ready : Ready support child := by
  intro arg present
  cases List.mem_singleton.mp present
  exact ⟨_,knows_row scalar rfl⟩

abbrev current : Occurrence := ⟨0,.actual,3⟩

theorem low : Trace (restriction support) .lower input.lower headExpr [current] :=
  .nominal (args := [3]) (alias_refl _) nomLo (.cons .capture .nil)

theorem high : Trace (restriction support) .upper input.upper headExpr [current] :=
  .nominal (args := [3]) (alias_refl _) nomHi (.cons .capture .nil)

theorem root_point : Read (restriction support) capture input headExpr [current,current] :=
  .point (s := restriction support) input_bounds (frozen_nominal _ _ _ _) low high

theorem both_linked : Links (restriction support) capture [current,current] := by
  intro o found
  simp only [List.mem_cons,List.not_mem_nil,or_false] at found
  rcases found with rfl|rfl <;> exact alias_refl 3

theorem one_linked : Links (restriction support) childCapture [current] := by
  intro o found
  cases List.mem_singleton.mp found
  exact alias_refl 3

theorem probe_root : HeadMatches (restriction support) registry.constructors interp root wrap :=
  .cons ⟨input_bounds,headExpr,[current],[current],rfl,low,high⟩ .nil

theorem probe_leaf : HeadMatches (restriction support) registry.constructors interp child leaf :=
  .cons ⟨point_bounds 3,.variable 0,[⟨0,.lower,3⟩],[⟨0,.upper,3⟩],rfl,.capture,.capture⟩ .nil

end Yulang.GeneralDeclarativeFixtureSupport321
