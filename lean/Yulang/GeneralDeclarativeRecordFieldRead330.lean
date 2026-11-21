import Yulang.GeneralDeclarativeRecordMaterial330
import Yulang.GeneralDeclarativeStableTrace329

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRecordFieldRead330
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeTrace321 (Trace)
open GeneralDeclarativeTraceTransfer325 (ordinary)
open GeneralDeclarativeTraceExpand323 (expands)
open GeneralDeclarativeTraceNames321 (trace_keys_modes)
open GeneralDeclarativeStableTrace329 (Located names)
open GeneralDeclarativeStableReads329 (One)
open GeneralDeclarativeRecordSpine330 (Spine)
open GeneralDeclarativeRecordMaterial330 (tailRow ready preserved read_ordinary)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeOrderedRecord326 (order)
open GeneralDeclarativeOpaqueConserve328 (Retains)
open GeneralDeclarativeOpaqueNominal328 (point point_bounded)
open GeneralDeclarativeOpaqueNested328 (occurrences)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeTermWalk322 (Walk)
open GeneralDeclarativeGrowth327 (Extends derives fits)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarationPatterns (normalize)
open CommonRoleCanonicalRows (Row)
open CommonRoleOutermostResolver (All₂)

/-- Actual field evidence is independent of the chosen binder map.
The original visible fields must have their own authorized traces,
and exactly those occurrence names have checked spans. -/
inductive Fields {s : State} (support : Supported s done) :
    Row Expr → Row Expr → List (Nat × Capture) → Prop where
  | nil : Fields support [] [] []
  | cons : Trace (restriction support) .actual n code used →
    All₂ (Located s) used here → Fields support old target rest →
    Fields support ((key,.variable n)::old) ((key,code)::target) (here++rest)

theorem walk {s t : State} {p : Supported s done}
    (observed : Fields p picked written captures) (grows : Extends s t)
    (tail : Walk .actual tailActual tailCode (occurrences tailUses)) :
    ∃ rebuilt, Derives t (withTail picked tailActual) rebuilt ∧
      Walk .actual rebuilt (withTail written tailCode) (occurrences (captures ++ tailUses)) ∧
      ∀ use ∈ captures, Bounds t use.2 := by
  induction observed with
  | nil => exact ⟨tailActual,.refl _,tail,fun _ h => False.elim (List.not_mem_nil h)⟩
  | cons trace seen _ ih =>
    obtain ⟨actual,read,walked⟩ := expands (ordinary p trace)
    obtain ⟨named,limits⟩ := names seen (fun u h => ((trace_keys_modes trace).2 u h).elim id id)
    rw [named] at walked
    obtain ⟨form,known,structureOf,rest⟩ := ih
    refine ⟨.record _ actual form,.record (derives grows read) known,?_,?_⟩
    · simpa only [withTail,occurrences,List.map_append,List.append_assoc] using
        (Walk.record walked structureOf)
    · intro u found
      rcases List.mem_append.mp found with now|later
      · exact fits grows (limits u now)
      · exact rest u later

/-- Reusable record argument producer: actual supported closed
source subtraction plus ordered independently authorized fields gives
an ordinary current head walk. The next selected stage, not this
observation, validates repeated binder writes. -/
theorem one {s : State} {p : Supported s done} (span : Bounds s arg)
    (spine : Spine (restriction p) arg.center raw terminal) (keys : keyList.Nodup)
    (ordered : order (CommonRoleCanonicalRows.normalize raw) keyList = some picked)
    (fields : Fields p picked written binds)
    (compiled : translate c i (normalize pat) = some (withTail written (.variable binder)))
    (protect : List Nat) :
    let t := ready s arg.center protect raw picked keyList terminal
    let remainder := point (tailRow s arg.center protect raw keyList terminal).left
    let all := binds ++ [(binder,remainder)]
    Retains s t protect ∧ One t c i arg pat all ∧ ∀ u ∈ all, Bounds t u.2 := by
  let t := ready s arg.center protect raw picked keyList terminal
  let name := (tailRow s arg.center protect raw keyList terminal).left
  have grows := preserved spine keys ordered protect
  have final : Walk .actual (.variable name) (.variable binder) (occurrences [(binder,point name)]) := .capture
  obtain ⟨form,rewritten,source,spans⟩ := walk fields grows.grows final
  have old := read_ordinary (s := s) arg.center protect raw picked keyList terminal
  refine ⟨grows,⟨fits grows.grows span,_,form,compiled,.trans old rewritten,source⟩,?_⟩
  intro u found
  rcases List.mem_append.mp found with actual|rest
  · exact spans u actual
  · cases List.mem_singleton.mp rest
    exact point_bounded t name

end Yulang.GeneralDeclarativeRecordFieldRead330
