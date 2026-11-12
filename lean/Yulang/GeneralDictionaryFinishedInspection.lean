import Yulang.GeneralDictionaryFinishedRefresh
import Yulang.GeneralDictionaryRefinementInspectionFacts

namespace Yulang.GeneralDictionaryFinishedInspection
open GeneralNominalInspection (Query Bounds)
open GeneralNominalRecursiveInspection
open GeneralNominalRecursiveCandidates (Context)
open GeneralDictionaryInspectionTransport
open GeneralDictionaryInspectionLocality
open GeneralDictionaryRefreshDescriptors
open GeneralDictionaryRefinementInspectionFacts
open GeneralDictionaryFinishedRefresh

mutual
 theorem inspect_finished (context : Context) (next : Observation context.state)
    (view : next.view = context.state.view)
    (refinement : GeneralNominalRefinements.Refines context.state (reobserve context next).state)
    (query : Query) (bounds : Bounds context.state) (origin : Option Origin)
    (finished : Finished (inspect context.state query bounds origin)) :
    inspect (reobserve context next).state query bounds origin =
      transferReport context next (inspect context.state query bounds origin) := by
  rcases next with ⟨v,n,c,o⟩
  dsimp only at view
  subst v
  let next : Observation context.state := ⟨context.state.view,n,c,o⟩
  cases query with
  | variables names => simp only [inspect,transferReport,capture,List.map_map,Function.comp_def]
  | deferred term => exact False.elim (block_not_finished bounds (by simpa only [inspect] using finished))
  | scalar expected =>
    cases recorded : context.state.nominals bounds.1 with
    | some descriptor => simp [inspect,recorded,Finished,Report.visit] at finished
    | none =>
      cases head : context.state.view.heads bounds.1 with
      | deferred reason => simp [inspect,recorded,head,Finished,Report.visit,block] at finished
      | structural kind children => simp [inspect,recorded,head,Finished,Report.visit] at finished
      | scalar actual =>
        have none := none_of_visible context next rfl bounds.1 (by rw [head]; intro h; cases h)
        dsimp only [next] at none
        simp only [inspect,reobserve,recorded,none,head]
        split <;> rfl
  | node expected patterns =>
    simp only [inspect] at finished
    simp only [inspect,reobserve]
    split
    · rename_i lower children upper targets observed
      split
      · rename_i shapes
        rw [inspectMany_finished context next rfl refinement patterns _ _ _ (by simpa only [observed,targets,shapes,and_self,ite_true,finished_visit] using finished)]
        rfl
      · rfl
    · rfl
    · rfl
  | nominal expected patterns =>
    obtain ⟨lower,recorded⟩ := finished_nominal_lower context.state expected patterns bounds origin finished
    obtain ⟨upper,upperRecorded⟩ := finished_nominal_upper context.state expected patterns bounds origin finished
    have low := descriptor_preserved context next refinement bounds.1 lower recorded
    have high := descriptor_preserved context next refinement bounds.2 upper upperRecorded
    dsimp only [next] at low high
    simp only [inspect,recorded,upperRecorded] at finished
    simp only [inspect,reobserve,recorded,upperRecorded,low,high]
    split
    · rename_i lowName
      split
      · rfl
      · rename_i arguments arguments_eq
        split
        · rename_i point
          rw [inspectMany_finished context next rfl refinement patterns arguments _ _ (by simpa only [lowName,arguments_eq,point,ite_true,finished_visit] using finished)]
          rfl
        · rename_i nonpoint
          split
          · rename_i highName
            split
            · rfl
            · rename_i targets targets_eq
              simp only [lowName,highName,arguments_eq,nonpoint,ite_false,targets_eq,ite_true,finished_visit] at finished
              have both := (finished_append _ _).mp finished
              rw [inspectMany_finished context next rfl refinement patterns arguments _ _ both.1,
                inspectMany_finished context next rfl refinement patterns targets _ _ both.2]
              simp only [transfer_visit,transfer_append]
              rfl
          · rfl
    · rfl
 termination_by sizeOf query
 theorem inspectMany_finished (context : Context) (next : Observation context.state)
    (view : next.view = context.state.view)
    (refinement : GeneralNominalRefinements.Refines context.state (reobserve context next).state)
    (queries : List Query) (bounds : List (Bounds context.state)) (origins : Nat → Option Origin) (index : Nat)
    (finished : Finished (inspectMany context.state queries bounds origins index)) :
    inspectMany (reobserve context next).state queries bounds origins index =
      transferReport context next (inspectMany context.state queries bounds origins index) := by
  cases queries with
  | nil => cases bounds <;> simp only [inspectMany,transferReport] <;> rfl
  | cons query queries =>
    cases bounds with
    | nil => simp only [inspectMany,transferReport]; rfl
    | cons bound bounds =>
      simp only [inspectMany] at finished
      have both := (finished_append _ _).mp finished
      rw [inspectMany,inspectMany,
        inspect_finished context next view refinement query bound (origins index) both.1,
        inspectMany_finished context next view refinement queries bounds origins (index+1) both.2,transfer_append]
 termination_by sizeOf queries
end
end Yulang.GeneralDictionaryFinishedInspection
