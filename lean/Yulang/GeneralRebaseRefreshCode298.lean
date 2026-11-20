import Yulang.GeneralRebaseRefreshSafety298
import Yulang.GeneralRebaseLocalProgram298

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 22000
set_option maxHeartbeats 9000000
namespace Yulang.GeneralRebaseRefreshCode298
open GeneralDictionaryOutputDepth252 (roles sourceRegistry registry root initial plan model)
open GeneralDictionaryOutputDepthInstall252 (smallModel)
open GeneralRebasePreInstallReplay297 (after candidate cert seen entries xs retained_coverage retained_table source_reachable)
open GeneralRebaseSignedDepth297 (checked)
open GeneralRebaseRawDepthReplay297 (checks)
open GeneralRebaseSourceWitnessProgram297 (Observed headTest questions Holds)
open GeneralRebaseLocalProgram298 (Local)
open GeneralRebaseSignedRefresh297 (refinement interp)
open GeneralRebaseFiniteWitnessTable297 (Covers)
open GeneralNominalVersionedPlans231 (private_models_iff HeadModels)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedMixedObservations233 (refresh_models)

theorem listed : entries = [candidate] := by
  have member := (GeneralRebasePreInstallReplay297.listed_after candidate).mpr rfl
  change candidate ∈ entries at member
  have count : entries.length = 1 := by decide +kernel
  generalize eq : entries = ps at count member ⊢
  cases ps with
  | nil => cases count
  | cons p ps =>
    cases ps with
    | nil => exact congrArg (fun a => [a]) (List.mem_singleton.mp member).symm
    | cons more ps => simp at count

theorem head_moves (m : Assignment) (prior : Models initial m) :
    headTest candidate m ↔ headTest plan m := by
  change HeadModels candidate.packet m ↔ HeadModels plan.packet m
  unfold HeadModels
  rw [private_models_iff,private_models_iff]
  apply and_congr
  · have old := prior.1.1
    have cur := ((refresh_models cert).mpr prior).1.1
    exact and_congr ⟨fun _ => old,fun _ => cur⟩
      (GeneralRebaseRetarget275.ordinary plan (refinement cert rfl) (interp cert rfl) seen m)
  · exact GeneralRebaseRetarget275.projection plan (refinement cert rfl) (interp cert rfl) seen m

theorem head_witness (m : Assignment) (member : m ∈ xs) : headTest candidate m := by
  change m ∈ [model,smallModel] at member
  have list := List.mem_cons.mp member
  rcases list with rfl|suffix
  · exact (head_moves model GeneralDictionaryOutputDepth252.initial_model).mpr GeneralDictionaryOutputDepth252.head_model
  · cases List.mem_singleton.mp suffix
    exact (head_moves smallModel GeneralDictionaryOutputDepthInstall252.small_initial).mpr GeneralRebaseRawDepthReplay297.small_head

theorem observed : Observed after xs entries checks := by
  refine ⟨?_,retained_table,?_⟩
  · intro p pm a am
    cases (GeneralRebasePreInstallReplay297.listed_after p).mp pm
    exact ⟨fun _ => head_witness a am,fun _ => rfl⟩
  · intro pair present a valid
    exact GeneralRebaseRawDepthReplay297.observed.2.2 pair present a valid

theorem coverage : Covers (Holds after) (questions sourceRegistry after root checked) xs := by
  intro q member yes
  cases q with
  | head p =>
    have lp : p ∈ entries := by
      unfold questions at member
      rcases List.mem_append.mp member with a | bad
      · rcases List.mem_append.mp a with h | bad
        · obtain ⟨prior,inside,which⟩ := List.mem_map.mp h
          cases which
          exact inside
        · obtain ⟨pair,_,wrong⟩ := List.mem_map.mp bad
          cases wrong
      · obtain ⟨pair,_,wrong⟩ := List.mem_map.mp bad
        cases wrong
    cases (GeneralRebasePreInstallReplay297.listed_after p).mp lp
    exact ⟨model,List.mem_cons_self ..,head_witness model (List.mem_cons_self ..)⟩
  | install p sign =>
    unfold questions at member
    rcases List.mem_append.mp member with a | bad
    · rcases List.mem_append.mp a with bad | h
      · obtain ⟨p,_,wrong⟩ := List.mem_map.mp bad
        cases wrong
      · obtain ⟨⟨p',sg⟩,inside,which⟩ := List.mem_map.mp h
        cases which
        exact retained_coverage (p',sg) inside yes
    · obtain ⟨pair,_,wrong⟩ := List.mem_map.mp bad
      cases wrong
  | mergeFailure pair =>
    obtain ⟨m,old,bad⟩ := yes
    have pairIn : pair ∈ GeneralRebaseSourceWitnessProgram297.registeredPairs after := by
      unfold questions at member
      rcases List.mem_append.mp member with first | h
      ·
        rcases List.mem_append.mp first with h | j
        · obtain ⟨p,_,wrong⟩ := List.mem_map.mp h
          cases wrong
        · obtain ⟨item,_,wrong⟩ := List.mem_map.mp j
          cases wrong
      · obtain ⟨p,inside,eq⟩ := List.mem_map.mp h
        cases eq
        exact inside
    have now : Models initial m := (refresh_models cert).mp old
    have counter : GeneralRebaseMergeQuestions297.counter initial pair m := ⟨now,bad⟩
    obtain ⟨a,member,found⟩ := GeneralRebaseWitnessContracts297.merge_coverage
      GeneralRebaseRawDepthReplay297.program_covers pair pairIn ⟨m,counter⟩
    exact ⟨a,member,(refresh_models cert).mpr found.1,found.2⟩

def rawCode : Local sourceRegistry after root checked :=
  ⟨xs,checks,fun _ => true,
    fun f generated => by
      cases GeneralNominalVersionedMixedTerminalStable234.generated_only rfl rfl generated
      exact ⟨fun _ => GeneralRebaseRefreshSafety298.safe,fun _ => rfl⟩,
    coverage,observed⟩

end Yulang.GeneralRebaseRefreshCode298
