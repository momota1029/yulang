import Yulang.GeneralFiniteAliasSearch262
import Yulang.GeneralRebaseSourceSnapshot261

namespace Yulang.GeneralRebaseExecutableRequests262
open GeneralSourceState (Output)
open GeneralSourceDictionaries (Occurrence)

/-- Exact executable selection on one finite snapshot. One finite frontier
search per root preserves the order and duplicates of the original requests. -/
def requests (source : GeneralNominalCenteredSteps.State roles) (root : Occurrence roles) : List Output :=
 let component := GeneralFiniteAliasSearch262.component source.erased.current.aliases root.identity
 (source.erased.current.sites.filter fun site => component.contains site.occurrence.identity).flatMap
   fun site => site.occurrence.demand.outputs

theorem requests_eq (source : GeneralNominalCenteredSteps.State roles) (root : Occurrence roles) :
 requests source root = GeneralNominalCenteredHeadOutputs.requests source root := by
 classical
 unfold requests GeneralNominalCenteredHeadOutputs.requests
 dsimp only
 congr 1
 apply List.filter_congr
 intro site _
 apply Bool.eq_iff_iff.mpr
 simp only [List.contains_iff_mem,decide_eq_true_eq,GeneralFiniteAliasSearch262.component_exact]

theorem mem_iff (source : GeneralNominalCenteredSteps.State roles) (root : Occurrence roles) (output : Output) :
 output ∈ requests source root ↔
 ∃ site ∈ source.erased.current.sites,
 GeneralNominalSaturationState.Alias source.erased.current root.identity site.occurrence.identity ∧
 output ∈ site.occurrence.demand.outputs := by
 rw [requests_eq]
 exact GeneralNominalCenteredHeadOutputs.mem_requests_iff

theorem covered (source : GeneralNominalCenteredSteps.State roles) (root : Occurrence roles) :
 ∀ output ∈ requests source root, output ∈ GeneralRebaseSourceSnapshot261.candidates source := by
 rw [requests_eq]
 exact GeneralRebaseSourceSnapshot261.covered source root

theorem same_class (source : GeneralNominalCenteredSteps.State roles) (first last : Occurrence roles)
 (alias : GeneralNominalSaturationState.Alias source.erased.current first.identity last.identity)
 (output : Output) : output ∈ requests source first ↔ output ∈ requests source last := by
 rw [requests_eq,requests_eq]
 exact GeneralNominalCenteredHeadOutputs.same_class_requests alias
end Yulang.GeneralRebaseExecutableRequests262
