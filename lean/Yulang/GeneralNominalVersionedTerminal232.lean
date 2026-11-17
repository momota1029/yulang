import Yulang.GeneralNominalVersionedInstall232
import Yulang.GeneralNominalVersionedFrameTransport232
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalVersionedTerminal232
open GeneralNominalCenters GeneralNominalVersionedInstall232
open GeneralNominalVersionedChildren232

theorem emitted_empty (terminal : GeneralNominalVersionedFrame231.children plan.packet = []) :
    emitted plan = [] := by
  apply List.eq_nil_of_length_eq_zero
  have same := congrArg List.length (emitted_occurrences plan)
  simp only [List.length_map,terminal,List.length_nil] at same
  exact same

theorem raw_empty (terminal : GeneralNominalVersionedFrame231.children plan.packet = []) :
    rawSites plan = [] := by rw [rawSites,emitted_empty terminal]; rfl

theorem sites_eq (terminal : GeneralNominalVersionedFrame231.children plan.packet = []) :
    (installCore core plan).sites = core.sites := by
  change core.sites ++ emitted plan = core.sites
  rw [emitted_empty terminal,List.append_nil]

theorem raw_eq (terminal : GeneralNominalVersionedFrame231.children plan.packet = []) :
    (installCore core plan).erased.current.sites = core.erased.current.sites := by
  change core.erased.current.sites ++ rawSites plan = core.erased.current.sites
  rw [raw_empty terminal,List.append_nil]

theorem requests_iff (terminal : GeneralNominalVersionedFrame231.children plan.packet = []) :
    output ∈ GeneralNominalCenteredHeadOutputs.requests (installCore core plan) root ↔
      output ∈ GeneralNominalCenteredHeadOutputs.requests core root := by
  constructor
  · apply GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
    · intro site member
      rw [raw_eq terminal] at member
      exact member
    · exact fun _ h => h
  · exact requests_included core plan output

theorem legacy_live (terminal : GeneralNominalVersionedFrame231.children plan.packet = [])
    (valid : GeneralNominalCenteredHeadMatStepJournal.Models legacy model) :
    LegacyLive legacy plan model := by
  intro effect member
  apply GeneralNominalCenteredHeadMatEffects.restrict
    (fun output present => (requests_iff terminal).mp present)
  exact (valid.2.2.2.2.2 effect member).2

end Yulang.GeneralNominalVersionedTerminal232
