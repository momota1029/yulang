import Yulang.GeneralRebaseChartBudget281
import Yulang.GeneralRebaseCompoundFiniteMeaning273
import Yulang.GeneralRebaseFixedDisplayGraph280

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 10800000
namespace Yulang.GeneralRebaseChartFixtures281
open GeneralNominalVersionedJournal232 (Models State)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseChartStep281 (Chart Public Recorded Strict Step)
open GeneralRebaseSemanticChart281 (Gain Loss)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralRebaseProjectedEdgeCount279 (Seen Fresh)
open CommonNominalFullCarrier (Equivalent)

def graphChart : Chart Unit Unit := ⟨[],fun _ _ => True,fun _ _ => True⟩

def outputChart : Chart Unit Assignment :=
  ⟨[()],GeneralRebaseCompoundPublic273.AgreesTypes,fun _ => GeneralRebaseCompoundSourceTypes273.Body⟩

namespace Compound
open GeneralDictionaryCompoundFrame238 (before installed)
open GeneralDictionaryCompoundSource238 (sourceRegistry)
open GeneralDictionaryJournalRefinement228Source (root roles)
open GeneralRebaseCompoundSourceTypes273 (PublicSource Body restricted_exact before_exact)
open GeneralRebaseCompoundPublic273 (public_exact)

theorem source (m : Assignment) : Public outputChart before m ↔ PublicSource m := by
  constructor
  · rintro ⟨internal,agree,held⟩
    exact (GeneralRebaseCompoundSourceTypes273.source_depends_on_types internal m agree).mp ((before_exact _).mp held)
  · intro valid
    exact ⟨m,fun _ _ => rfl,(before_exact m).mpr valid⟩

theorem installed_public (m : Assignment) : Public outputChart installed m ↔ PublicSource m ∧ Body m :=
  (public_exact m).trans (restricted_exact m)

theorem exact_relative (m : Assignment) (valid : PublicSource m) :
    Public outputChart installed m ↔
      ∀ f ∈ outputChart.facts, Recorded outputChart installed f → outputChart.meaning f m := by
  apply GeneralRebaseSemanticChart281.exact_with_base (obligations := [()])
  · exact fun v h => ((installed_public v).mp h).1
  · exact fun _ h => h
  · intro v source
    rw [installed_public, and_iff_right source]
    constructor
    · intro body _ _; exact body
    · intro works; exact works () List.mem_cons_self
  all_goals assumption

theorem before_not_entailed : ¬ Recorded outputChart before () := by
  intro yes
  let m := GeneralDictionaryJournalRefinement228Source.model false
  have valid : PublicSource m := by
    refine ⟨?_,CommonNominalFullCarrier.exactEmpty_below_width⟩
    intro i small
    have is : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases is with rfl | rfl | rfl | rfl <;> exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
  have lifted : Public outputChart before m := (source m).mpr valid
  have body := yes _ lifted
  change Equivalent .exactEmpty GeneralDictionaryOptionalOutput229.value at body
  exact GeneralDictionaryOptionalOutput229.not_exact ⟨body.2,body.1⟩

theorem fact_gained : Gain outputChart.facts outputChart.meaning (Public outputChart) before installed :=
  ⟨(),List.mem_cons_self,before_not_entailed,fun m ok => ((installed_public m).mp ok).2⟩

theorem semantic_install : Step outputChart sourceRegistry root before installed :=
  GeneralRebaseChartStep281.semantic_kept GeneralDictionaryCompoundStep238.step fact_gained

theorem public_cut : Loss (Public outputChart) before installed :=
  GeneralRebaseSemanticChart281.gain_cuts fact_gained

theorem point_same (m : Assignment) :
    Public outputChart GeneralDictionaryCompoundPoint238.point m ↔ Public outputChart installed m :=
  exists_congr (fun m => and_congr Iff.rfl (GeneralDictionaryCompoundPoint238.models_iff m))

theorem point_kept :
    Step outputChart sourceRegistry root installed GeneralDictionaryCompoundPoint238.point :=
  GeneralRebaseChartStep281.quiet_kept GeneralDictionaryCompoundPoint238.step rfl

end Compound

namespace Display
open GeneralNominalExamples (registry displayRoot displayChild)
open GeneralRebaseDisplayFrame276 (before)
open GeneralRebaseCompiledInstall277 (adapter_step)
open GeneralRebaseCompiledDisplay277 (after)
open GeneralDeclarationExamples (roles)

theorem graph_fresh : Fresh before after := by
  refine ⟨(displayRoot.identity,displayChild.identity),?_,?_⟩
  · intro seen
    obtain ⟨edge,member,_⟩ := List.mem_map.mp seen
    cases member
  · apply List.mem_map.mpr
    rw [GeneralRebaseFixedDisplayGraph280.actual_edge_list]
    exact ⟨(displayRoot,displayChild),List.mem_cons_self,rfl⟩

theorem graph_only : Step graphChart registry displayRoot before after :=
  GeneralRebaseChartStep281.graph_kept adapter_step graph_fresh

theorem no_public_loss (chart : Chart F V) : ¬ Loss (Public chart) before after := by
  rintro ⟨v,⟨m,agree,valid⟩,rejected⟩
  exact rejected ⟨m,agree,(GeneralRebaseCompiledInstall277.models m).mpr valid⟩

theorem sole_transition (next : State roles) :
    Step graphChart registry displayRoot before next ↔ next = after :=
  ⟨fun h => (GeneralRebaseCompiledAcc277.adapter_next _).mp h.1,fun h => h.symm ▸ graph_only⟩

theorem terminal (next : State roles) : ¬ Step graphChart registry displayRoot after next :=
  fun h => GeneralRebaseCompiledStable277.halted _ h.1

end Display
end Yulang.GeneralRebaseChartFixtures281
