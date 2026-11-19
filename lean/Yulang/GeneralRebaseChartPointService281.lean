import Yulang.GeneralRebaseChartSilent281
import Yulang.GeneralRebaseTerminalRepair274
import Yulang.GeneralRebaseTerminalPayload274

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebaseChartPointService281
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryJournalRefinement228Source (root roles)
open GeneralDictionaryOptionalInitial229 (sourceRegistry registry declaration)
open GeneralDictionaryVersionedPointStage233 (point raw_sites centered_sites)
open GeneralDictionaryVersionedSecondInstall233 (installed plan effect terminal)
open GeneralDictionaryVersionedSecondStep233 (counter counter_model no_packet)
open GeneralRebaseTerminalPublic274 (point_exact terminal_exact)
open GeneralRebaseChartFixtures281 (outputChart)
open GeneralRebaseChartStep281 (Public Step)
open GeneralRebaseMixedCounts277 (Actual)
open GeneralNominalVersionedEvidence231 (Evidence Frame)

theorem raw_service : Actual sourceRegistry root point installed :=
  GeneralNominalVersionedMixedKernel234.old_step GeneralDictionaryVersionedSecondStep233.step

theorem same_type_public (m : Assignment) : Public outputChart installed m ↔ Public outputChart point m :=
  (terminal_exact m).trans (point_exact m).symm

theorem edges_same : installed.core.erased.current.edges = point.core.erased.current.edges := by
  change point.core.erased.current.edges ++ GeneralNominalVersionedChildren232.edges plan = _
  unfold GeneralNominalVersionedChildren232.edges
  rw [terminal]
  simp only [List.map_nil,List.append_nil]

theorem chart_blocks_service : ¬ Step outputChart sourceRegistry root point installed :=
  GeneralRebaseChartSilent281.blocked
    (by change (_ :: point.plans).length ≠ point.plans.length; simp)
    edges_same same_type_public

theorem point_plan {candidate : GeneralNominalCenters.Plan roles} {key : Nat}
    (given : Frame registry point.core root key candidate) : candidate = plan :=
  GeneralNominalVersionedFrameFunctional232.frame_plan_unique rfl raw_sites centered_sites
    given GeneralDictionaryVersionedPointSafety233.frame

theorem counter_no_leaf :
    ¬ Evidence registry point.core counter root (.node declaration.id []) := by
  intro impossible
  have erased := (GeneralDictionaryReadback.payload_iff_erased _ _ _).mpr impossible
  cases erased with
  | node rule children =>
    obtain ⟨p,cert⟩ := rule
    have same := point_plan cert.frame
    exact no_packet (same ▸ cert.packet)

theorem counter_repaired (m : Assignment) (valid : Models point m) :
    ∃ better, GeneralRebaseCompoundPublic273.AgreesTypes better m ∧ Models installed better ∧
      Evidence registry installed.core better root (.node declaration.id []) := by
  let tuned := GeneralRebaseTerminalRepair274.repair m
  have repaired := GeneralRebaseTerminalRepair274.repairs _ valid
  refine ⟨tuned,?_,repaired,GeneralDictionaryVersionedSecondInstall233.evidence repaired⟩
  exact fun id small => congrArg Prod.fst ((GeneralRebaseTerminalRepair274.public_preserved m _ _).1 id small)

theorem point_leaf_on_repaired (m : Assignment) (valid : Models point m) :
    ∃ better, GeneralRebaseCompoundPublic273.AgreesTypes better m ∧ Models point better ∧
      Evidence registry point.core better root (.node declaration.id []) := by
  let tuned := GeneralRebaseTerminalRepair274.repair m
  have kept : Models point tuned := GeneralRebaseTerminalRepair274.write_point _ valid _ _
  have fields := GeneralRebaseTerminalRepair274.repair_new m
  have certificate := GeneralNominalVersionedEvidence231.certificate_of_semantics
    GeneralDictionaryVersionedPointSafety233.frame terminal.symm
    (GeneralRebaseTerminalPointExact274.packet_of_point tuned kept fields) effect.ready
    (GeneralRebaseTerminalPointExact274.classes_of_point tuned kept fields)
  refine ⟨tuned,(fun id small => congrArg Prod.fst ((GeneralRebaseTerminalRepair274.public_preserved m _ _).1 id small)),kept,?_⟩
  exact GeneralNominalVersionedEvidence231.evidence_leaf ⟨plan,certificate⟩

end Yulang.GeneralRebaseChartPointService281
