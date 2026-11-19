import Yulang.GeneralRebaseCompoundSchema273
import Yulang.GeneralDictionaryCompoundStep238
import Yulang.GeneralNominalOriginCongruence238
import Yulang.GeneralRebaseOriginCongruence269

set_option maxRecDepth 12000
set_option maxHeartbeats 1800000
namespace Yulang.GeneralRebaseCompoundActual238273
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection (Origin Test Observes)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedCycles232 (Head Edge Cyclic)
open GeneralDictionaryCompoundFrame238 (before installed)
open GeneralDictionaryCompoundPacket238 (plan)
open GeneralDictionaryCompoundSource238 (registry)
open GeneralDictionaryJournalRefinement228Source (root modelHigh)
open GeneralRebaseCompoundSchema273 (derive empty Uniform)

noncomputable def extracted := derive empty plan

theorem extracted_output : extracted 4 = some GeneralDictionaryOptionalOutput229.value := by
 unfold extracted derive
 rw [GeneralDictionaryCompoundVersionedPacket238.emitted_schema,GeneralDictionaryCompoundTotal238.emitted_schema]
 rfl

theorem sound : Uniform installed extracted :=
 GeneralRebaseCompoundSchema273.derive_uniform installed empty plan
   (GeneralRebaseCompoundSchema273.empty_uniform _) (List.mem_cons_self ..)

theorem exact_output (m : Assignment) (valid : Models installed m) :
 Equivalent (m 4).1 GeneralDictionaryOptionalOutput229.value :=
 sound m valid 4 _ extracted_output

theorem no_exact_head (m : Assignment) (valid : Models installed m) (test : Test) :
 ¬ test.Holds (m 4).1 := fun holds =>
 GeneralDictionaryOptionalOutput229.no_test test
   ((GeneralNominalOriginCongruence238.test_iff (exact_output m valid) test).mp holds)

theorem no_head (test : Test) : ¬ Head installed (.source 4) test := by
 intro head
 let ext := GeneralDictionaryCompoundVersionedModel238.extended
 have model := GeneralDictionaryCompoundStep238.installed_model
 exact no_exact_head ext model test ((head ext model).2 _ (.source 4))

theorem no_edge (o : Origin) : ¬ Edge installed (.source 4) o := by
 rintro ⟨p,t,_,head,same,_⟩
 exact no_head t (GeneralRebaseOriginCongruence269.head_transport
   (fun m valid => GeneralNominalOriginTerms.same_symm (same m valid)) head)

theorem no_cycle : ¬ Cyclic installed (.source 4) := by
 rintro ⟨⟨next,out,_⟩,_⟩
 exact no_edge next out

theorem high_before : Models before modelHigh :=
 (GeneralNominalVersionedJournal232.initial_models ..).mpr
  ⟨GeneralDictionaryJournalRefinement228Source.source_models true,
   GeneralNominalCenters.point_root_holds _ _ GeneralDictionaryJournalRefinement228Source.root_point _⟩

theorem no_public_width (m : Assignment) (valid : Models installed m) :
 ¬ Equivalent (m 4).1 (modelHigh 4).1 := by
 intro preserved
 rw [GeneralDictionaryJournalRefinement228Source.high_value] at preserved
 have emitted := exact_output m valid
 exact GeneralDictionaryOptionalOutput229.not_width
  (GeneralDictionaryDefaultExpression209.equivalent_trans ⟨emitted.2,emitted.1⟩ preserved)

theorem step_changes_public_projection :
 GeneralNominalVersionedMixedKernel234.Step registry root before installed ∧
 (∃ first, Models before first ∧ ¬ ∃ last, Models installed last ∧ Equivalent (last 4).1 (first 4).1) :=
 ⟨GeneralDictionaryCompoundStep238.step,modelHigh,high_before,fun ⟨last,valid,preserved⟩ =>
  no_public_width last valid preserved⟩

end Yulang.GeneralRebaseCompoundActual238273
