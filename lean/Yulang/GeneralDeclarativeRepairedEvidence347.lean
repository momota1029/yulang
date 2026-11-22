import Yulang.GeneralDeclarativeNativeBoundary347
import Yulang.GeneralDeclarativeWhereNamedSource346

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 30000000
namespace Yulang.GeneralDeclarativeRepairedEvidence347
open GeneralWhereVersionInstall317 (Models)
open GeneralWherePhysicalCommit319 (final models newChild)
open GeneralWherePhysicalCurrentRead319 (plan low high)
open GeneralWherePhysicalReobserve319 (updated)
open GeneralWherePhysicalPatch319 (n)
open GeneralWherePhysicalEvidence319 (Evidence outputs recursive recorded)
open GeneralWhereOriginSingleSource318 (declaration)
open GeneralLiveCompoundRegistry316 (leaf)
open GeneralDictionaryJournalRefinement228Source (root)
open GeneralDeclarativeJournalRelease347 (release)
open GeneralDeclarativeJournalFixture347 (released_both)
open GeneralDeclarativeNamedProjection347 (project)
open GeneralWhereOriginTrace318 (rawOf)
open GeneralDeclarativeVersionedSeparation342 (root_output)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent)

abbrev dictionary : GeneralDictionaryReadback.Payload := .node declaration.id [.node leaf.id []]

theorem input_output_tree (m : Assignment) (fit : Models final m) :
    (project (rawOf final)).Models m ∧
    release final plan 1 2 0 .lower ∧ release final plan 1 2 0 .upper ∧
    Evidence m root dictionary ∧
    (∀ out ∈ root.demand.outputs, GeneralDictionaryDefaultEvidence204.OutputWitness plan m out) ∧
    Equivalent (m 4).1 GeneralDictionaryOptionalOutput229.value := by
  obtain ⟨lo,hi⟩ := released_both m fit
  exact ⟨(GeneralDeclarativeNamedProjection347.preserves_models _ _).mpr fit.1.1.1,
    lo,hi,recursive m fit,outputs m fit,root_output m fit⟩

/-- This is a real repaired prototype witness with same-model checked
input release, recursive evidence and unchanged output target 4. It
does not transfer to the old native transition relation. -/
theorem inhabited :
    Models final n ∧
    release final plan 1 2 0 .lower ∧ release final plan 1 2 0 .upper ∧
    Evidence n root dictionary ∧
    Equivalent (n 4).1 GeneralDictionaryOptionalOutput229.value := by
  obtain ⟨_,lo,hi,evidence,_,out⟩ := input_output_tree n models
  exact ⟨models,lo,hi,evidence,out⟩

end Yulang.GeneralDeclarativeRepairedEvidence347
