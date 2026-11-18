import Yulang.GeneralRebaseSourceInstallProjection264
import Yulang.GeneralDictionaryCompoundStep238
#print axioms Yulang.GeneralRebaseSourceInstallProjection264.historical_facts
#print axioms Yulang.GeneralRebaseSourceInstallProjection264.liveFacts_exact
#print axioms Yulang.GeneralRebaseSourceInstallProjection264.project_install
#print axioms Yulang.GeneralRebaseSourceInstallProjection264.current_requests
#print axioms Yulang.GeneralRebaseSourceInstallProjection264.current_proposal
#print axioms Yulang.GeneralRebaseSourceInstallProjection264.project_install_current
namespace Yulang.Cycle264SourceInstallProjection
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryCompoundSource238
open GeneralDictionaryCompoundFrame238
open GeneralDictionaryCompoundPacket238 (plan)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebaseMultiSelection263 (proposal ofPlan)
/-- An actual operational installation, not an arbitrary effect fixture. -/
theorem compound_square (owners : List Nat) (pool : List GeneralSourceState.Output) :
 project owners pool installed = GeneralRebaseStep258.write (project owners pool before)
   (proposal before.core (ofPlan plan)) := by
 exact GeneralRebaseSourceInstallProjection264.project_install_current sourceRegistry ⟨rfl,checked⟩ root before
   ⟨before,⟨start,initial,rfl⟩,.refl⟩ effect GeneralDictionaryCompoundStep238.installable owners pool
#print axioms compound_square
end Yulang.Cycle264SourceInstallProjection
