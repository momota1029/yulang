import Yulang.GeneralDeclarativeCurrentPeer345
import Yulang.GeneralDeclarativeRootReplay344

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 21000
set_option maxHeartbeats 15000000
namespace Yulang.GeneralDeclarativeCurrentPeerOutput345
open GeneralDeclarationExamples (roles)
open GeneralLatePeerRoot311 (z direct)
open GeneralLatePeerMerge311 (final inherited)
open GeneralLatePeerRoutePlan311 (child)
open GeneralLatePeerFinalPeerPlan311 (plan)
open GeneralWhereVersionInstall317 (Journal)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeRootReplay344 (actualDemand requests_exact)
open GeneralDeclarativeRawCapture344 (rawCap)
open GeneralDeclarativeNormalizeAssoc324 (one)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeCurrentPeer345 (ready_with_peer row after_row)
open GeneralDeclarativeCurrentOrder345 (rows)

noncomputable abbrev view : Journal roles := ⟨final,[]⟩

theorem inherited_body (m : Assignment) (fit : Models final m) :
    ∃ eq, one plan.packet.registry plan.packet.context.interpretation plan.packet.declaration
      (actualDemand plan view) (rawCap plan) ⟨1,z⟩ = some [eq] ∧
      eq.left = z ∧ Holds m eq ∧ row ∈ rows final.core child.occurrence := by
  have ready := ready_with_peer.2.2.1
  have effects := GeneralLatePeerCurrent311.classes m fit
  have listed : (⟨1,z⟩ : GeneralSourceState.Output) ∈ (actualDemand plan view).outputs := by
    rw [requests_exact]
    exact inherited
  obtain ⟨eq,ran,target,model⟩ := GeneralDeclarativeRootReplay344.output plan view m rfl ready effects ⟨1,z⟩ listed
  exact ⟨eq,ran,target,model,after_row⟩

end Yulang.GeneralDeclarativeCurrentPeerOutput345
