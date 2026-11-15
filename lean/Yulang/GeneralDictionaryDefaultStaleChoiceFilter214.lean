import Yulang.GeneralDictionaryDefaultChoice214
import Yulang.GeneralDictionaryJournalObstruction

/-! The old raw stale-choice obstruction is not a counterexample to the
corrected reachable EvidenceNode domain: its stored declaration is invisible.
This does not prove general current ChoiceCompatible. -/
namespace Yulang.GeneralDictionaryDefaultStaleChoiceFilter214
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralDictionaryJournalObstruction
open GeneralDictionaryRecursiveObstruction (registry)

theorem stale_invisible : staleDeclaration ∉ registry.declarations := by
  intro member
  have same := List.mem_singleton.mp member
  have keys := congrArg GeneralDeclarations.Declaration.id same
  cases keys

theorem raw_obstruction_not_reachable
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (same : state.core.erased.current = journal) : False := by
  have present : stalePacket ∈ state.core.erased.current.packets := by
    rw [same]
    exact List.mem_singleton_self _
  exact stale_invisible (GeneralDictionaryDefaultChoice214.visible_packets path stalePacket present)

end Yulang.GeneralDictionaryDefaultStaleChoiceFilter214
