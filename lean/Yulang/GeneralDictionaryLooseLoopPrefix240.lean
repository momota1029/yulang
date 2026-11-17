import Yulang.GeneralDictionaryLooseLoopInstall240
import Yulang.GeneralDictionaryLooseLoopRetarget240
set_option backward.isDefEq.respectTransparency false
/-! A finite, genuine successor-boundary path from its checked ground source.
The nonpoint root retarget is permitted by I45. No infinite trace is asserted. -/
namespace Yulang.GeneralDictionaryLooseLoopPrefix240
open GeneralDictionaryLooseLoopSource240 GeneralDictionaryLooseLoopRetarget240

theorem path : B4Target.Steps (GeneralNominalPointKernel240.Step registry root)
 initial retargeted :=
 .tail (.tail (.tail .refl GeneralDictionaryLooseLoopInstall240.step) refresh_step) retarget_step

theorem reachable : B4TargetV8.Reachable (GeneralNominalPointSourceBoundary240.boundary roles)
 sourceRegistry root retargeted :=
 ⟨initial,GeneralDictionaryLooseLoopInitial240.initial_source,path⟩

theorem inhabited : GeneralNominalVersionedJournal232.Models retargeted model := retargeted_model

theorem root_changed : revision.entries (3 : Fin 6) ≠
 refreshed.core.erased.current.context.state.nominals (3 : Fin 6) := by
 intro equal
 have descriptors := Option.some.inj equal
 have arguments := congrArg GeneralNominalState.Descriptor.arguments descriptors
 simp [GeneralDictionaryLooseLoopRefreshBase240.pairOld,
     GeneralNominalRefinements.renameDescriptor,GeneralNominalRefinements.renameParameter,
     GeneralDictionaryLooseLoopRefreshBase240.embed] at arguments
end Yulang.GeneralDictionaryLooseLoopPrefix240
