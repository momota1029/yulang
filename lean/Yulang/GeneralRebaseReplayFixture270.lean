import Yulang.GeneralRebaseReplayScript270
import Yulang.GeneralRebaseCompoundExecutable270
import Yulang.GeneralDictionaryVersionLoopPrefix238

set_option maxHeartbeats 5000000
set_option maxRecDepth 22000
namespace Yulang.GeneralRebaseReplayFixture270
open GeneralRebaseReplayCommand270 (Command run)
open GeneralRebaseReplayScript270 (Script bundle first)
open GeneralRebaseWeakSpine270 (count)
open GeneralRebaseLiveProjection264 (project)

namespace Compound
open GeneralDictionaryCompoundSource238 (registry)
open GeneralDictionaryJournalRefinement228Source (root)
open GeneralDictionaryCompoundFrame238 (before installed effect)
open GeneralRebaseSourceStrictFixture265 (owners pool)
open GeneralDictionaryCompoundStep238 (installable not_committed)

noncomputable def installCmd : Command registry root before :=
 .install effect .root installable not_committed

noncomputable def actual : Script registry root before installed :=
 .execute installCmd (.done installed)

theorem computed_count : count (bundle owners pool actual) = 1 := by decide +kernel

theorem concrete_exit : (first owners pool actual).map Subtype.val = some installed := by
 have changeBit : GeneralRebaseLullSpine270.changed owners pool (GeneralRebaseReplayCommand270.edge installCmd) = true :=
   (GeneralRebaseLullSpine270.changed_exact ..).mpr GeneralRebaseSourceStrictFixture265.strict
 unfold first bundle actual GeneralRebaseReplayScript270.path
 simp only [GeneralRebaseWeakSpine270.normalize]
 rw [dite_eq_left changeBit]
 rfl

theorem end_matches_code :
 GeneralRebaseCompoundExecutable270.run.2.label = (project owners pool installed).remaining := by
 rw [GeneralRebaseCompoundExecutable270.computed_run,GeneralRebaseBehaviorFixture269.exhausted]
 rfl

end Compound

namespace Refresh
open GeneralDictionaryVersionLoopSource237 (registry root)
open GeneralDictionaryVersionLoopFrame237 (installed)
open GeneralDictionaryVersionLoopRefreshBase237 (extendedContext)
open GeneralDictionaryVersionLoopRefresh237 (lower_supported lower_unknown lower_known)
open GeneralDictionaryVersionLoopPacket237 (lo)
open GeneralDictionaryVersionLoopRetarget237 (refreshed retargeted revision certificate improved)

noncomputable def refreshCmd : Command registry root installed :=
 .refresh root extendedContext lo .root
   (GeneralNominalVersionedMixedObservations233.of_versioned_refresh GeneralDictionaryVersionLoopRefresh237.certificate)
   lower_supported lower_unknown lower_known

noncomputable def reviseCmd : Command registry root refreshed :=
 .reobserve root revision .root certificate improved

noncomputable def genuine : Script registry root installed retargeted :=
 .execute refreshCmd (.execute reviseCmd (.done retargeted))

def owners : List Nat := [0]
def pool : List GeneralSourceState.Output := [⟨0,4⟩]

theorem computed_zero : count (bundle owners pool genuine) = 0 := by decide +kernel

theorem no_hit : first owners pool genuine = none := by
 have test : (first owners pool genuine).isNone = true := by decide +kernel
 exact Option.isNone_iff_eq_none.mp test

theorem genuine_lull : GeneralRebaseWeakProgress268.Lull registry root owners pool installed retargeted :=
 GeneralRebaseReplayScript270.no_hit owners pool genuine no_hit

end Refresh
end Yulang.GeneralRebaseReplayFixture270
