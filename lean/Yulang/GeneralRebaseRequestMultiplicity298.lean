import Yulang.GeneralRebaseExecutableJournal298
import Yulang.GeneralRebaseRefreshInstall298

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseRequestMultiplicity298
open GeneralDictionaryOutputDepth252 (roles root initial plan)
open Core.PresenceGeneration (CompTerm)
open GeneralRebaseExecutableJournal298 (cls)
open GeneralRebaseExecutableRequests262 (requests)

-- Explicit order/duplicate data control, not another source initialization.
def doubled : GeneralNominalCenteredSteps.State roles :=
  { initial.core with erased :=
    { initial.core.erased with current :=
      { initial.core.erased.current with sites :=
        initial.core.erased.current.sites ++ initial.core.erased.current.sites } } }

theorem repetitions : requests doubled root = [⟨0,3⟩,⟨0,3⟩] := by decide +kernel

def compiled := cls doubled root plan CompTerm.var

theorem literal_size : compiled.equations.length = 2 ∧ compiled.equalities.length = 8 := by decide +kernel

theorem unchanged_semantics (m : GeneralNominalCommonBridge.Assignment) :
    compiled.Holds m ↔ GeneralNominalVersionedEffects231.ClassEffects doubled root plan m := by
  unfold compiled
  rw [GeneralRebaseExecutableJournal298.cls_exact]
  exact GeneralNominalRebaseClassView243.compile_exact doubled root plan CompTerm.var m

end Yulang.GeneralRebaseRequestMultiplicity298
