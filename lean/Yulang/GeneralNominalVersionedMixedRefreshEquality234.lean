import Yulang.GeneralNominalVersionedMixedTerminalStable234
import Yulang.GeneralNominalVersionedTerminalStable233
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalVersionedMixedRefreshEquality234
open GeneralNominalVersionedMixedObservations233
open GeneralNominalVersionedMixedTerminalStable234
open GeneralNominalVersionedJournal232
open GeneralNominalVersionedRefresh232

theorem equality_closed (certificate : Refresh state context) (closed : EqualityClosed state) :
    EqualityClosed (refresh state context) := by
  intro first last one two equal
  have oldEqual : GeneralNominalVersionedMixedKernel234.Equal state first last := by
    intro model valid
    exact equal model ((refresh_models certificate).mpr valid)
  have raw := closed first last (certificate.support first one) (certificate.support last two) oldEqual
  intro model valid
  exact raw model (GeneralNominalRefinements.models certificate.refines model valid)

theorem old_equality_closed
    (certificate : Refresh state context)
    (closed : GeneralNominalVersionedTerminalStable233.EqualityClosed state) :
    EqualityClosed (refresh state context) := equality_closed certificate closed

end Yulang.GeneralNominalVersionedMixedRefreshEquality234
