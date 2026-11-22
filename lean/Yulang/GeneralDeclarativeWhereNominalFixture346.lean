import Yulang.GeneralDeclarativeWhereNominal346
import Yulang.GeneralDeclarativeWhereNonPoint346

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 18000000
namespace Yulang.GeneralDeclarativeWhereNominalFixture346
open GeneralWherePhysicalPast319 (loose two four)
open GeneralWherePhysicalCurrentRead319 (zero desc nominal0)
open GeneralWherePhysicalReobserve319 (updated)
open GeneralDictionaryBinderLocations (sourceSlot sourceSlot_exact)
open GeneralDeclarativeWhereNominal346 (scan observed)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralDeclarativeHead320 (environment)
open GeneralStoppedShape335 (point)
open CommonNominalFullCarrier (Equivalent)

theorem exact_current :
    scan GeneralWherePhysicalPast319.point 0 0 [2,2] = some zero := by
  have atHead : sourceSlot GeneralWherePhysicalPast319.point.base 0 = some zero := (sourceSlot_exact ..).mpr rfl
  have atTwo : sourceSlot GeneralWherePhysicalPast319.point.base 2 = some two := (sourceSlot_exact ..).mpr rfl
  have encoded : point desc.arguments = some [two,two] := rfl
  have key : desc.declaration.name = 0 := rfl
  simp [scan,atHead,nominal0,encoded,List.mapM_cons,atTwo,key]

theorem no_stale_argument :
    scan GeneralWherePhysicalPast319.point 0 0 [4,2] = none := by
  have atHead : sourceSlot GeneralWherePhysicalPast319.point.base 0 = some zero := (sourceSlot_exact ..).mpr rfl
  have atTwo : sourceSlot GeneralWherePhysicalPast319.point.base 2 = some two := (sourceSlot_exact ..).mpr rfl
  have atFour : sourceSlot GeneralWherePhysicalPast319.point.base 4 = some four := (sourceSlot_exact ..).mpr rfl
  have encoded : point desc.arguments = some [two,two] := rfl
  have diff : two ≠ four := by decide +kernel
  simp [scan,atHead,nominal0,encoded,List.mapM_cons,atTwo,atFour,diff]

theorem actual_source (m : Assignment) (fit : GeneralWhereVersionInstall317.Models updated m) :
    Equivalent (m 0).1 (value (environment m) .actual (.nominal 0 [.variable 2,.variable 2])) :=
  observed exact_current m fit.1.1.1

end Yulang.GeneralDeclarativeWhereNominalFixture346
