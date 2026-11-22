import Yulang.GeneralDeclarativeStoppedOrigins339
import Yulang.GeneralDeclarativeStoppedLower339
import Yulang.GeneralDictionaryCompoundStep238

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace Yulang.GeneralDeclarativeStoppedFixture339
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryCompoundSource238 (registry)
open GeneralDictionaryCompoundFrame238 (before installed effect frame)
open GeneralDictionaryCompoundPacket238 (plan)
open GeneralDictionaryCompoundStep238 (step installed_model)
open GeneralDictionaryCompoundVersionedModel238 (extended)
open GeneralNominalCenteredHeadOutputs (requests request_retained)
open GeneralNominalVersionedInstall232 (requests_included)
open GeneralDeclarativeStoppedOutput339 (ordinary Receipt row_present)
open GeneralStoppedInstallHistory335 (InstalledBetween saved_projection)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralSourceState (Output)
open B4Target (Steps)

abbrev fixed : Output := ⟨0,4⟩
abbrev expression := GeneralDictionaryOptionalExpression229.expression
abbrev row : Equation := ⟨4,expression⟩

theorem initial_request : fixed ∈ requests before.core root := by
  exact request_retained plan.packet.site frame.raw_recorded (.refl _) List.mem_cons_self

theorem persisted_request : fixed ∈ requests installed.core effect.plan.packet.site.occurrence :=
  requests_included before.core effect.plan _ initial_request

theorem compiled_exact : ordinary effect.plan fixed
    (.explicit ⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩) = some row := rfl

theorem actual : Receipt installed effect fixed row :=
  ⟨persisted_request,_,rfl,compiled_exact⟩

/-- Nonvacuity at an actual raw install, not a claimed full solver
success: the C238 original path and established model produce the
literal associated row at fixed target 4, with its exact real writer. -/
theorem installed_valid :
    InstalledBetween registry root before installed effect ∧
      Receipt installed effect fixed row ∧ Holds extended row ∧ row.left = 4 := by
  have retained : effect ∈ installed.effects := List.mem_cons_self
  obtain ⟨origin,_,_⟩ := saved_projection (.tail .refl step) rfl retained installed_model
  obtain ⟨holds,exactName⟩ := row_present retained actual installed_model
  exact ⟨origin,actual,holds,exactName⟩

theorem recognized_boundary :
    GeneralStoppedProjectedTrace335.normalized installed = none := rfl

/-- The width head on an actual raw slot now has a literal faithful
encoding, but another unsupported stored slot still keeps the *whole*
old fixture outside structural lowering. The install receipt above
does not require this whole-state projection. -/
theorem concrete_width_head :
    GeneralDeclarativeStoppedLower339.headAt
      (GeneralStoppedProjectedTrace335.current installed) ⟨2,by decide⟩ = some [⟨2,.primitive .emptyRecord []⟩] := rfl

theorem structural_boundary :
    GeneralDeclarativeStoppedLower339.lower
      (GeneralStoppedProjectedTrace335.current installed) = none := rfl

end Yulang.GeneralDeclarativeStoppedFixture339
