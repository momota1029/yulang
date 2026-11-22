import Yulang.GeneralDeclarativeJournalInput347
import Yulang.GeneralDeclarativeNativeCompound347

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 27000000
namespace Yulang.GeneralDeclarativeNativeBoundary347
open GeneralWhereVersionInstall317 (Journal)
open GeneralWhereOriginTrace318 (rawOf)
open GeneralWhereOriginDelta318 (Cell)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralDeclarativeObservedSyntax347 (structural structural_exact)
open GeneralDeclarativeWhereAttributed346 (literal)
open GeneralDeclarativeNativeWhere347 (layout no_lookup)
open GeneralDeclarativeJournalFixture347 (lower_observed upper_observed)
open GeneralWherePhysicalCommit319 (final)
open GeneralWherePhysicalCurrentRead319 (plan low)
open GeneralDictionaryBinderLocations (sourceSlot)

theorem no_native_observed_where {j : Journal rs} (run : Reachable r root j.mixed) {p : Plan rs}
    (same : (rawOf j).seed = p.packet.context.state.seed) (c : Cell p) :
    structural (rawOf j) c.row.target = none := by
  have absent := no_lookup run (c.high (t := layout j.mixed) same)
  unfold structural
  rw [show sourceSlot (rawOf j).base c.row.target = none from absent]
  rfl

/-- C319's repaired path has a genuinely observed current *physical*
lower cell. It is impossible to identify even its raw mixed component
with an arbitrary run of the unmodified native kernel. -/
theorem corrected_not_native {r : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence _} :
    ¬ Reachable r root final.mixed := by
  intro run
  have missing := no_native_observed_where run (p := plan) (by rfl) low
  have present : structural (rawOf final) low.row.target = some (literal low) := lower_observed
  rw [missing] at present
  cases present

end Yulang.GeneralDeclarativeNativeBoundary347
