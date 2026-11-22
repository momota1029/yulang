import Yulang.GeneralDeclarativeWhereRawTicket346
import Yulang.GeneralWherePhysicalCommit319

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 22000
set_option maxHeartbeats 14000000
namespace Yulang.GeneralDeclarativeWherePhysical346
open GeneralDictionaryJournalRefinement228Source (roles)
open GeneralWherePhysicalCurrentRead319 (plan low high address_lo address_hi reads)
open GeneralWherePhysicalReobserve319 (updated)
open GeneralWherePhysicalActive319 (ctx active_models)
open GeneralWherePhysicalFresh319 (finalLayout newAtoms oldTwo oldTwo_id lowerSlot lower_id upperSlot upper_id)
open GeneralWhereOriginSingleCells318 (loNow hi)
open GeneralWhereOriginInstall318 (RawTicket)
open GeneralWhereVersionInstall317 (Models)
open GeneralWherePhysicalBase319 (expand)
open GeneralDictionaryBinderLocations (sourceSlot sourceSlot_exact)
open GeneralDeclarativeWhereRawTicket346 (emitted gives_ticket)
open GeneralDeclarativeWhereRawAtoms346 (cell batch)
open GeneralDeclarativeWhereRawExpr346 (compile)
open GeneralNominalVersionedPlans231 (variables)
open GeneralWhereOriginDelta318 (Cell)
open GeneralNominalCommonBridge (Assignment)
open GeneralWhereVersionCase317 (expr)

noncomputable abbrev basis := expand finalLayout []

theorem reads_two : sourceSlot basis 2 = some oldTwo :=
  (sourceSlot_exact ..).mpr oldTwo_id

theorem fresh_lower : cell basis low = some newAtoms := by
  have target : sourceSlot basis loNow = some lowerSlot := (sourceSlot_exact ..).mpr lower_id
  unfold cell
  change (do let slot ← sourceSlot basis (GeneralVersionedEndpointAddress315.atCell plan .lower
              GeneralLiveCompoundRegistry316.otherChild.id 0 expr)
             let rhs ← compile (fun name => sourceSlot basis
               (GeneralNominalVersionedExpressionFrame236.variableSource plan .lower name)) expr
             return GeneralSourceState.equationAtoms slot rhs) = some newAtoms
  rw [address_lo,target]
  have lowered : compile (fun name => sourceSlot basis
      (GeneralNominalVersionedExpressionFrame236.variableSource plan .lower name)) expr =
      some (.variant 0 (.var oldTwo)) := by
    simp [compile,reads.1,reads_two]
  rw [lowered]
  rfl

theorem exact_batch : emitted (j := updated) finalLayout [low] = some newAtoms := by
  change batch basis [low] = some newAtoms
  unfold batch
  rw [fresh_lower]
  rfl

theorem derived_ticket : RawTicket updated plan ctx := by
  have formal := gives_ticket (j := updated) (p := plan) finalLayout exact_batch
    (ctx := ⟨GeneralWherePhysicalFresh319.raw,ctx.interpretation⟩) rfl
  intro m before selected
  exact (active_models m).mpr (formal m before selected)

theorem retained_upper (m : Assignment) (valid : Models updated m) :
    sourceSlot basis hi = some upperSlot ∧ high.row.Holds (variables plan m) m :=
  ⟨(sourceSlot_exact ..).mpr upper_id,GeneralWherePhysicalTicket319.current_upper_stored m valid⟩

end Yulang.GeneralDeclarativeWherePhysical346
