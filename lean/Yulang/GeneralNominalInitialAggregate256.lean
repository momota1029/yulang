import Yulang.GeneralNominalFrameAggregate256
import Yulang.GeneralNominalSourcePublicBasis255
namespace Yulang.GeneralNominalInitialAggregate256
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232
open GeneralNominalFrameAggregate256
open GeneralNominalHistoricalAggregate256
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

/-- The same basis fixed before the trace handles every declared input of
any actually prepared initial frame, without adding a closure assumption. -/
theorem prepared (context : GeneralNominalCandidates.Context) (root : Occurrence roles)
 (labels : List GeneralDeclarationPatterns.Pattern)
 (frame : GeneralNominalVersionedEvidence231.Frame registry (initial context root).core focus key plan)
 (name : Nat) (named : name ∈ plan.packet.declaration.inputNames) :
 prepare (GeneralNominalSourcePublicBasis255.basis registry context root labels) [] (pairs plan name) =
 some (rewrite (GeneralNominalSourcePublicBasis255.basis registry context root labels) [] (pairs plan name)) := by
 have same : plan.packet.context = context := frame.context_eq
 have success := identity_prepared frame
   (GeneralNominalOwnerCandidates252.owners registry context.state.seed root.identity
     (GeneralNominalPatersonLineage.mass labels)) name named
 simpa only [same,GeneralNominalSourcePublicBasis255.basis] using success

theorem fits (context : GeneralNominalCandidates.Context) (root : Occurrence roles)
 (labels : List GeneralDeclarationPatterns.Pattern)
 (frame : GeneralNominalVersionedEvidence231.Frame registry (initial context root).core focus key plan)
 (name : Nat) (named : name ∈ plan.packet.declaration.inputNames)
 (assignment : Assignment) (actual : Ty) :
 (rewrite (GeneralNominalSourcePublicBasis255.basis registry context root labels) [] (pairs plan name)).Fits assignment actual ↔
 ∀ pair ∈ pairs plan name, GeneralNominalCaptureMerges.Fits assignment pair actual :=
 fits_exact _ [] _ _ (prepared context root labels frame name named) assignment actual
end Yulang.GeneralNominalInitialAggregate256
