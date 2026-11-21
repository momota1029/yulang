import Yulang.GeneralWhereVersionEndpointChoice317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 33000
set_option maxHeartbeats 50000000
namespace Yulang.GeneralWhereVersionReuseCertificate317
open GeneralNominalCenters (Plan)
open GeneralNominalCenteredHeadMatPlanData (Same)
open GeneralWhereVersionCompiler317 (schema children)
open GeneralNominalVersionedPlans231 (variables)
open GeneralNominalCommonBridge (Assignment)

/-- A true semantic condition for reuse: when the erased view agrees,
the entire compiled equation obligation, not merely its numeric keys,
agrees in the very same assignment. -/
theorem compiled_obligation {p q : Plan roles} (same : Same p q) (m : Assignment) :
    ((schema p).unknown = false ∧ (schema p).Holds (variables p m) m) ↔
      ((schema q).unknown = false ∧ (schema q).Holds (variables q m) m) := by
  rw [GeneralWhereVersionRecompile317.schema_eq same,
    GeneralWhereVersionReobserved317.variables_eq same]

open GeneralDictionaryJournalRefinement228Source (root)
open GeneralLiveCompoundRegistry316 (registry declaration leaf otherChild)
open GeneralLiveCompoundFullResult316 (dictionary)
open GeneralWhereVersionCase317 (occ expr)
open GeneralWhereVersionBase317 (loSlot hiSlot)
open GeneralWhereVersionSnapshot317 (snap)
open GeneralWhereVersionRootReport317 (plan)
open GeneralWhereVersionCommit317 (core framedState)
open GeneralWhereVersionInstall317 (Models fixed)
open GeneralWhereVersionEndpointChoice317 (lookup)
open GeneralVersionedEndpointAddress315 (atCell)
open GeneralNominalVersionedEvidence231 (Frame)

/-- Read-only reuse result: no second transaction, fresh variable, or
replacement historical entry is needed for this immediate re-read.
This is not a proposed scheduler rule for arbitrary versioned history. -/
theorem read_only (m : Assignment) (valid : Models fixed m) :
    lookup snap (atCell plan .lower otherChild.id 0 expr) = .slot loSlot ∧
    lookup snap (atCell plan .upper otherChild.id 0 expr) = .slot hiSlot ∧
    Frame registry core root declaration.id plan ∧ GeneralWhereVersionSemantics317.Holds plan m ∧
    (∀ out ∈ root.demand.outputs, GeneralDictionaryDefaultEvidence204.OutputWitness plan m out) ∧
    children plan = [occ] ∧
    GeneralNominalVersionedDiagnostic232.Local registry framedState occ (.selected leaf.id []) ∧
    GeneralWhereVersionRegression317.Evidence m root dictionary := by
  have slots := GeneralWhereVersionEndpointChoice317.reuses
  have certificate := GeneralWhereVersionCurrentCert317.current_certified m valid
  have cfg := GeneralWhereVersionReobserved317.rechecked m valid
  exact ⟨slots.1,slots.2,certificate.1,certificate.2.1,certificate.2.2.1,cfg.2.1,cfg.2.2.2.2.2.1,
    GeneralWhereVersionRegression317.acceptance_sound m valid GeneralWhereVersionRegression317.accepted_root⟩

end Yulang.GeneralWhereVersionReuseCertificate317
