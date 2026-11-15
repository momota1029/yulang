import Yulang.GeneralDictionaryMergeCompletion216
import Yulang.GeneralDictionaryDefault214ActualJournal
import Yulang.GeneralDictionaryCurrentRawHead215

/-! Apply finite merge completion to the actual corrected journal. The explicit
separation hypothesis remains an obligation for later reachable states; it is
not inserted into Local, Initial, Selected, or the requested EvidenceNode. -/
namespace Yulang.GeneralDictionaryJournalMerge216
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryMergeSlots216 GeneralDictionaryMergeCompletion216
open GeneralNominalAllocationSupport
open GeneralDictionaryDefault214ActualJournal (journalSources)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}
set_option backward.isDefEq.respectTransparency false

theorem journal (candidate : Plan roles) (pool : List Nat)
    (separate : Separate candidate.packet.context.state candidate.packet.registry candidate.packet.site.occurrence.identity
      candidate.packet.declaration candidate.packet.bindings pool)
    (support : journalSources state ⊆ pool) (previous : Assignment) (valid : Models state previous) :
    Models state (patch candidate.packet.context.state candidate.packet.registry candidate.packet.site.occurrence.identity
      candidate.packet.declaration candidate.packet.bindings previous) :=
  (GeneralDictionaryDefault214ActualJournal.models_iff state
    (fun n h => (preserves separate previous n (support h)).symm)).mp valid

theorem aliased_head (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (historical candidate : Plan roles) (registered : historical ∈ state.core.plans)
    (current : candidate.packet.context = state.core.erased.current.context)
    (inputRegistered : candidate.input ∈ state.core.sites)
    (located : GeneralNominalRecursiveCandidates.arguments candidate.packet.context
      (GeneralNominalCenteredHeadCandidates.inputs candidate.input.occurrence) = some candidate.packet.bounds)
    (alias : GeneralNominalSaturationState.Alias state.core.erased.current
      candidate.packet.site.occurrence.identity historical.packet.site.occurrence.identity)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (pool : List Nat)
    (separate : Separate candidate.packet.context.state candidate.packet.registry candidate.packet.site.occurrence.identity
      candidate.packet.declaration candidate.packet.bindings pool)
    (support : journalSources state ⊆ pool) (endpoints : Endpoints candidate.packet.bindings pool)
    (previous : Assignment) (valid : Models state previous) :
    ∃ extended, Models state extended ∧
      GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
        candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds extended ∧
      ∀ n ∈ pool, extended n = previous n := by
  let extended := patch candidate.packet.context.state candidate.packet.registry candidate.packet.site.occurrence.identity
    candidate.packet.declaration candidate.packet.bindings previous
  have kept := journal candidate pool separate support previous valid
  refine ⟨extended,kept,?_,preserves separate previous⟩
  exact (GeneralDictionaryCurrentRawHead215.head_iff_merges checked source path historical candidate registered
    current inputRegistered located alias declaration extended kept).mpr (merges_valid separate endpoints previous)

end Yulang.GeneralDictionaryJournalMerge216
