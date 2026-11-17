import Yulang.GeneralNominalPointSourceBoundary240
import Yulang.GeneralNominalPointErasure240
import Yulang.GeneralNominalVersionedMixedSourceBoundary234
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalPointEvidenceTransfer240
open GeneralNominalVersionedJournal232
variable {roles : Roles.RoleDecls} {state : State roles}

theorem local_iff : GeneralNominalPointSourceBoundary240.Local registry state root outcome ↔
 GeneralNominalVersionedMixedSourceBoundary234.Local registry state root outcome :=
 GeneralNominalPointSourceBoundary240.local_iff.trans
 (GeneralNominalPointBoundary240.local_iff.trans
 (GeneralNominalVersionedMixedBoundary234.local_iff.symm.trans
 GeneralNominalVersionedMixedSourceBoundary234.local_iff.symm))

theorem evidenceAt
 (stable : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Stable registry state root)
 (coverage : ∀ demand key children, (demand = root ∨ GeneralNominalSaturationState.Generated state.core.erased.current root demand) →
  GeneralNominalVersionedMixedSourceBoundary234.Local registry state demand (.selected key children) →
  ∀ child ∈ children, GeneralNominalSaturationState.Generated state.core.erased.current root child)
 (held : B4SkeletonV8.EvidenceAt (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry state root) :
 B4SkeletonV8.EvidenceAt (GeneralNominalPointSourceBoundary240.boundary roles) registry state root := by
 intro model valid demand key children dictionaries reached _newStable _newChildStable chosen evidence
 have reached' : GeneralNominalSaturationState.Generated state.core.erased.current root demand := by
   rcases reached with rfl | generated
   · exact .root
   · exact generated
 have localStable : GeneralNominalVersionedMixedKernel234.Stable
   (GeneralNominalCenteredHeadAllocEncoding.registry registry) state demand :=
   fun focus generated => stable focus (GeneralNominalSaturationState.generated_trans reached' generated)
 apply held model valid demand key children dictionaries reached localStable ?_ (local_iff.mp chosen) evidence
 intro child member
 exact fun focus generated => stable focus (GeneralNominalSaturationState.generated_trans (coverage demand key children reached (local_iff.mp chosen) child member) generated)
end Yulang.GeneralNominalPointEvidenceTransfer240
