import Yulang.GeneralNominalVersionedMixedSourceBoundary234
import Yulang.GeneralNominalVersionedMixedKernelCache234
import Yulang.GeneralNominalVersionedMixedRecorded234
set_option backward.isDefEq.respectTransparency false
/-! Old paths embed into the mixed-cache successor. Local diagnostics and model
meaning are identical, but Stable is only transported from new to old. -/
namespace Yulang.GeneralNominalVersionedMixedEmbedding234
open GeneralNominalVersionedJournal232
variable {roles : Roles.RoleDecls}

theorem reachable
    (path : B4TargetV8.Reachable (GeneralNominalVersionedSourceBoundary232.boundary roles) registry root state) :
    B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state := by
  obtain ⟨first,initial,path⟩ := path
  exact ⟨first,initial,GeneralNominalVersionedMixedKernel234.old_steps path⟩

theorem local_iff :
    GeneralNominalVersionedMixedSourceBoundary234.Local registry state root frontier ↔
    GeneralNominalVersionedSourceBoundary232.Local registry state root frontier := by
  rw [GeneralNominalVersionedMixedSourceBoundary234.local_iff,GeneralNominalVersionedSourceBoundary232.local_iff,
    GeneralNominalVersionedMixedBoundary234.local_iff,GeneralNominalVersionedBoundary232.local_iff]

theorem source_cache
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state) :
    GeneralNominalVersionedMixedKernelCache234.Valid state :=
  GeneralNominalVersionedMixedKernelCache234.reachable_cache
    (GeneralNominalVersionedMixedSourceBoundary234.reachable_compiled path)

theorem source_recorded
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state) :
    GeneralNominalVersionedMixedRecorded234.Recorded state :=
  GeneralNominalVersionedMixedRecorded234.reachable path

end Yulang.GeneralNominalVersionedMixedEmbedding234
