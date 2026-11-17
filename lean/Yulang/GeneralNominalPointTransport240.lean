import Yulang.GeneralNominalPointSourceBoundary240
import Yulang.GeneralNominalPointErasure240
import Yulang.GeneralNominalVersionedMixedEmbedding234
namespace Yulang.GeneralNominalPointTransport240
open GeneralNominalVersionedJournal232
variable {roles : Roles.RoleDecls} {state : State roles}

theorem initial_iff :
 (GeneralNominalPointSourceBoundary240.boundary roles).Initial registry root state ↔
 (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial registry root state := Iff.rfl

theorem reachable_old (path : B4TargetV8.Reachable (GeneralNominalPointSourceBoundary240.boundary roles) registry root state) :
 B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state := by
 obtain ⟨start,initial,path⟩ := path
 exact ⟨start,initial,GeneralNominalPointErasure240.steps_old path⟩

theorem local_iff : GeneralNominalPointSourceBoundary240.Local registry state root frontier ↔
 GeneralNominalVersionedMixedSourceBoundary234.Local registry state root frontier := by
 rw [GeneralNominalPointSourceBoundary240.local_iff,GeneralNominalVersionedMixedSourceBoundary234.local_iff]
 exact GeneralNominalPointBoundary240.local_iff.trans GeneralNominalVersionedMixedBoundary234.local_iff.symm

theorem old_stable (stable : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Stable registry state root) :
 (GeneralNominalPointSourceBoundary240.boundary roles).Stable registry state root :=
 GeneralNominalPointErasure240.old_stable stable

theorem source_cache (path : B4TargetV8.Reachable (GeneralNominalPointSourceBoundary240.boundary roles) registry root state) :
 GeneralNominalVersionedMixedKernelCache234.Valid state :=
 GeneralNominalVersionedMixedEmbedding234.source_cache (reachable_old path)

theorem source_recorded (path : B4TargetV8.Reachable (GeneralNominalPointSourceBoundary240.boundary roles) registry root state) :
 GeneralNominalVersionedMixedRecorded234.Recorded state :=
 GeneralNominalVersionedMixedEmbedding234.source_recorded (reachable_old path)
end Yulang.GeneralNominalPointTransport240
