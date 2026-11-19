import Yulang.GeneralRebaseCertifiedPath266

namespace Yulang.GeneralRebaseCertifiedSteps266
open GeneralRebaseStep258
open GeneralRebaseCertifiedObserver266 (Edge)
open GeneralRebaseCertifiedPath266 (Path edges)
open GeneralRebaseLiveProjection264 (SourceState project)
open GeneralSourceState (Output)
variable {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}

theorem prepend {before middle last : SourceState roles}
 (head : GeneralNominalVersionedMixedKernel234.Step registry root before middle)
 (tail : B4Target.Steps (GeneralNominalVersionedMixedKernel234.Step registry root) middle last) :
 B4Target.Steps (GeneralNominalVersionedMixedKernel234.Step registry root) before last := by
 induction tail with
 | refl => exact .tail .refl head
 | tail _ step ih => exact .tail ih step

theorem to_steps (path : Path registry root first last) :
 B4Target.Steps (GeneralNominalVersionedMixedKernel234.Step registry root) first last := by
 induction path with
 | nil => exact .refl
 | cons edge _ ih => exact prepend edge.actual ih

theorem edge_suffix (path : Path registry root first last) (edge : Edge registry root)
 (listed : edge ∈ edges path) :
 B4Target.Steps (GeneralNominalVersionedMixedKernel234.Step registry root) edge.after last := by
 induction path with
 | nil => simp [edges] at listed
 | cons head tail ih =>
   rcases List.mem_cons.mp listed with same | later
   · cases same
     exact to_steps tail
   · exact ih later

theorem model_restrict (path : Path registry root first last)
 (valid : GeneralNominalVersionedJournal232.Models last assignment) :
 GeneralNominalVersionedJournal232.Models first assignment :=
 GeneralNominalVersionedMixedKernel234.steps_models (to_steps path) valid

theorem final_write (owners : List Nat) (pool : List Output)
 (path : Path registry root first last) :
 write (project owners pool first) (present (project owners pool last)) = project owners pool last := by
 rw [GeneralRebaseSourceProjection264.steps_square owners pool (to_steps path)]
 exact GeneralRebaseProjectionObserver266.write_present _ _

theorem final_known (owners : List Nat) (pool : List Output)
 (path : Path registry root first last) :
 present (project owners pool first) ⊆ present (project owners pool last) := by
 intro fact known
 rw [←final_write owners pool path]
 exact (GeneralRebaseFactSemantics259.present_write _ _ fact).mpr (Or.inl known)

end Yulang.GeneralRebaseCertifiedSteps266
