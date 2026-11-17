import Yulang.GeneralNominalFiniteEquationRealization236
set_option backward.isDefEq.respectTransparency false
/-! A single conservative assignment for mixed fresh/reused finite equations.
Only targets outside the protected semantic pool are changed. Reused targets
must already satisfy their equations; neither witness is silently combined. -/
namespace Yulang.GeneralNominalSelectiveEquationRealization236
open GeneralNominalFiniteEquationRealization236 (Entry)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredModelExtension
variable (entries : List Entry) (pool : List Nat)
noncomputable def freshEntries : List Entry := by
 classical
 exact entries.filter fun entry => decide (entry.1 ∉ pool)

theorem member_iff : entry ∈ freshEntries entries pool ↔ entry ∈ entries ∧ entry.1 ∉ pool := by
 classical
 simp only [freshEntries,List.mem_filter,decide_eq_true_eq]

noncomputable def patch (model : Assignment) : Assignment :=
 GeneralNominalFiniteEquationRealization236.patch (freshEntries entries pool) model

theorem preserves (identity) (member : identity ∈ pool) : patch entries pool model identity = model identity :=
 GeneralNominalFiniteEquationRealization236.preserves _
   (fun _ present => ((member_iff entries pool).mp present).2) identity member

theorem outside (identity) (absent : ∀ entry ∈ entries, entry.1 ≠ identity) :
 patch entries pool model identity = model identity :=
 GeneralNominalFiniteEquationRealization236.outside _
   (fun entry present => absent entry ((member_iff entries pool).mp present).1)

theorem row (identity) : (patch entries pool model identity).2 = (model identity).2 :=
 GeneralNominalFiniteEquationRealization236.row _ identity

theorem equations
 (coherent : ∀ first ∈ entries, ∀ last ∈ entries, first.1 = last.1 → first.2 = last.2)
 (supported : ∀ entry ∈ entries, ∀ identity ∈ GeneralNominalState.typeSources entry.2, identity ∈ pool)
 (old : ∀ entry ∈ entries, entry.1 ∈ pool →
   PresenceNormalForm.All CommonNominalFullCarrier.model model (GeneralNominalAllocation.equations entry.1 entry.2)) :
 ∀ entry ∈ entries, PresenceNormalForm.All CommonNominalFullCarrier.model (patch entries pool model)
   (GeneralNominalAllocation.equations entry.1 entry.2) := by
 classical
 intro entry member
 by_cases reused : entry.1 ∈ pool
 · apply (GeneralNominalCaptureMerges.equations_exact ..).mpr
   have equal := (GeneralNominalCaptureMerges.equations_exact ..).mp (old entry member reused)
   have meaning := type_eval_same (first := patch entries pool model) (last := model) entry.2
     (fun identity present => preserves entries pool identity (supported entry member identity present))
   rw [preserves entries pool entry.1 reused,meaning]
   exact equal
 · exact GeneralNominalFiniteEquationRealization236.equations _
     (fun one present two found same => coherent one ((member_iff entries pool).mp present).1
       two ((member_iff entries pool).mp found).1 same)
     (fun one present => ((member_iff entries pool).mp present).2)
     (fun one present identity within => supported one ((member_iff entries pool).mp present).1 identity within)
     entry ((member_iff entries pool).mpr ⟨member,reused⟩)
end Yulang.GeneralNominalSelectiveEquationRealization236
