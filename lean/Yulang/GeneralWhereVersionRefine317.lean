import Yulang.GeneralWhereVersionSnapshot317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 43000000
namespace Yulang.GeneralWhereVersionRefine317
open GeneralWhereVersionBase317 (base injectOld source_old)
open GeneralWhereVersionSnapshot317 (snap base_heads zero one nextDesc)
open GeneralLiveCompoundPost316 (raw)
open GeneralLiveCompoundUpperSnapshot316 (desc)
open GeneralNominalState (Known sources)

theorem ordinary_member (a : PresenceNormalForm.Atom (Fin 8))
    (member : a ∈ raw.base.ordinary) : a.rename injectOld ∈ base.ordinary :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨a,member,rfl⟩))

theorem base_known (i : Fin 8) :
    raw.base.graph i ≠ .unresolved → base.graph (injectOld i) ≠ .unresolved := by
  revert i
  decide +kernel

theorem view_known (i : Fin 8) :
    raw.view.graph i ≠ .unresolved → snap.view.graph (injectOld i) ≠ .unresolved := by
  revert i
  decide +kernel

theorem nominal_keep (i : Fin 8) (d) (found : raw.nominals i = some d) :
    snap.nominals (injectOld i) = some (GeneralNominalRefinements.renameDescriptor injectOld d) := by
  change (if i = 0 ∨ i = 1 then some desc else none) = some d at found
  split at found
  · rename_i yes
    cases Option.some.inj found
    rcases yes with rfl|rfl <;> rfl
  · cases found

noncomputable def refines : GeneralNominalRefinements.Refines raw snap where
  base := ⟨injectOld,source_old,source_old,ordinary_member,base_known,fun _ h => nomatch h⟩
  heads := by
    intro i t recorded
    change Fin 8 at i
    change Core.PresenceGeneration.TyTerm (Fin 8) at t
    change (GeneralMixedCompoundUpperBase307.base.heads i).equation = some t at recorded
    exact .head (by
      change (base.heads (injectOld i)).equation = some (t.rename injectOld)
      rw [base_heads,recorded]; rfl)
  nominals := nominal_keep
  ordinary := fun _ h => h
  known := by
    rintro n ⟨slot,eq,head|⟨d,recorded⟩⟩
    · exact ⟨injectOld slot,(source_old slot).trans eq,.inl (view_known slot head)⟩
    · exact ⟨injectOld slot,(source_old slot).trans eq,.inr ⟨_,nominal_keep slot d recorded⟩⟩
  reserved := fun _ h => h
  allocated := fun _ h => h
  seed := rfl
  constructors := rfl

theorem restrict (m : GeneralNominalCommonBridge.Assignment) (given : GeneralNominalState.Models snap m) :
    GeneralNominalState.Models raw m :=
  GeneralNominalRefinements.models refines m given

end Yulang.GeneralWhereVersionRefine317
