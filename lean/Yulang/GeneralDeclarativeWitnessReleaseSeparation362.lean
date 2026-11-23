import Yulang.GeneralDeclarativeWitnessSeparateAuthorOrder362

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessReleaseSeparation362
open GeneralDeclarativeWitnessNativeInstall360 (Board World Fits atTarget)
open GeneralDeclarativeWitnessNativeRelease360 (ReleaseAuthority ExactRelease Released openWrite checkExactRelease)
open GeneralDeclarativeWitnessNativeValue360 (Write)
open GeneralDeclarativeWitnessTypedRelease354 (Stamp position)

def revokeOwner (b : Board) (departed : Stamp) : Board :=
  {b with active := b.active.filter fun x => decide (x ≠ departed)}

theorem cannot_read_one_address_as_two_writes {b : Board} {g h : ReleaseAuthority} {a c : Write}
    (first : ExactRelease b g a) (second : ExactRelease b h c)
    (same : a.address.target = c.address.target) : a = c := by
  have other := second.released.located
  rw [← same] at other
  exact first.same.symm.trans ((Option.some.inj (first.released.located.symm.trans other)).trans second.same)

theorem different_actual_codes_require_different_addresses {b : Board} {g h : ReleaseAuthority} {a c : Write}
    (first : ExactRelease b g a) (second : ExactRelease b h c) (distinct : a.code ≠ c.code) :
    a.address.target ≠ c.address.target :=
  fun same => distinct (congrArg Write.code (cannot_read_one_address_as_two_writes first second same))

theorem exact_release_exists_iff {b : Board} {g : ReleaseAuthority} {w : Write} :
    Nonempty (ExactRelease b g w) ↔
      atTarget b w.address.target = some w ∧ w.address.owner ∈ b.active ∧
      (b.active.map position).Nodup ∧ w.address ∈ g.grants := by
  constructor
  · rintro ⟨read⟩
    exact ⟨read.released.located.trans (congrArg some read.same),read.released.active,read.released.unique,read.released.granted⟩
  · rintro ⟨found,active,unique,granted⟩
    exact ⟨⟨⟨w,found,rfl,active,unique,granted⟩,rfl⟩⟩

theorem retired_owner_preserves_exactly_other_current_releases {b : Board} {g : ReleaseAuthority} {w : Write}
    (departed : Stamp) (unique : (b.active.map position).Nodup) :
    Nonempty (ExactRelease (revokeOwner b departed) g w) ↔
      Nonempty (ExactRelease b g w) ∧ w.address.owner ≠ departed := by
  -- Old table uniqueness is independently supplied; it is not
  -- reconstructed merely by observing the pruned table.
  constructor
  · rintro ⟨release⟩
    have orig : w.address.owner ∈ b.active ∧ decide (w.address.owner ≠ departed) = true :=
      List.mem_filter.mp release.released.active
    exact ⟨exact_release_exists_iff.mpr
      ⟨release.released.located.trans (congrArg some release.same),orig.1,unique,release.released.granted⟩,
      of_decide_eq_true orig.2⟩
  · rintro ⟨⟨previous⟩,notRetired⟩
    have kept : w.address.owner ∈ (revokeOwner b departed).active :=
      List.mem_filter.mpr ⟨previous.released.active,decide_eq_true notRetired⟩
    have monotone := (List.filter_sublist (p := fun x : Stamp => decide (x ≠ departed)) (l := b.active)).map position
    exact exact_release_exists_iff.mpr ⟨previous.released.located.trans (congrArg some previous.same),
      kept,monotone.nodup unique,previous.released.granted⟩

end Yulang.GeneralDeclarativeWitnessReleaseSeparation362
