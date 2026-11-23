import Yulang.GeneralDeclarativeWitnessReleaseSeparation362

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessExecutableRelease362
open GeneralDeclarativeWitnessReleaseSeparation362 (revokeOwner exact_release_exists_iff retired_owner_preserves_exactly_other_current_releases)
open GeneralDeclarativeWitnessNativeInstall360 (Board atTarget)
open GeneralDeclarativeWitnessNativeRelease360 (ReleaseAuthority ExactRelease Released openWrite checkExactRelease)
open GeneralDeclarativeWitnessNativeValue360 (Write)
open GeneralDeclarativeWitnessTypedRelease354 (Stamp position)

theorem open_from_exact_facts {b : Board} {g : ReleaseAuthority} {w : Write}
    (located : atTarget b w.address.target = some w)
    (active : w.address.owner ∈ b.active) (unique : (b.active.map position).Nodup)
    (allowed : w.address ∈ g.grants) :
    ∃ actual, openWrite b g w.address = some actual ∧ actual.stored = w := by
  unfold openWrite
  split
  · rename_i absent
    rw [located] at absent
    cases absent
  · rename_i row seen
    have same := Option.some.inj (seen.symm.trans located)
    subst row
    simp only [active,unique,allowed,and_self,dite_true,Option.some.injEq]
    exact ⟨_,rfl,rfl⟩

/-- The actual executable guard reflects the exact named row, current
owner/version, table uniqueness and independent grant, not model truth. -/
theorem exact_release_checker {b : Board} {g : ReleaseAuthority} {w : Write} :
    (checkExactRelease b g w).isSome = true ↔ Nonempty (ExactRelease b g w) := by
  constructor
  · intro h
    cases observed : checkExactRelease b g w with
    | none => simp [observed] at h
    | some certificate => exact ⟨certificate⟩
  · intro plausible
    obtain ⟨exists_,active,unique,allowed⟩ := exact_release_exists_iff.mp plausible
    obtain ⟨actual,read,same⟩ := open_from_exact_facts exists_ active unique allowed
    simp [checkExactRelease,read,same]

theorem executable_retirement_only_removes_own_release {b : Board} {g : ReleaseAuthority} {w : Write}
    (departed : Stamp) (original : (b.active.map position).Nodup) :
    (checkExactRelease (revokeOwner b departed) g w).isSome = true ↔
      (checkExactRelease b g w).isSome = true ∧ w.address.owner ≠ departed := by
  rw [exact_release_checker,exact_release_checker,
    retired_owner_preserves_exactly_other_current_releases departed original]

end Yulang.GeneralDeclarativeWitnessExecutableRelease362
