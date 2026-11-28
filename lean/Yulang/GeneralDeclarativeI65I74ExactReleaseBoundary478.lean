import Yulang.GeneralDeclarativeWitnessNativeRelease360

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessNativeRelease360
open GeneralDeclarativeWitnessNativeValue360 (Address Write)
open GeneralDeclarativeWitnessNativeInstall360 (Board World atTarget)

def dropOnlyOneNativeGrant478 (authority : ReleaseAuthority) (target : Address) : ReleaseAuthority :=
  ⟨authority.grants.filter (fun a => decide (a ≠ target))⟩

theorem dropping_one_native_grant_preserves_every_other_grant478
    (authority : ReleaseAuthority) (addr other : Address) (different : other ≠ addr) :
    other ∈ (dropOnlyOneNativeGrant478 authority addr).grants ↔ other ∈ authority.grants := by
  simp [dropOnlyOneNativeGrant478,different]

theorem old_installed_write_is_not_an_exact_release_without_the_grant478
    (world : World) (gate : ReleaseAuthority) (w : Write) :
    checkExactRelease world.board (dropOnlyOneNativeGrant478 gate w.address) w = none := by
  have denied : w.address ∉ (dropOnlyOneNativeGrant478 gate w.address).grants := by
    simp [dropOnlyOneNativeGrant478]
  have closed := not_granted_not_released (board := world.board) denied
  simp [checkExactRelease,closed,bind,Option.bind]

theorem positive_native_release_pins_exact_installed_write_owner_and_grant478
    {world : World} {authority : ReleaseAuthority} {w : Write}
    (actual : ExactRelease world.board authority w) :
    atTarget world.board w.address.target = some w ∧
    w.address.owner ∈ world.board.active ∧ w.address ∈ authority.grants := by
  have installed := actual.released.located
  rw [actual.same] at installed
  exact ⟨installed,actual.released.active,actual.released.granted⟩

theorem even_same_world_and_exact_write_do_not_recover_native_release478
    {world : World} {authority : ReleaseAuthority} {w : Write}
    {released : ExactRelease world.board authority w}
    (run : checkExactRelease world.board authority w = some released)
    (decode : World → Write → Bool)
    (claims : ∀ gate : ReleaseAuthority, decode world w = (checkExactRelease world.board gate w).isSome) :
    False := by
  have yes := claims authority
  have no := claims (dropOnlyOneNativeGrant478 authority w.address)
  rw [run] at yes
  rw [old_installed_write_is_not_an_exact_release_without_the_grant478] at no
  have impossible : true = false := yes.symm.trans no
  cases impossible



theorem installed_later_write_never_authorizes_another_write_at_the_same_target478
    (world : World) (gate : ReleaseAuthority) (current other : Write)
    (installed : atTarget world.board current.address.target = some current)
    (sameTarget : other.address.target = current.address.target)
    (different : other ≠ current) :
    checkExactRelease world.board gate other = none := by
  cases got : checkExactRelease world.board gate other with
  | none => rfl
  | some attested =>
    have whereAt := (positive_native_release_pins_exact_installed_write_owner_and_grant478 attested).1
    rw [sameTarget] at whereAt
    have forced := Option.some.inj (whereAt.symm.trans installed)
    exact (different forced).elim

end Yulang.GeneralDeclarativeWitnessNativeRelease360

