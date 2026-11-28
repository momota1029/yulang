import Yulang.GeneralDeclarativeI65I74ExactReleaseBoundary478
open Yulang.GeneralDeclarativeWitnessNativeRelease360
#print axioms dropping_one_native_grant_preserves_every_other_grant478
#print axioms old_installed_write_is_not_an_exact_release_without_the_grant478
#print axioms positive_native_release_pins_exact_installed_write_owner_and_grant478
#print axioms even_same_world_and_exact_write_do_not_recover_native_release478
#print axioms installed_later_write_never_authorizes_another_write_at_the_same_target478

namespace Yulang.GeneralDeclarativeWitnessNativeRelease360.ObservedBoundary478
open GeneralDeclarativeWitnessNativeValue360 (Address Write)
open GeneralDeclarativeWitnessNativeInstall360 (Board World)
open GeneralDeclarativeWitnessTypedRelease354 (Stamp)

def ownerFresh : Stamp := ⟨[71,2],19,218,2⟩
def ownerPast : Stamp := ⟨[71,2],19,218,1⟩
def currentAddr : Address := ⟨ownerFresh,0,0,29,6,1⟩
def oldAddr : Address := ⟨ownerPast,0,0,29,6,1⟩
def currentWrite : Write := ⟨currentAddr,.leaf 7⟩
def oldWrite : Write := ⟨oldAddr,.leaf 7⟩
def substituteSameAddr : Write := ⟨currentAddr,.leaf 8⟩
def here : World := ⟨⟨⟨[],[]⟩,[]⟩,⟨[ownerFresh],[currentWrite]⟩⟩
def allGrants : ReleaseAuthority := ⟨[oldAddr,currentAddr]⟩
def reports : List Bool :=
  [(checkExactRelease here.board allGrants currentWrite).isSome,
   (checkExactRelease here.board allGrants oldWrite).isSome,
   (checkExactRelease here.board allGrants substituteSameAddr).isSome,
   (checkExactRelease here.board (dropOnlyOneNativeGrant478 allGrants currentAddr) currentWrite).isSome,
   (checkExactRelease ⟨[ownerFresh],[]⟩ allGrants currentWrite).isSome]

theorem old_checker_example_excludes_old_versions_payload_substitution_and_ungranted_source478 :
    reports = [true,false,false,false,false] := by decide +kernel

/-- info: [true, false, false, false, false] -/
#guard_msgs in
#eval reports

#print axioms old_checker_example_excludes_old_versions_payload_substitution_and_ungranted_source478
end Yulang.GeneralDeclarativeWitnessNativeRelease360.ObservedBoundary478
