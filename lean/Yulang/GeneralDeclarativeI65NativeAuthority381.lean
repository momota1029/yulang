import Yulang.GeneralDeclarativeI65NativePrefix369

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarativeWitnessNativeInstall360 (World atTarget)
open GeneralDeclarativeWitnessNativeValue360 (Write)
open GeneralDeclarativeWitnessNativeRelease360 (ReleaseAuthority ExactRelease checkExactRelease)
open GeneralDeclarativeWitnessTypedRelease354 (position)

/-- The same current ordinary state, exact retained physical occurrence and
active owner can be fixed *before* any grant is considered.
This record does not create a release or select a candidate. -/
structure RetainedPhysicalOrigin381 (s : State) (world : World) (written : Write)
    (logical : Nat) : Prop where
  current : world.ordinary = s.current.ordinary
  atTarget : atTarget world.board written.address.target = some written
  active : written.address.owner ∈ world.board.active
  unique : (world.board.active.map position).Nodup
  retained : originalOfWrite written ∈ s.origins
  route : OriginRoute s (originalOfWrite written) logical

theorem retained_physical_origin_of_install381
    {s : State} {logical : Nat} {env frame d layout table wire version}
    {p : GeneralDeclarativeWitnessNativePreparation360.Prepared env frame d layout}
    (emission : GeneralDeclarativeWitnessNativeValue360.Compiled p table wire version)
    {base : GeneralDeclarativeWitnessNativeInstall360.Board} {out : World}
    (ran : GeneralDeclarativeWitnessNativeInstall360.install p emission base = some out)
    (current : out.ordinary = s.current.ordinary)
    (retained : originalOfWrite emission.write ∈ s.origins)
    (route : OriginRoute s (originalOfWrite emission.write) logical) :
    RetainedPhysicalOrigin381 s out emission.write logical := by
  obtain ⟨stored, active, unique⟩ := installed_literal_address emission ran
  exact ⟨current,stored,active,unique,retained,route⟩

/-- In the installed rail slice, the remaining discriminator for the
existing exact release is the independently indexed full grant. -/
theorem exact_native_authority_iff381
    {s : State} {world : World} {written : Write} {logical : Nat}
    (rail : RetainedPhysicalOrigin381 s world written logical) (gate : ReleaseAuthority) :
    (checkExactRelease world.board gate written).isSome = true ↔
      written.address ∈ gate.grants :=
  exact_open_iff_independent_grant rail.atTarget rail.active rail.unique

/-- A caller must name both the concrete world and its external authority.
This cut turns the actual already validated release into the existing
source observation without accepting any candidate. -/
def authorized_from_actual_native_release381
    {s : State} {world : World} {written : Write} {logical : Nat}
    (rail : RetainedPhysicalOrigin381 s world written logical) {gate : ReleaseAuthority}
    (read : ExactRelease world.board gate written) :
    AuthorizedEndpoint s (fun o => Nonempty (CurrentReleasedOrigin s o)) logical :=
  endpointFromCurrentRelease
    ⟨world,rail.current,gate,written,read,rfl,rfl,rfl⟩ rail.retained rail.route

/-- Same state, world, literal write and routed origin, distinct
independently supplied authority lists. Even retaining the exact native
board and its model interpretation cannot replace the authority input.
This is a no-erasure theorem, not a rejected language case. -/
theorem no_erasure_of_native_authority381
    {s : State} {world : World} {written : Write} {logical : Nat}
    (rail : RetainedPhysicalOrigin381 s world written logical)
    (denied allowed : ReleaseAuthority)
    (absent : written.address ∉ denied.grants) (present : written.address ∈ allowed.grants)
    (projected : State → World → Write → Prop) :
    ¬((projected s world written ↔ (checkExactRelease world.board denied written).isSome = true) ∧
      (projected s world written ↔ (checkExactRelease world.board allowed written).isSome = true)) := by
  rintro ⟨noneGate,yesGate⟩
  exact absent ((exact_native_authority_iff381 rail denied).mp
    (noneGate.mp (yesGate.mpr ((exact_native_authority_iff381 rail allowed).mpr present))))

end Yulang.GeneralDeclarativeI65
