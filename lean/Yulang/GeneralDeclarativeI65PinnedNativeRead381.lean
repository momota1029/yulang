import Yulang.GeneralDeclarativeI65NativeAuthority381

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarativeWitnessNativeInstall360 (World atTarget)
open GeneralDeclarativeWitnessNativeValue360 (Write)
open GeneralDeclarativeWitnessNativeRelease360 (ReleaseAuthority ExactRelease checkExactRelease)

/-- The prior origin view can be used as a source event only when its
physical world AND independent authority are the actual pinned inputs.
This subtype doesn't introduce an authority or choose the world. -/
def BoundNativeRead381 (s : State) (world : World) (gate : ReleaseAuthority)
    (written : Write) : Type :=
  { read : CurrentReleasedOrigin s (originalOfWrite written) //
    read.physicalWorld = world ∧ read.grantedAt = gate }

/-- The immutable source context identifies the exact installed write;
the previous origin abstraction alone identifies only endpoint/slot/issuer. -/
theorem bound_read_fixes_literal_write381
    {s : State} {world : World} {gate : ReleaseAuthority} {written : Write} {logical : Nat}
    (rail : RetainedPhysicalOrigin381 s world written logical)
    (pinned : BoundNativeRead381 s world gate written) :
    pinned.val.exactWrite = written := by
  have current := current_release_actual_at_origin pinned.val
  rw [pinned.property.1] at current
  change atTarget world.board written.address.target = some pinned.val.exactWrite at current
  exact Option.some.inj (current.symm.trans rail.atTarget)

/-- Equality of source context can discharge the two pin checks. No
semantic value can discharge them, and no model occurs in this cut. -/
theorem pinned_origin_exact_release381
    {s : State} {world : World} {gate : ReleaseAuthority} {written : Write} {logical : Nat}
    (rail : RetainedPhysicalOrigin381 s world written logical)
    (pinned : BoundNativeRead381 s world gate written) :
    Nonempty (ExactRelease world.board gate written) := by
  have release := pinned.val.opened
  rw [pinned.property.1,pinned.property.2,bound_read_fixes_literal_write381 rail pinned] at release
  exact ⟨release⟩

/-- The existing native release executable reflects the gate on a
given physical rail, but is not a classification or proof of election. -/
theorem native_context_read_iff_its_grant381
    {s : State} {world : World} {gate : ReleaseAuthority} {written : Write} {logical : Nat}
    (rail : RetainedPhysicalOrigin381 s world written logical) :
    Nonempty (BoundNativeRead381 s world gate written) ↔ written.address ∈ gate.grants := by
  constructor
  · rintro ⟨pinned⟩
    obtain ⟨release⟩ := pinned_origin_exact_release381 rail pinned
    exact release.released.granted
  · intro permit
    have opens := (exact_native_authority_iff381 rail gate).mpr permit
    cases seen : checkExactRelease world.board gate written with
    | none => simp [seen] at opens
    | some read =>
      exact ⟨⟨⟨world,rail.current,gate,written,read,rfl,rfl,rfl⟩,rfl,rfl⟩⟩

/-- A prior authorized-origin existential really can lose the gate:
the allowed authority supplies an endpoint of the same exact write,
but it does not make that endpoint readable under the denied authority.
Both regimes are explicit inputs; this is not a candidate verdict. -/
theorem unpinned_endpoint_does_not_authorize_actual_context381
    {s : State} {world : World} {written : Write} {logical : Nat}
    (rail : RetainedPhysicalOrigin381 s world written logical)
    (allowed denied : ReleaseAuthority)
    (yes : written.address ∈ allowed.grants) (no : written.address ∉ denied.grants) :
    Nonempty (AuthorizedEndpoint s (fun o => Nonempty (CurrentReleasedOrigin s o)) logical) ∧
      ¬Nonempty (BoundNativeRead381 s world denied written) := by
  obtain ⟨pinned⟩ := (native_context_read_iff_its_grant381 (gate := allowed) rail).mpr yes
  exact ⟨⟨endpointFromCurrentRelease pinned.val rail.retained rail.route⟩,
    fun imported => no ((native_context_read_iff_its_grant381 rail).mp imported)⟩

end Yulang.GeneralDeclarativeI65
