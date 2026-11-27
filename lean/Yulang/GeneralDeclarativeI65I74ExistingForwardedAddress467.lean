import Yulang.GeneralDeclarativeWitnessNativePortTransport361
import Yulang.GeneralDeclarativeI65I74NativeProducerPhaseOrigin465

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ExistingForwardedAddress467
open Yulang.GeneralDeclarativeI65
open GeneralDeclarativeI65.I72.NativeProducer465
open GeneralDeclarativeWitnessNativePortTransport361 (Port Part view)
open GeneralDeclarativeWitnessSequentialNative360 (Sequence)
open GeneralDeclarativeWitnessSequentialReceiver361 (Received)
open GeneralDeclarativeWitnessNestedInstall360 (Run)
open GeneralDeclarativeWitnessNativeRelease360 (ReleaseAuthority ExactRelease checked_exact_written_value)
open GeneralDeclarativeWitnessNativeInstall360 (NativeViews atTarget interpreted)
open GeneralNominalCommonBridge (Assignment)

theorem receiving_compiler_body_keeps_the_exact_parent_address_and_output
    {negative} {r : Run negative} {seq : Sequence r} {gate : ReleaseAuthority} {w}
    (route : Port seq gate w) (rec : Received seq) :
    rec.world.board = seq.final.board ∧
    rec.world.ordinary = rec.body.state ∧
    rec.span.center = r.typed.write.address.target ∧
    atTarget rec.world.board rec.span.center = some r.typed.write ∧
    rec.body.fixed = [] := by
  have same := rec.center.trans seq.readsNative
  have stored := route.release.released.located
  rw [route.release.same] at stored
  exact ⟨rfl,rfl,same,by rw [same]; exact stored,rec.noWrites⟩

theorem actual_receiver_preserves_the_old_code_in_all_fitting_new_models
    {negative} {r : Run negative} {seq : Sequence r} {gate : ReleaseAuthority} {w}
    (route : Port seq gate w) (rec : Received seq) (m : Assignment) (v : NativeViews)
    (fit : GeneralDeclarativeWitnessNativeInstall360.Fits rec.world m v) :
    v rec.span.center = some (r.typed.write.code.eval m) ∧
      ∀ n, atTarget rec.world.board n = atTarget seq.final.board n := by
  have exactRelease : ExactRelease rec.world.board gate r.typed.write := route.release
  have all := checked_exact_written_value (w := rec.world) exactRelease m v fit
  rw [← rec.center.trans seq.readsNative] at all
  exact ⟨all,fun _ => rfl⟩

/-- Positive issuer transport of an already emitted associated output.
An exact focused I65 ledger index/route is separately necessary; this
does not author any native input coordinate or alias. -/
theorem checked_child_phase_can_read_only_the_retained_original_address
    {negative} {r : Run negative} {seq : Sequence r} {gate : ReleaseAuthority} {w}
    (route : Port seq gate w) (rec : Received seq)
    (s : GeneralDeclarativeI65.State)
    (samePhase : rec.world.ordinary = s.current.ordinary)
    (ordinal : Nat)
    (retained : s.origins[ordinal]? = some (originalOfWrite r.typed.write))
    (authored : OriginRoute s (originalOfWrite r.typed.write) rec.span.center) :
    checkPhaseOrigin ⟨rec.world,samePhase,gate⟩ r.typed.write rec.span.center ordinal = true :=
  (finite_phase_origin_check_iff_literal_placed_active_row ..).mpr ⟨retained,authored,⟨route.release⟩⟩

theorem existing_forwarded_address_same_state_semantics
    {negative} {r : Run negative} {seq : Sequence r} {gate : ReleaseAuthority} {w}
    (route : Port seq gate w) (rec : Received seq)
    (s : GeneralDeclarativeI65.State) (samePhase : rec.world.ordinary = s.current.ordinary)
    (ordinal : Nat)
    (retained : s.origins[ordinal]? = some (originalOfWrite r.typed.write))
    (authored : OriginRoute s (originalOfWrite r.typed.write) rec.span.center)
    (m : Model) (fits : GeneralDeclarativeI65.Fits s m) :
    m.nativeSyntax rec.span.center = some (GeneralDeclarativeWitnessNativeOrder362.node r.typed.write.code)
      ∧ interpreted rec.world.board m.assignment rec.span.center = some (r.typed.write.code.eval m.assignment) := by
  rw [rec.center.trans seq.readsNative]
  exact actual_phase_origin_ordinal_and_native_view_hold_in_every_same_fit
    (checked_child_phase_can_read_only_the_retained_original_address route rec s samePhase ordinal retained authored)
    m fits

end Yulang.GeneralDeclarativeI65.I72.ExistingForwardedAddress467
