import Yulang.GeneralObservedMetadataStrict290

/-! On the actual paths, requiring total live compilation changes no
receipt outcome. The extra condition is not inferred from metadata alone. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 20000000
namespace Yulang.GeneralObservedMetadataStrictActual290
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentFrame287 (after effect)
open GeneralRebaseRowParentPacket287 (child)
open GeneralRebaseReceiptFixture289 (request)
open GeneralRebaseReceiptWitness289 (ActualPath)
open GeneralRebaseReceiptCompile289 (Mark actualMark)
open GeneralObservedMetadataActual290 (exact_install_diagnostics exact_initial_diagnostic)
open GeneralObservedMetadataGate290 (gate)
open GeneralObservedMetadataHistorical290 (qualifies)
open GeneralObservedMetadataSeal290 (Seal seals)
open GeneralObservedMetadataStrict290 (strictSeals strictPublish qualifiedTotal)
open GeneralObservedMetadataPublication290 (publish)
open GeneralObservedMetadataReleaseFixture290 (normalized certified_actual_effect)
open GeneralObservedMetadataTotalFixture290 (live_total_real)
open GeneralNominalVersionedJournal232 (State)

theorem strict_seals_preserve_actual (choice : Bool) {s : State roles} (path : ActualPath choice s) :
    strictSeals (registry choice) s root (child choice) (request choice) interp =
      seals (registry choice) s root (child choice) (request choice) interp := by
  rcases GeneralRebaseRowActualPaths287.one_or_zero choice s path with rfl | rfl
  · unfold strictSeals seals
    simp [exact_initial_diagnostic choice]
  · cases choice
    · unfold strictSeals seals
      simp [exact_install_diagnostics false]
    · have found : gate (registry true) (after true) root (child true) (request true) interp =
        .receipt .ready := exact_install_diagnostics true
      unfold strictSeals seals
      rw [ite_eq_left found,ite_eq_left found]
      change ([effect true].filter (qualifiedTotal (registry true) (after true) root (child true) (request true) interp)).map _ =
        ([effect true].filter (qualifies (registry true) (after true) root (child true) (request true) interp)).map _
      simp [List.filter,qualifiedTotal,certified_actual_effect,live_total_real true]

theorem strict_publish_preserves_actual (choice : Bool) {s : State roles}
    (path : ActualPath choice s) (token : Seal) :
    strictPublish (registry choice) s root (child choice) (request choice) interp token =
      publish (registry choice) s root (child choice) (request choice) interp token := by
  unfold strictPublish publish
  rw [strict_seals_preserve_actual choice path]

theorem strict_release_exact (choice : Bool) {s : State roles} (path : ActualPath choice s)
    (token : Seal) (value : Mark) :
    strictPublish (registry choice) s root (child choice) (request choice) interp token = .released value ↔
      choice = true ∧ s = after true ∧ token = normalized ∧ value = actualMark := by
  rw [strict_publish_preserves_actual choice path]
  exact GeneralObservedMetadataReleased290.released_exact choice path token value

end Yulang.GeneralObservedMetadataStrictActual290
