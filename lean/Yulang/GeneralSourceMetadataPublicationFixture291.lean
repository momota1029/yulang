import Yulang.GeneralSourceMetadataSnapshotFixture291

/-! Only with the exact original source attachment do we reuse the actual
two-branch readback. Re-expressing metadata never constructs another raw path. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralSourceMetadataPublicationFixture291
open GeneralRebaseRowChildSource287 (roles root registry interp)
open GeneralRebaseRowParentPacket287 (child)
open GeneralRebaseRowParentFrame287 (after)
open GeneralRebaseReceiptFixture289 (request)
open GeneralRebaseReceiptWitness289 (ActualPath)
open GeneralRebaseReceiptCompile289 (Mark actualMark)
open GeneralObservedMetadataSeal290 (Seal)
open GeneralObservedMetadataReleaseFixture290 (normalized)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralRebaseInertLeaf288 (SourceSlice)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralSourceMetadataFixture291 (source source_interpretation)
open GeneralSourceMetadataPublication291 (publish same_result)

theorem checked_source_release (choice : Bool) {s : State roles} (path : ActualPath choice s)
    (token : Seal) (value : Mark) :
    publish (registry choice) s root (child choice) (request choice) (interpretation source) token = .released value ↔
      choice = true ∧ s = after true ∧ token = normalized ∧ value = actualMark := by
  rw [same_result,source_interpretation]
  exact GeneralObservedMetadataStrictActual290.strict_release_exact choice path token value

theorem exact_source_model (choice : Bool) {s : State roles} (path : ActualPath choice s)
    (token : Seal) (value : Mark)
    (out : publish (registry choice) s root (child choice) (request choice) (interpretation source) token = .released value) :
    (∀ m, Models s m ↔ SourceSlice s m ∧ value.Holds m) ∧
      ¬ GeneralNominalState.Known s.core.erased.current.context.state value.target := by
  rw [same_result,source_interpretation] at out
  exact (GeneralObservedMetadataPublic290.strict_fixture_mark_sound choice path token value out).2

end Yulang.GeneralSourceMetadataPublicationFixture291
