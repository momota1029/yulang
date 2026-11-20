import Yulang.GeneralObservedMetadataOverlayFixture290

/-! A certified mark is an auxiliary readback, not a new Prepared frame
for the proposal. Only the original actual registry is used for the
following canonical dictionary theorem. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralObservedMetadataCanonical290
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentFrame287 (after)
open GeneralRebaseRowParentPacket287 (child)
open GeneralRebaseReceiptWitness289 (ActualPath)
open GeneralRebaseReceiptFixture289 (request)
open GeneralRebaseReceiptCompile289 (Mark actualMark concrete_compile)
open GeneralObservedMetadataSeal290 (Seal)
open GeneralObservedMetadataStrict290 (strictPublish)
open GeneralObservedMetadataReleaseFixture290 (normalized)
open GeneralObservedMetadataControls290 (primitiveOutside)
open GeneralRebaseRowParentOutput287 (replaceOutput)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedEvidence231 (Frame Evidence)
open GeneralRebaseInertLeaf288 (SourceSlice)
open GeneralRebaseReceiptCollision289 (removed no_current_frame)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)

theorem canonical_dictionary (choice : Bool) {s : State roles} (path : ActualPath choice s)
    (saved : Seal) (value : Mark)
    (pub : strictPublish (registry choice) s root (child choice) (request choice) interp saved = .released value)
    (m : Assignment) (p : Payload) :
    Models s (replaceOutput m) ∧ Evidence (registry choice) s.core (replaceOutput m) root p ↔
      SourceSlice s m ∧ p = .node 0 [.node 1 []] := by
  obtain ⟨rfl,rfl,rfl,rfl⟩ := (GeneralObservedMetadataStrictActual290.strict_release_exact choice path saved value).mp pub
  have supported := (GeneralRebaseReceiptScopedTrace289.family_iff true
    ⟨after true,.published (request true)⟩).mpr (.published rfl)
  exact GeneralRebaseReceiptPublic289.canonical_dictionary true supported actualMark (concrete_compile true) m p

theorem canonical_only_changes_target (m : Assignment) :
    (∀ row, (replaceOutput m row).2 = (m row).2) ∧
    (∀ t, t ≠ actualMark.target → (replaceOutput m t).1 = (m t).1) :=
  GeneralRebaseReceiptPublic289.preserves_all_rows m

theorem strict_finite_release_not_new_frame :
    strictPublish (removed 8) (after true) root (child true) (request true) primitiveOutside normalized =
      .released actualMark ∧ ∀ key p, ¬ Frame (removed 8) (after true).core (child true) key p :=
  ⟨GeneralObservedMetadataRegistryFixture290.whole_gate_unchanged_offscope.1,no_current_frame 8⟩

end Yulang.GeneralObservedMetadataCanonical290
