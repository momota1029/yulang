import Yulang.GeneralObservedMetadataRegistryCongr290

/-! An actual raw endpoint demonstrates the exact scope of the finite
predicate: simultaneous unseen catalogue and primitive edits can leave
the auxiliary result unchanged, and still fail full Metadata. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 20000000
namespace Yulang.GeneralObservedMetadataRegistryFixture290
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentFrame287 (after effect)
open GeneralRebaseRowParentPacket287 (child)
open GeneralRebaseReceiptFixture289 (request)
open GeneralRebaseReceiptCompile289 (actualMark)
open GeneralRebaseReceiptCollision289 (removed)
open GeneralObservedMetadataControls290 (primitiveOutside)
open GeneralObservedMetadataReleaseFixture290 (normalized)
open GeneralObservedMetadataStrict290 (strictPublish)
open GeneralObservedMetadataRegistryCongr290 (compare equal_publish)
open GeneralObservedMetadataNoninterference290 (allKeys)
open GeneralNominalCandidates (Metadata)

theorem actual_whole_key_list :
    allKeys (registry true) (after true) root (child true) = [6,0,0,0] := by
  decide +kernel

theorem offscope_double_edit_passes :
    compare (registry true) (removed 8) (after true) root (child true) interp primitiveOutside = true := by
  decide +kernel

theorem observed_edit_caught :
    compare (registry true) (removed 6) (after true) root (child true) interp interp = false := by
  decide +kernel

theorem original_strict_readback :
    strictPublish (registry true) (after true) root (child true) (request true) interp normalized =
      .released actualMark :=
  (GeneralObservedMetadataStrictActual290.strict_release_exact true
    (GeneralRebaseReceiptWitness289.after_reachable true) normalized actualMark).mpr ⟨rfl,rfl,rfl,rfl⟩

theorem whole_gate_unchanged_offscope :
    strictPublish (removed 8) (after true) root (child true) (request true) primitiveOutside normalized =
      .released actualMark ∧
    ¬ Metadata (removed 8) ⟨(GeneralObservedMetadataGate290.context (after true)).state,primitiveOutside⟩ := by
  refine ⟨(equal_publish offscope_double_edit_passes (request true) normalized).symm.trans original_strict_readback,?_⟩
  intro invalid
  have atEight := congrFun invalid.1 8
  change (none : Option GeneralDeclarationPatterns.Constructor) = some ⟨[],8⟩ at atEight
  cases atEight

end Yulang.GeneralObservedMetadataRegistryFixture290
