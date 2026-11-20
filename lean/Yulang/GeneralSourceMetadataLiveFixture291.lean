import Yulang.GeneralSourceMetadataLiveDiagnostics291

/-! The false source branch is not globally materializable, but its existing
parent has an exactly ready output. This is a real, fixed raw state. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28500
namespace Yulang.GeneralSourceMetadataLiveFixture291
open GeneralRebaseRowChildSource287 (root before registry constructors interp)
open GeneralRebaseRowParentFrame287 (after effect)
open GeneralRebaseRowParentPacket287 (plan)
open GeneralSourceMetadataBundleFixture291 (actual executable_both)
open GeneralSourceMetadataBundle291 (inspect)
open GeneralSourceMetadataLive291 (liveCheck original_live_ready_exact)
open GeneralSourceMetadataLiveDiagnostics291 (faults diagnose)
open GeneralObservedMetadataTotalFixture290 (unsupported)

theorem local_parent_ready_both (choice : Bool) :
    liveCheck (after choice).core root (effect choice).plan (registry choice).constructors interp = true := by
  rw [GeneralSourceMetadataLive291.live_compiler_eq]
  exact GeneralObservedMetadataTotalFixture290.live_total_real choice

theorem strict_local_not_global :
    liveCheck (after false).core root (effect false).plan constructors interp = true ∧
    (inspect (actual false)).ready = false :=
  ⟨local_parent_ready_both false,executable_both false⟩

theorem unsupported_live_body_diagnostic :
    faults before.core root unsupported constructors interp =
      [⟨⟨0,2⟩,.unsupported [⟨⟨.associated 0 0,(1,1)⟩,.missingClassification⟩]⟩] := by
  decide +kernel

theorem missing_lookup_not_empty :
    diagnose constructors interp 0 (⟨0,2⟩,none) = some ⟨⟨0,2⟩,.missingBody⟩ := rfl

end Yulang.GeneralSourceMetadataLiveFixture291
