import Yulang.GeneralObservedMetadataPublication290

/-! A finite runnable replay, exactly attached to the actual installed
whole-type branch. The row-destructuring branch is not given a release seal. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 20000000
namespace Yulang.GeneralObservedMetadataReleaseFixture290
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentFrame287 (after effect)
open GeneralRebaseRowParentPacket287 (child)
open GeneralRebaseReceiptFixture289 (request)
open GeneralRebaseReceiptStampFixtures289 (normalizedStamp same_extracted_stamp)
open GeneralRebaseReceiptCompile289 (Mark actualMark concrete_compile)
open GeneralObservedMetadataBook290 (book)
open GeneralObservedMetadataRequestBook290 (RequestBook requestBook)
open GeneralObservedMetadataGate290 (context footprint)
open GeneralObservedMetadataActual290 (exact_initial_diagnostic exact_install_diagnostics)
open GeneralObservedMetadataHistorical290 (qualifies owner_exact)
open GeneralObservedMetadataHistoryFixture290 (actual_owner recorded_body_keys)
open GeneralObservedMetadataSeal290 (Seal dataSeal seals)
open GeneralObservedMetadataPublication290 (issue publishFrom publish Output)

def normalizedRequests : RequestBook := [(⟨0,2⟩,some (.explicit ⟨0,0,.app 0 [.app 0 [.var 0]]⟩))]

def normalized : Seal :=
  ⟨normalizedStamp true,book [6,0] constructors interp,book [0,0] constructors interp,normalizedRequests⟩

theorem actual_class_book : requestBook (after true).core root (effect true).plan = normalizedRequests := by
  decide +kernel

theorem current_keys :
    footprint (registry true) (after true) (child true) = [6,0] := by decide +kernel

theorem normalized_exact :
    dataSeal (registry true) (after true) root (child true) (request true) interp (effect true) = normalized := by
  unfold dataSeal normalized
  rw [current_keys,recorded_body_keys,actual_class_book]
  change (⟨GeneralRebaseReceiptStampedProduct289.currentStamp true (after true),_,_,_⟩ : Seal) = _
  rw [same_extracted_stamp]

theorem certified_actual_effect :
    qualifies (registry true) (after true) root (child true) (request true) interp (effect true) = true := by
  have works := (owner_exact ..).mpr (actual_owner true)
  change [effect true].any (qualifies (registry true) (after true) root (child true) (request true) interp) = true at works
  simpa using works

theorem accepted_seals :
    seals (registry true) (after true) root (child true) (request true) interp = [normalized] := by
  unfold seals
  have gateReady : GeneralObservedMetadataGate290.gate (registry true) (after true) root
      (child true) (request true) interp = .receipt .ready := exact_install_diagnostics true
  rw [ite_eq_left gateReady]
  change ([effect true].filter (qualifies (registry true) (after true) root (child true) (request true) interp)).map _ = _
  simp [List.filter,certified_actual_effect,normalized_exact]

theorem before_seals (choice : Bool) :
    seals (registry choice) before root (child choice) (request choice) interp = [] := by
  unfold seals
  rw [exact_initial_diagnostic choice]
  rfl

theorem pending_seals :
    seals (registry false) (after false) root (child false) (request false) interp = [] := by
  unfold seals
  rw [exact_install_diagnostics false]
  rfl

theorem ready_issues :
    issue (registry true) (after true) root (child true) (request true) interp = some normalized := by
  unfold issue
  rw [accepted_seals]
  rfl

def wrongHead : Seal :=
  { normalized with current := book [6,0] constructors (GeneralObservedMetadataControls290.removeInvariant interp 6) }

def wrongHistory : Seal :=
  { normalized with history := book [0,0] constructors (GeneralObservedMetadataControls290.removeInvariant interp 0) }

theorem same_typed_stamp :
    wrongHead.stamp = normalized.stamp ∧ wrongHistory.stamp = normalized.stamp := ⟨rfl,rfl⟩

theorem changed_entries :
    wrongHead ≠ normalized ∧ wrongHistory ≠ normalized := by decide +kernel

def lostRequest : Seal := { normalized with requests := [] }

theorem missing_request_same_metadata :
    lostRequest.stamp = normalized.stamp ∧ lostRequest.current = normalized.current ∧
      lostRequest.history = normalized.history ∧ lostRequest ≠ normalized :=
  ⟨rfl,rfl,rfl,by decide +kernel⟩

theorem executable_release_expected :
    (publishFrom [normalized] root (request true) normalized,
     publishFrom [normalized] root (request true) wrongHead,
     publishFrom [normalized] root (request true) wrongHistory,
     publishFrom [normalized] root (request true) lostRequest) =
      (.released actualMark,.staleOrUnsupported,.staleOrUnsupported,.staleOrUnsupported) := by decide +kernel

theorem actual_replay (token : Seal) :
    publish (registry true) (after true) root (child true) (request true) interp token =
      publishFrom [normalized] root (request true) token := by
  unfold publish
  rw [accepted_seals]

end Yulang.GeneralObservedMetadataReleaseFixture290
