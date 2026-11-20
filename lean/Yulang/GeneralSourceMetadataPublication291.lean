import Yulang.GeneralSourceMetadataLiveFixture291

/-! Replace the old totality calculation by exact source-use checking
inside the existing optional strict publication. The result is identical
on every fixed input, not a change to the kernel or the prior API. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralSourceMetadataPublication291
open GeneralDeclarations (Registry)
open GeneralNominalInspection (Interpretation)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralRebaseReceiptWire289 (Offer)
open GeneralObservedMetadataGate290 (gate)
open GeneralObservedMetadataHistorical290 (qualifies)
open GeneralObservedMetadataSeal290 (Seal dataSeal)
open GeneralObservedMetadataPublication290 (Output publishFrom)
open GeneralObservedMetadataStrict290 (qualifiedTotal strictSeals strictPublish)
open GeneralSourceMetadataLive291 (liveCheck live_compiler_eq)

def sourceQualified (r : Registry) (s : State roles) (up down : Occurrence roles)
    (ask : Offer) (proposed : Interpretation) (e : Effect roles) : Bool :=
  qualifies r s up down ask proposed e && liveCheck s.core up e.plan r.constructors proposed

theorem same_qualification (r : Registry) (s : State roles) (up down : Occurrence roles)
    (ask : Offer) (proposed : Interpretation) (e : Effect roles) :
    sourceQualified r s up down ask proposed e = qualifiedTotal r s up down ask proposed e := by
  unfold sourceQualified qualifiedTotal
  rw [live_compiler_eq]

def sourceSeals (r : Registry) (s : State roles) (up down : Occurrence roles)
    (ask : Offer) (proposed : Interpretation) : List Seal :=
  if gate r s up down ask proposed = .receipt .ready then
    (s.effects.filter (sourceQualified r s up down ask proposed)).map (dataSeal r s up down ask proposed)
  else []

theorem same_seals (r : Registry) (s : State roles) (up down : Occurrence roles)
    (ask : Offer) (proposed : Interpretation) :
    sourceSeals r s up down ask proposed = strictSeals r s up down ask proposed := by
  unfold sourceSeals strictSeals
  have same : sourceQualified r s up down ask proposed = qualifiedTotal r s up down ask proposed :=
    funext (same_qualification r s up down ask proposed)
  rw [same]

def publish (r : Registry) (s : State roles) (up down : Occurrence roles)
    (ask : Offer) (proposed : Interpretation) (saved : Seal) : Output :=
  publishFrom (sourceSeals r s up down ask proposed) up ask saved

theorem same_result (r : Registry) (s : State roles) (up down : Occurrence roles)
    (ask : Offer) (proposed : Interpretation) (saved : Seal) :
    publish r s up down ask proposed saved = strictPublish r s up down ask proposed saved := by
  unfold publish strictPublish
  rw [same_seals]

end Yulang.GeneralSourceMetadataPublication291
