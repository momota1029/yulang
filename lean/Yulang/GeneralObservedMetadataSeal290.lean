import Yulang.GeneralObservedMetadataRequestBook290

/-! Recomputed finite readback for an actual matching producer. A saved
capsule is data, not permission to skip any current receipt check. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29200
set_option maxHeartbeats 18000000
namespace Yulang.GeneralObservedMetadataSeal290
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalInspection (Interpretation)
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralRebaseReceiptWire289 (Offer)
open GeneralRebaseReceiptTypedStamp289 (Stamp capture)
open GeneralObservedMetadataBook290 (Book book)
open GeneralObservedMetadataGate290 (context footprint gate)
open GeneralObservedMetadataLive290 (liveKeys)
open GeneralObservedMetadataRequestBook290 (RequestBook requestBook)
open GeneralObservedMetadataHistorical290 (qualifies)

structure Seal where
  stamp : Stamp
  current : Book
  history : Book
  requests : RequestBook
  deriving DecidableEq

def dataSeal (r : Registry) (s : State roles) (up down : Occurrence roles)
    (ask : Offer) (proposed : Interpretation) (e : Effect roles) : Seal :=
  ⟨capture (context s).state up down ask,
   book (footprint r s down) r.constructors proposed,
   book (liveKeys s.core up e.plan) r.constructors proposed,requestBook s.core up e.plan⟩

def seals (r : Registry) (s : State roles) (up down : Occurrence roles)
    (ask : Offer) (proposed : Interpretation) : List Seal :=
  if gate r s up down ask proposed = .receipt .ready then
    (s.effects.filter (qualifies r s up down ask proposed)).map (dataSeal r s up down ask proposed)
  else []

theorem membership (r : Registry) (s : State roles) (up down : Occurrence roles)
    (ask : Offer) (proposed : Interpretation) (token : Seal) :
    token ∈ seals r s up down ask proposed ↔
      gate r s up down ask proposed = .receipt .ready ∧
      ∃ e ∈ s.effects, qualifies r s up down ask proposed e = true ∧
        dataSeal r s up down ask proposed e = token := by
  unfold seals
  by_cases good : gate r s up down ask proposed = .receipt .ready
  · rw [ite_eq_left good]
    simp only [List.mem_map,List.mem_filter]
    constructor
    · rintro ⟨e,⟨inList,found⟩,value⟩
      exact ⟨good,e,inList,found,value⟩
    · rintro ⟨_,e,inList,found,value⟩
      exact ⟨e,⟨inList,found⟩,value⟩
  · simp [good]

theorem membership_implies_historical {r : Registry} {s : State roles} {up down : Occurrence roles}
    {ask : Offer} {proposed : Interpretation} {token : Seal}
    (consistent : token ∈ seals r s up down ask proposed) :
    GeneralObservedMetadataHistorical290.resolve r s up down ask proposed = .prior (.receipt .ready) := by
  obtain ⟨prior,e,present,qualifier,_⟩ := (membership ..).mp consistent
  apply (GeneralObservedMetadataHistorical290.ready_exact ..).mpr
  exact ⟨prior,(GeneralObservedMetadataHistorical290.owner_exact ..).mp
    (List.any_eq_true.mpr ⟨e,present,qualifier⟩)⟩

theorem kept_has_reference_books {r : Registry} {s : State roles} {up down : Occurrence roles}
    {ask : Offer} {proposed : Interpretation} {token : Seal}
    (consistent : token ∈ seals r s up down ask proposed) :
    token.current = book (footprint r s down) (context s).state.constructors (context s).interpretation ∧
    ∃ e ∈ s.effects, e.plan.packet.site.occurrence = up ∧
      token.history = book (liveKeys s.core up e.plan) e.plan.packet.registry.constructors
        e.plan.packet.context.interpretation ∧ token.requests = requestBook s.core up e.plan := by
  obtain ⟨prior,e,present,qual,eq⟩ := (membership ..).mp consistent
  have checkOk := ((GeneralObservedMetadataGate290.receipt_exact ..).mp prior).1
  have tri := ((GeneralObservedMetadataScope290.good_exact ..).mp checkOk).1
  simp only [qualifies,Bool.and_eq_true,decide_eq_true_eq] at qual
  have target := (GeneralRebaseReceiptExactLink289.exactProducer_iff ..).mp qual.1
  have history := ((GeneralObservedMetadataScope290.good_exact ..).mp qual.2).1
  refine ⟨?_,e,present,target.1,?_,?_⟩
  · rw [← eq]
    exact ((GeneralObservedMetadataBook290.book_exact ..).mpr tri).symm
  · rw [← eq]
    exact ((GeneralObservedMetadataBook290.book_exact ..).mpr history).symm
  · rw [← eq]
    rfl

end Yulang.GeneralObservedMetadataSeal290
