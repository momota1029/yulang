import Yulang.GeneralObservedMetadataTotalFixture290

/-! Optional stricter auxiliary release: the exact same historical owner
must have a total compiler over current live outputs. This is not a
language rejection rule or a replacement for the original MixedKernel. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralObservedMetadataStrict290
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalInspection (Interpretation)
open GeneralRebaseReceiptWire289 (Offer)
open GeneralObservedMetadataGate290 (gate)
open GeneralObservedMetadataHistorical290 (qualifies)
open GeneralObservedMetadataSeal290 (Seal dataSeal seals membership)
open GeneralObservedMetadataPublication290 (Output publishFrom publish publishFrom_exact)
open GeneralObservedMetadataTotal290 (total certified_total_iff_ready)
open GeneralRebaseReceiptCompile289 (Mark)
open GeneralNominalCenteredHeadMatEffects (Ready)
open GeneralObservedMetadataLive290 (ProposedModels accepted_live_models)

def qualifiedTotal (r : Registry) (s : State roles) (up down : Occurrence roles)
    (ask : Offer) (proposed : Interpretation) (e : Effect roles) : Bool :=
  qualifies r s up down ask proposed e && total s.core up e.plan r.constructors proposed

def strictSeals (r : Registry) (s : State roles) (up down : Occurrence roles)
    (ask : Offer) (proposed : Interpretation) : List Seal :=
  if gate r s up down ask proposed = .receipt .ready then
    (s.effects.filter (qualifiedTotal r s up down ask proposed)).map (dataSeal r s up down ask proposed)
  else []

theorem strict_membership (r : Registry) (s : State roles) (up down : Occurrence roles)
    (ask : Offer) (proposed : Interpretation) (saved : Seal) :
    saved ∈ strictSeals r s up down ask proposed ↔ gate r s up down ask proposed = .receipt .ready ∧
    ∃ e ∈ s.effects, qualifies r s up down ask proposed e = true ∧
      total s.core up e.plan r.constructors proposed = true ∧
      dataSeal r s up down ask proposed e = saved := by
  unfold strictSeals
  by_cases allowed : gate r s up down ask proposed = .receipt .ready
  · rw [ite_eq_left allowed]
    simp only [List.mem_map,List.mem_filter,qualifiedTotal,Bool.and_eq_true]
    constructor
    · rintro ⟨e,⟨present,separate,good⟩,value⟩
      exact ⟨allowed,e,present,separate,good,value⟩
    · rintro ⟨_,e,present,separate,good,value⟩
      exact ⟨e,⟨present,separate,good⟩,value⟩
  · simp [allowed]

theorem permitted_subset (r : Registry) (s : State roles) (up down : Occurrence roles)
    (ask : Offer) (proposed : Interpretation) :
    strictSeals r s up down ask proposed ⊆ seals r s up down ask proposed := by
  intro saved consistent
  obtain ⟨ready,e,present,owner,_,found⟩ := (strict_membership ..).mp consistent
  exact (membership ..).mpr ⟨ready,e,present,owner,found⟩

def strictPublish (r : Registry) (s : State roles) (up down : Occurrence roles)
    (ask : Offer) (proposed : Interpretation) (saved : Seal) : Output :=
  publishFrom (strictSeals r s up down ask proposed) up ask saved

theorem actual_owner_total {r : Registry} {s : State roles} {up down : Occurrence roles}
    {ask : Offer} {proposed : Interpretation} {saved : Seal} {value : Mark}
    (out : strictPublish r s up down ask proposed saved = .released value) :
    publish r s up down ask proposed saved = .released value ∧
      ∃ e ∈ s.effects, e.plan.packet.site.occurrence = up ∧
        down ∈ GeneralNominalVersionedFrame231.children e.plan.packet ∧ Ready s.core up e.plan ∧
        (∀ m, ProposedModels s.core up e.plan r.constructors proposed m ↔ e.Live s.core m) := by
  obtain ⟨supported,code⟩ := (publishFrom_exact _ _ _ _ _).mp out
  have old := (publishFrom_exact _ _ _ _ _).mpr
    ⟨permitted_subset r s up down ask proposed supported,code⟩
  obtain ⟨_,e,present,qual,operational,_⟩ := (strict_membership ..).mp supported
  simp only [qualifies,Bool.and_eq_true,decide_eq_true_eq] at qual
  have matched := (GeneralRebaseReceiptExactLink289.exactProducer_iff ..).mp qual.1
  refine ⟨old,e,present,matched.1,matched.2.1, ?_,?_⟩
  · exact (certified_total_iff_ready _ _ _ _ _ qual.2).mp operational
  · intro m
    unfold Effect.Live
    rw [matched.1]
    exact (accepted_live_models qual.2 m).trans (GeneralNominalVersionedEffects231.class_effects_iff _ _ _ _).symm

end Yulang.GeneralObservedMetadataStrict290
