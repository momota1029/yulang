import Yulang.GeneralObservedMetadataLive290

/-! A single recorded producer must pass both exact occurrence matching
and the finite live-body table check. Two different journal effects
cannot discharge the two conjuncts. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29100
set_option maxHeartbeats 18000000
namespace Yulang.GeneralObservedMetadataHistorical290
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalInspection (Interpretation)
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralRebaseReceiptWire289 (Offer)
open GeneralRebaseReceiptCatalogue289 (constructorKeys)
open GeneralRebaseReceiptExactLink289 (exactProducer exactProducer_iff)
open GeneralObservedMetadataGate290 (Outcome context gate)
open GeneralObservedMetadataScope290 (certify)
open GeneralObservedMetadataLive290 (liveKeys ProposedModels accepted_live_models)
open GeneralNominalCommonBridge (Assignment)

def bodyCheck (r : Registry) (s : State roles) (up : Occurrence roles)
    (proposed : Interpretation) (e : Effect roles) : GeneralObservedMetadataScope290.Result :=
  certify (liveKeys s.core up e.plan)
    e.plan.packet.registry.constructors e.plan.packet.context.interpretation r.constructors proposed

def qualifies (r : Registry) (s : State roles) (up down : Occurrence roles)
    (ask : Offer) (proposed : Interpretation) (e : Effect roles) : Bool :=
  exactProducer (constructorKeys (context s).state) r up down ask e &&
    decide (bodyCheck r s up proposed e = .good)

def HasOwner (r : Registry) (s : State roles) (up down : Occurrence roles)
    (ask : Offer) (proposed : Interpretation) : Prop :=
  ∃ e ∈ s.effects,
    e.plan.packet.site.occurrence = up ∧ down ∈ GeneralNominalVersionedFrame231.children e.plan.packet ∧
    (GeneralRebaseReceiptExtract289.effectSummary e).matches ask = true ∧
    (∀ key ∈ constructorKeys (context s).state, r.constructors key = e.registry.constructors key) ∧
    bodyCheck r s up proposed e = .good

theorem owner_exact (r : Registry) (s : State roles) (up down : Occurrence roles)
    (ask : Offer) (proposed : Interpretation) :
    s.effects.any (qualifies r s up down ask proposed) = true ↔ HasOwner r s up down ask proposed := by
  unfold HasOwner qualifies
  simp only [List.any_eq_true,Bool.and_eq_true,decide_eq_true_eq,exactProducer_iff,and_assoc]

inductive Result where
  | prior (value : Outcome)
  | historicalDisagreement
  deriving DecidableEq, Repr

def resolve (r : Registry) (s : State roles) (up down : Occurrence roles)
    (ask : Offer) (proposed : Interpretation) : Result :=
  match gate r s up down ask proposed with
  | .receipt .ready =>
    if s.effects.any (qualifies r s up down ask proposed)
    then .prior (.receipt .ready) else .historicalDisagreement
  | result => .prior result

theorem ready_exact (r : Registry) (s : State roles) (up down : Occurrence roles)
    (ask : Offer) (proposed : Interpretation) :
    resolve r s up down ask proposed = .prior (.receipt .ready) ↔
    gate r s up down ask proposed = .receipt .ready ∧ HasOwner r s up down ask proposed := by
  unfold resolve
  rw [← owner_exact]
  cases h : gate r s up down ask proposed with
  | metadata issue => simp
  | receipt d =>
    cases d <;> simp

theorem preserved_other_outcome {r : Registry} {s : State roles} {up down : Occurrence roles}
    {ask : Offer} {proposed : Interpretation} {result : Outcome}
    (prior : gate r s up down ask proposed = result) (notReady : result ≠ .receipt .ready) :
    resolve r s up down ask proposed = .prior result := by
  unfold resolve
  rw [prior]
  cases result with
  | metadata _ => rfl
  | receipt d => cases d <;> first | rfl | exact (notReady rfl).elim

theorem one_effect_sound {r : Registry} {s : State roles} {up down : Occurrence roles}
    {ask : Offer} {proposed : Interpretation}
    (ready : resolve r s up down ask proposed = .prior (.receipt .ready)) :
    (up,down) ∈ s.core.erased.current.edges ∧
    ∃ e ∈ s.effects, e.plan.packet.site.occurrence = up ∧
      down ∈ GeneralNominalVersionedFrame231.children e.plan.packet ∧
      (∀ m, ProposedModels s.core up e.plan r.constructors proposed m ↔ e.Live s.core m) := by
  obtain ⟨was,⟨e,present,site,generated,_,_,pass⟩⟩ := (ready_exact ..).mp ready
  refine ⟨(GeneralObservedMetadataGate290.ready_has_provenance was).1.1,e,present,site,generated,?_⟩
  intro m
  unfold Effect.Live
  rw [site]
  exact (accepted_live_models pass m).trans (GeneralNominalVersionedEffects231.class_effects_iff _ _ _ _).symm

end Yulang.GeneralObservedMetadataHistorical290
