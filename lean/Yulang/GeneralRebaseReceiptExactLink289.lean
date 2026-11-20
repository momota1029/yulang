import Yulang.GeneralRebaseReceiptOccurrence289

/-! Bind the actual raw edge and its owning historical effect by complete
occurrences at a fixed role environment. Keep the finite catalogue gate. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29100
set_option maxHeartbeats 19000000
namespace Yulang.GeneralRebaseReceiptExactLink289
open GeneralRebaseReceiptOccurrence289 (encode code_eq_iff)
open GeneralRebaseReceiptWire289 (Wire Offer Decision check)
open GeneralRebaseReceiptExtract289 (effectSummary)
open GeneralRebaseReceiptCatalogue289 (boundedWire constructorKeys agreement)
open GeneralNominalVersionedFrame231 (children)
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralSourceDictionaries (Occurrence)
open GeneralDeclarations (Registry)

def exactEdge (s : State roles) (up down : Occurrence roles) : Bool :=
  s.core.erased.current.edges.any (fun p => decide (encode p.1 = encode up ∧ encode p.2 = encode down))

theorem exactEdge_iff (s : State roles) (up down : Occurrence roles) :
    exactEdge s up down = true ↔ (up,down) ∈ s.core.erased.current.edges := by
  unfold exactEdge
  constructor
  · intro has
    obtain ⟨⟨first,last⟩,present,proof⟩ := List.any_eq_true.mp has
    have both := of_decide_eq_true proof
    have one := code_eq_iff.mp both.1
    have two := code_eq_iff.mp both.2
    change first = up at one
    change last = down at two
    subst first
    subst last
    exact present
  · intro h
    exact List.any_eq_true.mpr ⟨(up,down),h,by simp⟩

def exactProducer (keys : List Nat) (r : Registry) (up down : Occurrence roles) (ask : Offer) (e : Effect roles) : Bool :=
  decide (encode e.plan.packet.site.occurrence = encode up) &&
    (children e.plan.packet).any (fun seen => decide (encode seen = encode down)) &&
    (effectSummary e).matches ask && agreement keys r.constructors e.registry.constructors

theorem exactProducer_iff (keys : List Nat) (r : Registry) (up down : Occurrence roles)
    (ask : Offer) (e : Effect roles) :
    exactProducer keys r up down ask e = true ↔
    e.plan.packet.site.occurrence = up ∧ down ∈ children e.plan.packet ∧
      (effectSummary e).matches ask = true ∧
      ∀ key ∈ keys, r.constructors key = e.registry.constructors key := by
  unfold exactProducer
  simp only [Bool.and_eq_true,decide_eq_true_eq,code_eq_iff,List.any_eq_true,
    GeneralRebaseReceiptCatalogue289.agreement_exact,and_assoc]
  constructor
  · rintro ⟨h1,⟨o,present,rfl⟩,h2,h3⟩
    exact ⟨h1,present,h2,h3⟩
  · rintro ⟨h1,member,h2,h3⟩
    exact ⟨h1,⟨_,member,rfl⟩,h2,h3⟩

def anchors (r : Registry) (s : State roles) (up down : Occurrence roles) (ask : Offer) : Bool :=
  exactEdge s up down &&
    s.effects.any (exactProducer (constructorKeys s.core.erased.current.context.state) r up down ask)

def Anchored (r : Registry) (s : State roles) (up down : Occurrence roles) (ask : Offer) : Prop :=
  (up,down) ∈ s.core.erased.current.edges ∧
    ∃ e : Effect roles, e ∈ s.effects ∧
      e.plan.packet.site.occurrence = up ∧ down ∈ children e.plan.packet ∧
      (effectSummary e).matches ask = true ∧
      ∀ key ∈ constructorKeys s.core.erased.current.context.state,
        r.constructors key = e.registry.constructors key

theorem anchors_exact (r : Registry) (s : State roles) (up down : Occurrence roles) (ask : Offer) :
    anchors r s up down ask = true ↔ Anchored r s up down ask := by
  simp only [anchors,Anchored,Bool.and_eq_true,exactEdge_iff,List.any_eq_true,exactProducer_iff]

def anchoredWire (r : Registry) (s : State roles) (up down : Occurrence roles) (ask : Offer) : Option Wire :=
  (boundedWire r s down).map fun w =>
    if anchors r s up down ask then w else { w with edges := [] }

def boundedDecision (r : Registry) (s : State roles) (up down : Occurrence roles) (ask : Offer) : Decision :=
  match anchoredWire r s up down ask with
  | some w => check w ask
  | none => .wrongWorld

theorem accept_has_actual_anchor {r : Registry} {s : State roles} {up down : Occurrence roles} {ask : Offer}
    (success : boundedDecision r s up down ask = .ready) : Anchored r s up down ask := by
  unfold boundedDecision anchoredWire at success
  cases prior : boundedWire r s down with
  | none =>
    rw [prior] at success
    cases success
  | some w =>
    rw [prior] at success
    by_cases yes : anchors r s up down ask = true
    · exact (anchors_exact ..).mp yes
    · simp only [Option.map_some,ite_eq_right yes] at success
      have fields := (GeneralRebaseReceiptWire289.check_ready ..).mp success
      exact (List.not_mem_nil fields.2.2.2.1).elim

end Yulang.GeneralRebaseReceiptExactLink289
