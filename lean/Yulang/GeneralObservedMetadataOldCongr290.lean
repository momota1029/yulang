import Yulang.GeneralObservedMetadataNoninterference290

/-! Congruence of the previous receipt computation itself. Keep the declared
world fixed and only vary catalogue entries outside the recorded footprint. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralObservedMetadataOldCongr290
open GeneralDeclarations (Registry)
open GeneralDeclarationPatterns (Constructors)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralRebaseReceiptWire289 (Offer)
open GeneralRebaseReceiptCatalogue289 (agreement signature constructorKeys boundedWire)
open GeneralRebaseReceiptExactLink289 (anchors exactProducer anchoredWire boundedDecision)
open GeneralRebaseReceiptExtract289 (candidates extract)
open GeneralObservedMetadataAgreement290 (all_local)

theorem compare_first {keys : List Nat} {a b old : Constructors}
    (same : ∀ k ∈ keys, a k = b k) : agreement keys a old = agreement keys b old := by
  apply all_local
  intro k hk
  unfold signature
  rw [same k hk]

theorem candidate_world {r q : Registry} (same : r.declarations = q.declarations) (down : Occurrence roles) :
    candidates r down = candidates q down := by
  unfold candidates
  rw [same]

theorem same_extract {r q : Registry} (same : r.declarations = q.declarations)
    (s : State roles) (down : Occurrence roles) : extract r s down = extract q s down := by
  unfold extract
  rw [same,candidate_world same down]

theorem same_wire {r q : Registry} (world : r.declarations = q.declarations) (s : State roles)
    (down : Occurrence roles)
    (same : ∀ k ∈ constructorKeys s.core.erased.current.context.state, r.constructors k = q.constructors k) :
    boundedWire r s down = boundedWire q s down := by
  unfold boundedWire
  simp only [compare_first same,same_extract world s down]

theorem same_anchors {r q : Registry} (s : State roles) (up down : Occurrence roles) (ask : Offer)
    (same : ∀ k ∈ constructorKeys s.core.erased.current.context.state, r.constructors k = q.constructors k) :
    anchors r s up down ask = anchors q s up down ask := by
  have predicate : exactProducer (constructorKeys s.core.erased.current.context.state) r up down ask =
      exactProducer (constructorKeys s.core.erased.current.context.state) q up down ask := by
    funext e
    unfold exactProducer
    rw [compare_first same]
  unfold anchors
  rw [predicate]

theorem same_decision {r q : Registry} (s : State roles) (up down : Occurrence roles) (ask : Offer)
    (world : r.declarations = q.declarations)
    (same : ∀ k ∈ constructorKeys s.core.erased.current.context.state, r.constructors k = q.constructors k) :
    boundedDecision r s up down ask = boundedDecision q s up down ask := by
  unfold boundedDecision anchoredWire
  rw [same_wire world s down same,same_anchors s up down ask same]

end Yulang.GeneralObservedMetadataOldCongr290
