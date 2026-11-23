import Yulang.GeneralDeclarativeWitnessNominalOverlap364

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 92000
set_option maxHeartbeats 128000000
namespace Yulang.GeneralDeclarativeWitnessOrientedNativeRange364
open GeneralDeclarativeWitnessSeparateEndpointAuthors362 (Ordered run)
open GeneralDeclarativeWitnessSeparateAuthorOrder362 (lo mid hi)
open GeneralDeclarativeWitnessSelectedNonpointRoot363 (Root)
open GeneralDeclarativeWitnessOriginalEndpointProjection364 (exact_endpoint_provenance)
open GeneralDeclarativeWitnessActualCompoundElection364 (Read)
open GeneralDeclarativeWitnessCompoundCandidate364 (parameter head_proved_from_both_ends)
open GeneralDeclarativeWitnessElectedPayload364 (Elected Payload makeCapture)
open GeneralDeclarativeWitnessNativeOrder362 (node)
open GeneralDeclarativeWitnessNativeValue360 (Code)
open GeneralDeclarativeWitnessNativeInstall360 (Fits NativeViews)
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)
open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives context_derives_nominal_exact context_derives_ordinary_exact)
open CommonRecursiveNominalIntervals (Endpoint)
open CommonNominalFullCarrier (Subtype)
open GeneralNominalCommonBridge (Assignment)

abbrev point (x : Nat) : Endpoint Nat := .ordinary (.var x)
abbrev boxed (ctor n : Nat) : Endpoint Nat := node (.unary ctor (.leaf n))

theorem payload_step (m : Assignment) (mode : Bool) {key a b : Nat}
    (written : table[key]? = some [parameter mode])
    (checked : ContextDerives table m false (boxed key a) (boxed key b)) :
    if mode then Subtype (m b).1 (m a).1 else Subtype (m a).1 (m b).1 := by
  obtain ⟨_,row,decl,how⟩ :=
    (context_derives_nominal_exact table m false key key [.inl (.point (point a))] [.inl (.point (point b))]).mp checked
  have same := Option.some.inj (decl.symm.trans written)
  subst row
  cases mode
  · change Subtype (m a).1 (m b).1
    have edge : ContextDerives table m false (point a) (point b) := by
      exact how.1
    exact (context_derives_ordinary_exact table m false _ _).mp edge
  · change Subtype (m b).1 (m a).1
    have edge : ContextDerives table m false (point b) (point a) := by
      exact how.1
    exact (context_derives_ordinary_exact table m false _ _).mp edge

/-- An independently selected, single unary occurrence preserves the
whole captured payload window in either declared direction. No name
equalities between the public logical aliases and the original native
positions are used to transport this semantic comparison. -/
theorem oriented_whole_payload_in_every_fit {contra} {x : Ordered contra} {t : Read x}
    {f} {won : Elected t f} (p : Payload won) (made : run contra = some x) (m : Assignment)
    (v : NativeViews) (fit : Fits t.sourceRoot.world m v) :
    Subtype (m p.capture.lower).1 (m p.capture.center).1 ∧
    Subtype (m p.capture.center).1 (m p.capture.upper).1 := by
  have ⟨_,_,lower,upper⟩ := exact_endpoint_provenance t.independently made m v fit
  obtain ⟨left,right⟩ := head_proved_from_both_ends won.unary won.positive
  have center := p.center.exact.trans
    (congrArg (fun c => Code.unary c (.leaf p.center.payload)) p.same)
  unfold lo mid at lower
  unfold mid hi at upper
  rw [left,center] at lower
  rw [center,right] at upper
  have l := payload_step m won.unary.variance won.unary.registry lower
  have u := payload_step m won.unary.variance won.unary.registry upper
  cases behavior : won.unary.variance
  · exact ⟨by simpa [Payload.capture,makeCapture,behavior] using l,
      by simpa [Payload.capture,makeCapture,behavior] using u⟩
  · exact ⟨by simpa [Payload.capture,makeCapture,behavior] using u,
      by simpa [Payload.capture,makeCapture,behavior] using l⟩

end Yulang.GeneralDeclarativeWitnessOrientedNativeRange364
