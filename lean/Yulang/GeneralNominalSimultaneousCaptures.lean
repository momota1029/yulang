import Yulang.GeneralNominalPacketCaptureReadback

/-! One finite normalized Pattern label per needed declaration variable.
Minimum mass prevents repeated semantic presentations from inflating one
occurrence's budget. Agreement comes from actual shared capture origins. -/
namespace Yulang.GeneralNominalSimultaneousCaptures
open GeneralDeclarationPatterns GeneralNominalGroundAccessibility
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms GeneralNominalFiniteMeaning
open GeneralNominalReadbackFunctionality GeneralNominalSharedCaptures
open GeneralNominalSaturationState GeneralNominalCompoundReadback
open GeneralNominalPacketCaptureReadback GeneralNominalClosedPatternNormal
open GeneralNominalClosedPatternMass CommonNominalFullCarrier
open GeneralNominalPatersonLineage (mass)

variable {model : GeneralNominalCommonBridge.Assignment}

theorem closed_normal (closed : ClosedTerm context pattern term) :
    normalize (normalize pattern) = normalize pattern ∧ ClosedTerm context (normalize pattern) term ∧
      mass [normalize pattern] = mass [pattern] := by
  have fixed := translated_normal (normalize pattern) (by
    rw [closed.1]; exact quote_closed term closed.2.1 closed.2.2)
  have normalized : ClosedTerm context (normalize pattern) term := ⟨by rw [fixed]; exact closed.1,closed.2⟩
  exact ⟨fixed,normalized,by rw [closed_mass closed,closed_mass normalized]⟩

theorem at_same (known : At model .actual first value) (same : Same model first last) :
    At model .actual last value := by
  obtain ⟨actual,observed⟩ := known.1
  refine ⟨same.2.1,?_⟩
  intro other seen
  have equal := same.2.2 actual other observed seen
  have finite := known.2 actual observed
  exact ⟨subtype_trans equal.2 finite.1,subtype_trans finite.2 equal.1⟩

def Meaning (context : GeneralNominalCandidates.Context) (packet : Packet roles)
    (model : GeneralNominalCommonBridge.Assignment) (name : Nat) (pattern : Pattern) : Prop :=
  ∃ term, ClosedTerm context pattern term ∧
    ∀ origin, Usable packet name origin → At model .actual origin (denote (fun _ => .bottom) term)

theorem meaning_of_readback (packet : Packet roles) (branch : packet.Holds model)
    (usable : Usable packet name origin) (closed : ClosedTerm context pattern term)
    (known : At model .actual origin (denote (fun _ => .bottom) term)) :
    Meaning context packet model name pattern := by
  refine ⟨term,closed,?_⟩
  intro other available
  exact at_same known (usable_same usable available model branch)

private theorem least (predicate : Nat → Prop) (nonempty : ∃ value, predicate value) :
    ∃ value, predicate value ∧ ∀ other, predicate other → value ≤ other := by
  classical
  obtain ⟨value,present⟩ := nonempty
  induction value using Nat.strongRecOn with
  | ind value ih =>
    by_cases smaller : ∃ other, other < value ∧ predicate other
    · obtain ⟨other,below,known⟩ := smaller
      exact ih other below known
    · exact ⟨value,present,fun other known => by
        by_cases below : value ≤ other
        · exact below
        · exact False.elim (smaller ⟨other,by omega,known⟩)⟩

theorem minimum_label (available : ∃ pattern, Meaning context packet model name pattern) :
    ∃ pattern, normalize pattern = pattern ∧ Meaning context packet model name pattern ∧
      ∀ other, Meaning context packet model name other → mass [pattern] ≤ mass [other] := by
  have nonempty : ∃ size, ∃ pattern, Meaning context packet model name pattern ∧ mass [pattern] = size := by
    obtain ⟨pattern,known⟩ := available
    exact ⟨mass [pattern],pattern,known,rfl⟩
  obtain ⟨size,⟨pattern,⟨term,closed,shared⟩,atSize⟩,minimal⟩ := least _ nonempty
  obtain ⟨fixed,normal,measured⟩ := closed_normal closed
  refine ⟨normalize pattern,fixed,⟨term,normal,shared⟩,?_⟩
  intro other known
  rw [measured,atSize]
  exact minimal (mass [other]) ⟨other,known,rfl⟩

theorem simultaneous (state : State roles) (packet : Packet roles) (same : state.context = packet.context)
    (safe : GeneralNominalActualInspectionSteps.Safe state packet)
    (located : GeneralNominalRecursiveCandidates.arguments packet.context packet.site.occurrence = some packet.bounds)
    (valid : Models state model) (branch : packet.Holds model) (known : Inputs context model packet.site labels)
    (generation : GenerationGuard tracked packet) :
    ∃ capture : Nat → Pattern, (∀ name, normalize (capture name) = capture name) ∧
      (∀ name, ¬ Needed packet name → capture name = .var name) ∧
      ∀ name, Needed packet name → Meaning context packet model name (capture name) ∧
        mass [capture name] ≤ mass labels ∧
        ∀ origin, Usable packet name origin → ∀ pattern term,
          ClosedTerm context pattern term → At model .actual origin (denote (fun _ => .bottom) term) →
            mass [capture name] ≤ mass [pattern] := by
  classical
  have witnesses : ∀ name, Needed packet name → ∃ pattern,
      normalize pattern = pattern ∧ Meaning context packet model name pattern ∧
      mass [pattern] ≤ mass labels ∧
      ∀ other, Meaning context packet model name other → mass [pattern] ≤ mass [other] := by
    intro name needed
    obtain ⟨origin,usable⟩ := generation name needed
    obtain ⟨pattern,term,closed,meaning,bound⟩ := usable_closed state packet same safe located valid branch known usable
    have shared := meaning_of_readback packet branch usable closed meaning
    obtain ⟨chosen,normal,readback,smallest⟩ := minimum_label ⟨pattern,shared⟩
    exact ⟨chosen,normal,readback,Nat.le_trans (smallest pattern shared) bound,smallest⟩
  let capture := fun name => if needed : Needed packet name then Classical.choose (witnesses name needed) else .var name
  refine ⟨capture,?_,?_,?_⟩
  · intro name
    by_cases needed : Needed packet name
    · simpa only [capture,dite_eq_left needed] using (Classical.choose_spec (witnesses name needed)).1
    · simp only [capture,dite_eq_right needed,normalize]
  · intro name unused
    simp only [capture,dite_eq_right unused]
  · intro name needed
    have selected := Classical.choose_spec (witnesses name needed)
    simp only [capture,dite_eq_left needed]
    refine ⟨selected.2.1,selected.2.2.1,?_⟩
    intro origin usable pattern term closed meaning
    exact selected.2.2.2 pattern (meaning_of_readback packet branch usable closed meaning)

end Yulang.GeneralNominalSimultaneousCaptures
