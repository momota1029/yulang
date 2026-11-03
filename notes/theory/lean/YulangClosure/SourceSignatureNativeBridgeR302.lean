import YulangClosure.SourceSignatureExtractedChecksR301
import YulangClosure.ComputedCallUnionRealizationR293

/-!
R302: the existing complete Union catalogue consumer, and the exact remaining
native-signature boundary. This is NOT a Rust-to-Lean simulation theorem.

SourceSignatureExtractionR300 authenticates a finite HIR signature, not emitted
Function terms. candidate_signature_value consumes CHILD rows for its two
effect ports; only the root Function's result port receives Self. The checked
R301 specialization below distinguishes that port from the returned Function's
own result port. See the handoff for exact source owners and missing incidence.

On the semantic side the existing R293 catalogue admits complete proof data
for precisely its original clause, without a second Packet existence axiom.
Reification preserves all dependent universal indices and existential scope.
It is classical proof reification, not executable extraction or authentication
of a native signature. It does not identify the chosen witnesses with a
previously licensed packet or prove naturality of those choices. The R159
application still requires original finite
Checking and original image membership at the same ViewLogic extension.
-/
namespace YulangClosure.SourceSignatureNativeBridgeR302

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment
open OriginalSourceChecking SourceSignatureConstruction SourceContributionConstruction
open ComputedCallUnionRealizationR293

theorem evidence_available (Z : Family s) (body : Positive s) :
    Nonempty (Evidence Z body) ↔ body.Holds Z := by
  constructor
  · rintro ⟨evidence⟩
    exact evidence_sound Z body evidence
  · intro holds
    induction body with
    | guard fact => exact ⟨⟨holds⟩⟩
    | field query => exact ⟨⟨holds⟩⟩
    | both left right ihl ihr =>
      obtain ⟨left⟩ := ihl holds.1
      obtain ⟨right⟩ := ihr holds.2
      exact ⟨left, right⟩
    | either left right ihl ihr =>
      cases holds with
      | inl h => obtain ⟨e⟩ := ihl h; exact ⟨.inl e⟩
      | inr h => obtain ⟨e⟩ := ihr h; exact ⟨.inr e⟩
    | all D body ih =>
      exact ⟨fun d => Classical.choice (ih d (holds d))⟩
    | existsE D body ih =>
      obtain ⟨d, h⟩ := holds
      obtain ⟨e⟩ := ih d h
      exact ⟨⟨d, e⟩⟩

/-- This is the EXISTING original branch catalogue, not a new signature model.
No interface endpoint, world, guard, provider or future field is replaced. -/
theorem source_packet_available (inputs : Inputs s) (state : Decoded s View)
    (scope : List Binder) (source : Endpoint) (raw : RawObservation s) :
    Nonempty (Packet (branchCatalogue inputs state scope source) raw) ↔
      Meaning inputs (.trace (raw.atInterface (state.interfaces source))) := by
  constructor
  · rintro ⟨packet⟩
    exact source_packet_meaning inputs state scope source raw packet
  · intro member
    obtain ⟨evidence⟩ := (evidence_available (Meaning inputs)
      (branchBody inputs state source raw)).mpr ((meaning_clause inputs _).mp member)
    exact ⟨⟨(), evidence⟩⟩

/-- Reifies the selected source OR an independently supplied original arm.
The Fin index keeps duplicates and the original arm order; arbitrary dependent
challenge domains inside each clause remain untouched. -/
theorem union_packet_available (inputs : Inputs s) (state : Decoded s View)
    (scope : List Binder) (source : Endpoint) (arms : List Endpoint)
    (raw : RawObservation s) :
    Nonempty (Packet (unionCatalogue inputs state scope source arms) raw) ↔
      (unionBody inputs state source arms raw).Holds (Meaning inputs) := by
  constructor
  · rintro ⟨⟨tag, evidence⟩⟩
    cases tag with
    | inl tag => exact Or.inl (evidence_sound _ _ evidence)
    | inr i => exact Or.inr ⟨i, evidence_sound _ _ evidence⟩
  · intro holds
    cases holds with
    | inl h =>
      obtain ⟨e⟩ := (evidence_available _ _).mpr h
      exact ⟨⟨.inl (), e⟩⟩
    | inr h =>
      obtain ⟨i, h⟩ := h
      obtain ⟨e⟩ := (evidence_available _ _).mpr h
      exact ⟨⟨.inr i, e⟩⟩

/-- Applied to R293's actual R159 comparison: the source packet goes through
the existing injectSource constructor, retaining its complete value. This
removes separate packet-supply from this consumer, not the independent image
membership, finite Checking, GR1 registration or original admission premises. -/
theorem app_source_packet_and_target (inputs : Inputs s) (registry : GuardRegistry inputs)
    (readout : RuntimeReadout s View) (ports : PortReadout s View)
    (declarations : Declarations inputs registry) (original : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (context : Context) (mark : Mark)
    (occurrence : Nat) (data : Logical s View) (state : Decoded s View)
    (decoded : decode readout environment = some state) (scope : List Binder)
    (arms : List Endpoint) (raw : RawObservation s)
    (checked : Checking (OriginalSourceChecking.kernel inputs registry declarations
      (environmentReading inputs readout ports) original)
      (environment.extend ⟨mark.site, .viewLogic, 0⟩
        (scopeCandidate environment occurrence (.logical .viewLogic data)))
      ⟨.computation, mark.site, context, ⟨mark.site, .callableImage⟩, ⟨mark.site, .synthesis⟩⟩)
    (member : Meaning inputs (.trace (raw.atInterface
      ((state.logical data).interfaces ⟨mark.site, .callableImage⟩)))) :
    (∃ packet : Packet (branchCatalogue inputs (state.logical data) scope
        ⟨mark.site, .callableImage⟩) raw,
      (injectSource inputs (state.logical data) scope ⟨mark.site, .callableImage⟩ arms packet).port =
        .inl packet.port ∧
      (injectSource inputs (state.logical data) scope ⟨mark.site, .callableImage⟩ arms packet).value =
        packet.value) ∧
    Meaning inputs (.trace (raw.atInterface ((state.logical data).interfaces ⟨mark.site, .synthesis⟩))) := by
  obtain ⟨packet⟩ := (source_packet_available inputs (state.logical data) scope
    ⟨mark.site, .callableImage⟩ raw).mpr member
  exact ⟨⟨packet, rfl, rfl⟩,
    (app_result_pair inputs registry readout ports declarations original environment context
      mark occurrence data state decoded arms raw checked member).2⟩

open SourceSignatureRealizationR300 SourceSignatureExtractedChecksR301

/-- Source-located pure-plan check against the authentic finite R301 encoding.
The root re consumes row 6 and prefixes Self; the returned Function's re
consumes row 7 without that prefix. Both mention E because E is explicitly in
row 7; family membership alone cannot authenticate the Self incidence. -/
theorem extracted_result_ports_distinct :
    operationEffectPlan 4 (effects expectedResult) (selfFamily 0 []) true true =
      some (.view true 6 [0, 1, 0, 1] (some "'out")) ∧
    operationEffectPlan 4 (effects (.primitive (Hole := Nat) (some resultRow) .int))
      (selfFamily 0 [.result]) true true =
      some (.view true 7 [0] none) := ⟨rfl, rfl⟩

end YulangClosure.SourceSignatureNativeBridgeR302
