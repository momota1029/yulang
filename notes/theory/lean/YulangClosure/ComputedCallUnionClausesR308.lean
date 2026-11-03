import YulangClosure.ComputedCallPhaseDescriptorR306

/-!
R308: full original trace clauses at the actual R293 tagged Union consumer.

Source: computed-call-result-constructor §§3–5 (EI-All), generated-computed-
result-correspondence GR1/GR5, and source Generalize §§3.1–3.3. These are
conversions of the EXISTING original clauses, not a new EI interpretation.
Every branch keeps its own guards, trace form and observation fields. The
world factored below is exactly raw.event, with the SAME whole raw tuple.

The forward finite Proof is constructed in the original proof grammar.
The reverse is supplied as typed Evidence, not claimed as a finite Proof.
No q_c registration, semantic admission, independent arm law or original
source child is inferred from these conversions.
-/
namespace YulangClosure.ComputedCallUnionClausesR308

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment
open OriginalSourceChecking SourceSignatureConstruction SourceContributionConstruction
open ComputedCallUnionRealizationR293 ComputedCallPhaseDescriptorR306

variable {s : Sorts} {View : Type}

/-- The actual original Return/unfinished clause; no return is invented. -/
def formBody (inputs : Inputs s) (row : TraceRow s) : Positive s :=
  match inputs.traceForm row with
  | .pureReturn value => .both (.guard (value.event = row.event)) (.field (.value value))
  | .unfinished => .guard True

/-- Only the common world field is removed. All branch-specific guards,
form, actual result row and recursively dependent observation fields remain. -/
def remainder (inputs : Inputs s) (row : TraceRow s) : Positive s :=
  .both (.guard (inputs.eventCoherent row.event ∧ (inputs.observationGuards row).Valid))
    (.both (formBody inputs row) (inputs.observationFields row))

def branchRemainder (inputs : Inputs s) (state : Decoded s View)
    (endpoint : Endpoint) (raw : RawObservation s) : Positive s :=
  remainder inputs (raw.atInterface (state.interfaces endpoint))

/-- This is a derived normal form, NOT a clause readback for a new Interface. -/
def factoredBody (inputs : Inputs s) (state : Decoded s View)
    (source : Endpoint) (arms : List Endpoint) (raw : RawObservation s) : Positive s :=
  .both (.field (.world raw.event))
    (.either (branchRemainder inputs state source raw)
      (.existsE (Fin arms.length) fun i => branchRemainder inputs state arms[i] raw))

/-- Semantic truth can be reified into the complete dependent packet.
Classical choice is explicit here; no executable extraction is claimed. -/
noncomputable def evidenceOfHolds (Z : Family s) (body : Positive s)
    (valid : body.Holds Z) : Evidence Z body := by
  classical
  induction body with
  | guard fact => exact ⟨valid⟩
  | field query => exact ⟨valid⟩
  | both left right ihl ihr => exact ⟨ihl valid.1, ihr valid.2⟩
  | either left right ihl ihr =>
      exact if h : left.Holds Z then .inl (ihl h) else .inr (ihr (valid.resolve_left h))
  | all D body ih => exact fun d => ih d (valid d)
  | existsE D body ih => exact ⟨valid.choose, ih valid.choose valid.choose_spec⟩

theorem evidence_nonempty_iff (Z : Family s) (body : Positive s) :
    Nonempty (Evidence Z body) ↔ body.Holds Z :=
  ⟨fun ⟨packet⟩ => evidence_sound Z body packet,
    fun valid => ⟨evidenceOfHolds Z body valid⟩⟩

/-- Exact rearrangement of the original full trace packet. -/
def splitBranch (inputs : Inputs s) (state : Decoded s View)
    (endpoint : Endpoint) (raw : RawObservation s) (Z : Family s)
    (packet : Evidence Z (branchBody inputs state endpoint raw)) :
    Evidence Z (.field (.world raw.event)) ×
      Evidence Z (branchRemainder inputs state endpoint raw) :=
  ⟨packet.2.1, packet.1, packet.2.2⟩

def joinBranch (inputs : Inputs s) (state : Decoded s View)
    (endpoint : Endpoint) (raw : RawObservation s) (Z : Family s)
    (packet : Evidence Z (.field (.world raw.event)) ×
      Evidence Z (branchRemainder inputs state endpoint raw)) :
    Evidence Z (branchBody inputs state endpoint raw) :=
  ⟨packet.2.1, packet.1, packet.2.2⟩

theorem join_split_branch (inputs : Inputs s) (state : Decoded s View)
    (endpoint : Endpoint) (raw : RawObservation s) (Z : Family s)
    (packet : Evidence Z (branchBody inputs state endpoint raw)) :
    joinBranch inputs state endpoint raw Z (splitBranch inputs state endpoint raw Z packet) = packet := rfl

theorem split_join_branch (inputs : Inputs s) (state : Decoded s View)
    (endpoint : Endpoint) (raw : RawObservation s) (Z : Family s)
    (packet : Evidence Z (.field (.world raw.event)) ×
      Evidence Z (branchRemainder inputs state endpoint raw)) :
    splitBranch inputs state endpoint raw Z (joinBranch inputs state endpoint raw Z packet) = packet := rfl

/-- Keep the SAME source/arm tag and SAME Fin index, including duplicates. -/
def factorEvidence (inputs : Inputs s) (state : Decoded s View)
    (source : Endpoint) (arms : List Endpoint) (raw : RawObservation s) (Z : Family s) :
    Evidence Z (unionBody inputs state source arms raw) →
      Evidence Z (factoredBody inputs state source arms raw)
  | .inl packet =>
      let split := splitBranch inputs state source raw Z packet
      ⟨split.1, .inl split.2⟩
  | .inr ⟨i, packet⟩ =>
      let split := splitBranch inputs state arms[i] raw Z packet
      ⟨split.1, .inr ⟨i, split.2⟩⟩

def unfactorEvidence (inputs : Inputs s) (state : Decoded s View)
    (source : Endpoint) (arms : List Endpoint) (raw : RawObservation s) (Z : Family s) :
    Evidence Z (factoredBody inputs state source arms raw) →
      Evidence Z (unionBody inputs state source arms raw)
  | ⟨world, .inl packet⟩ => .inl (joinBranch inputs state source raw Z ⟨world, packet⟩)
  | ⟨world, .inr ⟨i, packet⟩⟩ => .inr ⟨i, joinBranch inputs state arms[i] raw Z ⟨world, packet⟩⟩

theorem unfactor_factor (inputs : Inputs s) (state : Decoded s View)
    (source : Endpoint) (arms : List Endpoint) (raw : RawObservation s) (Z : Family s)
    (packet : Evidence Z (unionBody inputs state source arms raw)) :
    unfactorEvidence inputs state source arms raw Z
      (factorEvidence inputs state source arms raw Z packet) = packet := by
  cases packet with
  | inl packet => rfl
  | inr packet => cases packet; rfl

theorem factor_unfactor (inputs : Inputs s) (state : Decoded s View)
    (source : Endpoint) (arms : List Endpoint) (raw : RawObservation s) (Z : Family s)
    (packet : Evidence Z (factoredBody inputs state source arms raw)) :
    factorEvidence inputs state source arms raw Z
      (unfactorEvidence inputs state source arms raw Z packet) = packet := by
  rcases packet with ⟨world, packet⟩
  cases packet with
  | inl packet => rfl
  | inr packet => cases packet; rfl

theorem factored_holds_iff (inputs : Inputs s) (state : Decoded s View)
    (source : Endpoint) (arms : List Endpoint) (raw : RawObservation s) (Z : Family s) :
    (factoredBody inputs state source arms raw).Holds Z ↔
      (unionBody inputs state source arms raw).Holds Z := by
  constructor
  · rintro ⟨world, source | ⟨i, arm⟩⟩
    · exact Or.inl ⟨source.1, world, source.2⟩
    · exact Or.inr ⟨i, arm.1, world, arm.2⟩
  · rintro (source | ⟨i, arm⟩)
    · exact ⟨source.2.1, Or.inl ⟨source.1, source.2.2⟩⟩
    · exact ⟨arm.2.1, Or.inr ⟨i, arm.1, arm.2.2⟩⟩

/-- Forward finite Proof in the unmodified original proof grammar. -/
theorem branch_factor_proof (inputs : Inputs s) (registry : GuardRegistry inputs)
    (leaves : Positive s → Positive s → Prop) (state : Decoded s View)
    (endpoint : Endpoint) (raw : RawObservation s) :
    Proof inputs registry leaves (branchBody inputs state endpoint raw)
      (.both (.field (.world raw.event)) (branchRemainder inputs state endpoint raw)) :=
  .bothIntro (.compose (.right _ _) (.left _ _))
    (.bothIntro (.left _ _) (.compose (.right _ _) (.right _ _)))

theorem union_factor_proof (inputs : Inputs s) (registry : GuardRegistry inputs)
    (leaves : Positive s → Positive s → Prop) (state : Decoded s View)
    (source : Endpoint) (arms : List Endpoint) (raw : RawObservation s) :
    Proof inputs registry leaves (unionBody inputs state source arms raw)
      (factoredBody inputs state source arms raw) := by
  apply Proof.cases
  · exact .compose (branch_factor_proof inputs registry leaves state source raw)
      (.bothIntro (.left _ _) (.compose (.right _ _) (.inLeft _ _)))
  · apply Proof.existsElim
    intro i
    exact .compose (branch_factor_proof inputs registry leaves state arms[i] raw)
      (.bothIntro (.left _ _) (.compose (.right _ _)
        (.compose (.existsIntro (fun j : Fin arms.length => branchRemainder inputs state arms[j] raw) i)
          (.inRight _ _))))

/-- Apply the actual R293 source introduction, retaining all original fields. -/
theorem factored_introduction (inputs : Inputs s) (registry : GuardRegistry inputs)
    (leaves : Positive s → Positive s → Prop) (state : Decoded s View)
    (source : Endpoint) (arms : List Endpoint) (raw : RawObservation s) :
    Proof inputs registry leaves (.field (.trace (raw.atInterface (state.interfaces source))))
      (factoredBody inputs state source arms raw) :=
  .compose (union_introduction inputs registry leaves state source arms raw)
    (union_factor_proof inputs registry leaves state source arms raw)

/-- The existing Union consumer packet is precisely this tagged evidence. -/
def packetEvidence (inputs : Inputs s) (state : Decoded s View)
    (scope : List Binder) (source : Endpoint) (arms : List Endpoint) (raw : RawObservation s)
    (packet : Packet (unionCatalogue inputs state scope source arms) raw) :
    Evidence (Meaning inputs) (unionBody inputs state source arms raw) :=
  match packet with
  | ⟨.inl _, value⟩ => .inl value
  | ⟨.inr i, value⟩ => .inr ⟨i, value⟩

def evidencePacket (inputs : Inputs s) (state : Decoded s View)
    (scope : List Binder) (source : Endpoint) (arms : List Endpoint) (raw : RawObservation s) :
    Evidence (Meaning inputs) (unionBody inputs state source arms raw) →
      Packet (unionCatalogue inputs state scope source arms) raw
  | .inl packet => ⟨.inl (), packet⟩
  | .inr ⟨i, packet⟩ => ⟨.inr i, packet⟩

theorem evidence_packet_roundtrip (inputs : Inputs s) (state : Decoded s View)
    (scope : List Binder) (source : Endpoint) (arms : List Endpoint) (raw : RawObservation s)
    (packet : Evidence (Meaning inputs) (unionBody inputs state source arms raw)) :
    packetEvidence inputs state scope source arms raw
      (evidencePacket inputs state scope source arms raw packet) = packet := by
  cases packet with
  | inl packet => rfl
  | inr packet => cases packet; rfl

theorem packet_evidence_roundtrip (inputs : Inputs s) (state : Decoded s View)
    (scope : List Binder) (source : Endpoint) (arms : List Endpoint) (raw : RawObservation s)
    (packet : Packet (unionCatalogue inputs state scope source arms) raw) :
    evidencePacket inputs state scope source arms raw
      (packetEvidence inputs state scope source arms raw packet) = packet := by
  rcases packet with ⟨tag, packet⟩
  cases tag with
  | inl u => cases u; rfl
  | inr i => rfl

/-- Semantic source membership reifies the original full branch, not a
source execution or a finite native fixture. -/
noncomputable def sourcePacket (inputs : Inputs s) (state : Decoded s View)
    (scope : List Binder) (source : Endpoint) (raw : RawObservation s)
    (member : Meaning inputs (.trace (raw.atInterface (state.interfaces source)))) :
    Packet (branchCatalogue inputs state scope source) raw :=
  ⟨(), evidenceOfHolds (Meaning inputs) _ ((meaning_clause inputs _).mp member)⟩

/-- The reified full source packet is passed to the ACTUAL R306/R293 consumer.
The original child contribution and catalogue identification remain explicit. -/
theorem source_meaning_registered (inputs : Inputs s) (state : Decoded s View)
    (scope : List Binder) (graph : Graph (RawObservation s)) (old : Relations graph)
    (operators : Operators graph) (site : Site) (left right : Nat)
    (source : Endpoint) (arms : List Endpoint) (raw : RawObservation s)
    (member : Meaning inputs (.trace (raw.atInterface (state.interfaces source))))
    (childNode : Node (RawObservation s))
    (sameCatalogue : childNode.catalogue = branchCatalogue inputs state scope source)
    (child : DeclContribution graph old operators left raw childNode
      (sameCatalogue ▸ sourcePacket inputs state scope source raw member)) :
    let added := unionNode inputs state scope site left right source arms
    let installed := installUnion inputs state scope graph site left right source arms
    Nonempty (DeclContribution installed
      (relations installed (appendRelations graph added old) inputs state scope site source arms)
      (appendOperators graph added operators) graph.nodes.length raw added
      (injectSource inputs state scope source arms (sourcePacket inputs state scope source raw member))) :=
  source_contribution_registered inputs state scope graph old operators site left right
    source arms raw childNode sameCatalogue (sourcePacket inputs state scope source raw member) child

/-- Every existing independent arm supplies its OWN full original membership.
No source membership, endpoint equality or arm deduplication supplies it. -/
noncomputable def armPacket (inputs : Inputs s) (state : Decoded s View)
    (scope : List Binder) (arms : List Endpoint) (raw : RawObservation s)
    (i : Fin arms.length)
    (member : Meaning inputs (.trace (raw.atInterface (state.interfaces arms[i])))) :
    Packet (armsCatalogue inputs state scope arms) raw :=
  ⟨i, evidenceOfHolds (Meaning inputs) _ ((meaning_clause inputs _).mp member)⟩

/-- Apply the actual independent-arm R306/R293 consumer at the SAME Fin slot. -/
theorem arm_meaning_registered (inputs : Inputs s) (state : Decoded s View)
    (scope : List Binder) (graph : Graph (RawObservation s)) (old : Relations graph)
    (operators : Operators graph) (site : Site) (left right : Nat)
    (source : Endpoint) (arms : List Endpoint) (raw : RawObservation s)
    (i : Fin arms.length)
    (member : Meaning inputs (.trace (raw.atInterface (state.interfaces arms[i]))))
    (childNode : Node (RawObservation s))
    (sameCatalogue : childNode.catalogue = armsCatalogue inputs state scope arms)
    (child : DeclContribution graph old operators right raw childNode
      (sameCatalogue ▸ armPacket inputs state scope arms raw i member)) :
    let added := unionNode inputs state scope site left right source arms
    let installed := installUnion inputs state scope graph site left right source arms
    Nonempty (DeclContribution installed
      (relations installed (appendRelations graph added old) inputs state scope site source arms)
      (appendOperators graph added operators) graph.nodes.length raw added
      (injectArm inputs state scope source arms (armPacket inputs state scope arms raw i member))) :=
  arm_contribution_registered inputs state scope graph old operators site left right
    source arms raw childNode sameCatalogue (armPacket inputs state scope arms raw i member) child

/-- Every output packet is consumed at its ACTUAL selected branch interface.
The common event never permits reading a different branch's guards or fields. -/
theorem packet_branch_meaning (inputs : Inputs s) (state : Decoded s View)
    (scope : List Binder) (source : Endpoint) (arms : List Endpoint) (raw : RawObservation s)
    (packet : Packet (unionCatalogue inputs state scope source arms) raw) :
    Meaning inputs (.trace (raw.atInterface (state.interfaces
      (match packet.port with | .inl _ => source | .inr i => arms[i])))) := by
  rcases packet with ⟨tag, packet⟩
  cases tag with
  | inl u => exact (meaning_clause inputs _).mpr (evidence_sound _ _ packet)
  | inr i => exact (meaning_clause inputs _).mpr (evidence_sound _ _ packet)

/-- GR5/R293 application at R159's unchanged shared ViewLogic extension.
The original target check is retained, independently from the derived view.
Neither the common-world conversion nor the view proves that check. -/
theorem factored_app_result_pair (inputs : Inputs s) (registry : GuardRegistry inputs)
    (readout : RuntimeReadout s View) (ports : PortReadout s View)
    (declarations : Declarations inputs registry) (original : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (context : Context) (mark : Mark)
    (occurrence : Nat) (data : Logical s View) (state : Decoded s View)
    (decoded : decode readout environment = some state) (arms : List Endpoint)
    (raw : RawObservation s)
    (checked : Checking (OriginalSourceChecking.kernel inputs registry declarations
      (environmentReading inputs readout ports) original)
      (environment.extend ⟨mark.site, .viewLogic, 0⟩
        (scopeCandidate environment occurrence (.logical .viewLogic data)))
      ⟨.computation, mark.site, context, ⟨mark.site, .callableImage⟩, ⟨mark.site, .synthesis⟩⟩)
    (member : Meaning inputs (.trace (raw.atInterface
      ((state.logical data).interfaces ⟨mark.site, .callableImage⟩)))) :
    (factoredBody inputs (state.logical data) ⟨mark.site, .callableImage⟩ arms raw).Holds (Meaning inputs) ∧
    Meaning inputs (.trace (raw.atInterface ((state.logical data).interfaces ⟨mark.site, .synthesis⟩))) := by
  have pair := app_result_pair inputs registry readout ports declarations original
    environment context mark occurrence data state decoded arms raw checked member
  exact ⟨(factored_holds_iff inputs (state.logical data) ⟨mark.site, .callableImage⟩ arms raw
    (Meaning inputs)).mpr pair.1, pair.2⟩

/-- No original trace clause literally registers the R293 outer Either.
This is a syntax obstruction, not semantic inequivalence of their meanings. -/
theorem trace_clause_ne_union (inputs : Inputs s) (state : Decoded s View)
    (source : Endpoint) (arms : List Endpoint) (raw : RawObservation s) (row : TraceRow s) :
    clause inputs (.trace row) ≠ unionBody inputs state source arms raw := by
  intro equation
  cases equation

end YulangClosure.ComputedCallUnionClausesR308
