import YulangClosure.OriginalSourceEnvironment
import YulangClosure.CanonicalLiteralGeneratorR236

/-!
R241: exact original-consumer and frame equations, with the carrier-realization
boundary left explicit. This file does not choose original sorts, input
relations, descriptor/value embeddings, an observation encoding, or a new
satisfaction relation. In particular it does not identify PaperTypes.Ty with
Sorts.Descriptor or PaperTypes.Value with Sorts.Value.

The adopted all-eight generator supplies Paper data at original coordinates.
The original folded literal consumer additionally needs the declaration,
valueForm and ground facts in `folded_literal_build_exact` below. None of those
three original relations is defined by the adopted generator. The statements
below expose that boundary; they do not assume it as a new realization law.

The unchanged SourceProblem.InferenceSoundness parent remains open. No
SourceProblem instance or sameScoped interpretation is constructed here.
-/
namespace YulangClosure.OriginalLiteralCarrierRealizationR241

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment

/-- This specializes the adopted generator to original root/event/scope/witness
coordinates without identifying its Paper descriptor/value with original sorts.
The universal raw literal includes unit, bool, int, floatBits, string, bytes,
path and character with their complete payloads. -/
theorem canonical_data_at_original_coordinates (s : Sorts)
    (site : Site) (literal : Literal) (root : s.Root) (event : Event s)
    (scope : s.Scope) (witness : s.JointWitness) :
    let result := CanonicalLiteralGeneratorR236.generate site literal root event scope witness
    result.site = site ∧ result.literal = literal ∧
      result.descriptor = PaperTypes.literalType
        (CanonicalLiteralGeneratorR236.toPaperLiteral literal) ∧
      result.value = PaperTypes.Value.literal
        (CanonicalLiteralGeneratorR236.toPaperLiteral literal) ∧
      result.root = root ∧ result.event = event ∧
      result.scope = scope ∧ result.witness = witness := by
  simp [CanonicalLiteralGeneratorR236.generate,
    CanonicalLiteralGeneratorR236.generateType_matches_adopted_l1,
    CanonicalLiteralGeneratorR236.generateValue_matches_adopted_l1]

/-- The exact original atom, without a caller-supplied payload witness or a
surrogate local declaration. This is an equivalence, not a proved ground fact. -/
theorem original_literal_atom_exact (inputs : Inputs s)
    (declarations : LiteralDeclaration s) (assignment : SourceAssignment s)
    (context : Context) (site : Site) (literal : Literal) :
    LiteralAtom inputs declarations assignment
      (CanonicalSourceInferenceModelR196.literalObligation context site literal) ↔
      declarations literal (assignment.row site) ∧
      inputs.valueForm (assignment.descriptor ⟨site, .finalRoot⟩) = .ground ∧
      inputs.ground (assignment.row site) := by
  simp [LiteralAtom, CanonicalSourceInferenceModelR196.literalObligation, atom]

/-- The actual folded Build leaf reads the complete decoded prefix. Its exact
remaining premise is three original local facts under that same assignment. -/
theorem folded_literal_build_exact (inputs : Inputs s)
    (readout : RuntimeReadout s View) (declarations : LiteralDeclaration s)
    (original : Kernel (Payload s View))
    (environment : Environment (Payload s View))
    (context : Context) (site : Site) (literal : Literal) :
    Satisfies (foldedLiteralKernel inputs readout declarations original site literal)
      environment (Build context (.literal ⟨site, none⟩ literal)) ↔
      ∃ state, decode readout environment = some state ∧
        declarations literal (state.assignment.row site) ∧
        inputs.valueForm (state.assignment.descriptor ⟨site, .finalRoot⟩) = .ground ∧
        inputs.ground (state.assignment.row site) := by
  rw [CanonicalSourceInferenceModelR196.literal_generated_formula]
  change ((Local (foldedLiteralKernel inputs readout declarations original site literal)
    environment (.atom (CanonicalSourceInferenceModelR196.literalObligation context site literal)) ∧
      True) ∧ True) ↔ _
  constructor
  · rintro ⟨⟨localProof, _⟩, _⟩
    cases localProof with
    | atom valid =>
      simpa [foldedLiteralKernel, LiteralAtom,
        CanonicalSourceInferenceModelR196.literalObligation, atom] using valid
  · rintro ⟨state, decoded, facts⟩
    refine ⟨⟨Local.atom ?_, True.intro⟩, True.intro⟩
    simpa [foldedLiteralKernel, LiteralAtom,
      CanonicalSourceInferenceModelR196.literalObligation, atom] using
      (show ∃ state, decode readout environment = some state ∧
        declarations literal (state.assignment.row site) ∧
        inputs.valueForm (state.assignment.descriptor ⟨site, .finalRoot⟩) = .ground ∧
        inputs.ground (state.assignment.row site) from ⟨state, decoded, facts⟩)

/-- Application of the exact leaf equation to the existing original source
reconstruction consumer. No original declaration/ground premise is discharged
by this equivalence; no parent delta is claimed. -/
theorem folded_literal_source_rule_exact (inputs : Inputs s)
    (readout : RuntimeReadout s View) (declarations : LiteralDeclaration s)
    (original : Kernel (Payload s View))
    (environment : Environment (Payload s View))
    (context : Context) (site : Site) (literal : Literal) :
    SourceJudgment (foldedLiteralKernel inputs readout declarations original site literal)
      environment context (.literal ⟨site, none⟩ literal) ↔
      ∃ state, decode readout environment = some state ∧
        declarations literal (state.assignment.row site) ∧
        inputs.valueForm (state.assignment.descriptor ⟨site, .finalRoot⟩) = .ground ∧
        inputs.ground (state.assignment.row site) := by
  exact (source_reconstruction
    (foldedLiteralKernel inputs readout declarations original site literal)
    environment context (.literal ⟨site, none⟩ literal)).symm.trans
    (folded_literal_build_exact inputs readout declarations original environment context site literal)

/-- Root decoding uses the actual complete stored frame fold. In particular
the initial assignment is not silently substituted for the decoded one. -/
theorem original_assignment_frame_commutes (readout : RuntimeReadout s View)
    (environment : Environment (Payload s View)) (root : Root s View)
    (rootData : environment.root = .root root) :
    decode readout environment =
      some (environment.frames.foldl (decodeFrame readout) root.decoded) := by
  simp only [decode, rootData]

/-- Logical frames can update the final-root descriptor and eta/witness;
the row keeps the original value and root, and all other event fields. -/
theorem logical_literal_row_commutes (state : Decoded s View)
    (data : Logical s View) (site : Site) :
    (state.logical data).assignment.row site =
      ⟨put state.assignment.descriptor data.descriptors ⟨site, .finalRoot⟩,
        state.assignment.value ⟨site, .finalRoot⟩,
        state.assignment.root ⟨site, .finalRoot⟩,
        {state.assignment.event with eta := data.eta, witness := data.witness}⟩ := rfl

/-- Shared frames retain the whole original literal row, rather than replacing
its event witness with the independent Shared.witness field. -/
theorem shared_literal_row_commutes (state : Decoded s View)
    (data : Shared s) (site : Site) :
    (state.shared data).assignment.row site = state.assignment.row site := rfl

/-- Runtime readout uses the full fixed prefix and original incoming event.
Every event component, including eta0, fiber, current world and witness, is
retained in this equality; no endpoint or empty-effect approximation is used. -/
theorem runtime_literal_row_commutes (readout : RuntimeReadout s View)
    (state : Decoded s View) (binder : Binder) (data : Runtime s View) (site : Site) :
    (state.runtime readout binder data).assignment.row site =
      { (data.endpoints.foldl Decoded.object state).assignment.row site with
        event := readout.event state.fixedFrames state.assignment.event binder data } := rfl

#check @canonical_data_at_original_coordinates
#print axioms canonical_data_at_original_coordinates
#check @original_literal_atom_exact
#print axioms original_literal_atom_exact
#check @folded_literal_build_exact
#print axioms folded_literal_build_exact
#check @folded_literal_source_rule_exact
#print axioms folded_literal_source_rule_exact
#check @original_assignment_frame_commutes
#print axioms original_assignment_frame_commutes
#check @logical_literal_row_commutes
#print axioms logical_literal_row_commutes
#check @shared_literal_row_commutes
#print axioms shared_literal_row_commutes
#check @runtime_literal_row_commutes
#print axioms runtime_literal_row_commutes

-- Existing pure-Return consumer, reused at its actual full-premise type.
#check @OriginalSourceInterpretation.return_observation_iff
#print axioms OriginalSourceInterpretation.return_observation_iff
#check @OriginalSourceEnvironment.folded_generated_literal_membership
#print axioms OriginalSourceEnvironment.folded_generated_literal_membership
#print YulangClosure.SourceProblem.InferenceSoundness

end YulangClosure.OriginalLiteralCarrierRealizationR241
