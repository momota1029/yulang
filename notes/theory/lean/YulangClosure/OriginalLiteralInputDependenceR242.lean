import YulangClosure.OriginalSourceEnvironment
import YulangClosure.CanonicalLiteralGeneratorR236

/-!
R242 diagnostic of the existing parameterized original consumer. All statements
are universal over the original Sorts; no semantic carriers or SourceProblem
instance are chosen. Record updates below are diagnostic comparisons, not
adopted Yulang interpretations. The same state, complete frame prefix, source
occurrence, literal payload, root, event, scope and shared witness are retained.

R241 has no cached olean in this assignment. Its exact folded Build proof is
reproduced below, without changing its premises or consumer, so this file can
be checked using only existing import artifacts. The unchanged parent
SourceProblem.InferenceSoundness remains open: in particular no arbitrary
solution-to-original-carrier/readout/declaration/ground bridge is proved here.
-/
namespace YulangClosure.OriginalLiteralInputDependenceR242

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment

/-- R241's exact original folded consumer equation, reproduced with attribution. -/
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

/-- The actual decoder is functional: the existential cannot evade a failed
ground fact by selecting another assignment under the same fixed prefix. -/
theorem build_at_fixed_decode (inputs : Inputs s)
    (readout : RuntimeReadout s View) (declarations : LiteralDeclaration s)
    (original : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state)
    (context : Context) (site : Site) (literal : Literal)
    (declared : declarations literal (state.assignment.row site))
    (kind : inputs.valueForm (state.assignment.descriptor ⟨site, .finalRoot⟩) = .ground) :
    Satisfies (foldedLiteralKernel inputs readout declarations original site literal)
      environment (Build context (.literal ⟨site, none⟩ literal)) ↔
      inputs.ground (state.assignment.row site) := by
  rw [folded_literal_build_exact]
  constructor
  · rintro ⟨other, otherDecoded, _, _, primitive⟩
    have same : other = state := Option.some.inj (otherDecoded.symm.trans decoded)
    subst other
    exact primitive
  · intro primitive
    exact ⟨state, decoded, declared, kind, primitive⟩

/-- Only ground changes. Every other Inputs projection is definitionally the
original projection; restoring ground restores the complete original record. -/
theorem ground_update_preserves_other_fields (inputs : Inputs s)
    (ground : ValueRow s → Prop) :
    ({ {inputs with ground := ground} with ground := inputs.ground } : Inputs s) = inputs := rfl

/-- Explicit same-state diagnostic pair. The hypotheses fix the declaration
and classification but assume neither LiteralAtom nor any ground/readout law.
All other Inputs fields, Sorts, readout, environment, state and coordinates
are literally shared. This is not a source-qualified semantic counterexample. -/
theorem ground_variation_changes_original_build (inputs : Inputs s)
    (readout : RuntimeReadout s View) (declarations : LiteralDeclaration s)
    (original : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state)
    (context : Context) (site : Site) (literal : Literal)
    (declared : declarations literal (state.assignment.row site))
    (kind : inputs.valueForm (state.assignment.descriptor ⟨site, .finalRoot⟩) = .ground) :
    Satisfies (foldedLiteralKernel {inputs with ground := fun _ => True}
      readout declarations original site literal)
      environment (Build context (.literal ⟨site, none⟩ literal)) ∧
    ¬ Satisfies (foldedLiteralKernel {inputs with ground := fun _ => False}
      readout declarations original site literal)
      environment (Build context (.literal ⟨site, none⟩ literal)) := by
  constructor
  · exact (build_at_fixed_decode {inputs with ground := fun _ => True}
      readout declarations original environment state decoded context site literal declared kind).mpr True.intro
  · intro solved
    exact (build_at_fixed_decode {inputs with ground := fun _ => False}
      readout declarations original environment state decoded context site literal declared kind).mp solved

/-- Apply the diagnostic to the existing source reconstruction edge. No full
SourceProblem instance or sameScoped witness is supplied by this application. -/
theorem ground_variation_changes_original_source_rule (inputs : Inputs s)
    (readout : RuntimeReadout s View) (declarations : LiteralDeclaration s)
    (original : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state)
    (context : Context) (site : Site) (literal : Literal)
    (declared : declarations literal (state.assignment.row site))
    (kind : inputs.valueForm (state.assignment.descriptor ⟨site, .finalRoot⟩) = .ground) :
    SourceJudgment (foldedLiteralKernel {inputs with ground := fun _ => True}
      readout declarations original site literal)
      environment context (.literal ⟨site, none⟩ literal) ∧
    ¬ SourceJudgment (foldedLiteralKernel {inputs with ground := fun _ => False}
      readout declarations original site literal)
      environment context (.literal ⟨site, none⟩ literal) := by
  obtain ⟨yes, no⟩ := ground_variation_changes_original_build inputs readout declarations
    original environment state decoded context site literal declared kind
  exact ⟨(source_reconstruction _ _ _ _).mp yes,
    fun source => no ((source_reconstruction _ _ _ _).mpr source)⟩

/-- The adopted generator has no Inputs argument. This constant-function
equation records its exact independence without changing its definition. -/
theorem canonical_generator_inputs_noninterference (first second : Inputs s)
    (site : Site) (literal : Literal) (root : s.Root) (event : Event s)
    (scope : s.Scope) (witness : s.JointWitness) :
    (fun _ : Inputs s => CanonicalLiteralGeneratorR236.generate
      site literal root event scope witness) first =
    (fun _ : Inputs s => CanonicalLiteralGeneratorR236.generate
      site literal root event scope witness) second := rfl

/-- Decode reads readout and the actual stored frames, never Inputs. Neither
ground nor traceForm can change the decoded assignment while these are fixed. -/
theorem decoder_inputs_noninterference (first second : Inputs s)
    (readout : RuntimeReadout s View) (environment : Environment (Payload s View)) :
    (fun _ : Inputs s => decode readout environment) first =
    (fun _ : Inputs s => decode readout environment) second := rfl

/-- Trace variation preserves every other input, including ground. -/
theorem trace_update_preserves_other_fields (inputs : Inputs s)
    (trace : TraceRow s → TraceForm s) :
    ({ {inputs with traceForm := trace} with traceForm := inputs.traceForm } : Inputs s) = inputs := rfl

/-- The actual original literal kernel is independent of traceForm, even
though the later original Return meaning consumer explicitly reads that field. -/
theorem trace_update_preserves_literal_kernel (inputs : Inputs s)
    (trace : TraceRow s → TraceForm s)
    (readout : RuntimeReadout s View) (declarations : LiteralDeclaration s)
    (original : Kernel (Payload s View)) (site : Site) (literal : Literal) :
    foldedLiteralKernel {inputs with traceForm := trace} readout declarations original site literal =
      foldedLiteralKernel inputs readout declarations original site literal := rfl

/-- Actual existing Return consumer applied to the diagnostic pure-Return
record. Every remaining guard, world, same-event, value and field obligation
is retained under that record's own Meaning; no Meaning invariance is assumed. -/
theorem diagnostic_pure_return_consumer (inputs : Inputs s)
    (returned : TraceRow s) (value : ValueRow s) :
    let varied : Inputs s := {inputs with traceForm := fun _ => .pureReturn value}
    Meaning varied (.trace returned) ↔
      varied.eventCoherent returned.event ∧ (varied.observationGuards returned).Valid ∧
      Meaning varied (.world returned.event) ∧
      (value.event = returned.event ∧ Meaning varied (.value value)) ∧
      (varied.observationFields returned).Holds (Meaning varied) := by
  exact return_observation_iff {inputs with traceForm := fun _ => .pureReturn value} returned value rfl

/-- Applying the actual unfinished consumer makes the separate trace branch
visible. It is not a claim that Meaning is unchanged by a traceForm update. -/
theorem diagnostic_unfinished_consumer (inputs : Inputs s) (returned : TraceRow s) :
    let varied : Inputs s := {inputs with traceForm := fun _ => .unfinished}
    Meaning varied (.trace returned) ↔
      varied.eventCoherent returned.event ∧ (varied.observationGuards returned).Valid ∧
      Meaning varied (.world returned.event) ∧
      (varied.observationFields returned).Holds (Meaning varied) := by
  exact unfinished_observation_iff {inputs with traceForm := fun _ => .unfinished} returned rfl

#check @folded_literal_build_exact
#print axioms folded_literal_build_exact
#check @build_at_fixed_decode
#print axioms build_at_fixed_decode
#check @ground_update_preserves_other_fields
#print axioms ground_update_preserves_other_fields
#check @ground_variation_changes_original_build
#print axioms ground_variation_changes_original_build
#check @ground_variation_changes_original_source_rule
#print axioms ground_variation_changes_original_source_rule
#check @canonical_generator_inputs_noninterference
#print axioms canonical_generator_inputs_noninterference
#check @decoder_inputs_noninterference
#print axioms decoder_inputs_noninterference
#check @trace_update_preserves_other_fields
#print axioms trace_update_preserves_other_fields
#check @trace_update_preserves_literal_kernel
#print axioms trace_update_preserves_literal_kernel
#check @diagnostic_pure_return_consumer
#print axioms diagnostic_pure_return_consumer
#check @diagnostic_unfinished_consumer
#print axioms diagnostic_unfinished_consumer
#check @OriginalSourceInterpretation.return_observation_iff
#print axioms OriginalSourceInterpretation.return_observation_iff
#check @OriginalSourceEnvironment.folded_generated_literal_membership
#print axioms OriginalSourceEnvironment.folded_generated_literal_membership
#print YulangClosure.SourceProblem.InferenceSoundness

end YulangClosure.OriginalLiteralInputDependenceR242
