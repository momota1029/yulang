import YulangClosure.PaperCombinedExecution
import YulangClosure.PaperTypeApplicationPreservation

/-!
Concrete discriminators for the manuscript's structural eliminations.
False selects the left interface; true selects the right. Bottom examples use
an explicit open assumption and do not assert a closed-graph canonical form.
-/
namespace YulangClosure.PaperTypes.PaperEliminationExamples

/-- One raw function has two distinct callable interfaces by ignoring its input. -/
theorem distinct_callable_interfaces (d : DeclarationTable) (g : GraphEnvironment)
    (e : TypeEnvironment) (profile : AdapterMetadata) :
    PaperValueTyped d g e
      (.both (.lambda .value profile 0 (.ret (.literal (.integer 7)))))
      (.intersection (.callable (.base .int) (.base .int))
        (.callable (.base .bool) (.base .int))) :=
  .both (.valueLambda (.ret .literal)) (.valueLambda (.ret .literal))

/-- A fixed intersection slot prevents false from selecting the right type. -/
theorem choose_false_rejects_right (d : DeclarationTable) (g : GraphEnvironment)
    (e : TypeEnvironment) :
    ¬ PaperComputationTyped d g (.intersection (.base .int) (.base .bool) :: e)
      (.choose (.variable 0) false) (.base .bool) := by
  intro hc
  cases hc with
  | chooseLeft hv =>
      cases hv with
      | «variable» lookup => simp [lookupTypeEnvironment] at lookup

/-- The complementary fixed slot detects reversing true's polarity. -/
theorem choose_true_rejects_left (d : DeclarationTable) (g : GraphEnvironment)
    (e : TypeEnvironment) :
    ¬ PaperComputationTyped d g (.intersection (.base .int) (.base .bool) :: e)
      (.choose (.variable 0) true) (.base .int) := by
  intro hc
  cases hc with
  | chooseRight hv =>
      cases hv with
      | «variable» lookup => simp [lookupTypeEnvironment] at lookup

/-- The operational payload is identical for both evidence projections. -/
theorem choose_same_payload (value : Value) (side : Bool) :
    PaperCoreStep.step (.choose (.both value) side) = some (.ret value) := rfl

/-- The free replacement is lifted through the lambda's term binder. -/
theorem choose_term_binder_capture (profile : AdapterMetadata) (side : Bool) :
    termSubstituteValue (fun _ => .variable 0)
      (.lambda .value profile 7 (.choose (.variable 1) side)) =
      some (.lambda .value profile 7 (.choose (.variable 1) side)) := by
  simp [termSubstituteValue, supportedTermValue, supportedTermComputation,
    replaceTermValue, replaceTermComputation, liftTermSubstitution, renameTermValue]

/-- Bottom elimination also substitutes through the response binder. -/
theorem absurd_response_binder_capture :
    termSubstituteValue (fun _ => .variable 0)
      (.continuation [] 8 (.absurd (.variable 1))) =
      some (.continuation [] 8 (.absurd (.variable 1))) := by
  simp [termSubstituteValue, supportedTermValue, supportedTermComputation,
    replaceTermValue, replaceTermComputation, liftTermSubstitution, renameTermValue]

/-- Replacement type arguments stay free under a surrounding universal binder. -/
theorem absurd_type_binder_capture :
    termSubstituteValue (fun _ => .typeApplication (.variable 0) (.var 0))
      (.typeAbstraction (.delay (.absurd (.variable 0)))) =
      some (.typeAbstraction (.delay (.absurd
        (.typeApplication (.variable 0) (.var 1))))) := by
  simp [termSubstituteValue, supportedTermValue, supportedTermComputation,
    replaceTermValue, replaceTermComputation, shiftTermSubstitution,
    mapPaperValue, shiftTypeSubstitution, subst]

/-- An explicit Bottom assumption permits any result but supplies no raw step. -/
theorem absurd_open_typed_no_step (d : DeclarationTable) (g : GraphEnvironment)
    (e : TypeEnvironment) (resultType : Ty) :
    PaperComputationTyped d g (.bottom :: e) (.absurd (.variable 0)) resultType ∧
      PaperCoreStep.step (.absurd (.variable 0)) = none :=
  ⟨.absurd (.variable rfl), rfl⟩

/-- The new principal step is available through the unchanged combined machine. -/
theorem choose_combined_step (d : DeclarationTable) (binder : TermName)
    (value : Value) (side : Bool) (stack : List Computation) :
    PaperCombinedExecution.controlStep d binder ⟨.choose (.both value) side, stack⟩ =
      some ⟨.ret value, stack⟩ :=
  PaperCombinedExecution.controlStep_extends
    (PaperPerformLetExecution.controlStep_extends
      (PaperTupleSplitExecution.controlStep_extends rfl))

/-- The final result and arbitrary stored let bodies are preserved together. -/
theorem choose_combined_preservation {d g e value side stack resultType} {binder : TermName}
    (ht : PaperCoreControl.StateTyped d g e ⟨.choose (.both value) side, stack⟩ resultType) :
    PaperCoreControl.StateTyped d g e ⟨.ret value, stack⟩ resultType :=
  PaperCombinedExecution.preservation ht (choose_combined_step d binder value side stack)

/-- The frozen type-beta theorem composes with Force and the new choose redex. -/
theorem type_beta_choose_return {d g e value side argument resultType}
    (hc : PaperComputationTyped d g e
      (.force (.typeApplication
        (.typeAbstraction (.delay (.choose (.both value) side))) argument)) resultType) :
    let value' := mapPaperValue (instantiateSubstitution [argument]) value
    PaperTypeApplicationPreservation.typeBetaForce
        (.force (.typeApplication
          (.typeAbstraction (.delay (.choose (.both value) side))) argument)) =
        some (.force (.delay (.choose (.both value') side))) ∧
      PaperComputationTyped d g e (.ret value') resultType := by
  have hb := PaperTypeApplicationPreservation.force_typeBeta_delay hc
  dsimp at hb ⊢
  have hchoose : PaperComputationTyped d g e
      (.choose (.both (mapPaperValue (instantiateSubstitution [argument]) value)) side)
      resultType := by
    simpa only [mapPaperComputation, mapPaperValue] using hb.2.2.2
  exact ⟨by simpa only [mapPaperComputation, mapPaperValue] using hb.1,
    PaperCoreStep.preservation hchoose rfl⟩

end YulangClosure.PaperTypes.PaperEliminationExamples
