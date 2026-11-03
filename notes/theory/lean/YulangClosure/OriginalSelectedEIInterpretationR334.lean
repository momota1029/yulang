import YulangClosure.OriginalSourceEIInterpretationR331

/-!
R334: exact source-side obstruction at the selected R315 Code → Generated edge.

This is an audit/counterexample, NOT an EI interpretation. The actual Call
retains the sourceCallIncidence obligation, but its Atom.declaration is absent.
All locally recorded primitive declaration IDs are computed below, without an
assumed source lookup. R331 already proves that a PrimitiveLeaf by itself does
not authenticate a Key/use; that result is reused, not reimplemented here.

The final countermodel is confined to R330's actual registered result read:
the same code/formation/readback permits incompatible optional result forms.
Its generated guards are deliberately false. Neither choice is claimed to be
EI, source membership, an authentic arm family or a licensed R306 child.
Authority: selected EI §§2–5 and GR1/GR3/GR5. No production authority.
-/
namespace YulangClosure.OriginalSelectedEIInterpretationR334

open OriginalSource OriginalScopedClosure OriginalSourceInterpretation
open OriginalSourceEnvironment OriginalSourceChecking
open ComputedCallTypedFormationR310 OriginalComputedCallInterpretationR311
open OriginalInterfacePreservationR328

abbrev request := Selected.request

def localAtoms (origin : Declaration) : List Atom :=
  (request origin).original.premises.filterMap fun premise => match premise with
    | .atom data => some data
    | _ => none

/-- These are recorded source declarations, not inferred registry identifiers. -/
def localDeclarations (origin : Declaration) : List Declaration :=
  (localAtoms origin).filterMap Atom.declaration

theorem selected_atoms (origin : Declaration) :
    localAtoms origin =
      ([.descriptorFormation, .wholeArgumentCompatibility, .completeCallCertificate,
        .sourceCallIncidence, .callableImage] : List AtomKind).map
          (fun kind => atom kind 1 (request origin).original.context [2, 3]) := by
  rfl

/-- The owning obligation EXISTS. Absence of its declaration is not permission
to drop that obligation or to choose an empty independent arm family. -/
theorem selected_incidence_owner (origin : Declaration) :
    (localAtoms origin)[3]? = some
      (atom .sourceCallIncidence 1 (request origin).original.context [2, 3]) := by
  rfl

theorem selected_local_declarations_empty (origin : Declaration) :
    localDeclarations origin = [] := by
  rfl

theorem no_selected_local_declaration (origin identifier : Declaration) :
    ¬ ∃ data ∈ localAtoms origin, data.declaration = some identifier := by
  intro found
  obtain ⟨data, member, declared⟩ := found
  have present : identifier ∈ localDeclarations origin :=
    List.mem_filterMap.mpr ⟨data, member, declared⟩
  rw [selected_local_declarations_empty] at present
  exact List.not_mem_nil present

/-- Source occurrence, IF key, use and declaration are different obligations.
The first two are computed; no chosen declaration is read from this source row. -/
theorem selected_prefix_owner_gap {s : Sorts} (origin identifier : Declaration)
    (operands : List (Operand s)) :
    ((SourceGraphRegistrationR297.sourceInventory origin
      OriginalModuleContextBindingR315.externalContext
      OriginalScopedSourceEventMapR314.Fixture.root)[13]?).bind callRecord =
        some (request origin).original ∧
    (goal (request origin) .calleePrefix identifier operands).reference =
      (request origin).operands.incidence.key ∧
    (goal (request origin) .calleePrefix identifier operands).signature.declaration = identifier ∧
    ¬ ∃ data ∈ localAtoms origin, data.declaration = some identifier := by
  refine ⟨Selected.actual_request origin, ?_, rfl,
    no_selected_local_declaration origin identifier⟩
  rfl

/-- Applying the source audit at the real generated result read. Formation and
readback do not supply the missing local primitive declaration. All caller arms
remain verbatim in the registered code; their completeness is not inferred. -/
theorem registered_result_owner_gap {s : Sorts} {View : Type}
    {origin : Declaration} {declared : Key → Prop}
    (state : Decoded s View)
    (definition : OriginalSourceViewRegistrationR330.Definition origin declared)
    (identifier : Declaration) :
    Formed declared definition.code.2 ∧
    OriginalSourceViewRegistrationR330.resolve state
      (OriginalSourceViewRegistrationR330.register definition)
      (OriginalSourceViewRegistrationR330.owner origin)
      (.inr (request origin).generatedResult.key) =
        some (.inr (Selected.resultCode origin definition.arms)) ∧
    ¬ ∃ data ∈ localAtoms origin, data.declaration = some identifier :=
  ⟨OriginalSourceViewRegistrationR330.definition_formed definition,
    OriginalSourceViewRegistrationR330.generated_resolution state definition,
    no_selected_local_declaration origin identifier⟩

/-- Negative probes only. False guards forbid interpreting either arbitrary
result form as a constructed source witness. No original Inputs is changed. -/
def resultProbe {s : Sorts} (form : TraceForm s) : Generated s Selected.Code where
  guards := fun _ _ => ⟨False, False, False, False, False, False, False, False, False, False⟩
  form := fun _ _ => form
  fields := fun _ _ => .guard False

theorem result_probe_rejected {s : Sorts} (base : Inputs s) (form : TraceForm s)
    (code : Selected.Code) (raw : RawObservation s) :
    ¬ Meaning (inputs base (resultProbe form))
      (.trace ((upRaw raw).atInterface (.inr code))) := by
  intro member
  have body := (generated_meaning_iff base (resultProbe form) code raw).mp member
  exact body.1.2.1

/-- Concrete GR3 falsifier at the ACTUAL R330 consumer: the same formed,
registered result code does not determine whether the whole Call has returned.
Both probes preserve every old meaning, but neither has generated membership.
Thus conservation/readback cannot furnish the R306 source child or its result
incidence. This refutes only that proposed implication, not EI-Intro. -/
theorem registered_read_does_not_determine_result {s : Sorts} {View : Type}
    {origin : Declaration} {declared : Key → Prop}
    (base : Inputs s) (state : Decoded s View)
    (definition : OriginalSourceViewRegistrationR330.Definition origin declared)
    (raw : RawObservation s) (returned : ValueRow s) :
    OriginalSourceViewRegistrationR330.resolve state
      (OriginalSourceViewRegistrationR330.register definition)
      (OriginalSourceViewRegistrationR330.owner origin)
      (.inr (request origin).generatedResult.key) = some (.inr definition.code) ∧
    (inputs base (resultProbe .unfinished)).traceForm
      ((upRaw raw).atInterface (.inr definition.code)) = .unfinished ∧
    (inputs base (resultProbe (.pureReturn returned))).traceForm
      ((upRaw raw).atInterface (.inr definition.code)) = .pureReturn (upValue returned) ∧
    (inputs base (resultProbe .unfinished)).traceForm
      ((upRaw raw).atInterface (.inr definition.code)) ≠
    (inputs base (resultProbe (.pureReturn returned))).traceForm
      ((upRaw raw).atInterface (.inr definition.code)) ∧
    (∀ q : Query s, Meaning (inputs base (resultProbe .unfinished)) (upQuery q) ↔ Meaning base q) ∧
    (∀ q : Query s, Meaning (inputs base (resultProbe (.pureReturn returned))) (upQuery q) ↔ Meaning base q) := by
  refine ⟨OriginalSourceViewRegistrationR330.generated_resolution state definition,
    rfl, rfl, ?_, old_meaning_iff base (resultProbe .unfinished),
    old_meaning_iff base (resultProbe (.pureReturn returned))⟩
  intro same
  cases same

end YulangClosure.OriginalSelectedEIInterpretationR334
