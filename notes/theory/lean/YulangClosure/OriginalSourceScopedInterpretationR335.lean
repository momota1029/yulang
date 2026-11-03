import YulangClosure.OriginalSourceViewRegistrationR330
import YulangClosure.OriginalSourceAuthenticatedEIR332

/-!
R335: source-owned scoped computation references and primitive declarations.
The tables below are computed from the actual original source, never from a
caller-supplied `declared : Key → Prop`. Resolution retains the full Key and
original Program. Primitive resolution recognizes the ORIGINAL primitive rule
and its exact atom, rather than allocating a semantic law from a numeric ID.

This is a partial interpretation of existing source references, not an EI
interpretation. No independent whole-Call arm inventory, incidence guard law,
Generated instance, licensed EI child or source judgment is manufactured.
Authority: EI §§2–5; original SG source construction; R310/R330 addressing.
-/
namespace YulangClosure.OriginalSourceScopedInterpretationR335

open OriginalSource OriginalScopedClosure OriginalSourceInterpretation
open OriginalSourceEnvironment OriginalSourceChecking
open ComputedCallTypedFormationR310 SourceGraphRegistrationR297

/-- Every entry retains both source children, all local premises and the full
Call position. The resolver selects only its original callee reference. -/
def calleeTable (origin : Declaration) (context : Context) (raw : Source category) : List Request :=
  requests origin context raw

def readCallee (origin : Declaration) (context : Context) (raw : Source category)
    (key : Key) : Option Request :=
  (calleeTable origin context raw).find? (fun request => request.operands.callee.key == key)

/-- The full matching Key and actual original source row are consequences of
resolution, not inputs. This applies to all Source categories. -/
theorem callee_resolution_authentic (origin : Declaration) (context : Context)
    (raw : Source category) (key : Key) (request : Request)
    (found : readCallee origin context raw key = some request) :
    request.operands.callee.key = key ∧
    ∃ (index : Nat) (row : Row),
      (sourceInventory origin context raw)[index]? = some row ∧
      callRecord row = some request.original ∧ prepare request.original = request := by
  have matched := List.find?_some found
  have member := List.mem_of_find?_eq_some found
  exact ⟨beq_iff_eq.mp matched,
    OriginalSourceContractResolutionR311.request_source_row origin context raw request member⟩

/-- Successful resolution gives the original Program; no result/view code is
substituted at the old synthesis endpoint. -/
def calleeProgram (origin : Declaration) (context : Context) (raw : Source category)
    (key : Key) : Option Program :=
  (readCallee origin context raw key).map (fun request => request.original.callee)

/-- This interprets ONLY the resolved old computation reference. The complete
old clause keeps its actual world, optional result, request and future fields. -/
def calleeClause {s : Sorts} {View : Type} (inputs : Inputs s) (state : Decoded s View)
    (origin : Declaration) (context : Context) (raw : Source category)
    (key : Key) (observation : RawObservation s) : Option (Positive s) :=
  (readCallee origin context raw key).map fun request =>
    clause inputs (.trace (observation.atInterface
      (state.interfaces ⟨request.original.calleeSite, .synthesis⟩)))

abbrev relayContext := OriginalModuleContextBindingR315.externalContext
abbrev relaySource := OriginalScopedSourceEventMapR314.Fixture.root
abbrev selected := OriginalInterfacePreservationR328.Selected.request

/-- The previously absent R330 operand lookup is now computed from source.
This is a new source resolver, not a mutation of R330's result-only registry. -/
theorem selected_callee_resolves (origin : Declaration) :
    readCallee origin relayContext relaySource (selected origin).operands.callee.key =
      some (selected origin) := by
  with_unfolding_all
    change (match (selected origin).operands.callee.key == (selected origin).operands.callee.key with
      | true => some (selected origin) | false => _) = _
  simp only [beq_self_eq_true]

/-- All source scopes, captures, locals and children are returned verbatim. -/
theorem selected_program_resolves (origin : Declaration) :
    calleeProgram origin relayContext relaySource (selected origin).operands.callee.key =
      some (selected origin).original.callee := by
  simp only [calleeProgram, selected_callee_resolves, Option.map_some]

theorem selected_clause_resolves {s : Sorts} {View : Type}
    (inputs : Inputs s) (state : Decoded s View) (origin : Declaration)
    (observation : RawObservation s) :
    calleeClause inputs state origin relayContext relaySource
      (selected origin).operands.callee.key observation =
      some (clause inputs (.trace (observation.atInterface
        (state.interfaces ⟨(selected origin).original.calleeSite, .synthesis⟩)))) := by
  simp only [calleeClause, selected_callee_resolves, Option.map_some]

/-- Applied at the original meaning consumer; no guessed membership is needed
for the equivalence, and none is concluded unconditionally. -/
theorem selected_clause_meaning {s : Sorts} {View : Type}
    (inputs : Inputs s) (state : Decoded s View) (origin : Declaration)
    (observation : RawObservation s) :
    (∃ body, calleeClause inputs state origin relayContext relaySource
        (selected origin).operands.callee.key observation = some body ∧
      body.Holds (Meaning inputs)) ↔
    Meaning inputs (.trace (observation.atInterface
      (state.interfaces ⟨(selected origin).original.calleeSite, .synthesis⟩))) := by
  rw [selected_clause_resolves]
  simp only [Option.some.injEq, exists_eq_left']
  exact (meaning_clause inputs _).symm

/-- The source resolver returns the original R159 callee rule tree under its
actual complete prefix, with no reconstructed child or source judgment. -/
theorem selected_callee_erasure (origin : Declaration) :
    (selected origin).original.callee.erase =
      sourceRules (OriginalScopedSourceEventMapR314.Fixture.localContext relayContext)
        OriginalScopedSourceEventMapR314.Fixture.callee := by
  with_unfolding_all rfl

/-- Applied to the UNCHANGED selected outer R159 parent. The callee's actual
lookup is discharged; its original source proof is still required in the SAME
extended environment as all App locals and the inert argument. -/
theorem selected_parent_with_resolved_callee {Value : Type} (kernel : Kernel Value)
    (environment : Environment Value) (origin : Declaration) :
    SourceJudgment kernel environment
      (OriginalScopedSourceEventMapR314.Fixture.localContext relayContext)
      OriginalScopedSourceEventMapR314.Fixture.selected ↔
    ∃ candidate, kernel.admitted environment ⟨1, .viewLogic, 0⟩ candidate ∧
      let after := environment.extend ⟨1, .viewLogic, 0⟩ candidate
      (∀ premise ∈ SourceAppAdmissionR159.appPremises
        (OriginalScopedSourceEventMapR314.Fixture.localContext relayContext) ⟨1, none⟩
        OriginalScopedSourceEventMapR314.Fixture.callee
        OriginalScopedSourceEventMapR314.Fixture.argument, Local kernel after premise) ∧
      (∃ program, calleeProgram origin relayContext relaySource
          (selected origin).operands.callee.key = some program ∧
        Judgment kernel after program.erase) ∧
      SourceJudgment kernel after
        (OriginalScopedSourceEventMapR314.Fixture.localContext relayContext)
        OriginalScopedSourceEventMapR314.Fixture.argument := by
  rw [OriginalScopedSourceEventMapR314.Fixture.selected,
    SourceAppAdmissionR159.app_source_iff]
  simp only [SourceAppAdmissionR159.annotationPremises, List.not_mem_nil, false_implies,
    implies_true, true_and]
  apply exists_congr
  intro candidate
  apply and_congr_right
  intro _
  rw [SourceAppAdmissionR159.app_continuation_iff]
  apply and_congr_right
  intro _
  apply and_congr _ Iff.rfl
  rw [selected_program_resolves]
  simp only [Option.some.injEq, exists_eq_left']
  rw [selected_callee_erasure]
  rfl

/-- An actual source primitive declaration includes the whole original
position and context. Its Nat is copied from the source atom, not allocated. -/
structure ScopedPrimitive where
  position : Position
  site : Site
  context : Context
  identifier : Declaration
  deriving DecidableEq, Repr

def ScopedPrimitive.data (entry : ScopedPrimitive) : Atom :=
  {(atom .primitiveDeclarationInstance entry.site entry.context) with
    declaration := some entry.identifier}

def ScopedPrimitive.program (entry : ScopedPrimitive) : Program :=
  .rule entry.position .primitive entry.site entry.context [.atom entry.data] .nil

def ScopedPrimitive.key (entry : ScopedPrimitive) : Key :=
  (Ref.mk entry.position (.originalComputation ⟨entry.site, .synthesis⟩) : Ref [] .computation).key

/-- Exact original primitive source rule, including all atom fields. Failure
is explicit; no nonprimitive or extra-premise rule is silently coerced. -/
def primitiveOf : Program → Option ScopedPrimitive
  | .rule position .primitive site context [.atom data] .nil => do
      let identifier ← data.declaration
      let entry : ScopedPrimitive := ⟨position, site, context, identifier⟩
      if data = entry.data then some entry else none
  | _ => none

/-- Successful recognition reconstructs the same complete original rule. -/
theorem primitive_recognition_sound (program : Program) (entry : ScopedPrimitive)
    (found : primitiveOf program = some entry) : program = entry.program := by
  unfold primitiveOf at found
  split at found
  · rename_i position site context data
    cases declared : data.declaration with
    | none => simp [declared] at found
    | some identifier =>
      simp only [declared, Option.bind_eq_bind, Option.bind_some] at found
      split at found
      · rename_i same
        cases found
        simp only [ScopedPrimitive.program]
        rw [same]
      · contradiction
  · contradiction

def primitiveTable (origin : Declaration) (context : Context) (raw : Source category) :
    List ScopedPrimitive :=
  (sourceInventory origin context raw).filterMap (fun row => primitiveOf row.program)

/-- The use discriminator is the original primitive source use. R311's
calleePrefix/receipt/result uses are NOT aliases for this primitive atom. -/
def readPrimitive (origin : Declaration) (context : Context) (raw : Source category)
    (key : Key) (use : AtomKind) : Option ScopedPrimitive :=
  if use = .primitiveDeclarationInstance then
    (primitiveTable origin context raw).find? (fun entry => entry.key == key)
  else none

/-- A successful read authenticates the use, every Key field, and an actual
original source row decoded by the exact primitive-rule recognizer. -/
theorem primitive_resolution_authentic (origin : Declaration) (context : Context)
    (raw : Source category) (key : Key) (use : AtomKind) (entry : ScopedPrimitive)
    (found : readPrimitive origin context raw key use = some entry) :
    use = .primitiveDeclarationInstance ∧ entry.key = key ∧
    ∃ row ∈ sourceInventory origin context raw,
      primitiveOf row.program = some entry ∧ row.program = entry.program := by
  unfold readPrimitive at found
  split at found
  · rename_i correct
    have matched := List.find?_some found
    have member := List.mem_of_find?_eq_some found
    obtain ⟨row, present, decoded⟩ := List.mem_filterMap.mp member
    exact ⟨correct, beq_iff_eq.mp matched, row, present, decoded,
      primitive_recognition_sound row.program entry decoded⟩
  · contradiction

theorem primitive_wrong_use (origin : Declaration) (context : Context) (raw : Source category)
    (key : Key) (use : AtomKind) (wrong : use ≠ .primitiveDeclarationInstance) :
    readPrimitive origin context raw key use = none := by
  simp only [readPrimitive, wrong, ↓reduceIte]

/-- This Call is selected from the authenticated make source, including its
outer lambda/receipt/shared/event scopes and statement-block position. -/
def tickRequest (origin : Declaration) : Request :=
  ((requests origin [] OriginalModuleContextBindingR315.makeInitializer)[0]?).get (by
    with_unfolding_all rfl)

def tickPrimitive (origin : Declaration) : ScopedPrimitive :=
  ⟨programPosition (tickRequest origin).original.callee, 4,
    (tickRequest origin).original.context, 12⟩

theorem tick_source_table (origin : Declaration) :
    primitiveTable origin [] OriginalModuleContextBindingR315.makeInitializer =
      [tickPrimitive origin] := by
  with_unfolding_all rfl

theorem tick_original_program (origin : Declaration) :
    (tickPrimitive origin).program = (tickRequest origin).original.callee ∧
    (tickPrimitive origin).key = (tickRequest origin).operands.callee.key := by
  with_unfolding_all constructor <;> rfl

theorem tick_scoped_declaration_resolves (origin : Declaration) :
    readPrimitive origin [] OriginalModuleContextBindingR315.makeInitializer
      (tickRequest origin).operands.callee.key .primitiveDeclarationInstance =
        some (tickPrimitive origin) := by
  rw [readPrimitive, ite_eq_left rfl, tick_source_table, ← (tick_original_program origin).2]
  simp

/-- Full-address falsifier: an altered origin, route, original telescope,
frame, local telescope, sort or slot cannot resolve by numeric endpoint alone.
The statement also detects a mismatch in the original primitive-use tag. -/
theorem tick_resolution_exact (origin : Declaration) (key : Key) (use : AtomKind)
    (entry : ScopedPrimitive) :
    readPrimitive origin [] OriginalModuleContextBindingR315.makeInitializer key use = some entry ↔
      use = .primitiveDeclarationInstance ∧ (tickPrimitive origin).key = key ∧
        tickPrimitive origin = entry := by
  by_cases correct : use = .primitiveDeclarationInstance
  · subst use
    simp [readPrimitive, tick_source_table]
  · simp [readPrimitive, correct]

/-- Actual declaration identity and formal typed response domain are linked
without equating formal response typing to original Inputs/native execution. -/
theorem tick_declaration_and_responses (origin : Declaration) (value : TypedCall.Value) :
    readPrimitive origin [] OriginalModuleContextBindingR315.makeInitializer
      (tickRequest origin).operands.callee.key .primitiveDeclarationInstance =
        some (tickPrimitive origin) ∧
    (tickPrimitive origin).identifier =
      OriginalTickDeclaredResponseR321.tick.declaration.startByte ∧
    PrimitiveOperation.request OriginalTickDeclaredResponseR321.tickKeys
      (OriginalTickDeclaredResponseR321.declaration OriginalTickDeclaredResponseR321.tick) =
        some OriginalTickDeclaredResponseR321.tickOperation ∧
    (TypedCall.ValueTyped Original.emptyContext value
        OriginalTickDeclaredResponseR321.tickOperation.responseType ↔
      ∃ integer views, value = OriginalSourceAuthenticatedEIR332.response integer views) :=
  ⟨tick_scoped_declaration_resolves origin, rfl,
    (OriginalSourceAuthenticatedEIR332.source_response_domain value).1,
    (OriginalSourceAuthenticatedEIR332.source_response_domain value).2⟩

/-- Primitive source proof reduces to its exact original local law; syntax
resolution alone does not prove that law in any environment. -/
theorem primitive_source_iff {Value : Type} (kernel : Kernel Value)
    (environment : Environment Value) (entry : ScopedPrimitive) :
    SourceJudgment kernel environment entry.context
      (.primitive ⟨entry.site, none⟩ entry.identifier) ↔ kernel.atom environment entry.data := by
  simp only [SourceJudgment, sourceRules]
  constructor
  · intro proof
    cases proof with
    | rule locals _ =>
      have primitive :=  locals _ (List.mem_cons_self ..)
      cases primitive with
      | atom fact => exact fact
  · intro fact
    apply Judgment.rule
    · intro premise member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      subst premise
      exact .atom fact
    · exact .nil

/-- Actual R159 application at the source-generated tick Call. This removes
the opaque callee SourceJudgment in favor of the exact source-declared atom;
logical admission, every App local/check and the argument remain unchanged. -/
theorem tick_app_parent_iff {Value : Type} (kernel : Kernel Value)
    (environment : Environment Value) (origin : Declaration) :
    SourceJudgment kernel environment (tickRequest origin).original.context
      (.app ⟨3, none⟩ (.primitive ⟨4, none⟩ 12) (.name ⟨5, none⟩ 1)) ↔
    ∃ candidate, kernel.admitted environment ⟨3, .viewLogic, 0⟩ candidate ∧
      let after := environment.extend ⟨3, .viewLogic, 0⟩ candidate
      (∀ premise ∈ SourceAppAdmissionR159.appPremises (tickRequest origin).original.context
        ⟨3, none⟩ (.primitive ⟨4, none⟩ 12) (.name ⟨5, none⟩ 1), Local kernel after premise) ∧
      kernel.atom after (tickPrimitive origin).data ∧
      SourceJudgment kernel after (tickRequest origin).original.context (.name ⟨5, none⟩ 1) := by
  rw [SourceAppAdmissionR159.app_source_iff]
  simp only [SourceAppAdmissionR159.annotationPremises, List.not_mem_nil, false_implies,
    implies_true, true_and]
  apply exists_congr
  intro candidate
  apply and_congr_right
  intro _
  rw [SourceAppAdmissionR159.app_continuation_iff]
  apply and_congr_right
  intro _
  exact and_congr (primitive_source_iff kernel _ (tickPrimitive origin)) Iff.rfl

end YulangClosure.OriginalSourceScopedInterpretationR335
