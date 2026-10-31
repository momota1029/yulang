import YulangClosure.SourceInternalChoiceR77

/-!
R78 integrates the R77 source alignment into the two inventory consumer reads.
The original complete call list is retained; the selected call is joined by its
list index, separately from its owner-local expression index. The Apply checking
coordinate and module Name/target coordinate remain independent. This is a
finite declaration model, not authenticated Rust extraction or a genuine R66 Root.
-/
namespace YulangClosure.IntegratedSourceAlignmentR78
open SourceInternalContextR55 ProviderNativeContextR57 SourceInternalChoiceR77

variable {S T : Type} [DecidableEq S] [DecidableEq T]

/-- The root consumer reads the enclosing Apply at the retained expression.
Its result is compared to checking, never to the DefinitionUse occurrence. -/
def applyCoordinate (source : OwnerSource (Key S T)) (call : SourceCall (Key S T)) :
    Option (Key S T) := do
  let node ← source.expressions[call.expression]?
  if node.form = .apply call.callee call.argument then some node.occurrence else none

/-- The second consumer read resolves the exact Name and module target through
the same owner-local Group peel used by capture. -/
def nameTarget (source : OwnerSource (Key S T)) (call : SourceCall (Key S T)) :
    Option (Key S T × Key S T) :=
  peel source.expressions (source.expressions.length + 1) [] call.callee

def rootCoordinates (source : OwnerSource (Key S T))
    (calls : List (SourceCall (Key S T))) (callIndex : Nat)
    (u : Use Nat (Key S T)) (receiving target : Key S T) : Bool :=
  match calls[callIndex]? with
  | none => false
  | some call => decide (source.owner = receiving ∧ call.owner = receiving ∧
      applyCoordinate source call = some call.checking ∧
      nameTarget source call = some (u.occurrence, target))

structure Captured (s : Source S T) (source : OwnerSource (Key S T))
    (calls : List (SourceCall (Key S T))) (callIndex : Nat)
    (u : Use Nat (Key S T)) (receiving target : Key S T) where
  aligned : AlignedChoice s source calls u receiving target
  indexed : calls[callIndex]? = some aligned.alignment.call

/-- Neither consumer success nor a selected plan/registration is an input.
The R77 constructor checks the complete inventories before the indexed join. -/
def capture (s : Source S T) (source : OwnerSource (Key S T))
    (calls : List (SourceCall (Key S T))) (callIndex : Nat)
    (u : Use Nat (Key S T)) (receiving target : Key S T) :
    Option (Captured s source calls callIndex u receiving target) := do
  let aligned ← constructAligned s source calls u receiving target
  if indexed : calls[callIndex]? = some aligned.alignment.call then
    some ⟨aligned, indexed⟩
  else none

theorem alignment_apply_equation (source : OwnerSource (Key S T))
    (calls : List (SourceCall (Key S T))) (u : Use Nat (Key S T))
    (receiving target : Key S T) (a : Alignment source calls u receiving target) :
    applyCoordinate source a.call = some a.call.checking := by
  simp only [applyCoordinate, a.applyIndexed, Option.bind_some, if_pos a.applied]
  exact congrArg some a.checking

theorem alignment_name_target_equation (source : OwnerSource (Key S T))
    (calls : List (SourceCall (Key S T))) (u : Use Nat (Key S T))
    (receiving target : Key S T) (a : Alignment source calls u receiving target) :
    nameTarget source a.call = some (u.occurrence, target) := by
  exact a.resolved

/-- The root consumer succeeds by reducing both concrete reads. Its success
is a conclusion, not an assumed premise or a stored Captured field. -/
theorem capture_root_coordinates (s : Source S T) (source : OwnerSource (Key S T))
    (calls : List (SourceCall (Key S T))) (callIndex : Nat)
    (u : Use Nat (Key S T)) (receiving target : Key S T)
    (c : Captured s source calls callIndex u receiving target) :
    rootCoordinates source calls callIndex u receiving target = true := by
  have applyEq := alignment_apply_equation source calls u receiving target c.aligned.alignment
  have nameEq := alignment_name_target_equation source calls u receiving target c.aligned.alignment
  simp [rootCoordinates, c.indexed, c.aligned.alignment.sourceOwner,
    c.aligned.alignment.callOwner, applyEq, nameEq]

/-- The exact same use and target feed the unchanged R65/R66 parent seam. -/
theorem capture_applies_r66 (s : Source S T)
    (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T)
    (source : OwnerSource (Key S T)) (calls : List (SourceCall (Key S T)))
    (callIndex : Nat) (u : Use Nat (Key S T)) (receiving target : Key S T)
    (c : Captured s source calls callIndex u receiving target) :
    c.aligned.selectedUse.use = u ∧
    (OccurrenceQualifiedFactReadersR65.internalInputs s inventory u.occurrence).plan (use u) =
      some (SourceInternalContextR55.plan c.aligned.choice.plan) ∧
    OccurrenceQualifiedConsumerR66.ownerSelection s target c.aligned.choice.plan.targetRootComponent =
      some c.aligned.choice.origin ∧
    s.parameterRecipes[c.aligned.choice.formal.recipePosition]? =
      some c.aligned.choice.formal.parameter := by
  exact ⟨c.aligned.exactUse, choice_applies_r66 s inventory u receiving target c.aligned.choice⟩

theorem capture_exact_joins (s : Source S T) (source : OwnerSource (Key S T))
    (calls : List (SourceCall (Key S T))) (callIndex : Nat)
    (u : Use Nat (Key S T)) (receiving target : Key S T)
    (c : Captured s source calls callIndex u receiving target) :
    calls[callIndex]? = some c.aligned.alignment.call ∧
    alignedCalls source calls u receiving target = [c.aligned.alignment.call] ∧
    alignedUses s source calls receiving target = [c.aligned.selectedUse] ∧
    PeelsTo source.expressions c.aligned.alignment.call.callee u.occurrence target := by
  exact ⟨c.indexed, c.aligned.alignment.uniqueCall, c.aligned.uniqueUse,
    (alignment_has_name source calls u receiving target c.aligned.alignment).2.2⟩

theorem construction_certifies (s : Source S T)
    (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T)
    (source : OwnerSource (Key S T)) (calls : List (SourceCall (Key S T)))
    (callIndex : Nat) (u : Use Nat (Key S T)) (receiving target : Key S T) :
    match capture s source calls callIndex u receiving target with
    | none => True
    | some c =>
      rootCoordinates source calls callIndex u receiving target = true ∧
      applyCoordinate source c.aligned.alignment.call = some c.aligned.alignment.call.checking ∧
      nameTarget source c.aligned.alignment.call = some (u.occurrence, target) ∧
      (OccurrenceQualifiedFactReadersR65.internalInputs s inventory u.occurrence).plan (use u) =
        some (SourceInternalContextR55.plan c.aligned.choice.plan) ∧
      OccurrenceQualifiedConsumerR66.ownerSelection s target c.aligned.choice.plan.targetRootComponent =
        some c.aligned.choice.origin ∧
      s.parameterRecipes[c.aligned.choice.formal.recipePosition]? =
        some c.aligned.choice.formal.parameter := by
  cases capture s source calls callIndex u receiving target with
  | none => trivial
  | some c =>
    exact ⟨capture_root_coordinates s source calls callIndex u receiving target c,
      alignment_apply_equation source calls u receiving target c.aligned.alignment,
      alignment_name_target_equation source calls u receiving target c.aligned.alignment,
      (capture_applies_r66 s inventory source calls callIndex u receiving target c).2⟩

/-! The unrelated call remains at index 0; selected call index 1 is distinct
from selected expression index 2. Name 100 remains distinct from Apply 102. -/
def unrelatedCall : SourceCall (Key Nat Nat) := { fixtureCall with owner := .source 999 }
def completeCalls : List (SourceCall (Key Nat Nat)) := [unrelatedCall, fixtureCall]
def fixtureCaptured := capture fixture fixtureOwnerSource completeCalls 1 fixtureUse (.source 10) (.source 1)

theorem finite_distinct_coordinates_and_retained_calls :
    fixtureUse.occurrence ≠ fixtureCall.checking ∧
    completeCalls[0]? = some unrelatedCall ∧
    completeCalls[1]? = some fixtureCall ∧
    applyCoordinate fixtureOwnerSource fixtureCall = some fixtureCall.checking ∧
    nameTarget fixtureOwnerSource fixtureCall = some (fixtureUse.occurrence, .source 1) ∧
    fixtureCaptured.isSome = true ∧
    rootCoordinates fixtureOwnerSource completeCalls 1 fixtureUse (.source 10) (.source 1) = true := by
  decide

theorem finite_capture_rejects_bad_joins :
    (capture fixture fixtureOwnerSource [fixtureCall, fixtureCall] 0 fixtureUse
      (.source 10) (.source 1)).isSome = false ∧
    (capture {fixture with plans := fixture.plans ++ fixture.plans}
      fixtureOwnerSource completeCalls 1 fixtureUse (.source 10) (.source 1)).isSome = false ∧
    (capture fixture {fixtureOwnerSource with owner := .source 999} completeCalls 1
      fixtureUse (.source 10) (.source 1)).isSome = false ∧
    (capture fixture fixtureOwnerSource [unrelatedCall] 0 fixtureUse
      (.source 10) (.source 1)).isSome = false ∧
    (capture fixture fixtureOwnerSource completeCalls 1 fixtureUse
      (.source 10) (.source 999)).isSome = false ∧
    (capture fixture fixtureOwnerSource completeCalls 1
      {fixtureUse with occurrence := .source 102} (.source 10) (.source 1)).isSome = false ∧
    (capture fixture fixtureOwnerSource [{fixtureCall with checking := .source 100}] 0
      fixtureUse (.source 10) (.source 1)).isSome = false ∧
    (capture fixture fixtureOwnerSource completeCalls 0 fixtureUse
      (.source 10) (.source 1)).isSome = false ∧
    (capture fixture fixtureOwnerSource completeCalls 2 fixtureUse
      (.source 10) (.source 1)).isSome = false := by
  decide

theorem finite_root_rejects_bad_coordinates :
    rootCoordinates fixtureOwnerSource completeCalls 0 fixtureUse (.source 10) (.source 1) = false ∧
    rootCoordinates fixtureOwnerSource completeCalls 2 fixtureUse (.source 10) (.source 1) = false ∧
    rootCoordinates fixtureOwnerSource [{fixtureCall with checking := .source 100}] 0
      fixtureUse (.source 10) (.source 1) = false ∧
    rootCoordinates fixtureOwnerSource completeCalls 1 fixtureUse (.source 10) (.source 999) = false ∧
    rootCoordinates fixtureOwnerSource completeCalls 1 {fixtureUse with occurrence := .source 102}
      (.source 10) (.source 1) = false := by
  decide

end YulangClosure.IntegratedSourceAlignmentR78
