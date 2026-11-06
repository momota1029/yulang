import Yulang.CaseDataTerms
import Yulang.NominalListViews

/-!
# Resolved finite list literals with spread in any position

Every source occurrence is evaluated once in written order. An ordinary
element has an explicitly supplied pure conversion; a resolved list spread
contributes its already typed contents without inserting a hidden map. The
result is the concatenation of those chunks, retaining order and duplicates.

This is a common finite-list stage, not a source rule deciding whether any
Fold value may be spread or whether spreading an existing nominal list
creates fresh deferred cast sites. Those questions are recorded separately.
The conversion-value contract is explicit; conversion selection, weak-variable
solving and generation of source construction sites are not inferred here.
The observation bridge uses the existing finite-list Fold/Index views; it
does not select role dictionaries or replace the public integer-index error
protocol. The concrete leaves are the existing finite `CaseDataTerms` syntax.
-/

namespace Yulang.NominalListSpread

open CaseValues EvaluationTrace

inductive Part (Source Conversion : Type) where
  | element : Source → Conversion → Part Source Conversion
  | spread : Source → Part Source Conversion
  deriving Repr

def Part.source : Part Source Conversion → Source
  | .element code _ | .spread code => code

/-- Only ordinary element sites carry a chosen conversion. -/
def expand (convert : Conversion → Value F → Value F) (expectedList : R) :
    Part Source Conversion → Value F → Except R (List (Value F))
  | .element _ conversion, value => .ok [convert conversion value]
  | .spread _, .list values => .ok values
  | .spread _, _ => .error expectedList

def runPart (source : Source → Logged E R (Value F))
    (convert : Conversion → Value F → Value F) (expectedList : R)
    (part : Part Source Conversion) : Logged E R (List (Value F)) :=
  (source part.source).bind fun value => Logged.ofResult (expand convert expectedList part value)

def run (source : Source → Logged E R (Value F))
    (convert : Conversion → Value F → Value F) (expectedList : R) :
    List (Part Source Conversion) → Logged E R (List (Value F))
  | [] => Logged.ofResult (.ok [])
  | part :: rest => (runPart source convert expectedList part).bind fun first =>
      (run source convert expectedList rest).bind fun last => Logged.ofResult (.ok (first ++ last))

/-- One copy of each source observation, in source occurrence order. -/
def sourceTrace (source : Source → Logged E R (Value F)) (parts : List (Part Source Conversion)) : List E :=
  parts.flatMap fun part => (source part.source).trace

/-- Declarative contribution of one already evaluated source occurrence. -/
inductive PartMeaning (convert : Conversion → Value F → Value F) :
    Part Source Conversion → Value F → List (Value F) → Prop where
  | element : PartMeaning convert (.element code conversion) value [convert conversion value]
  | spread : PartMeaning convert (.spread code) (.list values) values

/-- The syntax determines a list of chunks, independently of `run`.
Concatenating them keeps every element in its written position. -/
inductive Meaning (source : Source → Logged E R (Value F))
    (convert : Conversion → Value F → Value F) :
    List (Part Source Conversion) → List (List (Value F)) → Prop where
  | nil : Meaning source convert [] []
  | cons : (source part.source).result = .ok value → PartMeaning convert part value chunk →
      Meaning source convert rest chunks → Meaning source convert (part :: rest) (chunk :: chunks)

theorem part_meaning_evaluates (source : Source → Logged E R (Value F))
    (convert : Conversion → Value F → Value F) (expectedList : R)
    (evaluated : (source part.source).result = .ok value)
    (meaning : PartMeaning convert part value chunk) :
    runPart source convert expectedList part = ⟨(source part.source).trace, .ok chunk⟩ := by
  cases meaning <;> simp [runPart, Logged.bind, evaluated, expand, Logged.ofResult]

theorem meaning_evaluates (source : Source → Logged E R (Value F))
    (convert : Conversion → Value F → Value F) (expectedList : R)
    (meaning : Meaning source convert parts chunks) :
    run source convert expectedList parts = ⟨sourceTrace source parts, .ok chunks.flatten⟩ := by
  induction meaning with
  | nil => rfl
  | cons evaluated expanded tail ih =>
      rw [run, part_meaning_evaluates source convert expectedList evaluated expanded, Logged.bind_ok, ih]
      simp [Logged.bind, Logged.ofResult, sourceTrace]

def SourceSound (SourceTyped : Source → Ty F → Prop) (source : Source → Logged E R (Value F)) : Prop :=
  ∀ code target, SourceTyped code target → ∃ value, (source code).result = .ok value ∧ target value

def ConversionSound (ConversionTyped : Conversion → Ty F → Ty F → Prop)
    (convert : Conversion → Value F → Value F) : Prop :=
  ∀ code input target, ConversionTyped code input target →
    ∀ value, input value → target (convert code value)

inductive PartTyping (SourceTyped : Source → Ty F → Prop)
    (ConversionTyped : Conversion → Ty F → Ty F → Prop) : Part Source Conversion → Ty F → Prop where
  | element : SourceTyped code input → ConversionTyped conversion input target →
      PartTyping SourceTyped ConversionTyped (.element code conversion) target
  | spread : SourceTyped code (Ty.list target) → PartTyping SourceTyped ConversionTyped (.spread code) target

inductive Typing (SourceTyped : Source → Ty F → Prop)
    (ConversionTyped : Conversion → Ty F → Ty F → Prop) : List (Part Source Conversion) → Ty F → Prop where
  | nil : Typing SourceTyped ConversionTyped [] target
  | cons : PartTyping SourceTyped ConversionTyped part target → Typing SourceTyped ConversionTyped rest target →
      Typing SourceTyped ConversionTyped (part :: rest) target

theorem typing_has_meaning (source : Source → Logged E R (Value F))
    (convert : Conversion → Value F → Value F) (sources : SourceSound SourceTyped source)
    (typed : Typing SourceTyped ConversionTyped parts target) :
    ∃ chunks, Meaning source convert parts chunks := by
  induction typed with
  | nil => exact ⟨[], .nil⟩
  | cons head tail ih =>
      obtain ⟨chunks, restMeaning⟩ := ih
      cases head with
      | element sourceTyped _ =>
          obtain ⟨value, evaluated, _⟩ := sources _ _ sourceTyped
          exact ⟨_ :: chunks, .cons evaluated .element restMeaning⟩
      | spread sourceTyped =>
          obtain ⟨value, evaluated, valueValid⟩ := sources _ _ sourceTyped
          cases value with
          | list values => exact ⟨values :: chunks, .cons evaluated .spread restMeaning⟩
          | _ => cases valueValid

/-- This is value safety for a chosen element type, not nominal covariance
or an inference procedure that chooses that type. -/
theorem part_typing_evaluates (source : Source → Logged E R (Value F))
    (convert : Conversion → Value F → Value F) (expectedList : R)
    (sources : SourceSound SourceTyped source) (conversions : ConversionSound ConversionTyped convert)
    (typed : PartTyping SourceTyped ConversionTyped part target) :
    ∃ values, runPart source convert expectedList part =
      ⟨(source part.source).trace, .ok values⟩ ∧ ∀ value ∈ values, target value := by
  cases typed with
  | @element code input conversion _ sourceTyped conversionTyped =>
      obtain ⟨value, evaluated, valueValid⟩ := sources _ _ sourceTyped
      refine ⟨[convert conversion value], ?_, ?_⟩
      · simp [runPart, Part.source, Logged.bind, evaluated, expand, Logged.ofResult]
      · intro item member
        have same : item = convert conversion value := by simpa using member
        subst item
        exact conversions _ _ _ conversionTyped value valueValid
  | spread sourceTyped =>
      obtain ⟨value, evaluated, valueValid⟩ := sources _ _ sourceTyped
      cases value with
      | list values =>
          exact ⟨values, by simp [runPart, Part.source, Logged.bind, evaluated, expand, Logged.ofResult], valueValid⟩
      | _ => cases valueValid

/-- All independently typed source expressions succeed. The final trace is
exactly one source trace per occurrence, left to right; flattening and pure
conversions contribute no repeated source evaluation. -/
theorem typing_evaluates (source : Source → Logged E R (Value F))
    (convert : Conversion → Value F → Value F) (expectedList : R)
    (sources : SourceSound SourceTyped source) (conversions : ConversionSound ConversionTyped convert)
    (typed : Typing SourceTyped ConversionTyped parts target) :
    ∃ values, run source convert expectedList parts = ⟨sourceTrace source parts, .ok values⟩ ∧
      ∀ value ∈ values, target value := by
  induction typed with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons head tail ih =>
      obtain ⟨first, firstEval, firstValid⟩ := part_typing_evaluates source convert expectedList sources conversions head
      obtain ⟨last, lastEval, lastValid⟩ := ih
      refine ⟨first ++ last, ?_, ?_⟩
      · simp [run, firstEval, lastEval, Logged.bind, Logged.ofResult, sourceTrace]
      · intro value member
        exact (List.mem_append.mp member).elim (firstValid value) (lastValid value)

theorem spread_values_unchanged (source : Source → Logged E R (Value F))
    (convert : Conversion → Value F → Value F) (expectedList : R)
    (code : Source) (events : List E) (values : List (Value F))
    (evaluated : source code = ⟨events, .ok (.list values)⟩) :
    runPart source convert expectedList (.spread code) = ⟨events, .ok values⟩ := by
  simp [runPart, Part.source, evaluated, Logged.bind, expand, Logged.ofResult]

/-- The middle spread may contain any finite number of values, including
zero. Its expression still contributes its complete observations once. -/
theorem middle_spread (source : Source → Logged E R (Value F))
    (convert : Conversion → Value F → Value F) (expectedList : R)
    (first spread last : Source) (firstConversion lastConversion : Conversion)
    (firstEvents spreadEvents lastEvents : List E) (firstValue lastValue : Value F)
    (spreadValues : List (Value F))
    (firstEval : source first = ⟨firstEvents, .ok firstValue⟩)
    (spreadEval : source spread = ⟨spreadEvents, .ok (.list spreadValues)⟩)
    (lastEval : source last = ⟨lastEvents, .ok lastValue⟩) :
    run source convert expectedList [.element first firstConversion, .spread spread, .element last lastConversion] =
      ⟨firstEvents ++ spreadEvents ++ lastEvents,
        .ok ([convert firstConversion firstValue] ++ spreadValues ++ [convert lastConversion lastValue])⟩ := by
  simp [run, runPart, Part.source, firstEval, spreadEval, lastEval, Logged.bind, expand, Logged.ofResult,
    List.append_assoc]

theorem failed_source_skips_rest (source : Source → Logged E R (Value F))
    (convert : Conversion → Value F → Value F) (expectedList : R) (part : Part Source Conversion)
    (rest : List (Part Source Conversion)) (events : List E) (error : R)
    (failed : source part.source = ⟨events, .error error⟩) :
    run source convert expectedList (part :: rest) = ⟨events, .error error⟩ := by
  simp [run, runPart, failed, Logged.bind]

abbrev DataPart (F Conversion : Type) := Part (CaseDataTerms.Expr F) Conversion

def eval (convert : Conversion → Value F → Value F) (environment : Bindings F)
    (parts : List (DataPart F Conversion)) : CaseDataTerms.Result F :=
  (run (CaseDataTerms.eval environment) convert CaseDataTerms.Error.expectedList parts).bind
    fun values => CaseDataTerms.pure (.list values)

theorem data_typing_evaluates (convert : Conversion → Value F → Value F)
    (conversions : ConversionSound ConversionTyped convert)
    (typed : Typing (CaseDataTerms.Typing types) ConversionTyped parts target)
    (environment : Bindings F) (valid : BindingsHold types environment) :
    ∃ values, eval convert environment parts =
      ⟨sourceTrace (CaseDataTerms.eval environment) parts, .ok (.list values)⟩ ∧
      Ty.list target (.list values) := by
  obtain ⟨values, evaluated, valueValid⟩ := typing_evaluates (CaseDataTerms.eval environment) convert
    CaseDataTerms.Error.expectedList
    (fun _ _ expressionTyped => CaseDataTerms.typing_evaluates expressionTyped environment valid)
    conversions typed
  exact ⟨values, by simp [eval, evaluated, Logged.bind, CaseDataTerms.pure, Logged.ofResult], valueValid⟩

/-- Metadata comes from resolved nominal construction; no list identity or
parameter type is selected by this wrapper. -/
def built (name site : Nat) (types : Fin parameters → NominalConstructions.ParameterType)
    (values : List (Value F)) : NominalConstructionRuntime.Built parameters (Value F) :=
  ⟨.listLiteral name, site, types, values⟩

def evalBuilt (convert : Conversion → Value F → Value F) (environment : Bindings F)
    (name site : Nat) (types : Fin parameters → NominalConstructions.ParameterType)
    (parts : List (DataPart F Conversion)) :
    Logged (CaseEvaluation.Event (CaseDataTerms.Expr F)) CaseDataTerms.Error
      (NominalConstructionRuntime.Built parameters (Value F)) :=
  (run (CaseDataTerms.eval environment) convert CaseDataTerms.Error.expectedList parts).bind
    fun values => Logged.ofResult (.ok (built name site types values))

/-- The concrete list value and nominal list views use the very same
flattened vector. Fold preserves its order; cursor and Index agree at every
natural position, including positions beyond the final element. -/
theorem constructed_views (convert : Conversion → Value F → Value F) (environment : Bindings F)
    (name site : Nat) (types : Fin parameters → NominalConstructions.ParameterType)
    (parts : List (DataPart F Conversion)) (events : List (CaseEvaluation.Event (CaseDataTerms.Expr F)))
    (values : List (Value F))
    (evaluated : run (CaseDataTerms.eval environment) convert CaseDataTerms.Error.expectedList parts =
      ⟨events, .ok values⟩) :
    eval convert environment parts = ⟨events, .ok (.list values)⟩ ∧
    evalBuilt convert environment name site types parts = ⟨events, .ok (built name site types values)⟩ ∧
    NominalListViews.listView (built name site types values) = some values ∧
    NominalListViews.fold (fun seen value => seen ++ [value]) [] (built name site types values).values = values ∧
    ∀ position, NominalListViews.nextItem ((built name site types values).values.drop position) =
      (NominalListViews.index values position).map (fun value => (value, values.drop (position + 1))) := by
  refine ⟨by simp [eval, evaluated, Logged.bind, CaseDataTerms.pure, Logged.ofResult],
    by simp [evalBuilt, evaluated, Logged.bind, Logged.ofResult], rfl, ?_, ?_⟩
  · simpa [built] using NominalListViews.fold_records_order values []
  · exact NominalListViews.cursor_index values

/-- The view bridge itself is available from independent syntax typing;
successful source execution need not be supplied by its caller. -/
theorem data_typed_views (convert : Conversion → Value F → Value F)
    (conversions : ConversionSound ConversionTyped convert)
    (typed : Typing (CaseDataTerms.Typing outerTypes) ConversionTyped parts target)
    (environment : Bindings F) (valid : BindingsHold outerTypes environment)
    (name site : Nat) (parameterTypes : Fin parameters → NominalConstructions.ParameterType) :
    ∃ values, (∀ value ∈ values, target value) ∧
      eval convert environment parts =
        ⟨sourceTrace (CaseDataTerms.eval environment) parts, .ok (.list values)⟩ ∧
      evalBuilt convert environment name site parameterTypes parts =
        ⟨sourceTrace (CaseDataTerms.eval environment) parts, .ok (built name site parameterTypes values)⟩ ∧
      NominalListViews.listView (built name site parameterTypes values) = some values ∧
      NominalListViews.fold (fun seen value => seen ++ [value]) []
        (built name site parameterTypes values).values = values ∧
      ∀ position, NominalListViews.nextItem ((built name site parameterTypes values).values.drop position) =
        (NominalListViews.index values position).map (fun value => (value, values.drop (position + 1))) := by
  obtain ⟨values, evaluated, valueValid⟩ := typing_evaluates (CaseDataTerms.eval environment) convert
    CaseDataTerms.Error.expectedList
    (fun _ _ expressionTyped => CaseDataTerms.typing_evaluates expressionTyped environment valid)
    conversions typed
  exact ⟨values, valueValid, constructed_views convert environment name site parameterTypes parts _ values evaluated⟩

end Yulang.NominalListSpread
