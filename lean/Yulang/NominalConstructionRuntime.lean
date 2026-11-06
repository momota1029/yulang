import Yulang.NominalConstructions
import Yulang.PureCasts

/-!
# Executing deferred nominal parameter sites

`NominalConstructions.finish` produces a compile-time plan for the original
invariant-parameter occurrences of a list, struct or enum construction. This
module executes that site's ordered argument vector with supplied checked pure
conversion code, and retains the constructor, enum tag and construction id.
It never maps a conversion inside an already constructed nominal value.

The source of each original site is a signed request tree. Conversion code is
`PureCasts.Plan`, so its purity is proved by that kernel rather than assumed.
The main result preserves the complete request tree of evaluating the original
sites in order, including every response branch, payload and signed weight.
EOF plans retain the exact original values. Value-typing preservation is stated
relative to source-value typing and the supplied conversion code's value-typing
contract; producing that code from the ground boundary checker remains open.

Only the parameter occurrences already present in the planner are represented.
Fixed struct fields, source name resolution, weak-variable solving, the surface
constructor AST and role method selection still belong to elaboration.
-/

namespace Yulang.NominalConstructionRuntime

open Directed Directed.Computation NominalConstructions PureCasts

universe u
variable {parameters n : Nat} {Key Payload Response Value : Type u}

structure Runtime (parameters n : Nat) (Key Payload Response Value : Type u) where
  fits : Casts.Compatibility
  source : Argument parameters → Computation n Key Payload Response Value
  convert : Argument parameters → Casts.Ty → PureCasts.Plan n Key Payload Response Value Value

/-- The construction's metadata is retained alongside the resulting argument vector. -/
structure Built (parameters : Nat) (Value : Type u) where
  constructor : Constructor
  construction : Nat
  parameterTypes : Fin parameters → ParameterType
  values : List Value

/-- Unknown target slots and compatible boundaries use identity, and do not
consult the conversion table (spec §6.5, decision 18). -/
def Runtime.code (runtime : Runtime parameters n Key Payload Response Value) :
    Instruction parameters → PureCasts.Plan n Key Payload Response Value Value
  | .keep _ => .keep
  | .boundary argument target =>
      if runtime.fits.check argument.original.source target then .keep
      else runtime.convert argument target

theorem compatible_site_kept (runtime : Runtime parameters n Key Payload Response Value)
    (argument : Argument parameters) (target : Casts.Ty)
    (compatible : runtime.fits.Rel argument.original.source target) :
    runtime.code (.boundary argument target) = .keep := by
  simp [Runtime.code, (runtime.fits.exact _ _).mpr compatible]

theorem identical_type_kept (runtime : Runtime parameters n Key Payload Response Value)
    (argument : Argument parameters) :
    runtime.code (.boundary argument argument.original.source) = .keep :=
  compatible_site_kept runtime argument _ (runtime.fits.refl _)

def runValues (runtime : Runtime parameters n Key Payload Response Value) :
    List (Instruction parameters) → Computation n Key Payload Response (List Value)
  | [] => .pure []
  | instruction :: rest =>
      (runtime.source instruction.original).bind (fun original =>
        ((runtime.code instruction).run original).bind (fun converted =>
          (runValues runtime rest).bind (fun values => .pure (converted :: values))))

/-- The reference sequence evaluates each original site in the same order. -/
def readValues (source : Argument parameters → Computation n Key Payload Response Value) :
    List (Argument parameters) → Computation n Key Payload Response (List Value)
  | [] => .pure []
  | argument :: rest =>
      (source argument).bind (fun value =>
        (readValues source rest).bind (fun values => .pure (value :: values)))

def execute (runtime : Runtime parameters n Key Payload Response Value)
    (plan : NominalConstructions.Plan parameters) :
    Computation n Key Payload Response (Built parameters Value) :=
  mapValue (fun values => ⟨plan.constructor, plan.construction, plan.parameterTypes, values⟩)
    (runValues runtime plan.instructions)

/-- Predicates hold at every possible return, including all request responses. -/
def AllReturns (predicate : A → Prop) : Computation n Key Payload Response A → Prop
  | .pure value => predicate value
  | .request _ _ resume => ∀ response, AllReturns predicate (resume response)

theorem allReturns_bind (source : Computation n Key Payload Response A)
    (next : A → Computation n Key Payload Response B) (P : A → Prop) (Q : B → Prop)
    (initial : AllReturns P source)
    (following : ∀ value, P value → AllReturns Q (next value)) :
    AllReturns Q (source.bind next) := by
  induction source with
  | pure value => exact following value initial
  | request occurrence payload resume ih =>
      exact fun response => ih response (initial response)

theorem allReturns_map (source : Computation n Key Payload Response A)
    (f : A → B) (P : B → Prop) :
    AllReturns P (mapValue f source) ↔ AllReturns (fun value => P (f value)) source := by
  induction source with
  | pure value => rfl
  | request occurrence payload resume ih =>
      simp only [mapValue, AllReturns, ih]

private theorem allReturns_true (source : Computation n Key Payload Response A) :
    AllReturns (fun _ => True) source := by
  induction source with
  | pure value => trivial
  | request occurrence payload resume ih => exact ih

private theorem requestTree_bind_congr (source : Computation n Key Payload Response A)
    (left : A → Computation n Key Payload Response B)
    (right : A → Computation n Key Payload Response C)
    (same : ∀ value, requestTree (left value) = requestTree (right value)) :
    requestTree (source.bind left) = requestTree (source.bind right) := by
  induction source with
  | pure value => exact same value
  | request occurrence payload resume ih =>
      exact congrArg (Computation.request occurrence payload) (funext ih)

private theorem requestTree_map (f : A → B) (source : Computation n Key Payload Response A) :
    requestTree (mapValue f source) = requestTree source :=
  mapValue_comp _ _ _

private theorem requestTree_pure_bind (f : A → B) (source : Computation n Key Payload Response A) :
    requestTree (source.bind (fun value => .pure (f value))) = requestTree source := by
  rw [bind_pure_map, requestTree_map]

/-- Purity is inserted after the source site; it cannot reorder the next site. -/
theorem runValues_cons (runtime : Runtime parameters n Key Payload Response Value)
    (instruction : Instruction parameters) (rest : List (Instruction parameters)) :
    runValues runtime (instruction :: rest) =
      (runtime.source instruction.original).bind (fun original =>
        (runValues runtime rest).bind (fun values =>
          .pure ((runtime.code instruction).value original :: values))) := by
  simp only [runValues, PureCasts.Plan.run_eq_pure, Computation.bind]

/-- Checked pure casts preserve the complete ordered request tree, for every
finite list of sites and every supplied signed source computation. -/
theorem runValues_requestTree (runtime : Runtime parameters n Key Payload Response Value)
    (instructions : List (Instruction parameters)) :
    requestTree (runValues runtime instructions) =
      requestTree (readValues runtime.source (instructions.map Instruction.original)) := by
  induction instructions with
  | nil => rfl
  | cons instruction rest ih =>
      rw [runValues_cons]
      simp only [List.map_cons, readValues]
      apply requestTree_bind_congr
      intro value
      rw [requestTree_pure_bind, requestTree_pure_bind, ih]

theorem execute_requestTree (runtime : Runtime parameters n Key Payload Response Value)
    (plan : NominalConstructions.Plan parameters) :
    requestTree (execute runtime plan) =
      requestTree (readValues runtime.source (plan.instructions.map Instruction.original)) := by
  rw [execute, requestTree_map, runValues_requestTree]

/-- A successful compile-time plan executes precisely the original site's
request tree; successful checking is not a runtime-correctness assumption. -/
theorem accepted_requestTree (runtime : Runtime parameters n Key Payload Response Value)
    (registry : CastGraph.Registry nodes) (construction : Construction parameters) (expected : Expectation parameters)
    (plan : NominalConstructions.Plan parameters)
    (accepted : finish runtime.fits registry construction expected = some plan) :
    requestTree (execute runtime plan) =
      requestTree (readValues runtime.source construction.arguments) := by
  have typed := (finish_exact runtime.fits registry construction expected plan).mp accepted
  cases typed
  rw [execute_requestTree, plan_retains_original_sites]

theorem runValues_keep (runtime : Runtime parameters n Key Payload Response Value)
    (arguments : List (Argument parameters)) :
    runValues runtime (arguments.map Instruction.keep) = readValues runtime.source arguments := by
  induction arguments with
  | nil => rfl
  | cons argument rest ih =>
      simp only [List.map_cons, runValues_cons, Runtime.code, PureCasts.Plan.value,
        Instruction.original, readValues, ih]

/-- EOF with no solved target executes no conversion and keeps all actual values. -/
theorem execute_eof (runtime : Runtime parameters n Key Payload Response Value)
    (construction : Construction parameters) :
    execute runtime (construction.plan (fun _ => none)) =
      mapValue (fun values =>
        (⟨construction.constructor, construction.construction,
          (construction.plan (fun _ => none)).parameterTypes, values⟩ : Built parameters Value))
        (readValues runtime.source construction.arguments) := by
  unfold execute
  rw [eof_no_boundaries, runValues_keep]
  rfl

/-- The output argument count matches the plan along every response branch. -/
theorem runValues_arity (runtime : Runtime parameters n Key Payload Response Value)
    (instructions : List (Instruction parameters)) :
    AllReturns (fun values => values.length = instructions.length) (runValues runtime instructions) := by
  induction instructions with
  | nil => rfl
  | cons instruction rest ih =>
      rw [runValues_cons]
      apply allReturns_bind _ _ (fun _ => True) _ (allReturns_true _)
      intro value _
      apply allReturns_bind _ _ (fun values => values.length = rest.length) _ ih
      intro values correct
      simpa only [AllReturns, List.length_cons] using congrArg Nat.succ correct

theorem execute_metadata (runtime : Runtime parameters n Key Payload Response Value)
    (plan : NominalConstructions.Plan parameters) :
    AllReturns (fun value => value.constructor = plan.constructor ∧
      value.construction = plan.construction ∧ value.parameterTypes = plan.parameterTypes)
      (execute runtime plan) := by
  apply (allReturns_map _ _ _).mpr
  simpa using allReturns_true (runValues runtime plan.instructions)

theorem execute_arity (runtime : Runtime parameters n Key Payload Response Value)
    (plan : NominalConstructions.Plan parameters) :
    AllReturns (fun value => value.values.length = plan.instructions.length)
      (execute runtime plan) :=
  (allReturns_map _ _ _).mpr (runValues_arity runtime plan.instructions)

def resultType : Instruction parameters → Casts.Ty
  | .keep argument => argument.original.source
  | .boundary _ target => target

inductive ValuesTyped (HasType : Casts.Ty → Value → Prop) :
    List (Instruction parameters) → List Value → Prop where
  | nil : ValuesTyped HasType [] []
  | cons {item : Instruction parameters} {rest : List (Instruction parameters)}
      {value : Value} {values : List Value} :
      HasType (resultType item) value → ValuesTyped HasType rest values →
      ValuesTyped HasType (item :: rest) (value :: values)

/-- The logical value types of original sites and converted results are kept
separate from the request-tree theorem, which needs no typing assumptions. -/
theorem runValues_typed (runtime : Runtime parameters n Key Payload Response Value)
    (HasType : Casts.Ty → Value → Prop) (instructions : List (Instruction parameters))
    (sources : ∀ instruction ∈ instructions,
      AllReturns (HasType instruction.original.original.source)
        (runtime.source instruction.original))
    (conversions : ∀ instruction ∈ instructions, ∀ value,
      HasType instruction.original.original.source value →
        HasType (resultType instruction) ((runtime.code instruction).value value)) :
    AllReturns (ValuesTyped HasType instructions) (runValues runtime instructions) := by
  induction instructions with
  | nil => exact .nil
  | cons instruction rest ih =>
      rw [runValues_cons]
      apply allReturns_bind _ _ (HasType instruction.original.original.source) _
        (sources instruction (by simp))
      intro original originalTyped
      have tailTyped := ih
        (fun item member => sources item (by simp [member]))
        (fun item member => conversions item (by simp [member]))
      apply allReturns_bind _ _ (ValuesTyped HasType rest) _ tailTyped
      intro values valuesTyped
      exact .cons (conversions instruction (by simp) original originalTyped) valuesTyped

end Yulang.NominalConstructionRuntime
