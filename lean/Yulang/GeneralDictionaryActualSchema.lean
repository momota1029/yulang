import Yulang.GeneralDictionarySemanticSchemaTransport

/-! Actual-mode schemas allow directional capture replay. Root output requests
use actual mode; compound emitted inputs may use lower/upper and are excluded. -/
namespace Yulang.GeneralDictionaryActualSchema
open GeneralDeclarations GeneralDeclarationDemands GeneralNominalMaterialization
open GeneralNominalRecursiveInspection CommonNominalFullCarrier
open GeneralNominalInspection (Query)

def ActualOnly (s : Schema) : Prop := ∀ entry ∈ s.variables, entry.mode = .actual

theorem empty_actual : ActualOnly {} := by simp [ActualOnly]

theorem append_actual (a b : Schema) (ha : ActualOnly a) (hb : ActualOnly b) :
    ActualOnly (a.append b) := by
  intro entry member
  rcases List.mem_append.mp member with h | h
  · exact ha entry h
  · exact hb entry h

mutual
  theorem schema_actual (query : Query) (origin : Origin) :
      ActualOnly (schema query origin .actual) := by
    cases query with
    | variables names =>
      rw [schema]
      intro entry member
      obtain ⟨name,_,rfl⟩ := List.mem_map.mp member
      rfl
    | scalar base => simp [schema,ActualOnly]
    | deferred name => simp [schema,ActualOnly]
    | node shape children =>
      simpa only [schema,ActualOnly] using schemas_actual children (fun index => .structural origin shape index) 0
    | nominal name children =>
      simpa only [schema,ActualOnly] using schemas_actual children (fun index => .nominal origin name index) 0
  termination_by sizeOf query

  theorem schemas_actual (queries : List Query) (origins : Nat → Origin) (index : Nat) :
      ActualOnly (schemas queries origins .actual index) := by
    cases queries with
    | nil => simpa only [schemas] using empty_actual
    | cons query rest =>
      rw [schemas]
      exact append_actual _ _ (schema_actual query (origins index))
        (schemas_actual rest origins (index+1))
  termination_by sizeOf queries
end

theorem fold_actual (ss : List Schema) (all : ∀ s ∈ ss, ActualOnly s) :
    ActualOnly (ss.foldr Schema.append {}) := by
  induction ss with
  | nil => exact empty_actual
  | cons s rest ih =>
    exact append_actual _ _ (all s (by simp)) (ih (fun t h => all t (by simp [h])))

theorem generated_actual (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (rs : List Request)
    (actual : ∀ r ∈ rs, r.mode = .actual) :
    ActualOnly (generated state interpretation rs) := by
  apply fold_actual
  intro s member
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp member
  rw [actual r hr]
  exact schema_actual _ _

theorem root_request_actual (declaration : Declaration)
    (root : GeneralSourceDictionaries.Occurrence roles) :
    ∀ r ∈ rootRequests declaration root, r.mode = .actual := by
  intro r member
  obtain ⟨output,_,member⟩ := List.mem_flatMap.mp member
  obtain ⟨equation,_,rfl⟩ := List.mem_map.mp member
  rfl

theorem root_generated_actual (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (declaration : Declaration)
    (root : GeneralSourceDictionaries.Occurrence roles) :
    ActualOnly (generated state interpretation (rootRequests declaration root)) :=
  generated_actual state interpretation _ (root_request_actual declaration root)

/-- Finite, model-relative sufficient premises. Actual Fits is directional;
endpoint equivalence and literal capture identity are not required. -/
structure Footprint (declaration : Declaration) (oldCapture currentCapture : Capture)
    {oldState currentState : GeneralNominalState.State}
    (oldReport : Report oldState) (currentReport : Report currentState) (s : Schema)
    (model : GeneralNominalCommonBridge.Assignment) : Prop where
  outputs : ∀ entry ∈ s.variables, entry.name ∈ declaration.outputNames →
    Equivalent (model (currentCapture.outputs entry.name)).1 (model (oldCapture.outputs entry.name)).1
  inputs : ∀ entry ∈ s.variables, entry.name ∉ declaration.outputNames → ∀ actual,
    GeneralNominalCaptureMerges.Fits model (oldCapture.inputs entry.name) actual →
    GeneralNominalCaptureMerges.Fits model (currentCapture.inputs entry.name) actual
  origins : ∀ entry ∈ s.variables, ∀ captured ∈ currentReport.captures,
    entry.name = captured.name → entry.mode = .actual → ∀ origin, captured.origin = some origin →
    ∃ old ∈ oldReport.captures, old.name = captured.name ∧ old.origin = some origin

theorem variable_replay (declaration : Declaration) (oldCapture currentCapture : Capture)
    {oldState currentState : GeneralNominalState.State} (oldReport : Report oldState)
    (currentReport : Report currentState) (s : Schema) (model : GeneralNominalCommonBridge.Assignment)
    (actualOnly : ActualOnly s)
    (footprint : Footprint declaration oldCapture currentCapture oldReport currentReport s model)
    (entry : Use) (member : entry ∈ s.variables) (actual : Ty)
    (valid : VariableHolds declaration oldCapture model entry.name entry.mode actual) :
    VariableHolds declaration currentCapture model entry.name entry.mode actual := by
  unfold VariableHolds at valid ⊢
  by_cases output : entry.name ∈ declaration.outputNames
  · simp only [output,ite_true] at valid ⊢
    exact (GeneralDictionarySemanticSchemaTransport.equivalent_right _ _ _
      (footprint.outputs entry member output)).mpr valid
  · simp only [output,ite_false,actualOnly entry member] at valid ⊢
    exact footprint.inputs entry member output actual valid

/-- Conditional one-way soundness for actual-mode schema materialization.
It does not claim all reobservations satisfy the finite footprint. -/
theorem replay (declaration : Declaration) (oldCapture currentCapture : Capture)
    {oldState currentState : GeneralNominalState.State} (oldReport : Report oldState)
    (currentReport : Report currentState) (small large : Schema)
    (variables : ∀ entry ∈ small.variables, entry ∈ large.variables)
    (tests : ∀ test ∈ small.tests, test ∈ large.tests)
    (model : GeneralNominalCommonBridge.Assignment) (actualOnly : ActualOnly small)
    (footprint : Footprint declaration oldCapture currentCapture oldReport currentReport small model)
    (valid : GeneralNominalMaterialization.Models oldState declaration oldCapture oldReport large model) :
    GeneralNominalMaterialization.Models currentState declaration currentCapture currentReport small model := by
  refine ⟨fun test member => valid.1 test (tests test member),?_,?_,?_⟩
  · intro entry member
    refine ⟨(valid.2.1 entry (variables entry member)).1,?_⟩
    intro actual seen
    exact variable_replay declaration oldCapture currentCapture oldReport currentReport small model
      actualOnly footprint entry member actual ((valid.2.1 entry (variables entry member)).2 actual seen)
  · intro first one last two same firstActual lastActual a b oneSeen twoSeen
    exact valid.2.2.1 first (variables first one) last (variables last two) same firstActual lastActual a b oneSeen twoSeen
  · intro entry member captured present same actual origin known a b seen observed
    obtain ⟨old,oldMember,names,oldOrigin⟩ := footprint.origins entry member captured present same actual origin known
    exact valid.2.2.2 entry (variables entry member) old oldMember (same.trans names.symm) actual
      origin oldOrigin a b seen observed
/-- Dropping capture occurrences weakens the actual-value restriction. This
uses real merge semantics on both sides, with no equality of endpoint types. -/
theorem capture_fits_subset
    (a b : GeneralNominalState.State) (ra rb : Registry) (ia ib : Nat)
    (da db : Declaration) (xs ys : GeneralNominalAllocation.Bindings)
    (model : GeneralNominalCommonBridge.Assignment) (name : Nat)
    (declaredA : name ∈ da.inputNames) (declaredB : name ∈ db.inputNames)
    (nonemptyA : GeneralNominalAllocation.occurrences xs name ≠ [])
    (nonemptyB : GeneralNominalAllocation.occurrences ys name ≠ [])
    (subset : ∀ pair, pair ∈ GeneralNominalAllocation.occurrences ys name →
      pair ∈ GeneralNominalAllocation.occurrences xs name)
    (mergeA : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.merges a ra ia da xs))
    (mergeB : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.merges b rb ib db ys))
    (actual : Ty)
    (old : GeneralNominalCaptureMerges.Fits model
      ((GeneralNominalAllocation.capture a ra ia da.id xs).inputs name) actual) :
    GeneralNominalCaptureMerges.Fits model
      ((GeneralNominalAllocation.capture b rb ib db.id ys).inputs name) actual := by
  rw [GeneralNominalCaptureMerges.capture_interval_exact a ra ia da xs model
    mergeA name declaredA nonemptyA] at old
  rw [GeneralNominalCaptureMerges.capture_interval_exact b rb ib db ys model
    mergeB name declaredB nonemptyB]
  exact fun pair member => old pair (subset pair member)

end Yulang.GeneralDictionaryActualSchema
