import Yulang.ValueBoundElimination

/-!
# Greatest solutions and negative occurrences of value unknowns

The upper-bound dual of `ValueBounds` propagates ground upper bounds backwards
along the existing finite variable-flow graph. Each unknown receives their
intersection, with the writable top type `any` for an empty intersection.
The result is a greatest assignment over all finite structural types, rather
than a greatest element of an enumerated candidate set.

The checked output entry point eliminates unknowns occurring only negatively.
Arrow inputs reverse polarity, so an unconstrained input in `alpha -> int`
becomes `any -> int`. Ambient parameters and all rows remain fixed. Mixed
positive and negative occurrences require a parameterized scheme; they are
not independently defaulted by this module.
-/

namespace Yulang.ValueUpperBounds

open StructuralBase ValueBounds

universe u

variable {n : Nat} {RowType : Type u}

/-- The upper half includes the original flow edges in their original direction. -/
def UpperHolds (leRow : RowType → RowType → Prop)
    (value : Valuation n RowType) : Constraint n RowType → Prop
  | .lower _ _ | .check _ _ => True
  | .flow source target => Subtype leRow (value source) (value target)
  | .upper source type => Subtype leRow (value source) type

def UpperModels (leRow : RowType → RowType → Prop) (problem : Problem n RowType)
    (value : Valuation n RowType) : Prop :=
  ∀ constraint ∈ problem, UpperHolds leRow value constraint

theorem models_upper {leRow : RowType → RowType → Prop}
    {problem : Problem n RowType} {value : Valuation n RowType}
    (model : Models leRow problem value) : UpperModels leRow problem value := by
  intro constraint member
  cases constraint <;> first | exact model _ member | trivial

def upperSeeds (problem : Problem n RowType) : List (Fin n × Ty RowType) :=
  problem.filterMap fun
    | .upper source type => some (source, type)
    | _ => none

@[simp] theorem mem_upperSeeds (problem : Problem n RowType) (source : Fin n)
    (type : Ty RowType) :
    (source, type) ∈ upperSeeds problem ↔ .upper source type ∈ problem := by
  simp only [upperSeeds, List.mem_filterMap]
  constructor
  · rintro ⟨constraint, member, found⟩
    cases constraint with
    | upper actual target =>
        have same := Prod.mk.inj (Option.some.inj found)
        obtain ⟨rfl, rfl⟩ := same
        exact member
    | _ => cases found
  · intro member
    exact ⟨.upper source type, member, rfl⟩

/-- A source is bounded by every upper bound of a reachable successor. -/
def upperTypes (problem : Problem n RowType) (source : Fin n) : List (Ty RowType) :=
  (upperSeeds problem).filterMap fun entry =>
    if entry.1 ∈ reachable problem source then some entry.2 else none

theorem mem_upperTypes (problem : Problem n RowType) (source : Fin n)
    (type : Ty RowType) :
    type ∈ upperTypes problem source ↔
      ∃ target, .upper target type ∈ problem ∧ Reaches problem source target := by
  simp only [upperTypes, List.mem_filterMap]
  constructor
  · rintro ⟨⟨target, actual⟩, member, found⟩
    split at found
    · rename_i path
      have equal : actual = type := Option.some.inj found
      subst actual
      exact ⟨target, (mem_upperSeeds problem target type).mp member,
        (reachable_exact problem source target).mp path⟩
    · cases found
  · rintro ⟨target, member, path⟩
    refine ⟨(target, type), (mem_upperSeeds problem target type).mpr member, ?_⟩
    simp only [(reachable_exact problem source target).mpr path, ↓reduceIte]

/-- The empty meet is the specified top type `any`. -/
def meetTypes : List (Ty RowType) → Ty RowType
  | [] => .top
  | type :: rest => .inter type (meetTypes rest)

theorem le_meetTypes_iff (leRow : RowType → RowType → Prop)
    (lower : Ty RowType) (types : List (Ty RowType)) :
    Subtype leRow lower (meetTypes types) ↔
      ∀ type ∈ types, Subtype leRow lower type := by
  induction types with
  | nil =>
      constructor
      · intro _ _ member
        cases member
      · intro _
        exact .top lower
  | cons type rest ih =>
      simp only [meetTypes, inter_is_meet, ih, List.mem_cons, forall_eq_or_imp]

theorem meetTypes_le (leRow : RowType → RowType → Prop)
    (types : List (Ty RowType)) (type : Ty RowType) (member : type ∈ types) :
    Subtype leRow (meetTypes types) type :=
  (le_meetTypes_iff leRow (meetTypes types) types).mp (.refl _) type member

/-- Adding upper bounds makes their intersection smaller. -/
theorem meetTypes_mono (leRow : RowType → RowType → Prop)
    (left right : List (Ty RowType)) (included : ∀ type ∈ right, type ∈ left) :
    Subtype leRow (meetTypes left) (meetTypes right) :=
  (le_meetTypes_iff leRow (meetTypes left) right).mpr
    (fun type member => meetTypes_le leRow left type (included type member))

def greatest (problem : Problem n RowType) : Valuation n RowType :=
  fun source => meetTypes (upperTypes problem source)

theorem greatest_upper (leRow : RowType → RowType → Prop)
    (problem : Problem n RowType) (source : Fin n) (type : Ty RowType)
    (member : .upper source type ∈ problem) :
    Subtype leRow (greatest problem source) type := by
  apply meetTypes_le leRow
  exact (mem_upperTypes problem source type).mpr ⟨source, member, .nil source⟩

theorem greatest_flow (leRow : RowType → RowType → Prop)
    (problem : Problem n RowType) (source target : Fin n)
    (member : .flow source target ∈ problem) :
    Subtype leRow (greatest problem source) (greatest problem target) := by
  apply meetTypes_mono leRow
  intro type contributes
  obtain ⟨finish, bound, path⟩ := (mem_upperTypes problem target type).mp contributes
  apply (mem_upperTypes problem source type).mpr
  exact ⟨finish, bound,
    .cons ((mem_successors problem source target).mpr member) path⟩

theorem greatest_upperModels (leRow : RowType → RowType → Prop)
    (problem : Problem n RowType) : UpperModels leRow problem (greatest problem) := by
  intro constraint member
  cases constraint with
  | upper source type => exact greatest_upper leRow problem source type member
  | flow source target => exact greatest_flow leRow problem source target member
  | lower | check => trivial

theorem reaches_subtype {leRow : RowType → RowType → Prop}
    {problem : Problem n RowType} {value : Valuation n RowType}
    (model : UpperModels leRow problem value) {source target : Fin n}
    (path : Reaches problem source target) :
    Subtype leRow (value source) (value target) := by
  induction path with
  | nil => exact .refl _
  | @cons source middle target edge rest ih =>
      exact .trans (model (.flow source middle)
        ((mem_successors problem source middle).mp edge)) ih

/-- Greatestness quantifies over every structural assignment, without a
candidate alphabet, a depth restriction, or a supplied greatest solution. -/
theorem greatest_above {leRow : RowType → RowType → Prop}
    {problem : Problem n RowType} {value : Valuation n RowType}
    (model : UpperModels leRow problem value) (source : Fin n) :
    Subtype leRow (value source) (greatest problem source) := by
  apply (le_meetTypes_iff leRow _ _).mpr
  intro type contributes
  obtain ⟨target, bound, path⟩ := (mem_upperTypes problem source type).mp contributes
  exact .trans (reaches_subtype model path) (model (.upper target type) bound)

theorem greatest_models_of_models {leRow : RowType → RowType → Prop}
    {problem : Problem n RowType} {value : Valuation n RowType}
    (model : Models leRow problem value) : Models leRow problem (greatest problem) := by
  intro constraint member
  cases constraint with
  | lower type target => exact .trans (model _ member) (greatest_above (models_upper model) target)
  | flow source target => exact greatest_flow leRow problem source target member
  | upper source type => exact greatest_upper leRow problem source type member
  | check source target => exact model _ member

theorem greatest_models_iff (leRow : RowType → RowType → Prop)
    (problem : Problem n RowType) :
    Models leRow problem (greatest problem) ↔ ∃ value, Models leRow problem value :=
  ⟨fun model => ⟨greatest problem, model⟩,
    fun ⟨_, model⟩ => greatest_models_of_models model⟩

/-- Only the final ground comparisons use the supplied comparison procedure. -/
def solveGreatest (typeCheck : Ty RowType → Ty RowType → Bool)
    (problem : Problem n RowType) : Option (Valuation n RowType) :=
  let value := greatest problem
  if accepts typeCheck problem value then some value else none

theorem solveGreatest_some_iff (typeCheck : Ty RowType → Ty RowType → Bool)
    {leRow : RowType → RowType → Prop}
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    (problem : Problem n RowType) (value : Valuation n RowType) :
    solveGreatest typeCheck problem = some value ↔
      value = greatest problem ∧ Models leRow problem value := by
  simp only [solveGreatest]
  split
  · rename_i accepted
    have model := (accepts_exact typeCheck typeExact problem (greatest problem)).mp accepted
    constructor
    · intro equal
      have same : greatest problem = value := Option.some.inj equal
      exact ⟨same.symm, same ▸ model⟩
    · rintro ⟨rfl, _⟩
      rfl
  · rename_i rejected
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨rfl, model⟩
      exact False.elim (rejected ((accepts_exact typeCheck typeExact problem _).mpr model))

theorem solveGreatest_sound (typeCheck : Ty RowType → Ty RowType → Bool)
    {leRow : RowType → RowType → Prop}
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    {problem : Problem n RowType} {value : Valuation n RowType}
    (solved : solveGreatest typeCheck problem = some value) : Models leRow problem value :=
  ((solveGreatest_some_iff typeCheck typeExact problem value).mp solved).2

theorem solveGreatest_greatest (typeCheck : Ty RowType → Ty RowType → Bool)
    {leRow : RowType → RowType → Prop}
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    {problem : Problem n RowType} {value : Valuation n RowType}
    (solved : solveGreatest typeCheck problem = some value)
    {other : Valuation n RowType} (model : Models leRow problem other) (source : Fin n) :
    Subtype leRow (other source) (value source) := by
  rw [((solveGreatest_some_iff typeCheck typeExact problem value).mp solved).1]
  exact greatest_above (models_upper model) source

/-- Failure excludes all assignments, including ones with unions,
intersections, arrows, records, and arbitrarily large finite types. -/
theorem solveGreatest_none_iff (typeCheck : Ty RowType → Ty RowType → Bool)
    {leRow : RowType → RowType → Prop}
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    (problem : Problem n RowType) :
    solveGreatest typeCheck problem = none ↔ ¬ ∃ value, Models leRow problem value := by
  constructor
  · intro failed ⟨value, model⟩
    have solved := (solveGreatest_some_iff typeCheck typeExact problem (greatest problem)).mpr
      ⟨rfl, greatest_models_of_models model⟩
    rw [failed] at solved
    cases solved
  · intro impossible
    simp only [solveGreatest]
    split
    · rename_i accepted
      exact False.elim (impossible ⟨greatest problem,
        (accepts_exact typeCheck typeExact problem _).mp accepted⟩)
    · rfl

theorem solveGreatest_exists_iff (typeCheck : Ty RowType → Ty RowType → Bool)
    {leRow : RowType → RowType → Prop}
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    (problem : Problem n RowType) :
    (∃ value, solveGreatest typeCheck problem = some value) ↔ ∃ value, Models leRow problem value := by
  constructor
  · rintro ⟨value, solved⟩
    exact ⟨value, solveGreatest_sound typeCheck typeExact solved⟩
  · rintro ⟨value, model⟩
    exact ⟨greatest problem, (solveGreatest_some_iff typeCheck typeExact problem _).mpr
      ⟨rfl, greatest_models_of_models model⟩⟩

/-! ## Exact elimination in negative outputs -/

open ValueBoundElimination (Pointwise evaluate polarity)

def Antitone (leRow : RowType → RowType → Prop)
    (output : Valuation n RowType → Ty RowType) : Prop :=
  ∀ left right, Pointwise leRow left right → Subtype leRow (output right) (output left)

def infer (typeCheck : Ty RowType → Ty RowType → Bool)
    (problem : Problem n RowType)
    (output : Valuation n RowType → Ty RowType) : Option (Ty RowType) :=
  (solveGreatest typeCheck problem).map output

theorem infer_some_iff (typeCheck : Ty RowType → Ty RowType → Bool)
    {leRow : RowType → RowType → Prop}
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    (problem : Problem n RowType)
    (output : Valuation n RowType → Ty RowType) (result : Ty RowType) :
    infer typeCheck problem output = some result ↔
      Models leRow problem (greatest problem) ∧ output (greatest problem) = result := by
  simp only [infer, Option.map_eq_some_iff]
  constructor
  · rintro ⟨value, solved, found⟩
    obtain ⟨rfl, model⟩ := (solveGreatest_some_iff typeCheck typeExact problem value).mp solved
    exact ⟨model, found⟩
  · rintro ⟨model, found⟩
    exact ⟨greatest problem,
      (solveGreatest_some_iff typeCheck typeExact problem _).mpr ⟨rfl, model⟩, found⟩

theorem infer_exact (typeCheck : Ty RowType → Ty RowType → Bool)
    {leRow : RowType → RowType → Prop}
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    (problem : Problem n RowType) (output : Valuation n RowType → Ty RowType)
    (antitone : Antitone leRow output) (expected : Ty RowType) :
    (∃ result, infer typeCheck problem output = some result ∧ Subtype leRow result expected) ↔
      ∃ value, Models leRow problem value ∧ Subtype leRow (output value) expected := by
  constructor
  · rintro ⟨result, inferred, below⟩
    obtain ⟨model, rfl⟩ := (infer_some_iff typeCheck typeExact problem output result).mp inferred
    exact ⟨greatest problem, model, below⟩
  · rintro ⟨value, model, below⟩
    refine ⟨output (greatest problem), ?_, ?_⟩
    · exact (infer_some_iff typeCheck typeExact problem output _).mpr
        ⟨greatest_models_of_models model, rfl⟩
    · exact .trans (antitone _ _ (greatest_above (models_upper model))) below

theorem infer_principal (typeCheck : Ty RowType → Ty RowType → Bool)
    {leRow : RowType → RowType → Prop}
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    {problem : Problem n RowType} {output : Valuation n RowType → Ty RowType}
    (antitone : Antitone leRow output) {result : Ty RowType}
    (inferred : infer typeCheck problem output = some result)
    {value : Valuation n RowType} (model : Models leRow problem value) :
    Subtype leRow result (output value) := by
  obtain ⟨_, rfl⟩ := (infer_some_iff typeCheck typeExact problem output result).mp inferred
  exact antitone _ _ (greatest_above (models_upper model))

theorem infer_none_iff (typeCheck : Ty RowType → Ty RowType → Bool)
    {leRow : RowType → RowType → Prop}
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    (problem : Problem n RowType) (output : Valuation n RowType → Ty RowType) :
    infer typeCheck problem output = none ↔ ¬ ∃ value, Models leRow problem value := by
  simp only [infer, Option.map_eq_none_iff, solveGreatest_none_iff typeCheck typeExact]

variable {Parameter : Type}

theorem evaluate_antitone (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (parameters : Parameter → Ty RowType) (rows : Parameter ⊕ Fin n → RowType)
    (term : Inference.TyTerm (Parameter ⊕ Fin n)) (checked : polarity false term = true) :
    Antitone leRow (evaluate empty join leRow parameters rows term) := by
  intro left right below
  exact ValueBoundElimination.polarity_sound empty join leRow rowRefl rowTrans
    parameters rows term false checked left right below

/-- A failed polarity check remains separate from inconsistent bounds. -/
def inferTerm (typeCheck : Ty RowType → Ty RowType → Bool)
    (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (problem : Problem n RowType)
    (parameters : Parameter → Ty RowType) (rows : Parameter ⊕ Fin n → RowType)
    (term : Inference.TyTerm (Parameter ⊕ Fin n)) : ValueBoundElimination.Result RowType :=
  if polarity false term then
    match infer typeCheck problem (evaluate empty join leRow parameters rows term) with
    | none => .inconsistent
    | some type => .inferred type
  else .unsupported

theorem inferTerm_inferred_iff (typeCheck : Ty RowType → Ty RowType → Bool)
    (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (problem : Problem n RowType)
    (parameters : Parameter → Ty RowType) (rows : Parameter ⊕ Fin n → RowType)
    (term : Inference.TyTerm (Parameter ⊕ Fin n)) (result : Ty RowType) :
    inferTerm typeCheck empty join leRow problem parameters rows term = .inferred result ↔
      polarity false term = true ∧
        infer typeCheck problem (evaluate empty join leRow parameters rows term) = some result := by
  unfold inferTerm
  split
  · rename_i checked
    cases found : infer typeCheck problem (evaluate empty join leRow parameters rows term) <;>
      simp [checked]
  · rename_i unsupported
    simp [unsupported]

theorem inferTerm_unsupported_iff (typeCheck : Ty RowType → Ty RowType → Bool)
    (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (problem : Problem n RowType)
    (parameters : Parameter → Ty RowType) (rows : Parameter ⊕ Fin n → RowType)
    (term : Inference.TyTerm (Parameter ⊕ Fin n)) :
    inferTerm typeCheck empty join leRow problem parameters rows term = .unsupported ↔
      polarity false term = false := by
  unfold inferTerm
  cases checked : polarity false term <;> simp
  cases infer typeCheck problem (evaluate empty join leRow parameters rows term) <;> simp

theorem inferTerm_inconsistent_iff (typeCheck : Ty RowType → Ty RowType → Bool)
    (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop)
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    (problem : Problem n RowType)
    (parameters : Parameter → Ty RowType) (rows : Parameter ⊕ Fin n → RowType)
    (term : Inference.TyTerm (Parameter ⊕ Fin n)) :
    inferTerm typeCheck empty join leRow problem parameters rows term = .inconsistent ↔
      polarity false term = true ∧ ¬ ∃ value, Models leRow problem value := by
  rw [← infer_none_iff typeCheck typeExact problem
    (evaluate empty join leRow parameters rows term)]
  unfold inferTerm
  split
  · rename_i checked
    cases found : infer typeCheck problem (evaluate empty join leRow parameters rows term) <;>
      simp [checked]
  · rename_i unsupported
    simp [unsupported]

theorem inferTerm_exact (typeCheck : Ty RowType → Ty RowType → Bool)
    (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    (problem : Problem n RowType)
    (parameters : Parameter → Ty RowType) (rows : Parameter ⊕ Fin n → RowType)
    (term : Inference.TyTerm (Parameter ⊕ Fin n)) (expected : Ty RowType) :
    (∃ result, inferTerm typeCheck empty join leRow problem parameters rows term = .inferred result ∧
      Subtype leRow result expected) ↔
      polarity false term = true ∧
        ∃ value, Models leRow problem value ∧
          Subtype leRow (evaluate empty join leRow parameters rows term value) expected := by
  constructor
  · rintro ⟨result, inferred, below⟩
    obtain ⟨checked, computed⟩ :=
      (inferTerm_inferred_iff typeCheck empty join leRow problem parameters rows term result).mp inferred
    exact ⟨checked,
      (infer_exact typeCheck typeExact problem _
        (evaluate_antitone empty join leRow rowRefl rowTrans parameters rows term checked) expected).mp
        ⟨result, computed, below⟩⟩
  · rintro ⟨checked, possible⟩
    obtain ⟨result, computed, below⟩ :=
      (infer_exact typeCheck typeExact problem _
        (evaluate_antitone empty join leRow rowRefl rowTrans parameters rows term checked) expected).mpr possible
    exact ⟨result,
      (inferTerm_inferred_iff typeCheck empty join leRow problem parameters rows term result).mpr
        ⟨checked, computed⟩, below⟩

/-- All ambient parameter instances are preserved by negative elimination. -/
theorem parameterized_exact (typeCheck : Ty RowType → Ty RowType → Bool)
    (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    (problems : (Parameter → Ty RowType) → Problem n RowType)
    (rows : Parameter ⊕ Fin n → RowType)
    (term : Inference.TyTerm (Parameter ⊕ Fin n)) (checked : polarity false term = true)
    (expected : Ty RowType) :
    (∃ parameters result,
      inferTerm typeCheck empty join leRow (problems parameters) parameters rows term = .inferred result ∧
        Subtype leRow result expected) ↔
      ∃ parameters value, Models leRow (problems parameters) value ∧
        Subtype leRow (evaluate empty join leRow parameters rows term value) expected := by
  apply exists_congr
  intro parameters
  rw [inferTerm_exact typeCheck empty join leRow rowRefl rowTrans typeExact]
  exact and_iff_right checked

end Yulang.ValueUpperBounds
