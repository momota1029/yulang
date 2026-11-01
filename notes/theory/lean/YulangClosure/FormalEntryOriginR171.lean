import YulangClosure.FormalEntryPrestateBridgeR169

/-!
R171 finite allocation/registration construction. The source correspondence is
the frozen R171 source handoff. This is a model of successful finite events,
not a theorem that Rust's work stack realizes those events. In particular the
permutation constructor must preserve the complete immutable expression, and
its realization by all HIR traversal routes is a separate obligation.

Header/receiver IDs consume the initial interval; record binders consume gaps;
all successful allocations check the u32 increment before returning the ID.
Source order may differ from allocation order. No final-map uniqueness premise
is used. Map writes are prepended, implementing last-write-wins with R169's
first-match lookup. Existing formal/recipe prefixes are arbitrary.
-/
namespace YulangClosure.FormalEntryOriginR171

open ComputationPermissionEntryR39
open FormalEntryPrestateBridgeR169

inductive Identity (Brand : Type) where
  | owner (brand : Brand)
  | parameter (brand : Brand) (ordinal : Nat)
  | occurrence (brand : Brand) (ordinal : Nat)
  | auxiliary (brand : Brand) (ordinal : Nat)
  deriving DecidableEq

def parameterKey {Id : Type} : Expression Id → Option Id
  | .lambda _ parameter => some parameter.id
  | .other _ => none

def keys {Id : Type} (expressions : List (Expression Id)) : List Id :=
  expressions.filterMap parameterKey

variable {Brand : Type} [DecidableEq Brand]

/-- A projection of successful allocation/retention events. `permute` accounts
for delayed header/local Lambda placement, and retains the entire payload.
The actual work-stack-to-permutation proof is deliberately not assumed closed.
`skip` includes receivers and record fields, which get IDs but no registration.
The limit is the maximal u32 value: returning that value would first overflow
the checked increment and therefore is not a successful allocation event. -/
inductive Construction (owner : Brand) : Nat → List (Expression (Identity Brand)) → Prop where
  | empty : Construction owner 0 []
  | skip (prior : Construction owner next expressions) (checked : next < 4294967295) :
      Construction owner (next + 1) expressions
  | lambda (prior : Construction owner next expressions) (checked : next < 4294967295)
      (occurrence : Identity Brand) (annotation : Option (Annotation (Identity Brand))) :
      Construction owner (next + 1)
        (expressions ++ [.lambda occurrence ⟨.parameter owner next, annotation⟩])
  | other (prior : Construction owner next expressions) (occurrence : Identity Brand) :
      Construction owner next (expressions ++ [.other occurrence])
  | permute (prior : Construction owner next expressions)
      (order : expressions.Perm reordered) : Construction owner next reordered

theorem construction_keys (owner : Brand) (next : Nat)
    (expressions : List (Expression (Identity Brand)))
    (construction : Construction owner next expressions) :
    (keys expressions).Nodup ∧
      ∀ key ∈ keys expressions, ∃ ordinal, ordinal < next ∧ key = .parameter owner ordinal := by
  induction construction with
  | empty => simp [keys]
  | @skip next expressions prior checked ih =>
    refine ⟨ih.1, ?_⟩
    intro key member
    obtain ⟨ordinal, bound, same⟩ := ih.2 key member
    exact ⟨ordinal, by omega, same⟩
  | @lambda next expressions prior checked occurrence annotation ih =>
    have fresh : Identity.parameter owner next ∉ keys expressions := by
      intro member
      obtain ⟨ordinal, bound, same⟩ := ih.2 _ member
      have equal : next = ordinal := by cases same; rfl
      omega
    constructor
    · have disjoint : ∀ a ∈ keys expressions, ∀ b ∈ [Identity.parameter owner next], a ≠ b := by
        intro a ha b hb equal
        have same : b = Identity.parameter owner next := by simpa using hb
        apply fresh
        simpa [equal, same] using ha
      have nd := List.nodup_append.mpr ⟨ih.1, by simp, disjoint⟩
      simpa only [keys, List.filterMap_append, List.filterMap_cons, parameterKey,
        List.filterMap_nil] using nd
    · intro key member
      simp only [keys, List.filterMap_append, List.filterMap_cons, parameterKey,
        List.filterMap_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with old | same
      · obtain ⟨ordinal, bound, equal⟩ := ih.2 _ old
        exact ⟨ordinal, by omega, equal⟩
      · exact ⟨next, by omega, same⟩
  | @other next expressions prior occurrence ih =>
    simpa only [keys, List.filterMap_append, List.filterMap_cons, parameterKey,
      List.filterMap_nil, List.append_nil] using ih
  | @permute next expressions reordered prior order ih =>
    have perm := order.filterMap parameterKey
    refine ⟨perm.nodup_iff.mp ih.1, ?_⟩
    intro key member
    exact ih.2 key (perm.mem_iff.mpr member)

variable {Id : Type} [DecidableEq Id]

structure ScanState (Id : Type) where
  formals : List (Registration Id)
  recipes : List Id
  registry : List (Id × Nat)

def roleFor (parameter : Parameter Id) : Role :=
  match parameter.annotation with
  | some annotation => if annotation.row.isSome then .computation else .value
  | none => .value

def newFormal (owner scope : Id) (index : Nat) (s : ScanState Id)
    (parameter : Parameter Id) : Registration Id :=
  ⟨owner, index, parameter.id, s.recipes.length, scope, roleFor parameter, none⟩

def appendFormal (owner scope : Id) (index : Nat) (s : ScanState Id)
    (parameter : Parameter Id) : ScanState Id :=
  ⟨s.formals ++ [newFormal owner scope index s parameter],
    s.recipes ++ [parameter.id], (parameter.id, s.formals.length) :: s.registry⟩

/-- The enumeration pass precedes action collection. Scope is the actual
per-parameter scope lookup, represented by one fixed function for the scan.
All non-Lambda source constructors remain in the same enumerated vector. -/
inductive Scan (owner : Id) (scope : Id → Id) :
    Nat → List (Expression Id) → ScanState Id → ScanState Id → Prop where
  | nil : Scan owner scope index [] s s
  | other (tail : Scan owner scope (index + 1) rest before after) :
      Scan owner scope index (.other occurrence :: rest) before after
  | lambda (tail : Scan owner scope (index + 1) rest
      (appendFormal owner (scope parameter.id) index before parameter) after) :
      Scan owner scope index (.lambda occurrence parameter :: rest) before after

theorem scan_prefix (owner : Id) (scope : Id → Id) (index : Nat)
    (expressions : List (Expression Id)) (before after : ScanState Id)
    (scan : Scan owner scope index expressions before after) :
    (∃ suffix, after.formals = before.formals ++ suffix) ∧
      (∃ suffix, after.recipes = before.recipes ++ suffix) := by
  induction scan with
  | nil => exact ⟨⟨[], by simp⟩, ⟨[], by simp⟩⟩
  | other tail ih => exact ih
  | @lambda index rest before parameter after occurrence tail ih =>
    obtain ⟨⟨fs, hf⟩, ⟨rs, hr⟩⟩ := ih
    exact ⟨⟨newFormal owner (scope parameter.id) index before parameter :: fs,
      by simpa [appendFormal, List.append_assoc] using hf⟩,
      ⟨parameter.id :: rs, by simpa [appendFormal, List.append_assoc] using hr⟩⟩

theorem lookup_unchanged (owner : Id) (scope : Id → Id) (index : Nat)
    (expressions : List (Expression Id)) (before after : ScanState Id)
    (scan : Scan owner scope index expressions before after)
    (key : Id) (absent : key ∉ keys expressions) :
    readRegistration after.registry key = readRegistration before.registry key := by
  induction scan with
  | nil => rfl
  | other tail ih => exact ih (by simpa only [keys, List.filterMap_cons, parameterKey] using absent)
  | @lambda index rest before parameter after occurrence tail ih =>
    have facts : key ≠ parameter.id ∧ key ∉ keys rest := by
      simpa [keys, parameterKey] using absent
    rw [ih facts.2]
    simp [appendFormal, readRegistration, Ne.symm facts.1]

theorem formal_read_preserved (owner : Id) (scope : Id → Id) (index : Nat)
    (expressions : List (Expression Id)) (before after : ScanState Id)
    (scan : Scan owner scope index expressions before after)
    (registration : Nat) (formal : Registration Id)
    (read : before.formals[registration]? = some formal) :
    after.formals[registration]? = some formal := by
  obtain ⟨suffix, same⟩ := (scan_prefix owner scope index expressions before after scan).1
  rw [same, List.getElem?_append_left]
  · exact read
  · exact List.getElem?_eq_some_iff.mp read |>.1

theorem recipe_read_preserved (owner : Id) (scope : Id → Id) (index : Nat)
    (expressions : List (Expression Id)) (before after : ScanState Id)
    (scan : Scan owner scope index expressions before after)
    (recipe : Nat) (parameter : Id) (read : before.recipes[recipe]? = some parameter) :
    after.recipes[recipe]? = some parameter := by
  obtain ⟨suffix, same⟩ := (scan_prefix owner scope index expressions before after scan).2
  rw [same, List.getElem?_append_left]
  · exact read
  · exact List.getElem?_eq_some_iff.mp read |>.1

/-- Each selected Lambda's final lookup points to its own appended record.
The key distinctness argument will be supplied by `construction_keys`, rather
than asserted about the final HashMap. -/
theorem scan_origin (owner : Id) (scope : Id → Id) (index : Nat)
    (expressions : List (Expression Id)) (before after : ScanState Id)
    (scan : Scan owner scope index expressions before after)
    (distinct : (keys expressions).Nodup) (offset : Nat)
    (occurrence : Id) (parameter : Parameter Id)
    (selected : expressions[offset]? = some (.lambda occurrence parameter)) :
    ∃ registration formal,
      readRegistration after.registry parameter.id = some registration ∧
      after.formals[registration]? = some formal ∧
      formal.owner = owner ∧ formal.lambda = index + offset ∧
      formal.parameter = parameter.id ∧ formal.scope = scope parameter.id ∧
      after.recipes[formal.recipe]? = some parameter.id := by
  induction scan generalizing offset with
  | nil => simp at selected
  | @other index rest before after occurrence' tail ih =>
    cases offset with
    | zero => simp at selected
    | succ offset =>
      have restDistinct : (keys rest).Nodup := by
        simpa only [keys, List.filterMap_cons, parameterKey] using distinct
      obtain ⟨registration, formal, hm, hf, ho, hl, hp, hs, hr⟩ :=
        ih restDistinct offset (by simpa using selected)
      exact ⟨registration, formal, hm, hf, ho, by omega, hp, hs, hr⟩
  | @lambda index rest before parameter' after occurrence' tail ih =>
    have distinctFacts : parameter'.id ∉ keys rest ∧ (keys rest).Nodup := by
      simpa [keys, parameterKey] using distinct
    cases offset with
    | zero =>
      have same : occurrence' = occurrence ∧ parameter' = parameter := by simpa using selected
      obtain ⟨sameOcc, sameParam⟩ := same
      subst occurrence'
      subst parameter'
      refine ⟨before.formals.length, newFormal owner (scope parameter.id) index before parameter,
        ?_, ?_, rfl, by simp [newFormal], rfl, rfl, ?_⟩
      · rw [lookup_unchanged owner scope (index + 1) rest _ after tail parameter.id distinctFacts.1]
        simp [appendFormal, readRegistration]
      · apply formal_read_preserved owner scope (index + 1) rest _ after tail
        simp [appendFormal]
      · apply recipe_read_preserved owner scope (index + 1) rest _ after tail
        simp [appendFormal, newFormal]
    | succ offset =>
      obtain ⟨registration, formal, hm, hf, ho, hl, hp, hs, hr⟩ :=
        ih distinctFacts.2 offset (by simpa using selected)
      exact ⟨registration, formal, hm, hf, ho, by omega, hp, hs, hr⟩

/-- No uniqueness premise: it is obtained from finite checked ID construction.
Annotation remains attached to the very same selected expression. -/
theorem constructed_scan_origin (brand : Brand) (next : Nat)
    (expressions : List (Expression (Identity Brand)))
    (construction : Construction brand next expressions)
    (scope : Identity Brand → Identity Brand) (before after : ScanState (Identity Brand))
    (scan : Scan (.owner brand) scope 0 expressions before after)
    (index : Nat) (occurrence : Identity Brand) (parameter : Parameter (Identity Brand))
    (selected : expressions[index]? = some (.lambda occurrence parameter)) :
    ∃ registration formal,
      readRegistration after.registry parameter.id = some registration ∧
      after.formals[registration]? = some formal ∧
      formal.owner = .owner brand ∧ formal.lambda = index ∧
      formal.parameter = parameter.id ∧ formal.scope = scope parameter.id ∧
      after.recipes[formal.recipe]? = some parameter.id := by
  simpa using scan_origin (.owner brand) scope 0 expressions before after scan
    (construction_keys brand next expressions construction).1 index occurrence parameter selected

/-- Transport the constructed origin to R169's actual Raw/action fields. The
shared snapshot equations are source-model correspondence obligations, not
independent arbitrary choices of vectors, map and action. -/
theorem collected_origin (brand : Brand) (next : Nat)
    (expressions : List (Expression (Identity Brand)))
    (construction : Construction brand next expressions)
    (scope : Identity Brand → Identity Brand) (before after : ScanState (Identity Brand))
    (scan : Scan (.owner brand) scope 0 expressions before after)
    (x : Raw (Identity Brand)) (a : Action (Identity Brand))
    (sharedFormals : x.formals = after.formals)
    (sharedRecipes : x.recipes = after.recipes)
    (sharedMap : x.formalRegistrations = after.registry)
    (sharedSource : readSource x.sources (.owner brand) = some expressions)
    (index : Nat) (parameter : Parameter (Identity Brand))
    (selected : expressions[index]? = some (.lambda a.occurrence parameter))
    (annotation : parameter.annotation = some a.annotation)
    (registration : readRegistration x.formalRegistrations parameter.id = some a.registration) :
    ∃ formal,
      x.formals[a.registration]? = some formal ∧ formal.owner = .owner brand ∧
      formal.lambda = index ∧ formal.parameter = parameter.id ∧
      x.recipes[formal.recipe]? = some parameter.id ∧
      ∃ sourceParameter,
        readSource x.sources formal.owner = some expressions ∧
        expressions[formal.lambda]? = some (.lambda a.occurrence sourceParameter) ∧
        sourceParameter.id = formal.parameter ∧ sourceParameter.annotation = some a.annotation := by
  obtain ⟨r, f, hm, hf, ho, hl, hp, hs, hr⟩ :=
    constructed_scan_origin brand next expressions construction scope before after scan
      index a.occurrence parameter selected
  have same : r = a.registration := by
    rw [sharedMap, hm] at registration
    exact Option.some.inj registration
  subst r
  exact ⟨f, by simpa [sharedFormals] using hf, ho, hl, hp,
    by simpa [sharedRecipes] using hr,
    parameter, by simpa [ho] using sharedSource, by simpa [hl] using selected, hp.symm, annotation⟩

/-- This supplies the annotation reread omitted from the R169 runtime guards.
The successful trace and its concrete row/permission remain unchanged. -/
theorem successful_annotation_origin (brand : Brand) (next : Nat)
    (expressions : List (Expression (Identity Brand)))
    (construction : Construction brand next expressions)
    (scope : Identity Brand → Identity Brand) (before afterScan : ScanState (Identity Brand))
    (scan : Scan (.owner brand) scope 0 expressions before afterScan)
    (x : Raw (Identity Brand)) (a : Action (Identity Brand))
    (sharedFormals : x.formals = afterScan.formals)
    (sharedRecipes : x.recipes = afterScan.recipes)
    (sharedMap : x.formalRegistrations = afterScan.registry)
    (sharedSource : readSource x.sources (.owner brand) = some expressions)
    (index : Nat) (parameter : Parameter (Identity Brand))
    (selected : expressions[index]? = some (.lambda a.occurrence parameter))
    (annotation : parameter.annotation = some a.annotation)
    (registration : readRegistration x.formalRegistrations parameter.id = some a.registration)
    (f : Registration (Identity Brand)) (r : Row (Identity Brand)) (port : Identity Brand)
    (pending : Option (Permission (Identity Brand))) (after : State (Identity Brand))
    (trace : Trace x a (.ok f r port pending) after) (nonempty : r.concrete ≠ []) :
    (∃ sourceParameter,
      readSource x.sources f.owner = some expressions ∧
      expressions[f.lambda]? = some (.lambda a.occurrence sourceParameter) ∧
      sourceParameter.id = f.parameter ∧ sourceParameter.annotation = some a.annotation) ∧
    ∃ p, pending = some p ∧ p.concrete = r.concrete ∧
      after.permissions = x.before.permissions ++ [p] := by
  obtain ⟨origin, read, ho, hl, hp, hr, payload⟩ :=
    collected_origin brand next expressions construction scope before afterScan scan x a
      sharedFormals sharedRecipes sharedMap sharedSource index parameter selected annotation registration
  obtain ⟨p, prepared, retained, published, state, concrete⟩ :=
    successful_nonempty x a f r port pending after trace nonempty
  have formalRead : x.formals[a.registration]? = some f :=
    ((prepare_exact (inputs x) a f r port).mp prepared).1
  have same : origin = f := Option.some.inj (read.symm.trans formalRead)
  subst origin
  exact ⟨payload, p, published, concrete, by rw [state]⟩

end YulangClosure.FormalEntryOriginR171
