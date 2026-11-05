import Yulang.EvaluationSafety

/-!
# Operational computed-read prefixes

This semantics contains no dependency checker. Closures store their lexical
local environment; computed global names access the supplied store. A `Reads`
derivation describes a finite CBV prefix ending at an attempted computed read,
so subsequent divergence does not make that read disappear. Earlier siblings
of the read have ordinary finite `Eval` derivations. The store is not assumed
to contain only initialized names.
-/

namespace Yulang.EvaluationSafety

open EvaluationOrder FiniteReachability

inductive Value (n : Nat) where
  | unit
  | bool : Bool → Value n
  | pair : Value n → Value n → Value n
  | closure : Expr n → List (Value n) → Value n
  deriving Repr

abbrev Store (n : Nat) := Fin n → Option (Value n)

/-- Closure origin is syntactic, not a premise about its reads or ordering. -/
inductive Closed (world : Module n) : Value n → Prop where
  | unit : Closed world .unit
  | bool : Closed world (.bool value)
  | pair : Closed world left → Closed world right → Closed world (.pair left right)
  | closure : Within world (.lam body) →
      (∀ value ∈ captured, Closed world value) → Closed world (.closure body captured)

def ClosedEnv (world : Module n) (environment : List (Value n)) : Prop :=
  ∀ value ∈ environment, Closed world value

def ClosedStore (world : Module n) (store : Store n) : Prop :=
  ∀ name value, store name = some value → Closed world value

/-- Ordinary finite evaluation; trace entries are computed-global reads. -/
inductive Eval (program : Program n) (store : Store n) :
    List (Value n) → Expr n → Value n → List (Fin n) → Prop where
  | bound : environment[index]? = some value →
      Eval program store environment (.bound index) value []
  | read : program.computed name = true → store name = some value →
      Eval program store environment (.reference name) value [name]
  | namedValue : program.computed name = false →
      Eval program store [] (program.body name) value reads →
      Eval program store environment (.reference name) value reads
  | unit : Eval program store environment .lit .unit []
  | bool : Eval program store environment (.bool value) (.bool value) []
  | closure : Eval program store environment (.lam body) (.closure body environment) []
  | app : Eval program store environment fn (.closure body captured) fnReads →
      Eval program store environment arg argument argReads →
      Eval program store (argument :: captured) body result bodyReads →
      Eval program store environment (.app fn arg) result (fnReads ++ argReads ++ bodyReads)
  | pair : Eval program store environment left first leftReads →
      Eval program store environment right second rightReads →
      Eval program store environment (.pair left right) (.pair first second) (leftReads ++ rightReads)
  | fst : Eval program store environment operand (.pair first second) reads →
      Eval program store environment (.fst operand) first reads
  | snd : Eval program store environment operand (.pair first second) reads →
      Eval program store environment (.snd operand) second reads
  | branchTrue : Eval program store environment condition (.bool true) conditionReads →
      Eval program store environment yes result armReads →
      Eval program store environment (.branch condition yes no) result (conditionReads ++ armReads)
  | branchFalse : Eval program store environment condition (.bool false) conditionReads →
      Eval program store environment no result armReads →
      Eval program store environment (.branch condition yes no) result (conditionReads ++ armReads)

theorem eval_closed (world : Module n) (store : Store n) (closedStore : ClosedStore world store)
    (evaluation : Eval world.program store environment expression result reads)
    (inside : Within world expression) (closedEnv : ClosedEnv world environment) :
    Closed world result := by
  induction evaluation with
  | bound found => exact closedEnv _ (List.mem_of_getElem? found)
  | read _ found => exact closedStore _ _ found
  | namedValue _ _ ih => exact ih (declaration_within world _) (by simp [ClosedEnv])
  | unit => exact .unit
  | bool => exact .bool
  | closure => exact .closure inside closedEnv
  | app fnEval argEval _ ihfn iharg ihbody =>
      have fnClosed := ihfn (inside.subexpression (.appLeft .refl)) closedEnv
      have argClosed := iharg (inside.subexpression (.appRight .refl)) closedEnv
      cases fnClosed with
      | closure origin capturedClosed =>
          exact ihbody (origin.subexpression (.lam .refl)) (by
            intro value member
            rcases List.mem_cons.mp member with same | present
            · subst value
              exact argClosed
            · exact capturedClosed value present)
  | pair _ _ ihleft ihright =>
      exact .pair (ihleft (inside.subexpression (.pairLeft .refl)) closedEnv)
        (ihright (inside.subexpression (.pairRight .refl)) closedEnv)
  | fst _ ih =>
      have pairClosed := ih (inside.subexpression (.fst .refl)) closedEnv
      cases pairClosed with
      | pair firstClosed _ => exact firstClosed
  | snd _ ih =>
      have pairClosed := ih (inside.subexpression (.snd .refl)) closedEnv
      cases pairClosed with
      | pair _ secondClosed => exact secondClosed
  | branchTrue _ _ _ ihyes => exact ihyes (inside.subexpression (.yes .refl)) closedEnv
  | branchFalse _ _ _ ihno => exact ihno (inside.subexpression (.no .refl)) closedEnv

/-- Prefix ending at a computed-global read, whether or not evaluation finishes. -/
inductive Reads (program : Program n) (store : Store n) :
    List (Value n) → Expr n → Fin n → Prop where
  | read : program.computed name = true → Reads program store environment (.reference name) name
  | namedValue : program.computed name = false →
      Reads program store [] (program.body name) target →
      Reads program store environment (.reference name) target
  | appFn : Reads program store environment fn target →
      Reads program store environment (.app fn arg) target
  | appArg : Eval program store environment fn (.closure body captured) fnReads →
      Reads program store environment arg target →
      Reads program store environment (.app fn arg) target
  | appBody : Eval program store environment fn (.closure body captured) fnReads →
      Eval program store environment arg argument argReads →
      Reads program store (argument :: captured) body target →
      Reads program store environment (.app fn arg) target
  | pairLeft : Reads program store environment left target →
      Reads program store environment (.pair left right) target
  | pairRight : Eval program store environment left first leftReads →
      Reads program store environment right target →
      Reads program store environment (.pair left right) target
  | fst : Reads program store environment operand target →
      Reads program store environment (.fst operand) target
  | snd : Reads program store environment operand target →
      Reads program store environment (.snd operand) target
  | condition : Reads program store environment condition target →
      Reads program store environment (.branch condition yes no) target
  | yes : Eval program store environment condition (.bool true) conditionReads →
      Reads program store environment yes target →
      Reads program store environment (.branch condition yes no) target
  | no : Eval program store environment condition (.bool false) conditionReads →
      Reads program store environment no target →
      Reads program store environment (.branch condition yes no) target

theorem Reads.computed (read : Reads program store environment expression target) :
    program.computed target = true := by
  induction read <;> assumption

/-- Every read in a completed trace is also an operational read prefix. -/
theorem Eval.reads (evaluation : Eval program store environment expression result trace)
    (present : target ∈ trace) : Reads program store environment expression target := by
  induction evaluation with
  | bound _ | unit | bool | closure => cases present
  | read computed _ =>
      have same := List.mem_singleton.mp present
      subst target
      exact .read computed
  | namedValue pure _ ih => exact .namedValue pure (ih present)
  | app fnEval argEval _ ihfn iharg ihbody =>
      rcases List.mem_append.mp present with present | present
      · rcases List.mem_append.mp present with present | present
        · exact .appFn (ihfn present)
        · exact .appArg fnEval (iharg present)
      · exact .appBody fnEval argEval (ihbody present)
  | pair leftEval _ ihleft ihright =>
      rcases List.mem_append.mp present with present | present
      · exact .pairLeft (ihleft present)
      · exact .pairRight leftEval (ihright present)
  | fst _ ih => exact .fst (ih present)
  | snd _ ih => exact .snd (ih present)
  | branchTrue conditionEval _ ihcondition ihyes =>
      rcases List.mem_append.mp present with present | present
      · exact .condition (ihcondition present)
      · exact .yes conditionEval (ihyes present)
  | branchFalse conditionEval _ ihcondition ihno =>
      rcases List.mem_append.mp present with present | present
      · exact .condition (ihcondition present)
      · exact .no conditionEval (ihno present)

theorem eval_named_lambda (shape : program.body name = .lam body)
    (evaluation : Eval program store environment (.reference name) result trace) :
    result = .closure body [] ∧ trace = [] := by
  cases evaluation with
  | read computed _ => simp [Program.computed, shape, Expr.isValue] at computed
  | namedValue _ evaluated =>
      rw [shape] at evaluated
      cases evaluated
      exact ⟨rfl, rfl⟩

theorem application_body_supported (world : Module n) (allowed : Fin n → Prop)
    (closed : GraphClosed world allowed)
    (evaluation : Eval world.program store environment fn (.closure body captured) trace)
    (origin : Within world (.lam body))
    (support : Supported world allowed (.app fn arg)) : Supported world allowed body := by
  have parts := support.app_parts
  cases known : knownCallee world.program fn with
  | false =>
      rw [unknown_callSeeds world fn known] at parts
      exact Supported.function_body world allowed body origin parts.2.2
  | true =>
      rcases (knownCallee_exact world.program fn).mp known with
        ⟨inlineBody, rfl⟩ | ⟨name, namedBody, rfl, shape⟩
      · cases evaluation
        exact parts.2.2
      · have equality := (eval_named_lambda shape evaluation).1
        have sameBody := (Value.closure.inj equality).1
        subst body
        intro target member
        apply closed name (parts.1 name (by simp [activeSeeds])) target
        simpa [Module.graph, shape, fullSeeds] using
          activeSeeds_subset_fullSeeds world namedBody target member

/-- The induction concerns real environment-based evaluation prefixes. Only
closure provenance and finite graph closure are premises; no read upper bound
or initialization order is assumed. -/
theorem reads_supported (world : Module n) (store : Store n)
    (closedStore : ClosedStore world store) (allowed : Fin n → Prop)
    (closed : GraphClosed world allowed)
    (event : Reads world.program store environment expression target)
    (inside : Within world expression) (closedEnv : ClosedEnv world environment)
    (support : Supported world allowed expression) : allowed target := by
  induction event with
  | read _ => exact support _ (by simp [activeSeeds])
  | namedValue _ _ ih =>
      exact ih (declaration_within world _) (by simp [ClosedEnv]) (support.named_body closed)
  | appFn _ ih =>
      exact ih (inside.subexpression (.appLeft .refl)) closedEnv support.app_parts.1
  | appArg _ _ ih =>
      exact ih (inside.subexpression (.appRight .refl)) closedEnv support.app_parts.2.1
  | appBody fnEval argEval _ ih =>
      have fnClosed := eval_closed world store closedStore fnEval
        (inside.subexpression (.appLeft .refl)) closedEnv
      have argClosed := eval_closed world store closedStore argEval
        (inside.subexpression (.appRight .refl)) closedEnv
      cases fnClosed with
      | closure origin capturedClosed =>
          apply ih (origin.subexpression (.lam .refl))
          · intro value member
            rcases List.mem_cons.mp member with same | present
            · subst value
              exact argClosed
            · exact capturedClosed value present
          · exact application_body_supported world allowed closed fnEval origin support
  | pairLeft _ ih =>
      exact ih (inside.subexpression (.pairLeft .refl)) closedEnv
        (fun t h => support t (List.mem_append_left _ h))
  | pairRight _ _ ih =>
      exact ih (inside.subexpression (.pairRight .refl)) closedEnv
        (fun t h => support t (List.mem_append_right _ h))
  | fst _ ih => exact ih (inside.subexpression (.fst .refl)) closedEnv support
  | snd _ ih => exact ih (inside.subexpression (.snd .refl)) closedEnv support
  | condition _ ih =>
      exact ih (inside.subexpression (.condition .refl)) closedEnv
        (fun t h => support t (List.mem_append_left _ (List.mem_append_left _ h)))
  | yes _ _ ih =>
      exact ih (inside.subexpression (.yes .refl)) closedEnv
        (fun t h => support t (List.mem_append_left _ (List.mem_append_right _ h)))
  | no _ _ ih =>
      exact ih (inside.subexpression (.no .refl)) closedEnv
        (fun t h => support t (List.mem_append_right _ h))

/-- The executable dependency calculation contains every operational read. -/
theorem reads_needed (world : Module n) (store : Store n)
    (closedStore : ClosedStore world store)
    (event : Reads world.program store environment expression target)
    (inside : Within world expression) (closedEnv : ClosedEnv world environment) :
    Needed world expression target := by
  have closed : GraphClosed world (Needed world expression) := by
    intro source included target edge
    exact Reach.step included edge
  exact reads_supported world store closedStore (Needed world expression) closed event inside closedEnv
    (fun _ seed => Reach.seed seed)

theorem reads_dependencies (world : Module n) (store : Store n)
    (closedStore : ClosedStore world store)
    (event : Reads world.program store environment expression target)
    (inside : Within world expression) (closedEnv : ClosedEnv world environment) :
    dependencies world expression target = true :=
  (dependencies_exact _ _ _).mpr (reads_needed world store closedStore event inside closedEnv)

/-- A read prefix cannot reach a self/future computed binding at an accepted site. -/
theorem accepted_read_earlier (world : Module n) (store : Store n)
    (closedStore : ClosedStore world store) (position : Nat)
    (accepted : checkAt world position expression = true)
    (event : Reads world.program store environment expression target)
    (inside : Within world expression) (closedEnv : ClosedEnv world environment) :
    world.program.position target < position :=
  (checkAt_exact _ _ _).mp accepted target
    (reads_needed world store closedStore event inside closedEnv) event.computed

theorem accepted_initializer_read_earlier (world : Module n) (store : Store n)
    (closedStore : ClosedStore world store) (accepted : check world = true)
    (source : Fin n) (computed : world.program.computed source = true)
    (event : Reads world.program store [] (world.program.body source) target) :
    world.program.position target < world.program.position source := by
  apply accepted_read_earlier world store closedStore _
    ((checkAt_exact _ _ _).mpr (((check_exact world).mp accepted).1 source computed)) event
  · exact declaration_within world source
  · simp [ClosedEnv]

theorem accepted_statement_read_earlier (world : Module n) (store : Store n)
    (closedStore : ClosedStore world store) (accepted : check world = true)
    (statement : Statement n) (present : statement ∈ world.statements)
    (event : Reads world.program store [] statement.expression target) :
    world.program.position target < statement.position := by
  apply accepted_read_earlier world store closedStore _
    ((checkAt_exact _ _ _).mpr (((check_exact world).mp accepted).2 statement present)) event
  · exact statement_within world statement present
  · simp [ClosedEnv]

/-- The ordinary sequential-execution invariant: all earlier computed bindings
have finished and their values are in the store. This says nothing about which
names the current expression will read. -/
def ReadyBefore (world : Module n) (store : Store n) (position : Nat) : Prop :=
  ∀ name, world.program.computed name = true → world.program.position name < position →
    ∃ value, store name = some value

theorem accepted_read_initialized (world : Module n) (store : Store n)
    (closedStore : ClosedStore world store) (position : Nat)
    (ready : ReadyBefore world store position)
    (accepted : checkAt world position expression = true)
    (event : Reads world.program store environment expression target)
    (inside : Within world expression) (closedEnv : ClosedEnv world environment) :
    ∃ value, store target = some value :=
  ready target event.computed
    (accepted_read_earlier world store closedStore position accepted event inside closedEnv)

/-- Record a completed initializer's value, without reordering declarations. -/
def record (store : Store n) (name : Fin n) (value : Value n) : Store n :=
  fun target => if target = name then some value else store target

theorem record_closed (world : Module n) (store : Store n) (name : Fin n) (value : Value n)
    (closedStore : ClosedStore world store) (closedValue : Closed world value) :
    ClosedStore world (record store name value) := by
  intro target result found
  by_cases same : target = name
  · simp [record, same] at found
    subst result
    exact closedValue
  · exact closedStore target result (by simpa [record, same] using found)

/-- A source-position prefix advances by recording the unique declaration at
that position. The distinct-position premise is a property of the schedule. -/
theorem record_ready_next (world : Module n) (store : Store n) (name : Fin n) (value : Value n)
    (ready : ReadyBefore world store (world.program.position name))
    (uniquePosition : ∀ other, world.program.position other = world.program.position name → other = name) :
    ReadyBefore world (record store name value) (world.program.position name + 1) := by
  intro target computed earlier
  by_cases same : target = name
  · exact ⟨value, by simp [record, same]⟩
  · have strict : world.program.position target < world.program.position name := by
      have different : world.program.position target ≠ world.program.position name :=
        fun equal => same (uniquePosition target equal)
      omega
    obtain ⟨previous, found⟩ := ready target computed strict
    exact ⟨previous, by simpa [record, same] using found⟩

theorem empty_store_closed (world : Module n) : ClosedStore world (fun _ => none) := by
  intro name value found
  cases found

theorem empty_prefix_ready (world : Module n) : ReadyBefore world (fun _ => none) 0 := by
  intro name computed earlier
  omega

/-- A completed step of sequential initialization keeps the actual stored
closure-origin and prefix invariants. Every read in this step found a value in
the old prefix store; future values need not have been installed. -/
theorem initialize_next (world : Module n) (store : Store n) (name : Fin n)
    (closedStore : ClosedStore world store)
    (ready : ReadyBefore world store (world.program.position name))
    (uniquePosition : ∀ other, world.program.position other = world.program.position name → other = name)
    (accepted : check world = true) (computed : world.program.computed name = true)
    (evaluation : Eval world.program store [] (world.program.body name) value trace) :
    ClosedStore world (record store name value) ∧
    ReadyBefore world (record store name value) (world.program.position name + 1) ∧
    (∀ target ∈ trace, ∃ result, store target = some result) := by
  refine ⟨record_closed world store name value closedStore ?_,
    record_ready_next world store name value ready uniquePosition, ?_⟩
  · exact eval_closed world store closedStore evaluation (declaration_within world name)
      (by simp [ClosedEnv])
  · intro target present
    apply accepted_read_initialized world store closedStore _ ready
      ((checkAt_exact _ _ _).mpr (((check_exact world).mp accepted).1 name computed))
      (evaluation.reads present) (declaration_within world name)
    simp [ClosedEnv]

/-- An actual evaluated source-position prefix. Every stored result is introduced
by an `Eval` derivation. Positions containing no computed declaration need no
step; value declarations are available through `Eval.namedValue`. -/
inductive EvaluatedPrefix (world : Module n) : Nat → Store n → Prop where
  | empty : EvaluatedPrefix world 0 (fun _ => none)
  | skip : EvaluatedPrefix world position store →
      (∀ name, world.program.computed name = true → world.program.position name ≠ position) →
      EvaluatedPrefix world (position + 1) store
  | step : EvaluatedPrefix world (world.program.position name) store →
      (∀ other, world.program.position other = world.program.position name → other = name) →
      world.program.computed name = true →
      Eval world.program store [] (world.program.body name) value trace →
      EvaluatedPrefix world (world.program.position name + 1) (record store name value)

theorem EvaluatedPrefix.invariants (completed : EvaluatedPrefix world position store) :
    ClosedStore world store ∧ ReadyBefore world store position := by
  induction completed with
  | empty => exact ⟨empty_store_closed _, empty_prefix_ready _⟩
  | skip _ noCurrent ih =>
      refine ⟨ih.1, ?_⟩
      intro name computed earlier
      apply ih.2 name computed
      have different := noCurrent name computed
      omega
  | step _ uniquePosition _ evaluation ih =>
      refine ⟨record_closed _ _ _ _ ih.1 ?_, record_ready_next _ _ _ _ ih.2 uniquePosition⟩
      exact eval_closed _ _ ih.1 evaluation (declaration_within _ _) (by simp [ClosedEnv])

/-- Prospective availability for an actual initialized prefix. The current
expression need not finish: a missing-store read prefix is already impossible. -/
theorem accepted_prefix_read_initialized (world : Module n) (store : Store n)
    (completed : EvaluatedPrefix world position store)
    (accepted : checkAt world position expression = true)
    (event : Reads world.program store [] expression target)
    (inside : Within world expression) : ∃ value, store target = some value :=
  accepted_read_initialized world store completed.invariants.1 position completed.invariants.2
    accepted event inside (by simp [ClosedEnv])

theorem accepted_prefix_initializer_read_initialized (world : Module n) (store : Store n)
    (source : Fin n) (completed : EvaluatedPrefix world (world.program.position source) store)
    (accepted : check world = true) (computed : world.program.computed source = true)
    (event : Reads world.program store [] (world.program.body source) target) :
    ∃ value, store target = some value :=
  accepted_prefix_read_initialized world store completed
    ((checkAt_exact _ _ _).mpr (((check_exact world).mp accepted).1 source computed))
    event (declaration_within world source)

end Yulang.EvaluationSafety
