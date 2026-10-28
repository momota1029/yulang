import YulangClosure.OriginalSourceGeneration
import YulangClosure.RecordBoundaryExecution

/-!
Source-owned direct record adapters. Construction is independent of runtime
presence and produces the ordered program and every indexed comparison.
The represented child conversions are identity and finite nested record
adapters. Their preservation is proved here, not supplied as ChildrenSafe.
This local source construction does not claim whole Kernel interpretation.
-/
namespace YulangClosure.OriginalSourceRecordBoundary

open RecordBoundary

/-- A depth-indexed presentation of finite nested record declarations. The
index bounds representation depth, not source evaluation or inference. -/
def Ty (Atom : Type) : Nat → Type
  | 0 => Atom
  | n + 1 => Sum Atom (List (Field (Ty Atom n)))

instance tyDecidableEq [DecidableEq Atom] (n : Nat) : DecidableEq (Ty Atom n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq Atom)
  | succ n ih =>
      letI := ih
      exact inferInstanceAs (DecidableEq (Sum Atom (List (Field (Ty Atom n)))))

def Value (Payload : Type) : Nat → Type
  | 0 => Payload
  | n + 1 => Sum Payload (List (Nat × Option (Value Payload n)))

instance valueDecidableEq [DecidableEq Payload] (n : Nat) : DecidableEq (Value Payload n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq Payload)
  | succ n ih =>
      letI := ih
      exact inferInstanceAs (DecidableEq (Sum Payload (List (Nat × Option (Value Payload n)))))

/-- Raw executable syntax: identity or one ordered record scan, retaining
its original boundary and complete source/target indexed shape. -/
def Cast (Meta Atom : Type) : Nat → Type
  | 0 => Unit
  | n + 1 => Sum Unit (Meta × List (NativeRecordPlan.Slot Meta (Ty Atom n)) ×
      List (FieldPlan (Ty Atom n) (Cast Meta Atom n)))

def construct [DecidableEq Atom] : (n : Nat) → Meta → Ty Atom n → Ty Atom n →
    Option (Cast Meta Atom n)
  | 0, _, source, target => if source = target then some () else none
  | _ + 1, _, .inl source, .inl target =>
      if source = target then some (.inl ()) else none
  | n + 1, boundary, .inr source, .inr target =>
      match NativeRecordPlan.shape boundary source 0 target with
      | .error _ => none
      | .ok slots => do
          let plan ← NativeRecordPlan.fill (construct n) slots
          pure (.inr (boundary, slots, plan))
  | _ + 1, _, _, _ => none

def run : (n : Nat) → Cast Meta Atom n → Value Payload n → Value Payload n
  | 0, _, value => value
  | _ + 1, .inl _, value => value
  | n + 1, .inr (_, _, plan), .inr values =>
      .inr (execute (run n) (visible values) plan)
  | _ + 1, .inr _, .inl value => .inl value

/-- Independent payload/visible-record typing; neither compiler nor run
success occurs in this definition. -/
def Typed (leaf : Payload → Atom → Prop) : (n : Nat) → Value Payload n → Ty Atom n → Prop
  | 0, value, ty => leaf value ty
  | _ + 1, .inl value, .inl ty => leaf value ty
  | n + 1, .inr values, .inr fields =>
      ViewTyped (Typed leaf n) (signature fields) (visible values)
  | _ + 1, _, _ => False

theorem construct_record [DecidableEq Atom]
    (n : Nat) (boundary : Meta) (source target : List (Field (Ty Atom n)))
    (adapter : Cast Meta Atom (n + 1))
    (built : construct (n + 1) boundary (.inr source) (.inr target) = some adapter) :
    ∃ slots plan,
      NativeRecordPlan.shape boundary source 0 target = .ok slots ∧
      NativeRecordPlan.fill (construct n) slots = some plan ∧
      adapter = .inr (boundary, slots, plan) := by
  simp only [construct] at built
  cases shaped : NativeRecordPlan.shape boundary source 0 target with
  | error failure => simp [shaped] at built
  | ok slots =>
      cases filled : NativeRecordPlan.fill (construct n) slots with
      | none => simp [shaped, filled] at built
      | some plan =>
          simp [shaped, filled] at built
          exact ⟨slots, plan, rfl, filled, Option.some.inj built.symm⟩

/-- All recursive child contracts are discharged by the same construction
induction; no plan, successful comparison oracle or child-safety law is input. -/
theorem construct_preserves [DecidableEq Atom] (leaf : Payload → Atom → Prop)
    (n : Nat) (boundary : Meta) (source target : Ty Atom n)
    (adapter : Cast Meta Atom n)
    (built : construct n boundary source target = some adapter)
    (value : Value Payload n) (typed : Typed leaf n value source) :
    Typed leaf n (run n adapter value) target := by
  induction n generalizing boundary with
  | zero =>
      simp only [construct] at built
      split at built
      next same => simpa [run, Typed, same] using typed
      next => contradiction
  | succ n ih =>
      cases source with
      | inl source =>
          cases target with
          | inl target =>
              simp only [construct] at built
              split at built
              next same =>
                  cases built
                  simpa [run, same] using typed
              next => contradiction
          | inr target => simp [construct] at built
      | inr source =>
          cases target with
          | inl target => simp [construct] at built
          | inr target =>
              obtain ⟨slots, plan, shaped, filled, rfl⟩ :=
                construct_record n boundary source target adapter built
              cases value with
              | inl value => exact False.elim typed
              | inr values =>
                  have compiled := NativeRecordPlan.filled_compile shaped filled
                  have children : ChildSound (Typed leaf n) (construct n boundary)
                      (PureChild (Event := Empty) (run n)) := by
                    intro a b cast input trace output resolved inputTyped executed
                    rcases executed with ⟨_, rfl⟩
                    exact ih boundary a b cast resolved input inputTyped
                  exact compiled_run_preserves compiled typed
                    (by intro label h; contradiction) children
                    (execute_runs (Event := Empty) (run n) (visible values) plan)

/-- No declared common optional payload is skipped statically, including
inputs in which that particular payload will be absent at runtime. -/
theorem common_payload_constructed [DecidableEq Atom]
    (n : Nat) (boundary : Meta) (source target : List (Field (Ty Atom n)))
    (adapter : Cast Meta Atom (n + 1))
    (built : construct (n + 1) boundary (.inr source) (.inr target) = some adapter)
    (field : Field (Ty Atom n)) (member : field ∈ target)
    (origin : Spec (Ty Atom n)) (common : signature source field.1 = some origin) :
    ∃ child, construct n boundary origin.ty field.2.ty = some child := by
  obtain ⟨slots, plan, shaped, filled, sameAdapter⟩ := construct_record n boundary source target adapter built
  have valid := compile_sound (NativeRecordPlan.filled_compile shaped filled)
  clear built shaped filled sameAdapter adapter slots
  induction valid with
  | nil => contradiction
  | @cons head entry tail rest first restValid ih =>
      cases List.mem_cons.mp member with
      | inl same =>
          subst field
          cases entry with
          | absent absent =>
              cases first.1
              simp only [FieldPlan.Valid] at first
              simp only [FieldPlan.target] at common
              rw [first.2.1] at common
              contradiction
          | convert actual declared child =>
              cases first.1
              have same : declared = origin := Option.some.inj (first.2.1.symm.trans common)
              subst declared
              exact ⟨child, first.2.2.2⟩
      | inr member => exact ih member

/-- Exact visible-label law for a constructed record adapter. -/
theorem constructed_survivors [DecidableEq Atom] (leaf : Payload → Atom → Prop)
    (n : Nat) (boundary : Meta) (source target : List (Field (Ty Atom n)))
    (adapter : Cast Meta Atom (n + 1))
    (built : construct (n + 1) boundary (.inr source) (.inr target) = some adapter)
    (values : List (Nat × Option (Value Payload n)))
    (typed : Typed leaf (n + 1) (.inr values) (.inr source)) :
    ∃ output, run (n + 1) adapter (.inr values) = .inr output ∧
      ∀ label, (visible output label).isSome =
        ((visible values label).isSome && (signature target label).isSome) := by
  obtain ⟨slots, plan, shaped, filled, rfl⟩ := construct_record n boundary source target adapter built
  refine ⟨execute (run n) (visible values) plan, rfl, ?_⟩
  exact run_survivors (compile_sound (NativeRecordPlan.filled_compile shaped filled)) typed
    (execute_runs (Event := Empty) (run n) (visible values) plan)

theorem successive_boundaries_survivors [DecidableEq Atom] (leaf : Payload → Atom → Prop)
    (n : Nat) (firstOwner secondOwner : Meta)
    (source middle target : List (Field (Ty Atom n)))
    (first second : Cast Meta Atom (n + 1))
    (firstBuilt : construct (n + 1) firstOwner (.inr source) (.inr middle) = some first)
    (secondBuilt : construct (n + 1) secondOwner (.inr middle) (.inr target) = some second)
    (values : List (Nat × Option (Value Payload n)))
    (typed : Typed leaf (n + 1) (.inr values) (.inr source)) :
    ∃ output, run (n + 1) second (run (n + 1) first (.inr values)) = .inr output ∧
      ∀ label, (visible output label).isSome =
        ((visible values label).isSome && (signature middle label).isSome &&
          (signature target label).isSome) := by
  obtain ⟨intermediate, firstRun, firstPresence⟩ :=
    constructed_survivors leaf n firstOwner source middle first firstBuilt values typed
  have intermediateTyped := construct_preserves leaf (n + 1) firstOwner
    (.inr source) (.inr middle) first firstBuilt (.inr values) typed
  rw [firstRun] at intermediateTyped
  obtain ⟨output, secondRun, secondPresence⟩ :=
    constructed_survivors leaf n secondOwner middle target second secondBuilt intermediate intermediateTyped
  refine ⟨output, by rw [firstRun, secondRun], ?_⟩
  intro label
  rw [secondPresence, firstPresence]

def pureObserve (value : Value Payload n) :
    RecordBoundaryExecution.Observation (Value Payload n) (Value Payload n) Empty Empty Empty := .returned value

private theorem trace_append
    {step : State → RecordBoundaryExecution.Observation State Result Request Response Failure}
    {response : Request → Response → Prop}
    (first : RecordBoundaryExecution.Trace step response a b)
    (second : RecordBoundaryExecution.Trace step response b c) :
    RecordBoundaryExecution.Trace step response a c := by
  induction second with
  | refl => exact first
  | tail hp hs ih => exact .tail ih hs

/-- The actual ordered scan has a finite execution to the pure evaluator's
output. This is constructed, not a supplied normal-run assumption. -/
theorem pure_scan_completes (n : Nat) (input : View (Value Payload n))
    (plan : List (FieldPlan (Ty Atom n) (Cast Meta Atom n)))
    (output : List (Nat × Option (Value Payload n))) :
    RecordBoundaryExecution.Trace (RecordBoundaryExecution.step (run n) pureObserve input)
      (fun _ _ : Empty => False) (.scan output plan)
      (.scan (output ++ execute (run n) input plan) []) := by
  induction plan generalizing output with
  | nil =>
      simp only [execute, List.append_nil]
      exact .refl _
  | cons entry rest ih =>
      cases entry with
      | absent target =>
          have first : RecordBoundaryExecution.Trace
              (RecordBoundaryExecution.step (run n) pureObserve input)
              (fun _ _ : Empty => False) (.scan output (.absent target :: rest))
              (.scan (output ++ [(target.1, none)]) rest) :=
            .tail (.refl _) (.internal rfl)
          simpa [execute, List.append_assoc] using trace_append first (ih (output ++ [(target.1, none)]))
      | convert target source cast =>
          cases found : input target.1 with
          | none =>
              have first : RecordBoundaryExecution.Trace
                  (RecordBoundaryExecution.step (run n) pureObserve input)
                  (fun _ _ : Empty => False) (.scan output (.convert target source cast :: rest))
                  (.scan (output ++ [(target.1, none)]) rest) :=
                .tail (.refl _) (.internal (by simp [RecordBoundaryExecution.step, found]))
              simpa [execute, found, List.append_assoc] using
                trace_append first (ih (output ++ [(target.1, none)]))
          | some value =>
              have first : RecordBoundaryExecution.Trace
                  (RecordBoundaryExecution.step (run n) pureObserve input)
                  (fun _ _ : Empty => False) (.scan output (.convert target source cast :: rest))
                  (.child output (.convert target source cast) rest (run n cast value)) :=
                .tail (.refl _) (.internal (by simp [RecordBoundaryExecution.step, found]))
              have second : RecordBoundaryExecution.Trace
                  (RecordBoundaryExecution.step (run n) pureObserve input)
                  (fun _ _ : Empty => False) (.scan output (.convert target source cast :: rest))
                  (.scan (output ++ [(target.1, some (run n cast value))]) rest) :=
                .tail first (.internal rfl)
              simpa [execute, found, List.append_assoc] using
                trace_append second (ih (output ++ [(target.1, some (run n cast value))]))

theorem constructed_record_execution [DecidableEq Atom]
    (n : Nat) (boundary : Meta) (source target : List (Field (Ty Atom n)))
    (adapter : Cast Meta Atom (n + 1))
    (built : construct (n + 1) boundary (.inr source) (.inr target) = some adapter)
    (values : List (Nat × Option (Value Payload n))) :
    ∃ slots plan output, adapter = .inr (boundary, slots, plan) ∧
      run (n + 1) adapter (.inr values) = .inr output ∧
      RecordBoundaryExecution.Trace
        (RecordBoundaryExecution.step (run n) pureObserve (visible values))
        (fun _ _ : Empty => False) (.scan [] plan) (.scan output []) ∧
      RecordBoundaryExecution.step (run n) pureObserve (visible values)
        (.scan output ([] : List (FieldPlan (Ty Atom n) (Cast Meta Atom n)))) = .returned output := by
  obtain ⟨slots, plan, _, _, rfl⟩ := construct_record n boundary source target adapter built
  exact ⟨slots, plan, execute (run n) (visible values) plan, rfl, rfl,
    pure_scan_completes n (visible values) plan [], rfl⟩

/-- Identity and recursively constructed record children need no foreign
request/response contract: their concrete evaluator returns a typed value. -/
theorem constructed_children_safe [DecidableEq Atom] (leaf : Payload → Atom → Prop)
    (n : Nat) (boundary : Meta) :
    RecordBoundaryExecution.ChildrenSafe (Typed leaf n) (construct n boundary) (run n)
      pureObserve (fun _ : Empty => False) (fun _ _ : Empty => False) := by
  intro source target adapter value built typed depth
  cases depth with
  | zero => trivial
  | succ depth => exact construct_preserves leaf n boundary source target adapter built value typed

/-- All finite outer scan/child prefixes are safe for the actually built
record program. The child contract is derived above, not supplied here. -/
theorem constructed_record_prefixes [DecidableEq Atom] (leaf : Payload → Atom → Prop)
    (n : Nat) (boundary : Meta) (source target : List (Field (Ty Atom n)))
    (adapter : Cast Meta Atom (n + 1))
    (built : construct (n + 1) boundary (.inr source) (.inr target) = some adapter)
    (values : List (Nat × Option (Value Payload n)))
    (typed : Typed leaf (n + 1) (.inr values) (.inr source)) :
    ∃ slots plan, adapter = .inr (boundary, slots, plan) ∧
      RecordBoundaryExecution.SafeAll
        (RecordBoundaryExecution.step (run n) pureObserve (visible values))
        (RecordBoundaryExecution.OutputsGood (Typed leaf n) (visible values) target)
        (fun _ : Empty => False) (fun _ _ : Empty => False)
        (.scan [] plan) := by
  obtain ⟨slots, plan, shaped, filled, same⟩ := construct_record n boundary source target adapter built
  exact ⟨slots, plan, same, RecordBoundaryExecution.native_filled_safe shaped filled typed
    (constructed_children_safe leaf n boundary)⟩

open OriginalSource

variable {Atom Payload Meta : Type}

inductive ScopeStep where
  | existsE (binder : Binder)
  | forallE (binder : Binder)
  | sharedE (binder : Binder)
  | initializerE (site : Site)
  | executionE (binder : Binder)
  | publishGroup (bindings : List (Name × Site))
  | atPublication (name : Name)
  | aliasPublication (original aliasName : Name)
  | choice (site : Site) (right : Bool)
  deriving DecidableEq, Repr

/-- The original boundary, distinct endpoints, and complete static enclosing
telescope. No inferred endpoint equality creates a boundary. -/
structure Owner where
  route : List Nat
  scope : List ScopeStep
  site : Site
  context : Context
  lower : Endpoint
  upper : Endpoint
  annotation : Annotation
  deriving DecidableEq, Repr

private def annotationAt (site : Site) (context : Context) (premises : List Premise) :
    Option Annotation := premises.findSome? fun premise => match premise with
  | .atom data => if data.kind = .finalAnnotationFormation ∧ data.site = site ∧
      data.context = context then data.annotation else none
  | _ => none

private def localOwners (route : List Nat) (scope : List ScopeStep)
    (premises : List Premise) : List Owner :=
  premises.filterMap fun premise => match premise with
  | .boundary site context lower upper =>
      (annotationAt site context premises).map fun annotation =>
        ⟨route, scope, site, context, lower, upper, annotation⟩
  | _ => none

mutual
/-- Registration order is a static syntax traversal, not an execution
schedule. Every enclosing source frame is retained in the owner. -/
def owners (route : List Nat) (scope : List ScopeStep) : RuleTree → List Owner
  | .rule _ _ _ premises children =>
      localOwners route scope premises ++ forestOwners route scope 0 children
  | .existsE binder body => owners route (scope ++ [.existsE binder]) body
  | .forallE binder body => owners route (scope ++ [.forallE binder]) body
  | .sharedE binder body => owners route (scope ++ [.sharedE binder]) body
  | .initializerE site body => owners route (scope ++ [.initializerE site]) body
  | .executionE binder body => owners route (scope ++ [.executionE binder]) body
  | .publishGroup bindings body => owners route (scope ++ [.publishGroup bindings]) body
  | .atPublication name body => owners route (scope ++ [.atPublication name]) body
  | .aliasPublication original aliasName body =>
      owners route (scope ++ [.aliasPublication original aliasName]) body
  | .choice site left right => owners (route ++ [0]) (scope ++ [.choice site false]) left ++
      owners (route ++ [1]) (scope ++ [.choice site true]) right

def forestOwners (route : List Nat) (scope : List ScopeStep) (index : Nat) : RuleForest → List Owner
  | .nil => []
  | .cons head tail => owners (route ++ [index]) scope head ++
      forestOwners route scope (index + 1) tail
end

def sourceOwners (context : Context) (source : Source category) : List Owner :=
  owners [] [] (sourceRules context source)

/-- Raw declaration readouts. These are independently registered original
types and direct conversion identities, not semantic safety promises. -/
structure Declarations (Atom : Type) (depth : Nat) where
  endpoint : Endpoint → Option (Ty Atom depth)
  annotation : Annotation → Option (Ty Atom depth)
  conversion : Owner → Option Declaration

structure Program (Atom : Type) (depth : Nat) where
  owner : Owner
  declaration : Declaration
  source : Ty Atom depth
  target : Ty Atom depth
  code : Cast Owner Atom depth

def compileOwner [DecidableEq Atom] (declarations : Declarations Atom depth)
    (owner : Owner) : Option (Program Atom depth) := do
  let source ← declarations.endpoint owner.lower
  let target ← declarations.annotation owner.annotation
  let declaration ← declarations.conversion owner
  let code ← construct depth owner source target
  pure ⟨owner, declaration, source, target, code⟩

def compileOwners [DecidableEq Atom] (declarations : Declarations Atom depth) :
    List Owner → Option (List (Program Atom depth))
  | [] => some []
  | owner :: rest => do
      let program ← compileOwner declarations owner
      let programs ← compileOwners declarations rest
      pure (program :: programs)

/-- A failed boundary fails this boundary inventory. Nothing is filtered
out and no native solver/source-typing success is consulted. -/
def compileSource [DecidableEq Atom] (declarations : Declarations Atom depth)
    (context : Context) (source : Source category) : Option (List (Program Atom depth)) :=
  compileOwners declarations (sourceOwners context source)

theorem compile_owner_readback [DecidableEq Atom]
    (declarations : Declarations Atom depth) (owner : Owner) (program : Program Atom depth)
    (compiled : compileOwner declarations owner = some program) :
    program.owner = owner ∧ declarations.endpoint owner.lower = some program.source ∧
      declarations.annotation owner.annotation = some program.target ∧
      declarations.conversion owner = some program.declaration ∧
      construct depth owner program.source program.target = some program.code := by
  obtain ⟨source, sourceAt, compiled⟩ := Option.bind_eq_some_iff.mp compiled
  obtain ⟨target, targetAt, compiled⟩ := Option.bind_eq_some_iff.mp compiled
  obtain ⟨declaration, declarationAt, compiled⟩ := Option.bind_eq_some_iff.mp compiled
  obtain ⟨code, built, compiled⟩ := Option.bind_eq_some_iff.mp compiled
  cases Option.some.inj compiled
  exact ⟨rfl, sourceAt, targetAt, declarationAt, built⟩

theorem compiled_owner_preserves [DecidableEq Atom]
    (leaf : Payload → Atom → Prop) (declarations : Declarations Atom depth)
    (owner : Owner) (program : Program Atom depth)
    (compiled : compileOwner declarations owner = some program)
    (value : Value Payload depth) (typed : Typed leaf depth value program.source) :
    Typed leaf depth (run depth program.code value) program.target :=
  construct_preserves leaf depth owner program.source program.target program.code
    (compile_owner_readback declarations owner program compiled).2.2.2.2 value typed

theorem compile_owners_exact [DecidableEq Atom]
    (declarations : Declarations Atom depth) (registered : List Owner)
    (programs : List (Program Atom depth))
    (compiled : compileOwners declarations registered = some programs) :
    Aligned (fun owner program => compileOwner declarations owner = some program) registered programs := by
  induction registered generalizing programs with
  | nil => cases Option.some.inj compiled; exact .nil
  | cons owner rest ih =>
      obtain ⟨program, first, compiled⟩ := Option.bind_eq_some_iff.mp compiled
      obtain ⟨tail, remaining, compiled⟩ := Option.bind_eq_some_iff.mp compiled
      cases Option.some.inj compiled
      exact .cons first (ih tail remaining)

theorem compiled_source_member [DecidableEq Atom]
    (declarations : Declarations Atom depth) (context : Context) (source : Source category)
    (programs : List (Program Atom depth))
    (compiled : compileSource declarations context source = some programs)
    (program : Program Atom depth) (member : program ∈ programs) :
    ∃ owner ∈ sourceOwners context source, compileOwner declarations owner = some program := by
  have aligned := compile_owners_exact declarations (sourceOwners context source) programs compiled
  clear compiled
  generalize sourceOwners context source = registered at aligned ⊢
  induction aligned with
  | nil => contradiction
  | @cons owner first rest tail compiled restAligned ih =>
      cases List.mem_cons.mp member with
      | inl same => subst program; exact ⟨owner, List.mem_cons_self, compiled⟩
      | inr remaining =>
          obtain ⟨found, present, compiled⟩ := ih remaining
          exact ⟨found, List.mem_cons_of_mem owner present, compiled⟩

theorem compiled_source_preserves [DecidableEq Atom]
    (leaf : Payload → Atom → Prop) (declarations : Declarations Atom depth)
    (context : Context) (source : Source category) (programs : List (Program Atom depth))
    (compiled : compileSource declarations context source = some programs)
    (program : Program Atom depth) (member : program ∈ programs)
    (value : Value Payload depth) (typed : Typed leaf depth value program.source) :
    Typed leaf depth (run depth program.code value) program.target := by
  obtain ⟨owner, _, built⟩ := compiled_source_member declarations context source programs compiled program member
  exact compiled_owner_preserves leaf declarations owner program built value typed

/-- This is the original direct Boundary.actual branch, with its source
owner and computed adapter. Other Kernel fields are not claimed interpreted. -/
def recordKernel [DecidableEq Atom] (original : Kernel SemanticValue)
    (declarations : Declarations Atom depth) (context : Context) (source : Source category) :
    Kernel SemanticValue :=
  {original with conversion := fun environment site localContext lower upper declaration =>
    original.conversion environment site localContext lower upper declaration ∨
    ∃ owner ∈ sourceOwners context source, ∃ program,
      owner.site = site ∧ owner.context = localContext ∧ owner.lower = lower ∧ owner.upper = upper ∧
      compileOwner declarations owner = some program ∧ program.declaration = declaration}

theorem constructed_original_boundary [DecidableEq Atom] (original : Kernel SemanticValue)
    (declarations : Declarations Atom depth) (context : Context) (source : Source category)
    (environment : Environment SemanticValue) (owner : Owner) (program : Program Atom depth)
    (registered : owner ∈ sourceOwners context source)
    (compiled : compileOwner declarations owner = some program) :
    Boundary (recordKernel original declarations context source) environment
      owner.site owner.context owner.lower owner.upper := by
  apply Boundary.actual _ _ _ _ program.declaration
  exact Or.inr ⟨owner, registered, program, rfl, rfl, rfl, rfl, compiled, rfl⟩

namespace Witness

def required : Ty Bool 1 := .inr [(0, ⟨true, false⟩)]
def empty : Ty Bool 1 := .inr []
def optional : Ty Bool 1 := .inr [(0, ⟨true, true⟩)]
def incompatible : Ty Bool 1 := .inr [(0, ⟨false, true⟩)]

def original : Source .bindings :=
  .binding 20 30 (some 101)
    (.record ⟨10, some 100⟩ (.recordField 11 0 (.literal ⟨12, none⟩ (.int 1)) .recordNil))
    .bindingsNil

def firstOwner : Owner :=
  ⟨[0], [.initializerE 20], 10, [], ⟨10, .synthesis⟩, ⟨10, .writtenTarget⟩, 100⟩
def secondOwner : Owner :=
  ⟨[1], [.initializerE 20], 20, [], ⟨10, .finalRoot⟩, ⟨20, .writtenTarget⟩, 101⟩

def declarations : Declarations Bool 1 where
  endpoint endpoint := if endpoint = ⟨10, .synthesis⟩ then some required
    else if endpoint = ⟨10, .finalRoot⟩ then some empty else none
  annotation id := if id = 100 then some empty else if id = 101 then some optional else none
  conversion owner := if owner = firstOwner then some 910
    else if owner = secondOwner then some 920 else none

def firstProgram : Program Bool 1 :=
  ⟨firstOwner, 910, required, empty, .inr (firstOwner, [], [])⟩
def secondProgram : Program Bool 1 :=
  ⟨secondOwner, 920, empty, optional,
    .inr (secondOwner, [.absent 0 (0, ⟨true, true⟩)], [.absent (0, ⟨true, true⟩)])⟩

def input : Value (Sum String Int) 1 := .inr [(0, some (.inr 1))]

def leaf : Sum String Int → Bool → Prop
  | .inl _, false | .inr _, true => True
  | _, _ => False

theorem original_boundary_owners : sourceOwners [] original = [firstOwner, secondOwner] := by
  simp only [sourceOwners, original, sourceRules, bindingsRulesK, expressionRulesK]
  rfl

theorem original_source_constructs_both :
    compileSource declarations [] original = some [firstProgram, secondProgram] := by
  rw [compileSource, original_boundary_owners]
  rfl

theorem exact_source_programs :
    firstProgram.owner.lower = ⟨10, .synthesis⟩ ∧
    secondProgram.owner.lower = ⟨10, .finalRoot⟩ ∧
    firstProgram.owner.scope = [.initializerE 20] ∧
    secondProgram.owner.scope = [.initializerE 20] ∧
    firstProgram.declaration ≠ secondProgram.declaration := by decide

/-- Both boundaries were built from the actual annotated record initializer
and outer annotated binding. The second receives the first visible output. -/
theorem source_sequence_does_not_resurrect :
    run 1 firstProgram.code input = .inr [] ∧
    run 1 secondProgram.code (run 1 firstProgram.code input) = .inr [(0, none)] := by
  exact ⟨rfl, rfl⟩

theorem input_typed : Typed leaf 1 input required := by
  intro label
  by_cases h : label = 0 <;>
    simp [Typed, signature, visible, SlotTyped, leaf, h]

/-- No typing or child-safety premise is supplied for this source instance.
Its actual data, raw source, declarations and both adapters are constructed. -/
theorem original_source_sequence_typed :
    Typed leaf 1 (run 1 firstProgram.code input) firstProgram.target ∧
      Typed leaf 1 (run 1 secondProgram.code (run 1 firstProgram.code input)) secondProgram.target := by
  have first := compiled_source_preserves leaf declarations [] original
    [firstProgram, secondProgram] original_source_constructs_both firstProgram
    (List.mem_cons_self) input input_typed
  have middle : Typed leaf 1 (run 1 firstProgram.code input) secondProgram.source := first
  exact ⟨first, compiled_source_preserves leaf declarations [] original
    [firstProgram, secondProgram] original_source_constructs_both secondProgram
    (List.mem_cons_of_mem _ List.mem_cons_self) _ middle⟩

theorem absent_common_is_statically_compared :
    construct 1 firstOwner optional incompatible = none ∧
    (visible ([] : List (Nat × Option (Sum String Int))) 0) = none := by
  exact ⟨rfl, rfl⟩

theorem nested_identity_and_record_construct :
    ∃ code : Cast Owner Bool 2,
      construct 2 firstOwner
        (.inr [(4, ⟨required, false⟩)]) (.inr [(4, ⟨empty, false⟩)]) = some code ∧
      run 2 code (.inr [(4, some input)]) =
        (.inr [(4, some (.inr []))] : Value (Sum String Int) 2) := by
  refine ⟨.inr (firstOwner,
    [.child ⟨firstOwner, 0, 0, ⟨required, false⟩, (4, ⟨empty, false⟩)⟩],
    [.convert (4, ⟨empty, false⟩) ⟨required, false⟩ firstProgram.code]), ?_, ?_⟩
  · rfl
  · rfl

end Witness

end YulangClosure.OriginalSourceRecordBoundary
