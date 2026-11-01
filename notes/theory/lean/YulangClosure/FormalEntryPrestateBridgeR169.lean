import YulangClosure.SuppressionPermissionR116

/-!
R169 finite constructor bridge. Source authentication: frozen R169 source
handoff, candidate_source.rs:1323--1327,2469--2475 and
candidate_effect.rs:1991--2063. This relation is a finite transcription of
those reads/events, not an operational semantics of Rust or whole source.
Ids are complete branded identities. Other source constructors are retained
as `other`; they cannot supply a Lambda entry. No source language is restricted
by claiming the remaining whole-language obligations here.

The raw Lambda owns its parameter annotation. There is no annotation table.
Fallible reserve/equality/sample outcomes are external events, not proved
native executions. State is only the R39 publication projection; allocation,
bytes, scratch, levels, propagation and caller rollback are omitted.
-/
namespace YulangClosure.FormalEntryPrestateBridgeR169

open ComputationPermissionEntryR39

structure Parameter (Id : Type) where
  id : Id
  annotation : Option (Annotation Id)
  deriving DecidableEq

inductive Expression (Id : Type) where
  | lambda (occurrence : Id) (parameter : Parameter Id)
  | other (occurrence : Id)
  deriving DecidableEq

def eraseExpression {Id : Type} : Expression Id → SourceExpr Id
  | .lambda occurrence parameter => .lambda occurrence parameter.id
  | .other occurrence => .other occurrence

structure Raw (Id : Type) where
  formals : List (Registration Id)
  recipes : List Id
  schedules : List Id
  sources : List (Id × List (Expression Id))
  owners : List (Id × Id)
  occupiedDomains : List Nat
  formalRegistrations : List (Id × Nat)
  before : State Id

variable {Id : Type} [DecidableEq Id]

def readSource : List (Id × List (Expression Id)) → Id → Option (List (Expression Id))
  | [], _ => none
  | (owner, expressions) :: rest, key =>
    if owner = key then some expressions else readSource rest key

def readRegistration : List (Id × Nat) → Id → Option Nat
  | [], _ => none
  | (parameter, registration) :: rest, key =>
    if parameter = key then some registration else readRegistration rest key

def eraseSources (sources : List (Id × List (Expression Id))) :=
  sources.map (fun entry => (entry.1, entry.2.map eraseExpression))

/-- Retained registrations are projected from the actual prior records. -/
def inputs (x : Raw Id) : Inputs Id :=
  ⟨x.formals, x.recipes, x.schedules, eraseSources x.sources, x.owners,
    x.occupiedDomains, x.before.permissions.map (fun p => p.registration)⟩

theorem erased_source_read (sources : List (Id × List (Expression Id))) (owner : Id) :
    localSource (eraseSources sources) owner =
      (readSource sources owner).map (List.map eraseExpression) := by
  induction sources with
  | nil => rfl
  | cons first rest ih =>
    rcases first with ⟨key, expressions⟩
    by_cases same : key = owner
    · simp [eraseSources, localSource, readSource, same]
    · simpa [eraseSources, localSource, readSource, same] using ih

/-- Each constructor appends exactly the action made by the Lambda collector.
The registry key is the actual parameter ID and scope is read from that
registration. Collection alone does not establish constructor acceptance. -/
inductive Collected (x : Raw Id) : Action Id → Prop where
  | lambda (owner : Id) (index : Nat) (expressions : List (Expression Id))
      (occurrence : Id) (parameter : Parameter Id) (annotation : Annotation Id)
      (row : Row Id) (registration : Nat) (formal : Registration Id)
      (source : readSource x.sources owner = some expressions)
      (expression : expressions[index]? = some (.lambda occurrence parameter))
      (annotated : parameter.annotation = some annotation)
      (hasRow : annotation.row = some row)
      (registered : readRegistration x.formalRegistrations parameter.id = some registration)
      (scopeRead : x.formals[registration]? = some formal) :
      Collected x ⟨registration, annotation, occurrence, formal.scope⟩

theorem collected_parameter_payload (x : Raw Id) (a : Action Id)
    (collected : Collected x a) :
    ∃ (owner : Id) (index : Nat) (expressions : List (Expression Id))
      (parameter : Parameter Id) (formal : Registration Id),
      readSource x.sources owner = some expressions ∧
      expressions[index]? = some (.lambda a.occurrence parameter) ∧
      parameter.annotation = some a.annotation ∧
      readRegistration x.formalRegistrations parameter.id = some a.registration ∧
      x.formals[a.registration]? = some formal ∧ a.scope = formal.scope := by
  cases collected with
  | lambda owner index expressions occurrence parameter annotation row registration formal hs he ha hr hg hf =>
    exact ⟨owner, index, expressions, parameter, formal, hs, he, ha, hg, hf, rfl⟩

/-- Copy the source vector in order, including duplicate entries. No equality
with an expected permission is an event premise. -/
def copiedRecord (a : Action Id) (f : Registration Id) (r : Row Id) (port : Id) : Permission Id :=
  ⟨a.registration, f.recipe, f.parameter, a.occurrence, a.annotation.owner,
    a.scope, a.annotation.position, r.position, port, r.concrete⟩

inductive Rejection where
  | noRow | tooManyVariables | noRegistration | alreadyRetained

inductive Phase (Id : Type) where
  | collected
  | row (r : Row Id)
  | registered (f : Registration Id) (r : Row Id)
  | identities (f : Registration Id) (r : Row Id)
  | source (f : Registration Id) (r : Row Id)
  | fresh (f : Registration Id) (r : Row Id)
  | entry (f : Registration Id) (r : Row Id) (port : Id)
  | copied (f : Registration Id) (r : Row Id) (port : Id) (pending : Option (Permission Id))
  | linked (f : Registration Id) (r : Row Id) (port : Id) (pending : Option (Permission Id))
  | published (f : Registration Id) (r : Row Id) (port : Id) (pending : Option (Permission Id))
  | ok (f : Registration Id) (r : Row Id) (port : Id) (pending : Option (Permission Id))
  | sampleError (f : Registration Id) (r : Row Id) (port : Id) (pending : Option (Permission Id))
  | rejected (reason : Rejection)

/-- Finite indexed small-step history: every constructor extends one prefix by
one event. There are no `Valid`, `prepare`, `permissionFor`, or final payload
identity premises. Guard failures shown here are selected early failures;
fallible native operations before publication are not exhaustively modeled. -/
inductive Trace (x : Raw Id) (a : Action Id) : Phase Id → State Id → Prop where
  | collect (source : Collected x a) : Trace x a .collected x.before
  | row (prior : Trace x a .collected x.before)
      (read : a.annotation.row = some r) (arity : r.variables.length ≤ 1) :
      Trace x a (.row r) x.before
  | registered (prior : Trace x a (.row r) x.before)
      (read : x.formals[a.registration]? = some f) :
      Trace x a (.registered f r) x.before
  | identities (prior : Trace x a (.registered f r) x.before)
      (owner : f.owner = a.annotation.owner) (role : f.role = .computation)
      (scope : f.scope = a.scope) (recipe : x.recipes[f.recipe]? = some f.parameter) :
      Trace x a (.identities f r) x.before
  | source (prior : Trace x a (.identities f r) x.before)
      (owner : ownerLookup x.owners a.occurrence = some a.annotation.owner)
      (expressions : List (Expression Id)) (annotation : Option (Annotation Id))
      (read : readSource x.sources f.owner = some expressions)
      (lambda : expressions[f.lambda]? =
        some (.lambda a.occurrence ⟨f.parameter, annotation⟩)) :
      Trace x a (.source f r) x.before
  | fresh (prior : Trace x a (.source f r) x.before)
      (domain : f.recipe ∉ x.occupiedDomains)
      (retained : a.registration ∉ x.before.permissions.map (fun p => p.registration)) :
      Trace x a (.fresh f r) x.before
  | entry (prior : Trace x a (.fresh f r) x.before) (read : f.entry = some port) :
      Trace x a (.entry f r port) x.before
  | copyEmpty (prior : Trace x a (.entry f r port) x.before) (empty : r.concrete = []) :
      Trace x a (.copied f r port none) x.before
  | copyConcrete (prior : Trace x a (.entry f r port) x.before)
      (nonempty : r.concrete ≠ []) (reserveSucceeded : Bool) (reserve : reserveSucceeded = true) :
      Trace x a (.copied f r port (some (copiedRecord a f r port))) x.before
  | linkEmpty (prior : Trace x a (.copied f r port pending) x.before)
      (empty : r.variables = []) :
      Trace x a (.linked f r port pending) x.before
  | linkSymbolic (prior : Trace x a (.copied f r port pending) x.before)
      (name : Id) (symbolic : r.variables = [name])
      (tailSucceeded equalitySucceeded : Bool)
      (tail : tailSucceeded = true) (equality : equalitySucceeded = true) :
      Trace x a (.linked f r port pending)
        ⟨x.before.permissions, x.before.links ++
          [⟨a.occurrence, 45, .entry port, .symbolic a.scope name⟩,
           ⟨a.occurrence, 46, .symbolic a.scope name, .entry port⟩], x.before.inflow⟩
  | publish (prior : Trace x a (.linked f r port pending) s) :
      Trace x a (.published f r port pending)
        ⟨s.permissions ++ pending.toList, s.links, s.inflow⟩
  | sampleOk (prior : Trace x a (.published f r port pending) s) :
      Trace x a (.ok f r port pending) s
  | sampleError (prior : Trace x a (.published f r port pending) s) :
      Trace x a (.sampleError f r port pending) s
  | noRow (prior : Trace x a .collected x.before) (missing : a.annotation.row = none) :
      Trace x a (.rejected .noRow) x.before
  | tooManyVariables (prior : Trace x a .collected x.before)
      (read : a.annotation.row = some r) (many : 1 < r.variables.length) :
      Trace x a (.rejected .tooManyVariables) x.before
  | noRegistration (prior : Trace x a (.row r) x.before)
      (missing : x.formals[a.registration]? = none) :
      Trace x a (.rejected .noRegistration) x.before
  | alreadyRetained (prior : Trace x a (.source f r) x.before)
      (retained : a.registration ∈ x.before.permissions.map (fun p => p.registration)) :
      Trace x a (.rejected .alreadyRetained) x.before

theorem entry_prepared (x : Raw Id) (a : Action Id) (f : Registration Id)
    (r : Row Id) (port : Id) (trace : Trace x a (.entry f r port) x.before) :
    prepare (inputs x) a = some (f, r, port) := by
  cases trace with
  | entry fresh hp =>
    cases fresh with
    | fresh source hd hr =>
      cases source with
      | source identities ho expressions annotation hs hl =>
        cases identities with
        | identities registered owner role scope recipe =>
          cases registered with
          | registered row hf =>
            cases row with
            | row collected rowRead arity =>
              apply prepare_of_valid (inputs x) a f r port hf rowRead hp
              refine ⟨owner, role, scope, recipe, ?_, ?_, hd, hr, arity⟩
              · simpa only [inputs, owner] using ho
              · simp only [sourceLambda, inputs, erased_source_read, hs,
                  Option.map_some, Option.bind_eq_bind, Option.bind_some, List.getElem?_map, hl, eraseExpression]

theorem copied_exact (x : Raw Id) (a : Action Id) (f : Registration Id)
    (r : Row Id) (port : Id) (pending : Option (Permission Id))
    (trace : Trace x a (.copied f r port pending) x.before) :
    prepare (inputs x) a = some (f, r, port) ∧ pending = permissionFor a f r port := by
  cases trace with
  | copyEmpty prior empty =>
    exact ⟨entry_prepared x a f r port prior, by simp [permissionFor, empty]⟩
  | copyConcrete prior nonempty ready reserve =>
    exact ⟨entry_prepared x a f r port prior, by
      simp [permissionFor, nonempty, copiedRecord, build]⟩

theorem linked_exact (x : Raw Id) (a : Action Id) (f : Registration Id)
    (r : Row Id) (port : Id) (pending : Option (Permission Id)) (after : State Id)
    (trace : Trace x a (.linked f r port pending) after) :
    prepare (inputs x) a = some (f, r, port) ∧ pending = permissionFor a f r port ∧
      after = ⟨x.before.permissions, x.before.links ++ symbolicLinks a r port, x.before.inflow⟩ := by
  cases trace with
  | linkEmpty prior empty =>
    obtain ⟨prepared, copied⟩ := copied_exact x a f r port pending prior
    exact ⟨prepared, copied, by simp [symbolicLinks, empty]⟩
  | linkSymbolic prior name symbolic tailReady equalityReady tail equality =>
    obtain ⟨prepared, copied⟩ := copied_exact x a f r port pending prior
    exact ⟨prepared, copied, by simp [symbolicLinks, symbolic]⟩

theorem published_exact (x : Raw Id) (a : Action Id) (f : Registration Id)
    (r : Row Id) (port : Id) (pending : Option (Permission Id)) (after : State Id)
    (trace : Trace x a (.published f r port pending) after) :
    prepare (inputs x) a = some (f, r, port) ∧ pending = permissionFor a f r port ∧
      after = ⟨x.before.permissions ++ pending.toList,
        x.before.links ++ symbolicLinks a r port, x.before.inflow⟩ := by
  cases trace with
  | publish prior =>
    obtain ⟨prepared, copied, state⟩ := linked_exact x a f r port pending _ prior
    subst state
    exact ⟨prepared, copied, rfl⟩

/-- A successful trace supplies the two exact R39 equations for the record
actually appended. These are conclusions, not assumed constructor equations. -/
theorem successful_nonempty (x : Raw Id) (a : Action Id) (f : Registration Id)
    (r : Row Id) (port : Id) (pending : Option (Permission Id)) (after : State Id)
    (trace : Trace x a (.ok f r port pending) after) (nonempty : r.concrete ≠ []) :
    ∃ p, prepare (inputs x) a = some (f, r, port) ∧
      permissionFor a f r port = some p ∧ pending = some p ∧
      after = ⟨x.before.permissions ++ [p],
        x.before.links ++ symbolicLinks a r port, x.before.inflow⟩ ∧
      p.concrete = r.concrete := by
  cases trace with
  | sampleOk prior =>
    obtain ⟨prepared, copied, state⟩ := published_exact x a f r port pending after prior
    have exactCopy : pending = some (copiedRecord a f r port) := by
      simpa [permissionFor, nonempty, build, copiedRecord] using copied
    refine ⟨copiedRecord a f r port, prepared, ?_, exactCopy, ?_, rfl⟩
    · simp [permissionFor, nonempty, build, copiedRecord]
    · simpa only [exactCopy, Option.toList_some] using state

theorem successful_empty (x : Raw Id) (a : Action Id) (f : Registration Id)
    (r : Row Id) (port : Id) (pending : Option (Permission Id)) (after : State Id)
    (trace : Trace x a (.ok f r port pending) after) (empty : r.concrete = []) :
    prepare (inputs x) a = some (f, r, port) ∧ permissionFor a f r port = none ∧
      pending = none ∧ after.permissions = x.before.permissions := by
  cases trace with
  | sampleOk prior =>
    obtain ⟨prepared, copied, state⟩ := published_exact x a f r port pending after prior
    have noneCopy : pending = none := by simpa [permissionFor, empty] using copied
    refine ⟨prepared, by simp [permissionFor, empty], noneCopy, ?_⟩
    rw [state, noneCopy]
    simp

theorem duplicate_guard_derived (x : Raw Id) (a : Action Id) (f : Registration Id)
    (r : Row Id) (port : Id) (trace : Trace x a (.entry f r port) x.before) :
    a.registration ∉ (inputs x).retainedRegistrations ∧
      ¬ ∃ p ∈ x.before.permissions, p.registration = a.registration := by
  have valid := ((prepare_exact (inputs x) a f r port).mp
    (entry_prepared x a f r port trace)).2.2.2
  have fresh := valid.2.2.2.2.2.2.2.1
  refine ⟨fresh, ?_⟩
  rintro ⟨p, member, same⟩
  apply fresh
  change a.registration ∈ x.before.permissions.map (fun p => p.registration)
  exact List.mem_map.mpr ⟨p, member, same⟩

theorem retained_input_rejected (x : Raw Id) (a : Action Id) (f : Registration Id)
    (registered : x.formals[a.registration]? = some f)
    (retained : ∃ p ∈ x.before.permissions, p.registration = a.registration) :
    prepare (inputs x) a = none := by
  apply duplicate_or_domain_rejected (inputs x) a f registered
  right
  obtain ⟨p, member, same⟩ := retained
  exact List.mem_map.mpr ⟨p, member, same⟩

theorem malformed_input_rejected (x : Raw Id) (a : Action Id)
    (malformed : a.annotation.row = none ∨ x.formals[a.registration]? = none) :
    prepare (inputs x) a = none := by
  rcases malformed with row | formal
  · cases hf : (inputs x).formals[a.registration]? <;> simp [prepare, hf, row]
  · exact invalid_registration_rejected (inputs x) a formal

/-- Sample failure has the already-published state, which differs from the
pre-state for every nonempty concrete row. No Err-implies-restoration law. -/
theorem sample_error_changed_state (x : Raw Id) (a : Action Id) (f : Registration Id)
    (r : Row Id) (port : Id) (pending : Option (Permission Id)) (after : State Id)
    (trace : Trace x a (.sampleError f r port pending) after) (nonempty : r.concrete ≠ []) :
    ∃ p, prepare (inputs x) a = some (f, r, port) ∧
      permissionFor a f r port = some p ∧ pending = some p ∧
      after.permissions = x.before.permissions ++ [p] ∧ after ≠ x.before := by
  cases trace with
  | sampleError prior =>
    obtain ⟨p, prepared, retained, same, state, concrete⟩ :=
      successful_nonempty x a f r port pending after (.sampleOk prior) nonempty
    have permissions : after.permissions = x.before.permissions ++ [p] := by rw [state]
    refine ⟨p, prepared, retained, same, permissions, ?_⟩
    intro equal
    have lengths := congrArg (fun s : State Id => s.permissions.length) equal
    rw [permissions, List.length_append] at lengths
    simp at lengths

/-- R116 application discharges only its prepared/retained producer premises.
SelectedSource, complete operation matching and endpoint decoding stay explicit. -/
theorem selected_endpoint_application (x : Raw Id) (a : Action Id) (f : Registration Id)
    (r : Row Id) (port endpoint : Id) (pending : Option (Permission Id)) (after : State Id)
    (provider arm : SuppressionPermissionR116.Operation Id)
    (trace : Trace x a (.ok f r port pending) after) (nonempty : r.concrete ≠ [])
    (selected : SuppressionPermissionR116.SelectedSource a r arm)
    (matched : SuppressionPermissionR116.operationMatch provider arm = true)
    (providerEndpoint : endpoint = provider.family) :
    ∃ p, pending = some p ∧ after.permissions = x.before.permissions ++ [p] ∧
      endpoint ∈ p.concrete := by
  obtain ⟨p, prepared, retained, same, state, concrete⟩ :=
    successful_nonempty x a f r port pending after trace nonempty
  refine ⟨p, same, ?_, ?_⟩
  · rw [state]
  · exact SuppressionPermissionR116.selected_endpoint_member (inputs x) a f r port endpoint p
      provider arm prepared retained selected matched providerEndpoint

/-- Ordered duplicates survive publication exactly. This is a conditional trace
consequence, not a native runtime or selected singleton-Suppress receipt. -/
theorem duplicate_order_preserved (x : Raw Id) (a : Action Id) (f : Registration Id)
    (r : Row Id) (port first last : Id) (pending : Option (Permission Id)) (after : State Id)
    (trace : Trace x a (.ok f r port pending) after)
    (row : r.concrete = [first, first, last]) :
    ∃ p, pending = some p ∧ after.permissions = x.before.permissions ++ [p] ∧
      p.concrete = [first, first, last] := by
  have nonempty : r.concrete ≠ [] := by simp [row]
  obtain ⟨p, prepared, retained, same, state, concrete⟩ :=
    successful_nonempty x a f r port pending after trace nonempty
  exact ⟨p, same, by rw [state], concrete.trans row⟩

/-- Fully explicit finite raw inputs used only to show the modeled path is
inhabited. Numeric IDs do not assert native/HIR reachability. -/
def exampleFormal : Registration Nat := ⟨1, 0, 2, 0, 3, .computation, some 4⟩
def exampleRow (concrete variables : List Nat) : Row Nat := ⟨5, concrete, variables⟩
def exampleAnnotation (concrete variables : List Nat) : Annotation Nat :=
  ⟨1, 6, some (exampleRow concrete variables)⟩
def exampleParameter (concrete variables : List Nat) : Parameter Nat :=
  ⟨2, some (exampleAnnotation concrete variables)⟩
def exampleAction (concrete variables : List Nat) : Action Nat :=
  ⟨0, exampleAnnotation concrete variables, 17, 3⟩
def exampleRaw (concrete variables : List Nat) : Raw Nat :=
  ⟨[exampleFormal], [2], [], [(1, [.lambda 17 (exampleParameter concrete variables)])],
    [(17, 1)], [], [(2, 0)], ⟨[], [], []⟩⟩

theorem finite_entry_example (concrete variables : List Nat)
    (arity : variables.length ≤ 1) :
    Trace (exampleRaw concrete variables) (exampleAction concrete variables)
      (.entry exampleFormal (exampleRow concrete variables) 4)
      (exampleRaw concrete variables).before := by
  refine Trace.entry (Trace.fresh (Trace.source
    (Trace.identities (Trace.registered (Trace.row (Trace.collect ?_) rfl arity) rfl)
      rfl rfl rfl rfl) rfl
    [.lambda 17 (exampleParameter concrete variables)]
    (some (exampleAnnotation concrete variables)) rfl rfl) (by simp [exampleRaw]) (by simp [exampleRaw])) rfl
  exact Collected.lambda 1 0 [.lambda 17 (exampleParameter concrete variables)] 17
    (exampleParameter concrete variables) (exampleAnnotation concrete variables)
    (exampleRow concrete variables) 0 exampleFormal rfl rfl rfl rfl rfl rfl

theorem finite_symbolic_publication_example :
    let x := exampleRaw [7, 7, 11] [13]
    let a := exampleAction [7, 7, 11] [13]
    let r := exampleRow [7, 7, 11] [13]
    let p := copiedRecord a exampleFormal r 4
    let after : State Nat := ⟨[p],
      [⟨17, 45, .entry 4, .symbolic 3 13⟩,
       ⟨17, 46, .symbolic 3 13, .entry 4⟩], []⟩
    Trace x a (.published exampleFormal r 4 (some p)) after := by
  exact Trace.publish (Trace.linkSymbolic
    (Trace.copyConcrete (finite_entry_example [7, 7, 11] [13] (by decide))
      (by decide) true rfl) 13 rfl true true rfl rfl)

theorem finite_symbolic_success_and_error_example :
    let x := exampleRaw [7, 7, 11] [13]
    let a := exampleAction [7, 7, 11] [13]
    let r := exampleRow [7, 7, 11] [13]
    let p := copiedRecord a exampleFormal r 4
    let after : State Nat := ⟨[p],
      [⟨17, 45, .entry 4, .symbolic 3 13⟩,
       ⟨17, 46, .symbolic 3 13, .entry 4⟩], []⟩
    Trace x a (.ok exampleFormal r 4 (some p)) after ∧
      Trace x a (.sampleError exampleFormal r 4 (some p)) after ∧
      p.concrete = [7, 7, 11] ∧ after ≠ x.before := by
  exact ⟨Trace.sampleOk finite_symbolic_publication_example,
    Trace.sampleError finite_symbolic_publication_example, rfl, by decide⟩

theorem finite_empty_example :
    let x := exampleRaw [] []
    let a := exampleAction [] []
    let r := exampleRow [] []
    Trace x a (.ok exampleFormal r 4 none) x.before ∧
      permissionFor a exampleFormal r 4 = none := by
  exact ⟨Trace.sampleOk (Trace.publish (Trace.linkEmpty
    (Trace.copyEmpty (finite_entry_example [] [] (by decide)) rfl) rfl)), rfl⟩

end YulangClosure.FormalEntryPrestateBridgeR169
