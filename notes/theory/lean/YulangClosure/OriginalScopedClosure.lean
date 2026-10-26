import YulangClosure.OriginalSourceEvents
import YulangClosure.OriginalSourceRecordBoundary

/-!
Lossless, source-constructed scoped programs and publication-root allocation.

Authority: SG §§3.3–5.2. The input is the existing full Source/Definition/Client,
not a supplied graph, typing proof, or presentation-correctness law. Every
original rule, premise, scope constructor and publication instruction survives
erasure. Copies change description-frame indices; actual event and Shared
references retain their original owners and the existing environment routing.

This is the lossless presentation/addressing part of allocation, not an
eligibility decision for every semantic Desc dependency. References do not
replace original Kernel admission or rename its endpoint meanings. The complete
semantic interpretation of originalNewInstance, symbolic endpoint grafts,
fixed-dependency closure and the all-valid-view extension theorem remain separate. In particular
Definition alone omits an outer binding annotation; publication roots below
are extracted from the full source program, including its actual boundary.
-/
namespace YulangClosure.OriginalScopedClosure

open OriginalSource
open OriginalSourceEvents (Route ScopeEntry)

abbrev ScopeStep := OriginalSourceRecordBoundary.ScopeStep
abbrev FrameId := List Route

structure Position where
  origin : Declaration
  route : Route
  telescope : List ScopeStep
  frame : FrameId
  deriving DecidableEq, Repr

def Position.child (position : Position) (tag : Nat) : Position :=
  {position with route := position.route ++ [tag]}

def Position.under (position : Position) (step : ScopeStep) : Position :=
  {(position.child 0) with telescope := position.telescope ++ [step]}

def Position.copy (framePrefix : FrameId) (position : Position) : Position :=
  {position with frame := framePrefix ++ position.frame}

structure BinderSite where
  origin : Declaration
  introduction : ScopeEntry
  telescope : List ScopeStep
  deriving DecidableEq, Repr

structure Occurrence where
  position : Position
  binder : Binder
  deriving DecidableEq, Repr

def Occurrence.site (occurrence : Occurrence) : BinderSite :=
  ⟨occurrence.position.origin,
    ⟨occurrence.position.route, occurrence.binder⟩, occurrence.position.telescope⟩

/-- These are presentation references, not replacement runtime identities.
An event reference is completed by the actual environment path below. -/
inductive Reference where
  | description (frame : FrameId) (site : BinderSite)
  | viewLogic (frame : FrameId) (site : BinderSite)
  | eventProof (frame : FrameId) (site : BinderSite)
  | instance (frame : FrameId) (site : BinderSite)
  | shared (site : BinderSite)
  | event (site : BinderSite)
  deriving DecidableEq, Repr

def Occurrence.reference (occurrence : Occurrence) : Reference :=
  match occurrence.binder.kind with
  | .description => .description occurrence.position.frame occurrence.site
  | .viewLogic => .viewLogic occurrence.position.frame occurrence.site
  | .eventProof => .eventProof occurrence.position.frame occurrence.site
  | .publishedInstance => .instance occurrence.position.frame occurrence.site
  | .shared => .shared occurrence.site
  | .invocation | .receipt | .returnRebind | .rigidOperation | .response | .oneShot =>
      .event occurrence.site

def Occurrence.copy (framePrefix : FrameId) (occurrence : Occurrence) : Occurrence :=
  {occurrence with position := occurrence.position.copy framePrefix}

/-- Only the original publishedInstance binder opens a description frame.
An alias has no such binder and therefore creates no frame. -/
def atBinder (position : Position) (binder : Binder) : Occurrence :=
  ⟨if binder.kind == .publishedInstance then
      {position with frame := position.frame ++ [position.route]} else position, binder⟩

mutual
inductive Program where
  | rule (position : Position) (rule : Rule) (site : Site) (context : Context)
      (premises : List Premise) (children : Programs)
  | existsE (occurrence : Occurrence) (body : Program)
  | forallE (occurrence : Occurrence) (body : Program)
  | initializerE (position : Position) (site : Site) (body : Program)
  | executionE (occurrence : Occurrence) (body : Program)
  | sharedE (occurrence : Occurrence) (body : Program)
  | publishGroup (position : Position) (bindings : List (Name × Site)) (body : Program)
  | atPublication (position : Position) (name : Name) (body : Program)
  | aliasPublication (position : Position) (original aliasName : Name) (body : Program)
  | choice (position : Position) (site : Site) (left right : Program)
inductive Programs where
  | nil
  | cons (head : Program) (tail : Programs)
end

mutual
def allocate (position : Position) : RuleTree → Program
  | .rule rule site context premises children =>
      .rule position rule site context premises (allocateForest (position.child 0) children)
  | .existsE binder body =>
      let occurrence := atBinder position binder
      .existsE occurrence (allocate (occurrence.position.under (.existsE binder)) body)
  | .forallE binder body =>
      let occurrence := atBinder position binder
      .forallE occurrence (allocate (occurrence.position.under (.forallE binder)) body)
  | .initializerE site body =>
      .initializerE position site (allocate (position.under (.initializerE site)) body)
  | .executionE binder body =>
      let occurrence := atBinder position binder
      .executionE occurrence (allocate (occurrence.position.under (.executionE binder)) body)
  | .sharedE binder body =>
      let occurrence := atBinder position binder
      .sharedE occurrence (allocate (occurrence.position.under (.sharedE binder)) body)
  | .publishGroup bindings body =>
      .publishGroup position bindings (allocate (position.under (.publishGroup bindings)) body)
  | .atPublication name body =>
      .atPublication position name (allocate (position.under (.atPublication name)) body)
  | .aliasPublication original aliasName body =>
      .aliasPublication position original aliasName
        (allocate (position.under (.aliasPublication original aliasName)) body)
  | .choice site left right =>
      .choice position site
        (allocate {(position.child 0) with telescope := position.telescope ++ [.choice site false]} left)
        (allocate {(position.child 3) with telescope := position.telescope ++ [.choice site true]} right)
def allocateForest (position : Position) : RuleForest → Programs
  | .nil => .nil
  | .cons head tail => .cons (allocate position head) (allocateForest (position.child 1) tail)
end

mutual
def Program.erase : Program → RuleTree
  | .rule _ rule site context premises children => .rule rule site context premises children.erase
  | .existsE occurrence body => .existsE occurrence.binder body.erase
  | .forallE occurrence body => .forallE occurrence.binder body.erase
  | .initializerE _ site body => .initializerE site body.erase
  | .executionE occurrence body => .executionE occurrence.binder body.erase
  | .sharedE occurrence body => .sharedE occurrence.binder body.erase
  | .publishGroup _ bindings body => .publishGroup bindings body.erase
  | .atPublication _ name body => .atPublication name body.erase
  | .aliasPublication _ original aliasName body => .aliasPublication original aliasName body.erase
  | .choice _ site left right => .choice site left.erase right.erase
def Programs.erase : Programs → RuleForest
  | .nil => .nil
  | .cons head tail => .cons head.erase tail.erase
end

mutual
theorem erase_allocate (position : Position) (tree : RuleTree) :
    (allocate position tree).erase = tree := by
  cases tree <;>
    simp only [allocate, Program.erase, erase_allocate, erase_allocate_forest,
      atBinder]
theorem erase_allocate_forest (position : Position) (forest : RuleForest) :
    (allocateForest position forest).erase = forest := by
  cases forest <;>
    simp only [allocateForest, Programs.erase, erase_allocate, erase_allocate_forest]
end

mutual
def Program.copy (framePrefix : FrameId) : Program → Program
  | .rule position rule site context premises children =>
      .rule (position.copy framePrefix) rule site context premises (children.copy framePrefix)
  | .existsE occurrence body => .existsE (occurrence.copy framePrefix) (body.copy framePrefix)
  | .forallE occurrence body => .forallE (occurrence.copy framePrefix) (body.copy framePrefix)
  | .initializerE position site body => .initializerE (position.copy framePrefix) site (body.copy framePrefix)
  | .executionE occurrence body => .executionE (occurrence.copy framePrefix) (body.copy framePrefix)
  | .sharedE occurrence body => .sharedE (occurrence.copy framePrefix) (body.copy framePrefix)
  | .publishGroup position bindings body =>
      .publishGroup (position.copy framePrefix) bindings (body.copy framePrefix)
  | .atPublication position name body => .atPublication (position.copy framePrefix) name (body.copy framePrefix)
  | .aliasPublication position original aliasName body =>
      .aliasPublication (position.copy framePrefix) original aliasName (body.copy framePrefix)
  | .choice position site left right =>
      .choice (position.copy framePrefix) site (left.copy framePrefix) (right.copy framePrefix)
def Programs.copy (framePrefix : FrameId) : Programs → Programs
  | .nil => .nil
  | .cons head tail => .cons (head.copy framePrefix) (tail.copy framePrefix)
end

mutual
theorem erase_copy (framePrefix : FrameId) (program : Program) :
    (program.copy framePrefix).erase = program.erase := by
  cases program <;> simp only [Program.copy, Program.erase, Occurrence.copy,
    erase_copy, erase_copy_forest]
theorem erase_copy_forest (framePrefix : FrameId) (programs : Programs) :
    (programs.copy framePrefix).erase = programs.erase := by
  cases programs <;> simp only [Programs.copy, Programs.erase, erase_copy, erase_copy_forest]
end

def Program.residual (program : Program) : Formula := compile program.erase

def source (origin : Declaration) (context : Context) (raw : Source category) : Program :=
  allocate ⟨origin, [], [], []⟩ (sourceRules context raw)

def definition (raw : Definition) : Program := source raw.declaration raw.context raw.source

def joint (origin : Declaration) (context : Context) (raw : Client) : Program :=
  allocate ⟨origin, [], [], []⟩ (clientRules context raw)

theorem source_residual (origin : Declaration) (context : Context) (raw : Source category) :
    (source origin context raw).residual = Build context raw := by
  simp only [source, Program.residual, erase_allocate, Build]

theorem definition_residual (raw : Definition) :
    (definition raw).residual = Build raw.context raw.source :=
  source_residual raw.declaration raw.context raw.source

theorem joint_residual (origin : Declaration) (context : Context) (raw : Client) :
    (joint origin context raw).residual = BuildJoint context raw := by
  simp only [joint, Program.residual, erase_allocate, BuildJoint]

theorem copy_residual (framePrefix : FrameId) (program : Program) :
    (program.copy framePrefix).residual = program.residual := by
  simp only [Program.residual, erase_copy]

/-- Representation adequacy for every original source constructor. This uses
the existing independent judgment and arbitrary local Kernel unchanged. -/
theorem source_copy_adequacy (kernel : Kernel Value) (environment : Environment Value)
    (origin : Declaration) (context : Context) (raw : Source category) (framePrefix : FrameId) :
    Satisfies kernel environment ((source origin context raw).copy framePrefix).residual ↔
      SourceJudgment kernel environment context raw := by
  rw [copy_residual, source_residual]
  exact source_reconstruction kernel environment context raw

theorem joint_copy_adequacy (kernel : Kernel Value) (environment : Environment Value)
    (origin : Declaration) (context : Context) (raw : Client) (framePrefix : FrameId) :
    Satisfies kernel environment ((joint origin context raw).copy framePrefix).residual ↔
      JointJudgment kernel environment context raw := by
  rw [copy_residual, joint_residual]
  exact joint_reconstruction kernel environment context raw

theorem copied_owner (framePrefix : FrameId) (occurrence : Occurrence) :
    (occurrence.copy framePrefix).site = occurrence.site := rfl

theorem copied_shared_reference (framePrefix : FrameId) (position : Position) (site arity : Nat) :
    (Occurrence.copy framePrefix ⟨position, ⟨site, .shared, arity⟩⟩).reference =
      (Occurrence.mk position ⟨site, .shared, arity⟩).reference := rfl

theorem copied_event_reference (framePrefix : FrameId) (occurrence : Occurrence)
    (event : occurrence.binder.isEvent = true) :
    (occurrence.copy framePrefix).reference = occurrence.reference := by
  cases occurrence with
  | mk position binder =>
    cases binder with
    | mk site kind arity =>
      cases kind <;> simp_all [Binder.isEvent, Occurrence.reference,
        Occurrence.copy, Occurrence.site, Position.copy]

theorem description_copy_distinct (position : Position) (site arity : Nat)
    (first second : FrameId) (different : first ≠ second) :
    (Occurrence.copy first ⟨position, ⟨site, .description, arity⟩⟩).reference ≠
      (Occurrence.copy second ⟨position, ⟨site, .description, arity⟩⟩).reference := by
  intro same
  simp only [Occurrence.copy, Occurrence.reference, Position.copy,
    Reference.description.injEq] at same
  exact different (List.append_cancel_right same.1)

/-- Both frame identity and the entire original event telescope remain in
an EventProof reference; no runtime payload is copied by this operation. -/
theorem copied_event_proof (framePrefix : FrameId) (position : Position) (site arity : Nat) :
    (Occurrence.copy framePrefix ⟨position, ⟨site, .eventProof, arity⟩⟩).reference =
      .eventProof (framePrefix ++ position.frame)
        ⟨position.origin, ⟨position.route, ⟨site, .eventProof, arity⟩⟩, position.telescope⟩ := rfl

def Occurrence.actualKey (occurrence : Occurrence) (environment : Environment Value)
    (candidate : ScopedValue Value) : BinderSite × List (EventStep Value) :=
  (occurrence.site, ActualEvent.path ⟨environment.eventPath, candidate.event.occurrence⟩
    occurrence.binder candidate.data)

theorem actual_key_uses_original_event (occurrence : Occurrence)
    (environment : Environment Value) (candidate : ScopedValue Value)
    (event : occurrence.binder.isEvent = true) :
    (occurrence.actualKey environment candidate).2 =
      (environment.extend occurrence.binder candidate).eventPath := by
  simp only [Occurrence.actualKey, Environment.extend, event, ↓reduceIte]

theorem actual_key_copy_independent (framePrefix : FrameId) (occurrence : Occurrence)
    (environment : Environment Value) (candidate : ScopedValue Value) :
    (occurrence.copy framePrefix).actualKey environment candidate =
      occurrence.actualKey environment candidate := rfl

/-- The EventProof key combines its incoming frame and source occurrence
with the actual current runtime event path, including all parent payloads. -/
def Occurrence.proofKey (occurrence : Occurrence) (environment : Environment Value) :
    FrameId × BinderSite × List (EventStep Value) :=
  (occurrence.position.frame, occurrence.site, environment.eventPath)

theorem proof_key_copy (framePrefix : FrameId) (occurrence : Occurrence)
    (environment : Environment Value) :
    (occurrence.copy framePrefix).proofKey environment =
      (framePrefix ++ occurrence.position.frame, occurrence.site, environment.eventPath) := rfl

theorem proof_key_logical_extension (occurrence : Occurrence)
    (environment : Environment Value) (binder : Binder) (candidate : ScopedValue Value)
    (logical : binder.isEvent = false) :
    occurrence.proofKey (environment.extend binder candidate) = occurrence.proofKey environment := by
  simp only [Occurrence.proofKey, Environment.extend, logical, Bool.false_eq_true, ↓reduceIte]

theorem shared_anchor_copy_independent (framePrefix : FrameId) (occurrence : Occurrence)
    (environment : Environment Value) :
    environment.anchorValue (occurrence.copy framePrefix).binder =
      environment.anchorValue occurrence.binder := rfl

abbrev Formation := OriginalSourceRecordBoundary.Owner

private def annotationAt (site : Site) (context : Context) (premises : List Premise) :
    Option Annotation := premises.findSome? fun premise => match premise with
  | .atom data => if data.kind = .finalAnnotationFormation ∧ data.site = site ∧
      data.context = context then data.annotation else none
  | _ => none

private def formationsAt (route : Route) (scope : List ScopeStep)
    (premises : List Premise) : List Formation := premises.filterMap fun premise =>
  match premise with
  | .boundary site context lower upper =>
      (annotationAt site context premises).map fun annotation =>
        ⟨route, scope, site, context, lower, upper, annotation⟩
  | _ => none

inductive ExportRoot where
  | final (endpoint : Endpoint)
  | annotated (formation : Formation)
  deriving DecidableEq, Repr

def ExportRoot.endpoint : ExportRoot → Endpoint
  | .final endpoint => endpoint
  | .annotated formation => formation.upper

structure Publication where
  route : Route
  telescope : List ScopeStep
  name : Name
  clause : Atom
  root : ExportRoot
  deriving DecidableEq, Repr

def Publication.endpoint (publication : Publication) : Endpoint := publication.root.endpoint

/-- An annotated publication selects its actual enclosing Boundary.upper.
Failure to find that owner produces no guessed old/internal root. -/
def publicationAt (formations : List Formation) (route : Route) (scope : List ScopeStep)
    (rule : Rule) (site : Site) (context : Context) (premise : Premise) : Option Publication :=
  match premise with
  | .atom clause =>
      if rule = .binding ∧ clause.kind = .publicationFinalRoot ∧ clause.site = site ∧
          clause.context = context then
        match clause.names, clause.operands with
        | [name], [initializer] =>
            match clause.annotation with
            | none => some ⟨route, scope, name, clause, .final ⟨initializer, .finalRoot⟩⟩
            | some target => do
                let formation ← formations.find? fun formation =>
                  formation.site == site && formation.context == context &&
                    formation.annotation == target && formation.lower == ⟨initializer, .finalRoot⟩
                pure ⟨route, scope, name, clause, .annotated formation⟩
        | _, _ => none
      else none
  | _ => none

mutual
def publications (route : Route) (scope : List ScopeStep)
    (formations : List Formation) : RuleTree → List Publication
  | .rule rule site context premises children =>
      let formed := formationsAt route scope premises ++ formations
      premises.filterMap (publicationAt formed route scope rule site context) ++
        forestPublications (route ++ [0]) scope formed children
  | .existsE binder body => publications (route ++ [0]) (scope ++ [.existsE binder]) formations body
  | .forallE binder body => publications (route ++ [0]) (scope ++ [.forallE binder]) formations body
  | .initializerE site body => publications (route ++ [0]) (scope ++ [.initializerE site]) formations body
  | .executionE binder body => publications (route ++ [0]) (scope ++ [.executionE binder]) formations body
  | .sharedE binder body => publications (route ++ [0]) (scope ++ [.sharedE binder]) formations body
  | .publishGroup bindings body =>
      publications (route ++ [0]) (scope ++ [.publishGroup bindings]) formations body
  | .atPublication name body => publications (route ++ [0]) (scope ++ [.atPublication name]) formations body
  | .aliasPublication original aliasName body =>
      publications (route ++ [0]) (scope ++ [.aliasPublication original aliasName]) formations body
  | .choice site left right =>
      publications (route ++ [0]) (scope ++ [.choice site false]) formations left ++
        publications (route ++ [3]) (scope ++ [.choice site true]) formations right
def forestPublications (route : Route) (scope : List ScopeStep)
    (formations : List Formation) : RuleForest → List Publication
  | .nil => []
  | .cons head tail => publications route scope formations head ++
      forestPublications (route ++ [1]) scope formations tail
end

def Program.publications (program : Program) : List Publication :=
  YulangClosure.OriginalScopedClosure.publications [] [] [] program.erase

theorem copy_publications (framePrefix : FrameId) (program : Program) :
    (program.copy framePrefix).publications = program.publications := by
  simp only [Program.publications, erase_copy]

structure ScopedClosure (category : Category) where
  origin : Declaration
  context : Context
  raw : Source category
  program : Program

/-- No correctness field is supplied. The complete program is computed. -/
def prepare (origin : Declaration) (context : Context) (raw : Source category) :
    ScopedClosure category := ⟨origin, context, raw, source origin context raw⟩

theorem prepare_residual (origin : Declaration) (context : Context) (raw : Source category) :
    (prepare origin context raw).program.residual = Build context raw :=
  source_residual origin context raw

structure Opened (Value : Type) where
  publication : Publication
  identity : PublicationId Value
  handle : Name
  caller : Environment Value
  restored : Environment Value
  program : Program

/-- Uses the original publication lookup/restore, never a new initializer.
The static root must have the same source origin and emitted binding site. This is a
representation operation, not a proof of source/native publication adequacy. -/
noncomputable def openPublication (closure : ScopedClosure category)
    (environment : Environment Value) (name : Name) (frame : FrameId) : Option (Opened Value) := do
  let publication ← closure.program.publications.find? (fun publication => publication.name == name)
  let identity ← environment.publicationName name
  if identity.origin != closure.origin || identity.site != publication.clause.site then none else do
    let restored ← environment.atPublication name
    pure ⟨publication, identity, name, environment, restored, closure.program.copy frame⟩

theorem opened_readback (closure : ScopedClosure category)
    (environment : Environment Value) (name : Name) (frame : FrameId) (opened : Opened Value)
    (built : openPublication closure environment name frame = some opened) :
    opened.publication ∈ closure.program.publications ∧
      environment.publicationName name = some opened.identity ∧
      opened.identity.site = opened.publication.clause.site ∧
      environment.atPublication name = some opened.restored ∧
      opened.program = closure.program.copy frame ∧
      opened.caller = environment ∧ opened.handle = name ∧
      opened.identity.origin = closure.origin := by
  simp only [openPublication] at built
  obtain ⟨publication, found, built⟩ := Option.bind_eq_some_iff.mp built
  obtain ⟨identity, named, built⟩ := Option.bind_eq_some_iff.mp built
  split at built
  next => contradiction
  next same =>
    obtain ⟨restored, restoredAt, built⟩ := Option.bind_eq_some_iff.mp built
    cases Option.some.inj built
    have matchingIdentity : identity.origin = closure.origin ∧ identity.site = publication.clause.site := by
      simpa using same
    exact ⟨List.mem_of_find?_eq_some found, named, matchingIdentity.2, restoredAt,
      rfl, rfl, rfl, matchingIdentity.1⟩

/-- Restore keeps the original root, global anchor strategy and publication
graph, and reinstalls the recorded entry/replay scopes. These are computed
field equalities, not an assumption of semantic world or carrier validity. -/
theorem opened_restore_fields (closure : ScopedClosure category)
    (environment : Environment Value) (name : Name) (frame : FrameId) (opened : Opened Value)
    (built : openPublication closure environment name frame = some opened) :
    opened.restored.root = environment.root ∧
      opened.restored.anchors = environment.anchors ∧
      opened.restored.publications = environment.publications ∧
      ∃ record, environment.publications opened.identity = some record ∧
        opened.restored.origin = record.identity.origin ∧
        opened.restored.eventPath = record.entryPath ∧
        opened.restored.names = record.entryNames ∧
        opened.restored.frames = record.entryFrames ++
          environment.frames.filter (fun frame => !frame.binder.isFixed) ∧
        opened.restored.replay = some record.fixedFrames ∧
        opened.restored.initializers = record.initializers := by
  classical
  have readback := opened_readback closure environment name frame opened built
  have restored := readback.2.2.2.1
  simp only [Environment.atPublication, readback.2.1,
    Option.bind_eq_bind, Option.bind_some] at restored
  obtain ⟨record, recorded, restored⟩ := Option.bind_eq_some_iff.mp restored
  split at restored
  next => contradiction
  next =>
    rw [← Option.some.inj restored]
    exact ⟨rfl, rfl, rfl, record, recorded, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem open_publication_of_readbacks (closure : ScopedClosure category)
    (environment : Environment Value) (name : Name) (frame : FrameId)
    (publication : Publication) (identity : PublicationId Value) (restored : Environment Value)
    (found : closure.program.publications.find? (fun publication => publication.name == name) =
      some publication)
    (named : environment.publicationName name = some identity)
    (sameOrigin : identity.origin = closure.origin)
    (sameSite : identity.site = publication.clause.site)
    (restoredAt : environment.atPublication name = some restored) :
    openPublication closure environment name frame =
      some ⟨publication, identity, name, environment, restored, closure.program.copy frame⟩ := by
  simp only [openPublication, found, named, Option.bind_eq_bind, Option.bind_some,
    sameOrigin, sameSite, bne_self_eq_false, Bool.false_or, Bool.false_eq_true,
    ↓reduceIte, restoredAt, Option.pure_def]

/-- The same existing description program is reused by an alias. The caller's
actual publication map is updated by the original alias constructor; neither
the captured source restoration nor a description frame is allocated again. -/
def Opened.alias (opened : Opened Value) (aliasName : Name) : Option (Opened Value) := do
  let aliased ← opened.caller.aliasPublication opened.handle aliasName
  pure {opened with handle := aliasName, caller := aliased}

theorem opened_alias_same_description (opened next : Opened Value) (aliasName : Name)
    (aliased : opened.alias aliasName = some next) :
    next.publication = opened.publication ∧ next.identity = opened.identity ∧
      next.program = opened.program ∧ next.restored = opened.restored ∧
      next.caller.anchors = opened.caller.anchors ∧
      next.caller.publications = opened.caller.publications := by
  simp only [Opened.alias] at aliased
  obtain ⟨caller, lookup, same⟩ := Option.bind_eq_some_iff.mp aliased
  cases Option.some.inj same
  cases found : opened.caller.publicationName opened.handle with
  | none => simp [Environment.aliasPublication, found] at lookup
  | some identity =>
      simp only [Environment.aliasPublication, found] at lookup
      cases Option.some.inj lookup
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem opened_source_residual (origin : Declaration) (context : Context) (raw : Source category)
    (environment : Environment Value) (name : Name) (frame : FrameId) (opened : Opened Value)
    (built : openPublication (prepare origin context raw) environment name frame = some opened) :
    opened.program.residual = Build context raw := by
  rw [(opened_readback _ _ _ _ _ built).2.2.2.2.1, copy_residual]
  exact prepare_residual origin context raw

/-- An actual existing source fixture has both an initializer annotation
and a distinct outer binding annotation. The exported root is the latter. -/
theorem actual_annotated_publication :
    ((source 7 [] OriginalSourceRecordBoundary.Witness.original).publications.map
      (fun publication => (publication.name, publication.clause.site, publication.endpoint,
        publication.clause.annotation, publication.clause.operands))) =
      [(30, 20, ⟨20, .writtenTarget⟩, some 101, [10])] := by
  simp only [source, Program.publications, erase_allocate]
  simp only [OriginalSourceRecordBoundary.Witness.original, sourceRules,
    bindingsRulesK, expressionRulesK]
  rfl

theorem actual_annotated_copy (frame : FrameId) :
    (((source 7 [] OriginalSourceRecordBoundary.Witness.original).copy frame).publications.map
      (fun publication => (publication.name, publication.clause.site, publication.endpoint,
        publication.clause.annotation, publication.clause.operands))) =
      [(30, 20, ⟨20, .writtenTarget⟩, some 101, [10])] := by
  rw [copy_publications]
  exact actual_annotated_publication

/-- The full source-generated annotated payload is opened at its actual
published record. The only inputs below are raw original map/frame readbacks;
no source judgment, Call certificate, safety, or presentation law is assumed. -/
theorem actual_annotated_export_opened (environment : Environment Value) (frame : FrameId)
    (identity : PublicationId Value) (record : PublicationRecord Value)
    (named : environment.publicationName 30 = some identity)
    (stored : environment.publications identity = some record)
    (sameIdentity : record.identity = identity)
    (fixed : record.fixedFrames.all (fun frame => frame.binder.isFixed) = true)
    (sameOrigin : identity.origin = 7)
    (sameSite : identity.site = 20) :
    ∃ opened, openPublication
        (prepare 7 [] OriginalSourceRecordBoundary.Witness.original) environment 30 frame = some opened ∧
      opened.publication.endpoint = ⟨20, .writtenTarget⟩ ∧
      opened.restored = environment.restore record ∧
      opened.program.residual = Build [] OriginalSourceRecordBoundary.Witness.original := by
  classical
  have mapped := actual_annotated_publication
  cases inventory : (source 7 [] OriginalSourceRecordBoundary.Witness.original).publications with
  | nil =>
      simp only [inventory, List.map_nil] at mapped
      cases mapped
  | cons publication rest =>
      rw [inventory] at mapped
      simp only [List.map_cons, List.cons.injEq, List.map_eq_nil_iff] at mapped
      obtain ⟨fields, rfl⟩ := mapped
      have publicationName : publication.name = 30 := congrArg Prod.fst fields
      have publicationSite : publication.clause.site = 20 :=
        congrArg (fun item => item.2.1) fields
      have endpoint : publication.endpoint = ⟨20, .writtenTarget⟩ :=
        congrArg (fun item => item.2.2.1) fields
      have found : (prepare 7 [] OriginalSourceRecordBoundary.Witness.original).program.publications.find?
          (fun publication => publication.name == 30) = some publication := by
        change (source 7 [] OriginalSourceRecordBoundary.Witness.original).publications.find? _ = _
        rw [inventory]
        simp [publicationName]
      have restoredAt : environment.atPublication 30 = some (environment.restore record) := by
        have valid : record.identity = identity ∧
            record.fixedFrames.all (fun frame => frame.binder.isFixed) = true :=
          ⟨sameIdentity, fixed⟩
        simp only [Environment.atPublication, named, stored, Option.bind_eq_bind,
          Option.bind_some, valid, true_and, not_true_eq_false, ↓reduceIte, Option.pure_def]
      have built := open_publication_of_readbacks
        (prepare 7 [] OriginalSourceRecordBoundary.Witness.original) environment 30 frame
        publication identity (environment.restore record) found named sameOrigin
        (sameSite.trans publicationSite.symm) restoredAt
      exact ⟨_, built, endpoint, rfl, opened_source_residual _ _ _ _ _ _ _ built⟩

end YulangClosure.OriginalScopedClosure
