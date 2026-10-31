import YulangClosure.OccurrenceQualifiedConsumerR66

/-!
R77 repairs R76 and computes choice from complete R55 inventories. The ordered walk stops on
malformed eligible recipes and a second component match in native order. Its
successful result is proved to agree with R66's actual mapM/singleton reader.
No plan, registration, R66 success, Root, or policy result is supplied as input.
This finite model does not authenticate Rust inventories or establish A/B.
-/
namespace YulangClosure.SourceInternalChoiceR77
open SourceInternalContextR55 ProviderNativeContextR57

variable {S T : Type} [DecidableEq S] [DecidableEq T]

abbrev Source (S T : Type) := OccurrenceQualifiedConsumerR66.Source S T
abbrev Origin (S T : Type) := Construction (Key S T) T

inductive Failure where
  | recipe (registration : Nat)
  | secondOrigin (registration : Nat)
  | noOrigin
  deriving DecidableEq

/-- No Function/entry equality filters this complete registration inventory. -/
def visit (s : Source S T) (target : Key S T) (component : Nat) (c : Origin S T) :
    Except Failure (Option (Origin S T)) :=
  match s.formals[c.registration]? with
  | none => .ok none
  | some f =>
    if f.role = .computation ∧ f.owner = target then
      match unique (fun r => decide (r.formalRegistration = some c.registration)) s.recipes with
      | none => .error (.recipe c.registration)
      | some recipe => .ok (if recipe.rootComponent = component then some c else none)
    else .ok none

/-- Keep the first match, but continue checking every later eligible origin.
A second match fails immediately, before reading subsequent origins. -/
def walk (s : Source S T) (target : Key S T) (component : Nat) :
    List (Origin S T) → List (Origin S T) → Except Failure (List (Origin S T))
  | [], selected => .ok selected
  | c :: rest, selected =>
    match visit s target component c with
    | .error err => .error err
    | .ok none => walk s target component rest selected
    | .ok (some chosen) => match selected with
      | [] => walk s target component rest [chosen]
      | _ :: _ => .error (.secondOrigin c.registration)

def orderedSelection (s : Source S T) (target : Key S T) (component : Nat) :
    Except Failure (Origin S T) :=
  match walk s target component s.constructions [] with
  | .error err => .error err
  | .ok choices => match choices with
    | [c] => .ok c
    | _ => .error .noOrigin

/-- Precisely the per-origin Option action used by R66. -/
theorem visit_agrees (s : Source S T) (target : Key S T) (component : Nat) (c : Origin S T) :
    (visit s target component c).toOption =
      (match s.formals[c.registration]? with
      | none => some none
      | some f => if f.role = .computation ∧ f.owner = target then do
          let recipe ← unique (fun r => decide (r.formalRegistration = some c.registration)) s.recipes
          some (if recipe.rootComponent = component then some c else none)
        else some none) := by
  unfold visit
  cases hf : s.formals[c.registration]? with
  | none => rfl
  | some f =>
    by_cases eligible : f.role = .computation ∧ f.owner = target
    · simp only [eligible, ite_true]
      cases hr : unique (fun r => decide (r.formalRegistration = some c.registration)) s.recipes <;> rfl
    · simp [eligible, Except.toOption]

/-- The successful ordered walk accounts for every inventory row and every
component match, including rows after its first match. -/
theorem walk_accounts_for_all (s : Source S T) (target : Key S T) (component : Nat)
    (origins selected out : List (Origin S T))
    (accepted : walk s target component origins selected = .ok out) :
    ∃ rows, origins.mapM (fun c => (visit s target component c).toOption) = some rows ∧
      selected ++ rows.filterMap id = out := by
  induction origins generalizing selected with
  | nil =>
    simp only [walk, Except.ok.injEq] at accepted
    exact ⟨[], rfl, by simpa using accepted⟩
  | cons c rest ih =>
    cases hv : visit s target component c with
    | error err => simp [walk, hv] at accepted
    | ok found =>
      cases found with
      | none =>
        have tail : walk s target component rest selected = .ok out := by
          simpa [walk, hv] using accepted
        obtain ⟨rows, read, equal⟩ := ih selected tail
        refine ⟨none :: rows, ?_, ?_⟩
        · simp [List.mapM_cons, hv, read, Except.toOption]
        · simpa using equal
      | some chosen =>
        cases selected with
        | nil =>
          have tail : walk s target component rest [chosen] = .ok out := by
            simpa [walk, hv] using accepted
          obtain ⟨rows, read, equal⟩ := ih [chosen] tail
          refine ⟨some chosen :: rows, ?_, ?_⟩
          · simp [List.mapM_cons, hv, read, Except.toOption]
          · simpa using equal
        | cons previous others => simp [walk, hv] at accepted

/-- Successful native-order selection derives the existing R66 result;
R66's Option reader does not retain diagnostic failure order. -/
theorem ordered_selection_agrees (s : Source S T) (target : Key S T) (component : Nat)
    (c : Origin S T) (accepted : orderedSelection s target component = .ok c) :
    OccurrenceQualifiedConsumerR66.ownerSelection s target component = some c := by
  unfold orderedSelection at accepted
  cases hw : walk s target component s.constructions [] with
  | error err => simp [hw] at accepted
  | ok choices =>
    cases choices with
    | nil => simp [hw] at accepted
    | cons chosen rest =>
      cases rest with
      | cons extra others => simp [hw] at accepted
      | nil =>
        have same : chosen = c := by simpa [hw] using accepted
        subst chosen
        obtain ⟨rows, read, equal⟩ := walk_accounts_for_all s target component s.constructions [] [c] hw
        have rowMatches : rows.filterMap id = [c] := by simpa using equal
        have nativeRead : s.constructions.mapM (fun c =>
            match s.formals[c.registration]? with
            | none => some none
            | some f => if f.role = .computation ∧ f.owner = target then do
                let recipe ← unique (fun r => decide (r.formalRegistration = some c.registration)) s.recipes
                some (if recipe.rootComponent = component then some c else none)
              else some none) = some rows := by
          simpa only [visit_agrees] using read
        simp only [OccurrenceQualifiedConsumerR66.ownerSelection, nativeRead,
          Option.bind_some, rowMatches]

/-- These equations expose the first native failure without evaluating rest. -/
theorem malformed_recipe_first (s : Source S T) (target : Key S T) (component : Nat)
    (c : Origin S T) (rest selected : List (Origin S T))
    (malformed : visit s target component c = .error (.recipe c.registration)) :
    walk s target component (c :: rest) selected = .error (.recipe c.registration) := by
  simp [walk, malformed]

theorem second_origin_first (s : Source S T) (target : Key S T) (component : Nat)
    (c chosen previous : Origin S T) (rest others : List (Origin S T))
    (matched : visit s target component c = .ok (some chosen)) :
    walk s target component (c :: rest) (previous :: others) = .error (.secondOrigin c.registration) := by
  simp [walk, matched]

/-- A result assembled solely by indexed/filter reads and primitive checks.
The formal's nativeRoot is never used as the registered Lambda root. -/
structure Choice (s : Source S T) (u : Use Nat (Key S T)) (receiving target : Key S T) where
  plan : Plan Nat (Key S T) T
  origin : Origin S T
  formal : Formal (Key S T) T
  recipe : Recipe (Key S T)
  receipt : Receipt Nat (Key S T) Fact
  artifact : u.artifact = s.artifact
  plans : s.plans.filter (fun p => decide (use p.use = use u)) = [plan]
  owners : plan.sourceOwner = receiving ∧ plan.targetOwner = target
  routes : s.receipts.filter (fun r => decide (r.use = u)) = [receipt]
  internal : receipt.kind = .internal ∧ receipt.fact.isSome = true
  selected : orderedSelection s target plan.targetRootComponent = .ok origin
  indexed : s.formals[origin.registration]? = some formal
  recipes : s.recipes.filter (fun r => decide (r.formalRegistration = some origin.registration)) = [recipe]
  lambda : recipe.occurrence = origin.lambda
  component : recipe.rootComponent = plan.targetRootComponent
  parameter : s.parameterRecipes[formal.recipePosition]? = some formal.parameter

/-- The caller supplies only source inventories and the exact use/owner keys.
No chosen plan or registration is an argument. Checks follow the native seam:
Internal route, global origin scan, exact selected recipe, parameter position. -/
def construct (s : Source S T) (u : Use Nat (Key S T)) (receiving target : Key S T) :
    Option (Choice s u receiving target) := do
  if artifact : u.artifact = s.artifact then
    match plans : s.plans.filter (fun p => decide (use p.use = use u)) with
    | [p] =>
      if owners : p.sourceOwner = receiving ∧ p.targetOwner = target then
        match routes : s.receipts.filter (fun r => decide (r.use = u)) with
        | [receipt] =>
          if internal : receipt.kind = .internal ∧ receipt.fact.isSome = true then
            match selected : orderedSelection s target p.targetRootComponent with
            | .error _ => none
            | .ok origin =>
              match indexed : s.formals[origin.registration]? with
              | none => none
              | some formal =>
                match recipes : s.recipes.filter (fun r => decide (r.formalRegistration = some origin.registration)) with
                | [recipe] =>
                  if lambda : recipe.occurrence = origin.lambda then
                    if component : recipe.rootComponent = p.targetRootComponent then
                      if parameter : s.parameterRecipes[formal.recipePosition]? = some formal.parameter then
                        some ⟨p,origin,formal,recipe,receipt,artifact,plans,owners,routes,internal,
                          selected,indexed,recipes,lambda,component,parameter⟩
                      else none
                    else none
                  else none
                | _ => none
          else none
        | _ => none
      else none
    | _ => none
  else none

theorem choice_three_premises (s : Source S T) (u : Use Nat (Key S T)) (receiving target : Key S T)
    (c : Choice s u receiving target) :
    (internalInputs s).plan (use u) = some (SourceInternalContextR55.plan c.plan) ∧
    OccurrenceQualifiedConsumerR66.ownerSelection s target c.plan.targetRootComponent = some c.origin ∧
    s.parameterRecipes[c.formal.recipePosition]? = some c.formal.parameter := by
  refine ⟨?_, ordered_selection_agrees s target c.plan.targetRootComponent c.origin c.selected, c.parameter⟩
  simp [internalInputs, unique, c.plans]

/-- Explicitly apply the plan premise to R66's actual occurrence-qualified
input; R65 changes fact readers, leaving this plan read intact. -/
theorem choice_applies_r66 (s : Source S T) (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T)
    (u : Use Nat (Key S T)) (receiving target : Key S T) (c : Choice s u receiving target) :
    (OccurrenceQualifiedFactReadersR65.internalInputs s inventory u.occurrence).plan (use u) =
      some (SourceInternalContextR55.plan c.plan) ∧
    OccurrenceQualifiedConsumerR66.ownerSelection s target c.plan.targetRootComponent = some c.origin ∧
    s.parameterRecipes[(SourceInternalContextR55.formal c.formal).recipe]? =
      some (SourceInternalContextR55.formal c.formal).parameter := by
  exact choice_three_premises s u receiving target c

theorem exact_use_unique (s : Source S T) (u : Use Nat (Key S T)) (receiving target : Key S T)
    (c : Choice s u receiving target) (p : Plan Nat (Key S T) T)
    (member : p ∈ s.plans) (same : use p.use = use u) : p = c.plan := by
  have belongs : p ∈ s.plans.filter (fun p => decide (use p.use = use u)) := by
    simp [member, same]
  rw [c.plans] at belongs
  simpa using belongs

/-- Every constructor output carries the three parent premises; no caller
supplied plan/registration or R66/policy success is a hypothesis. -/
theorem construction_certifies (s : Source S T) (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T)
    (u : Use Nat (Key S T)) (receiving target : Key S T) :
    match construct s u receiving target with
    | none => True
    | some c =>
      (OccurrenceQualifiedFactReadersR65.internalInputs s inventory u.occurrence).plan (use u) =
        some (SourceInternalContextR55.plan c.plan) ∧
      OccurrenceQualifiedConsumerR66.ownerSelection s target c.plan.targetRootComponent = some c.origin ∧
      s.parameterRecipes[(SourceInternalContextR55.formal c.formal).recipe]? =
        some (SourceInternalContextR55.formal c.formal).parameter := by
  cases construct s u receiving target with
  | none => trivial
  | some c => exact choice_applies_r66 s inventory u receiving target c

/-! Supplemental finite inventories preserve a distinct formal parameter root
(700) and registered Lambda root (component 20, term 300). -/
def fixture := OccurrenceQualifiedFactReadersR65.fixtureSource
def fixtureUse : Use Nat (Key Nat Nat) := ⟨99, .source 100⟩
def fixtureChoice := construct fixture fixtureUse (.source 10) (.source 1)

theorem finite_constructs_choice : fixtureChoice.isSome = true := by decide

theorem finite_bad_inventories_reject :
    (construct {fixture with plans := fixture.plans ++ fixture.plans} fixtureUse (.source 10) (.source 1)).isSome = false ∧
    (construct {fixture with parameterRecipes := []} fixtureUse (.source 10) (.source 1)).isSome = false ∧
    (construct {fixture with recipes := []} fixtureUse (.source 10) (.source 1)).isSome = false ∧
    (construct {fixture with recipes := fixture.recipes ++ fixture.recipes} fixtureUse (.source 10) (.source 1)).isSome = false ∧
    (construct {fixture with constructions := fixture.constructions ++ fixture.constructions} fixtureUse (.source 10) (.source 1)).isSome = false ∧
    (construct {fixture with plans := fixture.plans.map (fun p => {p with targetRootComponent := 900})}
      fixtureUse (.source 10) (.source 1)).isSome = false ∧
    (construct {fixture with parameterRecipes := [.source 999]} fixtureUse (.source 10) (.source 1)).isSome = false := by decide

/-- A foreign registration may share Function and entry images; its owner
coordinate still prevents it from selecting the requested target. -/
def foreignOrigin : Origin Nat Nat :=
  { ProviderNativeContextR57.fixtureConstruction with registration := 1 }
def foreignFormal : Formal (Key Nat Nat) Nat :=
  { ProviderNativeContextR57.fixtureFormal with owner := .source 999 }
def foreignSource : Source Nat Nat :=
  { fixture with formals := fixture.formals ++ [foreignFormal], constructions := [foreignOrigin] }

theorem finite_foreign_shared_images_rejected :
    foreignOrigin.function = ProviderNativeContextR57.fixtureConstruction.function ∧
    foreignOrigin.entryEffect = ProviderNativeContextR57.fixtureConstruction.entryEffect ∧
    orderedSelection foreignSource (.source 1) 20 = .error .noOrigin := by
  exact ⟨rfl, rfl, rfl⟩

/-- Missing recipe at an earlier eligible origin fails before the later
valid target. Duplicate target matches fail before a subsequent bad recipe. -/
def earlierBadSource : Source Nat Nat :=
  { fixture with
    formals := fixture.formals ++ [ProviderNativeContextR57.fixtureFormal]
    constructions := [foreignOrigin, ProviderNativeContextR57.fixtureConstruction] }

theorem finite_native_failure_order :
    orderedSelection earlierBadSource (.source 1) 20 = .error (.recipe 1) ∧
    orderedSelection {earlierBadSource with constructions :=
      [ProviderNativeContextR57.fixtureConstruction, ProviderNativeContextR57.fixtureConstruction, foreignOrigin]}
      (.source 1) 20 = .error (.secondOrigin 0) := by
  exact ⟨rfl, rfl⟩

theorem duplicate_plans_rejected (s : Source S T) (u : Use Nat (Key S T))
    (receiving target : Key S T) (first second : Plan Nat (Key S T) T)
    (rest : List (Plan Nat (Key S T) T))
    (duplicate : s.plans.filter (fun p => decide (use p.use = use u)) = first :: second :: rest) :
    construct s u receiving target = none := by
  by_cases same : u.artifact = s.artifact <;> simp [construct, same, duplicate]

/-! Source alignment keeps a module DefinitionUse at its callee Name and
an Apply checking occurrence at the enclosing Apply. Only Group is peeled,
as in the pinned owner-local HIR reader; every other form is explicit. -/
inductive HirForm (Id : Type) where
  | name (target : Id)
  | group (inner : Nat)
  | apply (callee argument : Nat)
  | other
  deriving DecidableEq

structure HirNode (Id : Type) where
  occurrence : Id
  form : HirForm Id
  deriving DecidableEq

structure OwnerSource (Id : Type) where
  owner : Id
  expressions : List (HirNode Id)

structure SourceCall (Id : Type) where
  owner : Id
  checking : Id
  expression : Nat
  callee : Nat
  argument : Nat
  deriving DecidableEq

/-- Finite, cycle-rejecting owner-local Group peeling. The returned coordinates
are the callee Name occurrence and its module target, never the Apply. -/
def peel (nodes : List (HirNode (Key S T))) :
    Nat → List Nat → Nat → Option (Key S T × Key S T)
  | 0, _, _ => none
  | fuel + 1, seen, index =>
    if index ∈ seen then none else
      match nodes[index]? with
      | none => none
      | some node => match node.form with
        | .name target => some (node.occurrence, target)
        | .group inner => peel nodes fuel (index :: seen) inner
        | .apply _ _ => none
        | .other => none

/-- A successful peel is backed by the actual indexed Name and every Group
edge, with a shared owner-local node inventory. -/
inductive PeelsTo (nodes : List (HirNode (Key S T))) :
    Nat → Key S T → Key S T → Prop where
  | name (node : HirNode (Key S T)) (index : Nat) (target : Key S T)
      (indexed : nodes[index]? = some node) (named : node.form = .name target) :
      PeelsTo nodes index node.occurrence target
  | group (node : HirNode (Key S T)) (index inner : Nat) (name target : Key S T)
      (indexed : nodes[index]? = some node) (grouped : node.form = .group inner)
      (tail : PeelsTo nodes inner name target) : PeelsTo nodes index name target

theorem peel_sound (nodes : List (HirNode (Key S T))) (fuel : Nat)
    (seen : List Nat) (index : Nat) (result : Key S T × Key S T)
    (found : peel nodes fuel seen index = some result) :
    PeelsTo nodes index result.1 result.2 := by
  induction fuel generalizing seen index with
  | zero => simp [peel] at found
  | succ fuel ih =>
    by_cases cycle : index ∈ seen
    · simp [peel, cycle] at found
    · cases indexed : nodes[index]? with
      | none => simp [peel, cycle, indexed] at found
      | some node =>
        cases form : node.form with
        | other => simp [peel, cycle, indexed, form] at found
        | apply callee argument => simp [peel, cycle, indexed, form] at found
        | name target =>
          have same : (node.occurrence, target) = result := by
            simpa only [peel, if_neg cycle, indexed, form, Option.some.injEq] using found
          cases same
          exact PeelsTo.name node index target indexed form
        | group inner =>
          have tail : peel nodes fuel (index :: seen) inner = some result := by
            simpa only [peel, if_neg cycle, indexed, form] using found
          exact PeelsTo.group node index inner result.1 result.2 indexed form
            (ih (index :: seen) inner tail)

def alignedCalls (source : OwnerSource (Key S T)) (calls : List (SourceCall (Key S T)))
    (u : Use Nat (Key S T)) (receiving target : Key S T) : List (SourceCall (Key S T)) :=
  calls.filter (fun call => match source.expressions[call.expression]? with
    | none => false
    | some node => decide (call.owner = receiving ∧ node.occurrence = call.checking ∧
        node.form = .apply call.callee call.argument ∧
        peel source.expressions (source.expressions.length + 1) [] call.callee =
          some (u.occurrence, target)))

/-- The native DefinitionUse coordinates retained by R55 plans are enumerated
before selecting the exact use. Distinct matching uses cannot be hidden by
first selecting the caller's desired key. -/
def alignedUses (s : Source S T) (source : OwnerSource (Key S T))
    (calls : List (SourceCall (Key S T))) (receiving target : Key S T) :
    List (Plan Nat (Key S T) T) :=
  s.plans.filter (fun p => decide (p.sourceOwner = receiving ∧ p.targetOwner = target ∧
    (alignedCalls source calls p.use receiving target).length ≠ 0))

structure Alignment (source : OwnerSource (Key S T)) (calls : List (SourceCall (Key S T)))
    (u : Use Nat (Key S T)) (receiving target : Key S T) where
  call : SourceCall (Key S T)
  applyNode : HirNode (Key S T)
  sourceOwner : source.owner = receiving
  uniqueCall : alignedCalls source calls u receiving target = [call]
  callOwner : call.owner = receiving
  applyIndexed : source.expressions[call.expression]? = some applyNode
  checking : applyNode.occurrence = call.checking
  applied : applyNode.form = .apply call.callee call.argument
  resolved : peel source.expressions (source.expressions.length + 1) [] call.callee =
    some (u.occurrence, target)

structure AlignedChoice (s : Source S T) (source : OwnerSource (Key S T))
    (calls : List (SourceCall (Key S T))) (u : Use Nat (Key S T))
    (receiving target : Key S T) where
  selectedUse : Plan Nat (Key S T) T
  uniqueUse : alignedUses s source calls receiving target = [selectedUse]
  exactUse : selectedUse.use = u
  choice : Choice s u receiving target
  alignment : Alignment source calls u receiving target

/-- Complete call and DefinitionUse inventories are read separately. The Name
coordinate is resolved from the Apply callee; Apply checking is authenticated
against the indexed Apply node. Neither coordinate is supplied as an equality
with the other, and no plan or registration is supplied by the caller. -/
def constructAligned (s : Source S T) (source : OwnerSource (Key S T))
    (calls : List (SourceCall (Key S T))) (u : Use Nat (Key S T))
    (receiving target : Key S T) : Option (AlignedChoice s source calls u receiving target) :=
  match uniqueUse : alignedUses s source calls receiving target with
  | [p] =>
    if exactUse : p.use = u then
      if owner : source.owner = receiving then
        match uniqueCall : alignedCalls source calls u receiving target with
        | [call] =>
          if callOwner : call.owner = receiving then
            match applyIndexed : source.expressions[call.expression]? with
            | none => none
            | some node =>
              if checking : node.occurrence = call.checking then
                if applied : node.form = .apply call.callee call.argument then
                  if resolved : peel source.expressions (source.expressions.length + 1) [] call.callee =
                      some (u.occurrence, target) then
                    match construct s u receiving target with
                    | none => none
                    | some choice => some ⟨p, uniqueUse, exactUse, choice,
                        ⟨call, node, owner, uniqueCall, callOwner, applyIndexed, checking, applied, resolved⟩⟩
                  else none
                else none
              else none
          else none
        | _ => none
      else none
    else none
  | _ => none

theorem alignment_has_name (source : OwnerSource (Key S T))
    (calls : List (SourceCall (Key S T))) (u : Use Nat (Key S T))
    (receiving target : Key S T) (a : Alignment source calls u receiving target) :
    source.owner = receiving ∧ a.call.owner = receiving ∧
      PeelsTo source.expressions a.call.callee u.occurrence target := by
  exact ⟨a.sourceOwner, a.callOwner,
    peel_sound source.expressions (source.expressions.length + 1) [] a.call.callee
      (u.occurrence, target) a.resolved⟩

theorem aligned_construction_certifies (s : Source S T)
    (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T)
    (source : OwnerSource (Key S T)) (calls : List (SourceCall (Key S T)))
    (u : Use Nat (Key S T)) (receiving target : Key S T) :
    match constructAligned s source calls u receiving target with
    | none => True
    | some c =>
      PeelsTo source.expressions c.alignment.call.callee u.occurrence target ∧
      (OccurrenceQualifiedFactReadersR65.internalInputs s inventory u.occurrence).plan (use u) =
        some (SourceInternalContextR55.plan c.choice.plan) ∧
      OccurrenceQualifiedConsumerR66.ownerSelection s target c.choice.plan.targetRootComponent =
        some c.choice.origin ∧
      s.parameterRecipes[c.choice.formal.recipePosition]? = some c.choice.formal.parameter := by
  cases constructAligned s source calls u receiving target with
  | none => trivial
  | some c =>
    exact ⟨(alignment_has_name source calls u receiving target c.alignment).2.2,
      choice_applies_r66 s inventory u receiving target c.choice⟩

/-- The source route `answer = relay (provider ())` has distinct callee Name
and enclosing Apply nodes. Group indirection is retained rather than collapsed
into a fictional equality of coordinates. This is a finite admitted-shape
inventory witness, not authenticated Rust-to-Lean extraction. -/
def fixtureOwnerSource : OwnerSource (Key Nat Nat) :=
  ⟨.source 10, [⟨.source 100, .name (.source 1)⟩,
    ⟨.source 101, .group 0⟩, ⟨.source 102, .apply 1 3⟩,
    ⟨.source 103, .other⟩]⟩
def fixtureCall : SourceCall (Key Nat Nat) := ⟨.source 10, .source 102, 2, 1, 3⟩
def fixtureAligned :=
  constructAligned fixture fixtureOwnerSource [fixtureCall] fixtureUse (.source 10) (.source 1)

theorem admitted_shape_constructs_distinct_coordinates :
    fixtureUse.occurrence ≠ fixtureCall.checking ∧
    peel fixtureOwnerSource.expressions (fixtureOwnerSource.expressions.length + 1) []
      fixtureCall.callee = some (fixtureUse.occurrence, .source 1) ∧
    fixtureAligned.isSome = true := by decide

theorem finite_alignment_rejects_duplicates_and_foreign_owners :
    (constructAligned { fixture with plans := fixture.plans ++ fixture.plans }
      fixtureOwnerSource [fixtureCall] fixtureUse (.source 10) (.source 1)).isSome = false ∧
    (constructAligned fixture fixtureOwnerSource [fixtureCall, fixtureCall] fixtureUse
      (.source 10) (.source 1)).isSome = false ∧
    (constructAligned fixture { fixtureOwnerSource with owner := .source 999 } [fixtureCall]
      fixtureUse (.source 10) (.source 1)).isSome = false ∧
    (constructAligned fixture fixtureOwnerSource [{ fixtureCall with owner := .source 999 }]
      fixtureUse (.source 10) (.source 1)).isSome = false ∧
    (constructAligned fixture fixtureOwnerSource [fixtureCall] fixtureUse
      (.source 10) (.source 999)).isSome = false ∧
    (constructAligned fixture fixtureOwnerSource [fixtureCall]
      { fixtureUse with occurrence := .source 102 } (.source 10) (.source 1)).isSome = false ∧
    (constructAligned fixture fixtureOwnerSource [{ fixtureCall with checking := .source 100 }]
      fixtureUse (.source 10) (.source 1)).isSome = false ∧
    (constructAligned fixture fixtureOwnerSource [{ fixtureCall with expression := 0 }]
      fixtureUse (.source 10) (.source 1)).isSome = false ∧
    (constructAligned fixture fixtureOwnerSource [{ fixtureCall with argument := 99 }]
      fixtureUse (.source 10) (.source 1)).isSome = false := by decide

theorem finite_peel_rejects_cycles_missing_and_other :
    peel [⟨.source 101, .group 0⟩] 2 [] 0 =
      (none : Option (Key Nat Nat × Key Nat Nat)) ∧
    peel fixtureOwnerSource.expressions 4 [] 99 = none ∧
    peel fixtureOwnerSource.expressions 5 [] 2 = none ∧
    peel fixtureOwnerSource.expressions 5 [] 3 = none := by decide

theorem duplicate_aligned_uses_rejected (s : Source S T)
    (source : OwnerSource (Key S T)) (calls : List (SourceCall (Key S T)))
    (u : Use Nat (Key S T)) (receiving target : Key S T)
    (first second : Plan Nat (Key S T) T) (rest : List (Plan Nat (Key S T) T))
    (duplicate : alignedUses s source calls receiving target = first :: second :: rest) :
    constructAligned s source calls u receiving target = none := by
  simp [constructAligned, duplicate]

end YulangClosure.SourceInternalChoiceR77
