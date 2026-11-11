import Yulang.GeneralCandidateInspection
import Yulang.GeneralDictionaryBinderLocations
import Yulang.B4TargetV3Totality

/-!
# Checked candidate boundary components

This supplies a conservative partial judgment on the general declaration and
state carriers. It is not a complete SourceBoundary. Constructor translation,
compound child materialization and root output materialization remain explicit
coverage limits. Missing supported-range certificates defer the candidate.
The supplied frame's source provenance and freshness remain unproved; this
judgment must not be used as a complete source classifier without that bridge.

The fixed frame's input endpoints are checked against the actual captures.
Children come from the existing complete canonical emission, without resolving
any child. K2 does not depend on the absence of another candidate's blockers.
-/
namespace Yulang.GeneralCandidateBoundaryParts

open GeneralSourceState (State Assignment Models)
open GeneralDeclarations (Registry Declaration DeclarationChecked Checked)
open GeneralSourceDictionaries (Occurrence)
open GeneralCandidateInspection

structure Context (roles : Roles.RoleDecls) where
  state : State
  primitives : Primitives
  view : GeneralNormalizedObservation.Snapshot state
  frames : Occurrence roles → GeneralDictionaryEmissionPlans.Frame roles
  merged : Occurrence roles → Nat → Nat → Fin state.slots × Fin state.slots

def vocabulary (roles : Roles.RoleDecls) : B4Target.Vocabulary where
  Registry := Registry
  State := Context roles
  Demand := Occurrence roles
  Model := Assignment

def RegistryChecked (roles : Roles.RoleDecls) (registry : Registry) : Prop :=
  registry.roles = roles ∧ Checked registry

def StateModels (context : Context roles) (model : Assignment) : Prop := Models context.state model

def RootPending (context : Context roles) (root : Occurrence roles) : Prop :=
  GeneralSourceK2.RootPending context.view root.demand (GeneralDeclarationDemands.needed roles root.demand)

/-- A complete recurrent argument is sufficient; another argument's unresolved
descendant does not suppress this K2 reason. All unnamed root heads still wait. -/
def RootK2 (context : Context roles) (root : Occurrence roles) : Prop :=
  GeneralSourceState.Linked context.state root.demand ∧ ¬ RootPending context root ∧
    ∃ argument slot, context.state.source slot = (root.demand.arguments argument).1 ∧
      GeneralSourceK2.Complete context.view slot ∧
      GeneralSourceBoundary.GraphK2 context.view.graph slot

/-- Only independently available fields are packaged. There is intentionally
no Step, Stable, Generated, Evidence, or executor in this record. Candidate
relations below still require source-frame and constructor-interpretation
bridges and are not installed as complete fields. -/
structure AvailableFields (roles : Roles.RoleDecls) where
  Checked : Registry → Prop
  Models : Context roles → Assignment → Prop
  RootPending : Registry → Context roles → Occurrence roles → Prop
  RootK2 : Registry → Context roles → Occurrence roles → Prop
  Reorders : Registry → Registry → Prop
  DictionaryEquivalent : CommonRoleOutermostResolver.Dictionary → CommonRoleOutermostResolver.Dictionary → Prop

def availableFields (roles : Roles.RoleDecls) : AvailableFields roles where
  Checked := RegistryChecked roles
  Models := StateModels
  RootPending := fun _ => RootPending
  RootK2 := fun _ => RootK2
  Reorders := GeneralRegistryReordering.Reorders
  DictionaryEquivalent := GeneralDictionaryPayloadOrder.Equivalent

def locate (state : State) (arguments : List GeneralSourceState.Interval) :
    Option (List (Bounds state)) :=
  arguments.mapM fun bounds => do
    let lower ← GeneralDictionaryBinderLocations.sourceSlot state bounds.1
    let upper ← GeneralDictionaryBinderLocations.sourceSlot state bounds.2
    pure (lower, upper)

def arguments (context : Context roles) (root : Occurrence roles) : Option (List (Bounds context.state)) :=
  locate context.state (List.ofFn root.demand.arguments)

def report (context : Context roles) (_root : Occurrence roles) (declaration : Declaration)
    (bounds : List (Bounds context.state)) : Report context.state :=
  inspectMany context.view (headQueries context.primitives declaration) bounds

def HeadReady (context : Context roles) (root : Occurrence roles) (declaration : Declaration) : Prop :=
  ∃ bounds, arguments context root = some bounds ∧
    Finished (headQueries context.primitives declaration) bounds (report context root declaration bounds) ∧
    GeneralCandidateIntervals.Survives context.state (report context root declaration bounds).captures

def Failed (constructors : GeneralDeclarationPatterns.Constructors) (context : Context roles) (root : Occurrence roles) (declaration : Declaration) : Prop :=
  PrimitivesCompatible constructors context.primitives ∧ ∃ bounds, arguments context root = some bounds ∧
    ((report context root declaration bounds).conflicts ≠ [] ∨
      GeneralCandidateIntervals.Eliminated context.state (report context root declaration bounds).captures)

def CaptureLinked (context : Context roles) (root : Occurrence roles) (declaration : Declaration)
    (bindings : GeneralCandidateIntervals.Bindings context.state) : Prop :=
  GeneralCandidateIntervals.MergeLinked context.state bindings (context.merged root declaration.id) ∧
    ∀ name ∈ CommonRoleCandidateConstraints.names bindings,
      ((context.frames root).capture declaration.id).inputs name =
        (context.state.source (context.merged root declaration.id name).1,
         context.state.source (context.merged root declaration.id name).2)

/-- Only already interpretable child requests are certified here. In particular,
an output-only binder uses its own target identity, never an interval centre. -/
def EmissionsReady (context : Context roles) (root : Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked constructors roles declaration)
    (bindings : GeneralCandidateIntervals.Bindings context.state) : Prop :=
  root.demand.outputs = [] ∧
    ∀ emission ∈ GeneralCanonicalChildOrder.canonicalEmit root.identity declaration checked
      ((context.frames root).capture declaration.id) ((context.frames root).allocation declaration.id),
      GeneralSourceState.Linked context.state emission.demand ∧
      (∀ input ∈ emission.inputs, ∃ name ∈ CommonRoleCandidateConstraints.names bindings,
        GeneralDeclarationPatterns.normalize input.pattern = .var name ∧
        input.endpoints = ((context.frames root).capture declaration.id).inputs name) ∧
      (∀ output ∈ emission.outputs, ∃ name ∈ declaration.outputNames,
        GeneralDeclarationPatterns.normalize output.pattern = .var name)

def Prepared (context : Context roles) (root : Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked constructors roles declaration) : Prop :=
  ∃ bounds, arguments context root = some bounds ∧
    Finished (headQueries context.primitives declaration) bounds (report context root declaration bounds) ∧
    GeneralCandidateIntervals.Survives context.state (report context root declaration bounds).captures ∧
    CaptureLinked context root declaration (report context root declaration bounds).captures ∧
    EmissionsReady context root declaration checked (report context root declaration bounds).captures ∧
    GeneralSourceState.Linked context.state root.demand ∧
    PrimitivesCompatible constructors context.primitives

/-- Certified candidates for the implemented observation/materialization range.
Unknown applications do not fail this judgment and become rejections: the
separate InspectionPending predicate retains those visible declarations. -/
def Survivor (registry : Registry) (context : Context roles) (root : Occurrence roles)
    (key : Nat) (children : List (Occurrence roles)) : Prop :=
  ¬ RootPending context root ∧
    ∃ declaration ∈ registry.declarations, ∃ checked : DeclarationChecked registry.constructors roles declaration,
      declaration.id = key ∧ declaration.role = root.demand.role ∧
      Prepared context root declaration checked ∧
      children = GeneralDictionaryEmissionPlans.children (context.frames root) root declaration checked

def InspectionPending (registry : Registry) (context : Context roles) (root : Occurrence roles) : Prop :=
  ¬ RootPending context root ∧
    ∃ declaration ∈ registry.declarations, ∃ checked : DeclarationChecked registry.constructors roles declaration,
      declaration.role = root.demand.role ∧ ¬ Failed registry.constructors context root declaration ∧
        ¬ Prepared context root declaration checked

/-- Child resolution is absent. Materialized capture/output obligations must
already be accounted for, but unrelated candidates may still be inspecting. -/
def CandidateK2 (registry : Registry) (context : Context roles) (root : Occurrence roles) : Prop :=
  ¬ RootPending context root ∧
    ∃ declaration ∈ registry.declarations, ∃ _checked : DeclarationChecked registry.constructors roles declaration,
      declaration.role = root.demand.role ∧ HeadReady context root declaration ∧
      root.demand.outputs = [] ∧ GeneralSourceState.Linked context.state root.demand ∧
      ∃ bounds, arguments context root = some bounds ∧ NeedsK2 context.view (report context root declaration bounds) ∧
        PrimitivesCompatible registry.constructors context.primitives

theorem pending_excludes_rootK2 (context : Context roles) (root : Occurrence roles)
    (pending : RootPending context root) : ¬ RootK2 context root := fun rejected => rejected.2.1 pending

theorem pending_excludes_candidateK2 (registry : Registry) (context : Context roles)
    (root : Occurrence roles) (pending : RootPending context root) : ¬ CandidateK2 registry context root :=
  fun rejected => rejected.1 pending

theorem rootK2_recurrence (context : Context roles) (root : Occurrence roles)
    (rejected : RootK2 context root) :
    ∃ argument slot, context.state.source slot = (root.demand.arguments argument).1 ∧
      GeneralSourceK2.RecursAt context.view slot := by
  obtain ⟨argument, slot, source, _, recursive⟩ := rejected.2.2
  exact ⟨argument, slot, source, GeneralSourceK2.graphK2_sound context.view slot recursive⟩

theorem prepared_headReady (context : Context roles) (root : Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked constructors roles declaration)
    (prepared : Prepared context root declaration checked) : HeadReady context root declaration := by
  obtain ⟨bounds, located, finished, survived, _, _⟩ := prepared
  exact ⟨bounds, located, finished, survived⟩

theorem headReady_not_failed (constructors : GeneralDeclarationPatterns.Constructors) (context : Context roles) (root : Occurrence roles) (declaration : Declaration)
    (ready : HeadReady context root declaration) : ¬ Failed constructors context root declaration := by
  rintro ⟨_, other, found, conflict | eliminated⟩ <;>
    obtain ⟨bounds, located, finished, survived⟩ := ready <;>
    have same := Option.some.inj (located.symm.trans found) <;> subst other
  · exact conflict finished.2.2.1
  · exact GeneralCandidateIntervals.survives_excludes_eliminated _ _ survived eliminated

theorem conservative_deferral (registry : Registry) (context : Context roles) (root : Occurrence roles)
    (started : ¬ RootPending context root) (declaration : Declaration)
    (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (role : declaration.role = root.demand.role) (notFailed : ¬ Failed registry.constructors context root declaration)
    (unfinished : ¬ Prepared context root declaration checked) :
    InspectionPending registry context root := ⟨started, declaration, visible, checked, role, notFailed, unfinished⟩

theorem blocked_unprepared (context : Context roles) (root : Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked constructors roles declaration) (bounds : List (Bounds context.state))
    (located : arguments context root = some bounds)
    (unfinished : (report context root declaration bounds).blocked ≠ []) :
    ¬ Prepared context root declaration checked := by
  rintro ⟨other, found, finished, _⟩
  have same := Option.some.inj (located.symm.trans found)
  subst other
  exact unfinished finished.2.1

theorem private_model_not_failed (constructors : GeneralDeclarationPatterns.Constructors) (context : Context roles) (root : Occurrence roles) (declaration : Declaration)
    (bounds : List (Bounds context.state)) (located : arguments context root = some bounds)
    (clear : (report context root declaration bounds).conflicts = [])
    (model : Assignment) (models : Models (GeneralCandidateIntervals.propagate context.state
      (report context root declaration bounds).captures) model) : ¬ Failed constructors context root declaration := by
  rintro ⟨_, other, found, conflict | eliminated⟩ <;>
    have same := Option.some.inj (located.symm.trans found) <;> subst other
  · exact conflict clear
  · exact GeneralCandidateIntervals.eliminated_no_model _ _ eliminated ⟨model, models⟩

theorem all_failed_no_survivors (registry : Registry) (context : Context roles) (root : Occurrence roles)
    (failed : ∀ declaration ∈ registry.declarations, declaration.role = root.demand.role →
      Failed registry.constructors context root declaration) :
    (∀ key children, ¬ Survivor registry context root key children) ∧
      ¬ InspectionPending registry context root := by
  constructor
  · intro key children survivor
    obtain ⟨_, declaration, visible, checked, _, role, prepared, _⟩ := survivor
    exact headReady_not_failed registry.constructors context root declaration (prepared_headReady _ _ _ checked prepared)
      (failed declaration visible role)
  · rintro ⟨_, declaration, visible, _, role, notFailed, _⟩
    exact notFailed (failed declaration visible role)

theorem survivor_children_functional (registry : Registry) (checked : Checked registry)
    (context : Context roles) (root : Occurrence roles) (key : Nat)
    (first last : List (Occurrence roles))
    (one : Survivor registry context root key first) (two : Survivor registry context root key last) :
    first = last := by
  obtain ⟨_, declaration₁, visible₁, checked₁, key₁, _, _, children₁⟩ := one
  obtain ⟨_, declaration₂, visible₂, checked₂, key₂, _, _, children₂⟩ := two
  have same := GeneralDictionaryEmissionPlans.declaration_key_unique registry checked declaration₁ declaration₂
    visible₁ visible₂ (key₁.trans key₂.symm)
  subst declaration₂
  exact children₁.trans children₂.symm

theorem survivor_interval_sound (registry : Registry) (context : Context roles) (root : Occurrence roles)
    (key : Nat) (children : List (Occurrence roles))
    (survivor : Survivor registry context root key children) :
    ∃ declaration ∈ registry.declarations, declaration.id = key ∧
      ∃ bounds, arguments context root = some bounds ∧
        ∀ model, Models (GeneralCandidateIntervals.propagate context.state
          (report context root declaration bounds).captures) model →
          Models context.state model ∧ CommonRoleCandidateConstraints.Compatible
            (report context root declaration bounds).captures (context.state.assignment model) := by
  obtain ⟨_, declaration, visible, checked, identity, _, prepared, _⟩ := survivor
  obtain ⟨bounds, located, _, _, _, _⟩ := prepared
  exact ⟨declaration, visible, identity, bounds, located,
    fun model valid => (GeneralCandidateIntervals.propagate_models _ _ model).mp valid⟩

theorem candidateK2_inspected_recurrence (registry : Registry) (context : Context roles)
    (root : Occurrence roles) (rejected : CandidateK2 registry context root) :
    ∃ declaration ∈ registry.declarations, ∃ bounds,
      arguments context root = some bounds ∧
      ∃ visit ∈ (report context root declaration bounds).inspected,
        GeneralSourceK2.Complete context.view visit.bounds.1 ∧
        GeneralSourceK2.RecursAt context.view visit.bounds.1 := by
  obtain ⟨_, declaration, visible, _, _, _, _, _, bounds, located, recursive, _⟩ := rejected
  exact ⟨declaration, visible, bounds, located, inspection_recurrence context.view _ recursive⟩

/-- The exact same-key premise needed by V3 local totality is available for a
future boundary extending these fields. No unfilled field is assigned a value. -/
theorem local_total_of_extension (roles : Roles.RoleDecls) (boundary : B4Target.SourceBoundary (vocabulary roles))
    (registry : Registry) (checked : Checked registry) (context : Context roles) (root : Occurrence roles)
    (agrees : ∀ key children, boundary.Survivor registry context root key children ↔
      Survivor registry context root key children) :
    ∃ frontier, B4TargetV3.Local boundary registry context root frontier := by
  apply B4TargetV3.local_total
  intro key first last one two
  exact survivor_children_functional registry checked context root key first last
    ((agrees key first).mp one) ((agrees key last).mp two)

end Yulang.GeneralCandidateBoundaryParts
