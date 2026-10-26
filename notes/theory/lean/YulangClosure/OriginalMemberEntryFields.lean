import YulangClosure.OriginalScopedClosure
import YulangClosure.OriginalRecursivePair

/-!
Source-owned MemberEntry fields at the actual recursive-pair installation.

SG §3.3 and §5.1 distinguish the fixed raw member object from its Internal
description edge. The constructor below derives that split at the existing
WorldRegistry.pairRegistration and retains one whole source-built component.
It does not classify a member by inspecting an opaque descriptor, comparing
providers, or following an installed-world back-reference.

This is a declaration-owner slice. Complete semantic free-field schemas,
the fixed dependency walk, eligible Desc, endpoint grafts and E_V remain open.
The stored original world is unchanged; no world validity or source judgment
is placed in an input field.
-/
namespace YulangClosure.OriginalMemberEntryFields

open OriginalSource OriginalSourceInterpretation OriginalRecursivePair
open OriginalScopedClosure (Position Program)

/-- A single retained component, at its real incoming position. The source
pair and complete outside context are preserved, not memberwise projected. -/
structure Component where
  position : Position
  outside : Context
  pair : SourcePair
  program : Program

def component (position : Position) (outside : Context) (pair : SourcePair) : Component :=
  ⟨position, outside, pair,
    OriginalScopedClosure.allocate position (sourceRules outside pair.statement)⟩

/-- Actual operational fields of one installed member. Its selected
description is deliberately a different constructor field below. -/
structure Operational (s : Sorts) where
  address : Nat
  provider : s.Provider
  value : s.Value
  root : s.Root

/-- An Internal edge is indexed by the retained component itself. Its
member selects a root; it does not carry a separate copied relation. -/
structure Internal (s : Sorts) (owner : Component) where
  member : Side
  descriptor : s.Descriptor

def Internal.program {s : Sorts} {owner : Component} (_edge : Internal s owner) : Program :=
  owner.program

def Internal.component {s : Sorts} {owner : Component} (_edge : Internal s owner) : Site :=
  owner.pair.group

def Internal.binding {s : Sorts} {owner : Component} (edge : Internal s owner) : Binding :=
  owner.pair.memberBinding edge.member

def Internal.publications {s : Sorts} {owner : Component} (_edge : Internal s owner) :
    List OriginalScopedClosure.Publication := owner.program.publications

structure MemberEntry (s : Sorts) (owner : Component) where
  operational : Operational s
  internal : Internal s owner

/-- Reassembly preserves the whole existing Installed object. Splitting
ownership does not erase or replace its descriptor. -/
def MemberEntry.installed {s : Sorts} {owner : Component} (entry : MemberEntry s owner) : Installed s :=
  .value entry.internal.descriptor entry.operational.value entry.operational.root

structure Registration (s : Sorts) where
  component : Component
  entries : Side → MemberEntry s component
  world : WorldRegistry s

/-- The field split is emitted at the genuine simultaneous installation.
The existing world constructor retains aliases, captures and witnesses.
All arguments are its actual original source/data inputs. -/
noncomputable def register (position : Position) (outside : Context) (pair : SourcePair)
    (before : WorldRegistry s) (assignment : PairAssignment s) (guards : WorldGuards)
    (providers : Side → s.Provider)
    (parent : Nat → Option (CaptureData before.bindings before.count)) : Registration s :=
  let owner := component position outside pair
  {component := owner
   entries := fun side =>
     ⟨⟨before.count + side.offset, providers side, assignment.value side, assignment.root side⟩,
       ⟨side, assignment.descriptor side⟩⟩
   world := before.pairRegistration assignment guards pair providers parent}

theorem component_erases (position : Position) (outside : Context) (pair : SourcePair) :
    (component position outside pair).program.erase = sourceRules outside pair.statement :=
  OriginalScopedClosure.erase_allocate position (sourceRules outside pair.statement)

theorem component_residual (position : Position) (outside : Context) (pair : SourcePair) :
    (component position outside pair).program.residual = Build outside pair.statement := by
  simp only [Program.residual, component_erases, Build]

/-- The original independent local Kernel remains arbitrary and unchanged.
This is source reconstruction, not a supplied complete-source certificate. -/
theorem component_source_reconstruction (kernel : Kernel Value) (environment : Environment Value)
    (position : Position) (outside : Context) (pair : SourcePair) :
    Satisfies kernel environment (component position outside pair).program.residual ↔
      SourceJudgment kernel environment outside pair.statement := by
  rw [component_residual]
  exact source_reconstruction kernel environment outside pair.statement

theorem registered_world (position : Position) (outside : Context) (pair : SourcePair)
    (before : WorldRegistry s) (assignment : PairAssignment s) (guards : WorldGuards)
    (providers : Side → s.Provider)
    (parent : Nat → Option (CaptureData before.bindings before.count)) :
    (register position outside pair before assignment guards providers parent).world =
      before.pairRegistration assignment guards pair providers parent := rfl

theorem registered_installed (position : Position) (outside : Context) (pair : SourcePair)
    (before : WorldRegistry s) (assignment : PairAssignment s) (guards : WorldGuards)
    (providers : Side → s.Provider)
    (parent : Nat → Option (CaptureData before.bindings before.count)) (side : Side) :
    ((register position outside pair before assignment guards providers parent).entries side).installed =
      assignment.object side := rfl

theorem registered_binding (position : Position) (outside : Context) (pair : SourcePair)
    (before : WorldRegistry s) (assignment : PairAssignment s) (guards : WorldGuards)
    (providers : Side → s.Provider)
    (parent : Nat → Option (CaptureData before.bindings before.count)) (side : Side) :
    let built := register position outside pair before assignment guards providers parent
    built.world.bindings (built.entries side).operational.address =
      some (built.entries side).installed := by
  classical
  cases side <;>
    simp [register, WorldRegistry.pairRegistration, WorldRegistry.twoBindings,
      WorldRegistry.rebind, extendBindings, Side.offset, MemberEntry.installed, PairAssignment.object]

theorem registered_internal_origin (position : Position) (outside : Context) (pair : SourcePair)
    (before : WorldRegistry s) (assignment : PairAssignment s) (guards : WorldGuards)
    (providers : Side → s.Provider)
    (parent : Nat → Option (CaptureData before.bindings before.count)) (side : Side) :
    let edge := (register position outside pair before assignment guards providers parent).entries side
    edge.internal.component = pair.group ∧
      edge.internal.binding = pair.memberBinding side ∧
      edge.internal.binding.kind = .internal ∧
      edge.internal.binding.component = some pair.group := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem registered_one_component (position : Position) (outside : Context) (pair : SourcePair)
    (before : WorldRegistry s) (assignment : PairAssignment s) (guards : WorldGuards)
    (providers : Side → s.Provider)
    (parent : Nat → Option (CaptureData before.bindings before.count)) (firstMember secondMember : Side) :
    let built := register position outside pair before assignment guards providers parent
    (built.entries firstMember).internal.program = built.component.program ∧
      (built.entries secondMember).internal.program = built.component.program := ⟨rfl, rfl⟩

theorem registered_whole_residual (position : Position) (outside : Context) (pair : SourcePair)
    (before : WorldRegistry s) (assignment : PairAssignment s) (guards : WorldGuards)
    (providers : Side → s.Provider)
    (parent : Nat → Option (CaptureData before.bindings before.count)) (side : Side) :
    ((register position outside pair before assignment guards providers parent).entries side).internal.program.residual =
      Build outside pair.statement := component_residual position outside pair

/-- Retain the actual publication inventory from the complete source, with
all final-root/annotation incidences. No older member synthesis root is
substituted and no independent memberwise publication program is invented. -/
theorem registered_whole_publications (position : Position) (outside : Context) (pair : SourcePair)
    (before : WorldRegistry s) (assignment : PairAssignment s) (guards : WorldGuards)
    (providers : Side → s.Provider)
    (parent : Nat → Option (CaptureData before.bindings before.count)) (side : Side) :
    ((register position outside pair before assignment guards providers parent).entries side).internal.publications =
      OriginalScopedClosure.publications [] [] [] (sourceRules outside pair.statement) := by
  simp only [register, Internal.publications, component, Program.publications,
    OriginalScopedClosure.erase_allocate]

theorem operational_fields_ignore_descriptions (position : Position) (outside : Context) (pair : SourcePair)
    (before : WorldRegistry s) (assignment : PairAssignment s) (guards : WorldGuards)
    (providers : Side → s.Provider)
    (parent : Nat → Option (CaptureData before.bindings before.count))
    (descriptors : Side → s.Descriptor) (side : Side) :
    ((register position outside pair before {assignment with descriptor := descriptors}
      guards providers parent).entries side).operational =
    ((register position outside pair before assignment guards providers parent).entries side).operational := rfl

/-- Every prior successfully stored object survives under the original
fresh-address premises. No semantic membership or hidden count restriction
replaces those existing premises. -/
theorem registered_preserves_old_binding (position : Position) (outside : Context) (pair : SourcePair)
    (before : WorldRegistry s) (assignment : PairAssignment s) (guards : WorldGuards)
    (providers : Side → s.Provider)
    (parent : Nat → Option (CaptureData before.bindings before.count))
    (freshFirst : before.bindings before.count = none)
    (freshSecond : before.bindings (before.count + 1) = none)
    (index : Nat) (object : Installed s) (present : before.bindings index = some object) :
    (register position outside pair before assignment guards providers parent).world.bindings index =
      some object :=
  pair_registration_preserves_every_old before assignment guards pair providers parent
    freshFirst freshSecond index object present

theorem registered_other_capture (position : Position) (outside : Context) (pair : SourcePair)
    (before : WorldRegistry s) (assignment : PairAssignment s) (guards : WorldGuards)
    (providers : Side → s.Provider)
    (parent : Nat → Option (CaptureData before.bindings before.count))
    (provider : s.Provider) (first : provider ≠ providers .first) (second : provider ≠ providers .second)
    (name : Nat) :
    (register position outside pair before assignment guards providers parent).world.captures provider name =
      (before.twoBindings assignment guards).captures provider name :=
  pair_registration_other_provider before assignment guards pair providers parent provider first second name

theorem registered_provider_captures (position : Position) (outside : Context) (pair : SourcePair)
    (before : WorldRegistry s) (assignment : PairAssignment s) (guards : WorldGuards)
    (providers : Side → s.Provider)
    (parent : Nat → Option (CaptureData before.bindings before.count)) (side : Side) (name : Nat) :
    let built := register position outside pair before assignment guards providers parent
    built.world.captures (built.entries side).operational.provider name =
      before.pairEnvironment assignment guards pair parent name := by
  classical
  cases side <;> simp [register, WorldRegistry.pairRegistration]

/-- Capture evidence changes its index type when the registry grows, but
both the original captured address and its entire Installed object survive. -/
theorem registered_old_capture_fields (position : Position) (outside : Context) (pair : SourcePair)
    (before : WorldRegistry s) (assignment : PairAssignment s) (guards : WorldGuards)
    (providers : Side → s.Provider)
    (parent : Nat → Option (CaptureData before.bindings before.count))
    (provider : s.Provider) (first : provider ≠ providers .first) (second : provider ≠ providers .second)
    (name : Nat) :
    let captured := (register position outside pair before assignment guards providers parent).world.captures provider name
    captured.map CaptureData.address = (before.captures provider name).map CaptureData.address ∧
      captured.map CaptureData.object = (before.captures provider name).map CaptureData.object := by
  dsimp only
  rw [registered_other_capture position outside pair before assignment guards providers parent provider first second name]
  cases found : before.captures provider name <;>
    simp [WorldRegistry.twoBindings, WorldRegistry.rebind, found, CaptureData.extend] <;>
    exact ⟨rfl, rfl⟩

/-- Original witness identity/value maps are retained by the actual two
extensions; neither Internal edge introduces an independent Shared witness. -/
theorem registered_shared_witnesses (position : Position) (outside : Context) (pair : SourcePair)
    (before : WorldRegistry s) (assignment : PairAssignment s) (guards : WorldGuards)
    (providers : Side → s.Provider)
    (parent : Nat → Option (CaptureData before.bindings before.count)) :
    let built := register position outside pair before assignment guards providers parent
    built.world.witnessReference = before.witnessReference ∧
      built.world.witnessValue = before.witnessValue := ⟨rfl, rfl⟩

end YulangClosure.OriginalMemberEntryFields
