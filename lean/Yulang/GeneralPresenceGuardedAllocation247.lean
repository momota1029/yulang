import Yulang.GeneralPresenceGuardedBlock246
import Yulang.GeneralPresenceGuardedConsumers247

/-! Concrete finite reservation above a listed support. Reserve once at initial
owner installation and retain the resulting target map on later refreshes;
recomputing a larger reservation at every refresh is not this design. Distinct
owners need distinct reservations, for example by including earlier reserved
names in the next support. Completeness of actual source support is not proved
here, and this allocator alone is not a solver termination argument. -/
namespace Yulang.GeneralPresenceGuardedAllocation247
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceGuardedBlock246
open CommonNominalFullCarrier

def maximum (support : List Nat) : Nat := support.foldr max 0

def seed (support : List Nat) : Nat := maximum support + 1

def targets (support : List Nat) (index : Fin nodes) : Nat := seed support + index.val

def reserved (support : List Nat) (nodes : Nat) : List Nat :=
  List.ofFn (targets support : Fin nodes → Nat)

theorem member_le_maximum (support : List Nat) (name : Nat) (member : name ∈ support) :
    name ≤ maximum support := by
  induction support with
  | nil => simp at member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | present
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih present) (Nat.le_max_right _ _)

theorem support_below_seed (support : List Nat) (name : Nat) (member : name ∈ support) :
    name < seed support := by
  have bound := member_le_maximum support name member
  unfold seed
  omega

theorem targets_injective (support : List Nat) :
    Function.Injective (targets support : Fin nodes → Nat) := by
  intro first last same
  apply Fin.ext
  simp only [targets] at same
  omega

theorem target_range (support : List Nat) (index : Fin nodes) :
    seed support ≤ targets support index ∧ targets support index < seed support + nodes := by
  have bound := index.isLt
  simp only [targets]
  omega

theorem target_not_support (support : List Nat) (index : Fin nodes) (name : Nat)
    (member : name ∈ support) : targets support index ≠ name := by
  have below := support_below_seed support name member
  have lower := (target_range support index).1
  omega

theorem parameters_separate (support : List Nat) (parametersAt : Fin parameters → Nat)
    (covered : ∀ parameter, parametersAt parameter ∈ support) :
    ∀ index : Fin nodes, ∀ parameter, targets support index ≠ parametersAt parameter := by
  intro index parameter
  exact target_not_support support index _ (covered parameter)

theorem reserved_length (support : List Nat) (nodes : Nat) :
    (reserved support nodes).length = nodes := by simp [reserved]

theorem reserved_range (support : List Nat) (nodes name : Nat)
    (member : name ∈ reserved support nodes) :
    maximum support < name ∧ name < maximum support + 1 + nodes := by
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
  have bound := target_range support index
  simp only [seed] at bound
  omega

theorem reserved_disjoint_support (support : List Nat) (nodes name : Nat)
    (member : name ∈ reserved support nodes) : name ∉ support := by
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
  intro present
  exact target_not_support support index _ present rfl

/-- Supplied support names are kept literally, including their row components. -/
theorem extend_support (support : List Nat) (body : Body Nat nodes parameters)
    (parametersAt : Fin parameters → Nat) (boundary : Nat → Comp model)
    (name : Nat) (member : name ∈ support) :
    extend body (targets support) parametersAt boundary name = boundary name :=
  extend_outside body (targets support) parametersAt boundary name
    (fun index => target_not_support support index name member)

theorem allocated_public_model (support : List Nat) (body : Body Nat nodes parameters)
    (parametersAt : Fin parameters → Nat) (covered : ∀ parameter, parametersAt parameter ∈ support)
    (boundary : Nat → Comp model) :
    ∃ assignment, All model assignment (block (entries body (targets support) parametersAt)) ∧
      (∀ name ∈ support, assignment name = boundary name) ∧
      (∀ name, (assignment name).2 = (boundary name).2) :=
  ⟨extend body (targets support) parametersAt boundary,
    block_satisfied body (targets support) (targets_injective support) parametersAt
      (parameters_separate support parametersAt covered) boundary,
    extend_support support body parametersAt boundary,
    extend_rows body (targets support) parametersAt boundary⟩

/-- Complete typed support for this actual atom list and parameter vector only.
Rows need no fresh names because the extension preserves every row coordinate. -/
def consumerSupport (parametersAt : Fin parameters → Nat) (atoms : List (Atom Nat)) : List Nat :=
  List.ofFn parametersAt ++ GeneralPresenceConsumerSupport246.listTypedReads atoms

theorem consumer_parameters (parametersAt : Fin parameters → Nat) (atoms : List (Atom Nat))
    (parameter : Fin parameters) : parametersAt parameter ∈ consumerSupport parametersAt atoms :=
  List.mem_append_left _ (List.mem_ofFn.mpr ⟨parameter,rfl⟩)

theorem consumer_outside (parametersAt : Fin parameters → Nat) (atoms : List (Atom Nat)) :
    GeneralPresenceGuardedConsumers247.OutsideReads
      (targets (consumerSupport parametersAt atoms) : Fin nodes → Nat) atoms := by
  intro name member index
  exact target_not_support _ index name (List.mem_append_right _ member)

theorem consumer_check (parametersAt : Fin parameters → Nat) (atoms : List (Atom Nat)) :
    GeneralPresenceGuardedConsumers247.outsideCheck
      (targets (consumerSupport parametersAt atoms) : Fin nodes → Nat) atoms = true :=
  (GeneralPresenceGuardedConsumers247.outsideCheck_exact _ _).mpr (consumer_outside parametersAt atoms)

/-- Fresh initial installation into any supplied actual atom list, without a
semantic solvability premise or an assumed outside-read certificate. -/
theorem initial_add_definitions (body : Body Nat nodes parameters)
    (parametersAt : Fin parameters → Nat) (atoms : List (Atom Nat))
    (boundary : Nat → Comp model) :
    All model boundary atoms ↔
      ∃ assignment, All model assignment
        (atoms ++ block (entries body (targets (consumerSupport parametersAt atoms)) parametersAt)) ∧
        (∀ name, (∀ index : Fin nodes, targets (consumerSupport parametersAt atoms) index ≠ name) →
          assignment name = boundary name) ∧
        (∀ name, (assignment name).2 = (boundary name).2) :=
  GeneralPresenceGuardedConsumers247.checked_add_definitions body
    (targets (consumerSupport parametersAt atoms)) (targets_injective _) parametersAt
    (parameters_separate _ parametersAt (consumer_parameters parametersAt atoms)) boundary atoms
    (consumer_check parametersAt atoms)

end Yulang.GeneralPresenceGuardedAllocation247
