import Yulang.GeneralNominalProjections
import Yulang.GeneralNominalAllocation

/-! Finite ordinary-constraint generation for projection-aware captures.
Type and row intervals retain both endpoints. Actual-occurrence equalities
remain in the same branch model; the generated inequalities do not replace
them. This module does not claim a complete pattern-to-capture compiler. -/
namespace Yulang.GeneralNominalProjectionPropagation

open GeneralNominalProjections
open PresenceNormalForm (Atom All)

def pairs (bindings : List (Binding state)) : List (Binding state × Binding state) :=
  bindings.flatMap fun first =>
    (bindings.filter fun last => first.name == last.name).map fun last => (first,last)

def compilePairs (state : GeneralNominalState.State) :
    List (Binding state × Binding state) → Option (List (Atom Nat))
  | [] => some []
  | (first,last) :: rest => do
      let head ← GeneralNominalIntervalLaws.checks state.base first.bounds last.bounds
      let tail ← compilePairs state rest
      pure (head ++ tail)

def compile (state : GeneralNominalState.State) (bindings : List (Binding state)) :
    Option (List (Atom Nat)) := compilePairs state (pairs bindings)

theorem mem_pairs (bindings : List (Binding state)) (first last : Binding state) :
    (first,last) ∈ pairs bindings ↔ first ∈ bindings ∧ last ∈ bindings ∧ first.name = last.name := by
  simp only [pairs, List.mem_flatMap, List.mem_map, List.mem_filter, beq_iff_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨a,ha,b,⟨hb,same⟩,rfl,rfl⟩
    exact ⟨ha,hb,same⟩
  · rintro ⟨ha,hb,same⟩
    exact ⟨first,ha,last,⟨hb,same⟩,rfl,rfl⟩

theorem compilePairs_exact (state : GeneralNominalState.State)
    (model : GeneralNominalCommonBridge.Assignment) (items : List (Binding state × Binding state)) :
    (∃ atoms, compilePairs state items = some atoms ∧ All CommonNominalFullCarrier.model model atoms) ↔
      ∀ pair ∈ items, GeneralNominalIntervalLaws.ParameterChecks state.base model pair.1.bounds pair.2.bounds := by
  induction items with
  | nil => simp [compilePairs, All]
  | cons pair rest ih =>
      have head := GeneralNominalIntervalLaws.checks_exact state.base model pair.1.bounds pair.2.bounds
      cases h : GeneralNominalIntervalLaws.checks state.base pair.1.bounds pair.2.bounds <;>
        cases t : compilePairs state rest <;>
        simp_all [compilePairs, PresenceNormalForm.all_append]

theorem compile_exact (state : GeneralNominalState.State)
    (model : GeneralNominalCommonBridge.Assignment) (bindings : List (Binding state)) :
    (∃ atoms, compile state bindings = some atoms ∧ All CommonNominalFullCarrier.model model atoms) ↔
      ∀ first ∈ bindings, ∀ last ∈ bindings, first.name = last.name →
        GeneralNominalIntervalLaws.ParameterChecks state.base model first.bounds last.bounds := by
  rw [compile, compilePairs_exact]
  constructor
  · intro all first one last two same
    exact all (first,last) ((mem_pairs ..).mpr ⟨one,two,same⟩)
  · intro all pair member
    obtain ⟨one,two,same⟩ := (mem_pairs ..).mp member
    exact all pair.1 one pair.2 two same

theorem compile_sound (state : GeneralNominalState.State)
    (model : GeneralNominalCommonBridge.Assignment) (bindings : List (Binding state))
    (compatible : Compatible state model bindings) :
    ∃ atoms, compile state bindings = some atoms ∧ All CommonNominalFullCarrier.model model atoms :=
  (compile_exact state model bindings).mpr
    (fun first one last two same => compatible_cross state model bindings compatible first last one two same)

/-- Adding the compiled ordinary atoms preserves exactly the models already
constrained by projection sharing. It does not discard that sharing. -/
theorem propagation_exact (state : GeneralNominalState.State)
    (model : GeneralNominalCommonBridge.Assignment) (bindings : List (Binding state))
    (atoms : List (Atom Nat)) (compiled : compile state bindings = some atoms) :
    (GeneralNominalState.Models (GeneralNominalState.extend state [] atoms) model ∧
      Compatible state model bindings) ↔ Models ⟨state,bindings⟩ model := by
  rw [GeneralNominalState.extend_models]
  constructor
  · rintro ⟨⟨source,_⟩,compatible⟩; exact ⟨source,compatible⟩
  · rintro ⟨source,compatible⟩
    obtain ⟨generated,equal,valid⟩ := compile_sound state model bindings compatible
    have same := Option.some.inj (equal.symm.trans compiled)
    subst generated
    exact ⟨⟨source,valid⟩,compatible⟩

/-- Extraction follows an ordered descriptor and source identity, without
testing endpoint equality. Constructor patterns require further inspection. -/
def extract (state : GeneralNominalState.State) (slot : Fin state.base.slots)
    (descriptor : GeneralNominalState.Descriptor state.base.slots) :
    Nat → List (List Nat) → List (GeneralNominalState.Parameter state.base.slots) →
      Option (List (Binding state))
  | _, [], [] => some []
  | index, names :: rest, bounds :: tail => do
      let suffix ← extract state slot descriptor (index+1) rest tail
      pure ((names.map fun name => parameterBinding state slot descriptor index name bounds) ++ suffix)
  | _, _, _ => none

theorem extract_one (state : GeneralNominalState.State) (slot : Fin state.base.slots)
    (descriptor : GeneralNominalState.Descriptor state.base.slots) (name : Nat)
    (bounds : GeneralNominalState.Parameter state.base.slots) :
    extract state slot descriptor 0 [[name]] [bounds] =
      some [parameterBinding state slot descriptor 0 name bounds] := rfl

theorem extract_valid (state : GeneralNominalState.State)
    (model : GeneralNominalCommonBridge.Assignment) (models : GeneralNominalState.Models state model)
    (slot : Fin state.base.slots) (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals slot = some descriptor) (offset : Nat) (names : List (List Nat))
    (parameters : List (GeneralNominalState.Parameter state.base.slots))
    (corresponds : ∀ (index : Nat) parameter, parameters[index]? = some parameter →
      descriptor.arguments[offset+index]? = some parameter)
    (bindings : List (Binding state)) (generated : extract state slot descriptor offset names parameters = some bindings) :
    ∀ binding ∈ bindings, binding.Valid state model := by
  induction names generalizing offset parameters bindings with
  | nil =>
      cases parameters with
      | nil => simp [extract] at generated; subst bindings; simp
      | cons => simp [extract] at generated
  | cons head tail ih =>
      cases parameters with
      | nil => simp [extract] at generated
      | cons parameter rest =>
          cases found : extract state slot descriptor (offset+1) tail rest with
          | none => simp [extract,found] at generated
          | some suffix =>
              have equal : (head.map fun name => parameterBinding state slot descriptor offset name parameter) ++ suffix = bindings := by
                simpa [extract,found] using generated
              subst bindings
              intro binding member
              rcases List.mem_append.mp member with present | present
              · obtain ⟨name,_,rfl⟩ := List.mem_map.mp present
                exact parameter_binding_valid state model models slot descriptor recorded offset name parameter
                  (by simpa using corresponds 0 parameter rfl)
              · apply ih (offset+1) rest ?_ suffix found binding present
                intro index argument atIndex
                have next := corresponds (index+1) argument atIndex
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using next

theorem single_capture_compatible (state : GeneralNominalState.State)
    (model : GeneralNominalCommonBridge.Assignment) (binding : Binding state)
    (valid : binding.Valid state model) : Compatible state model [binding] := by
  refine ⟨?_,?_⟩
  · intro item member
    have same := List.mem_singleton.mp member
    subst item
    exact valid
  · intro first one last two _
    have a := List.mem_singleton.mp one
    have b := List.mem_singleton.mp two
    subst first; subst last
    obtain ⟨value,seen,_⟩ := valid
    exact ⟨value,value,seen,seen,observation_unique model binding.origin value value seen seen⟩

end Yulang.GeneralNominalProjectionPropagation
