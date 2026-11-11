import Yulang.GeneralDictionaryEquationRecording
import Yulang.CommonRoleCandidateConstraints

/-!
# Candidate intervals in the actual shared state

Each alternative gets a private ordinary extension. The generator compares
every occurrence with every occurrence of the same variable, including itself.
No central type or selected substitution is constructed. Solver coverage is
checked explicitly; an uncovered ordinary state cannot justify elimination.
-/
namespace Yulang.GeneralCandidateIntervals

open GeneralSourceState (State Assignment Models)
open Core.PresenceGeneration (TyTerm)
open PresenceNormalForm (Atom All)

abbrev Bindings (state : State) := CommonRoleCandidateConstraints.Bindings state.slots

structure Covered (state : State) : Prop where
  child : PresenceGeneratedChildGrammar.GoodAtoms state.ordinary
  width : PresenceGeneratedWidth.WidthAtoms state.ordinary
  rows : PresenceSourceConstraintSupport.GoodAtoms state.ordinary
  /-- The existing ordinary solver has independent local row parameters.
  Shared row aliases need explicit equality generation before this restriction
  can be removed; lack of this certificate defers, rather than eliminates. -/
  rowSources : Function.Injective state.rowSource

def propagate (state : State) (bindings : Bindings state) : State :=
  GeneralDictionaryEquationRecording.append state (CommonRoleCandidateConstraints.generate bindings)

def Survives (state : State) (bindings : Bindings state) : Prop :=
  Covered state ∧ CommonRoleCandidateConstraints.solve state.ordinary bindings ≠ []

def Eliminated (state : State) (bindings : Bindings state) : Prop :=
  Covered state ∧ CommonRoleCandidateConstraints.solve state.ordinary bindings = []

theorem propagate_models (state : State) (bindings : Bindings state)
    (model : Assignment) :
    Models (propagate state bindings) model ↔
      Models state model ∧ CommonRoleCandidateConstraints.Compatible bindings (state.assignment model) := by
  rw [propagate, GeneralDictionaryEquationRecording.append_models, CommonRoleCandidateConstraints.generate_exact]

theorem propagated_capture_sound (state : State) (bindings : Bindings state)
    (model : Assignment) (models : Models (propagate state bindings) model) :
    CommonRoleCandidateConstraints.Compatible bindings (state.assignment model) :=
  ((propagate_models state bindings model).mp models).2

theorem propagated_original (state : State) (bindings : Bindings state)
    (model : Assignment) (models : Models (propagate state bindings) model) :
    Models state model := ((propagate_models state bindings model).mp models).1

theorem recorded_capture_sound (state : State) (bindings : Bindings state)
    (recorded : ∀ atom ∈ CommonRoleCandidateConstraints.generate bindings, atom ∈ state.ordinary)
    (model : Assignment) (models : Models state model) :
    CommonRoleCandidateConstraints.Compatible bindings (state.assignment model) :=
  (CommonRoleCandidateConstraints.generate_exact ..).mp (fun atom member => models.1 atom (recorded atom member))

theorem eliminated_no_model (state : State) (bindings : Bindings state)
    (eliminated : Eliminated state bindings) :
    ¬ ∃ model, Models (propagate state bindings) model := by
  rintro ⟨model, valid⟩
  have both := (propagate_models state bindings model).mp valid
  exact (CommonRoleCandidateConstraints.solve_empty_exact state.ordinary bindings eliminated.1.child
    eliminated.1.width eliminated.1.rows).mp eliminated.2
      ⟨state.assignment model, both.1.1, both.2⟩

theorem model_survives (state : State) (bindings : Bindings state)
    (covered : Covered state) (model : Assignment)
    (models : Models (propagate state bindings) model) : Survives state bindings := by
  refine ⟨covered, ?_⟩
  intro empty
  exact eliminated_no_model state bindings ⟨covered, empty⟩ ⟨model, models⟩

theorem uncovered_defers (state : State) (bindings : Bindings state)
    (uncovered : ¬ Covered state) :
    ¬ Survives state bindings ∧ ¬ Eliminated state bindings :=
  ⟨fun survived => uncovered survived.1, fun eliminated => uncovered eliminated.1⟩

theorem row_alias_defers (state : State) (bindings : Bindings state)
    (first last : Fin state.slots) (distinct : first ≠ last)
    (aliased : state.rowSource first = state.rowSource last) :
    ¬ Survives state bindings ∧ ¬ Eliminated state bindings :=
  uncovered_defers state bindings (fun covered => distinct (covered.rowSources aliased))

theorem survives_excludes_eliminated (state : State) (bindings : Bindings state)
    (survives : Survives state bindings) : ¬ Eliminated state bindings :=
  fun eliminated => survives.2 eliminated.2

private noncomputable def liftAssignment (state : State)
    (assignment : Fin state.slots → Core.PresenceGeneration.Comp Common.model) : Assignment := by
  classical
  exact fun source =>
    (if found : ∃ slot, state.source slot = source then (assignment (Classical.choose found)).1 else .bottom,
     if found : ∃ slot, state.rowSource slot = source then (assignment (Classical.choose found)).2 else Common.rowEmpty)

private theorem lifted_assignment (state : State) (rows : Function.Injective state.rowSource)
    (assignment : Fin state.slots → Core.PresenceGeneration.Comp Common.model) :
    state.assignment (liftAssignment state assignment) = assignment := by
  classical
  funext slot
  apply Prod.ext
  · have existsSlot : ∃ other, state.source other = state.source slot := ⟨slot, rfl⟩
    have same : Classical.choose existsSlot = slot := state.source_injective (Classical.choose_spec existsSlot)
    simp [GeneralSourceState.State.assignment, liftAssignment, existsSlot, same]
  · have existsSlot : ∃ other, state.rowSource other = state.rowSource slot := ⟨slot, rfl⟩
    have same : Classical.choose existsSlot = slot := rows (Classical.choose_spec existsSlot)
    simp [GeneralSourceState.State.assignment, liftAssignment, existsSlot, same]

/-- A positive ordinary-solver result has an actual original-source model.
This is a consistency witness theorem, not a search for head substitutions. -/
theorem survives_has_model (state : State) (bindings : Bindings state)
    (survived : Survives state bindings) : ∃ model, Models (propagate state bindings) model := by
  cases result : CommonRoleCandidateConstraints.solve state.ordinary bindings with
  | nil => exact False.elim (survived.2 result)
  | cons scheme rest =>
      have member : scheme ∈ CommonRoleCandidateConstraints.solve state.ordinary bindings := by
        rw [result]; exact List.mem_cons_self
      let parameters : scheme.Parameters := (fun _ => .bottom, fun _ => .bottom)
      let assignment := scheme.instantiate (fun _ => Common.rowEmpty) parameters
      have valid := CommonRoleCandidateConstraints.solve_sound state.ordinary bindings scheme member
        (fun _ => Common.rowEmpty) parameters
      refine ⟨liftAssignment state assignment, (propagate_models ..).mpr ⟨?_, ?_⟩⟩
      · apply (GeneralSourceState.models_ordinary ..).mpr
        change All Common.model (state.assignment (liftAssignment state assignment)) state.ordinary
        rw [lifted_assignment state survived.1.rowSources]
        exact valid.1
      · rw [lifted_assignment state survived.1.rowSources]
        exact (CommonRoleCandidateConstraints.generate_exact ..).mp valid.2

theorem survives_iff_model (state : State) (bindings : Bindings state) (covered : Covered state) :
    Survives state bindings ↔ ∃ model, Models (propagate state bindings) model :=
  ⟨survives_has_model state bindings, fun ⟨model, valid⟩ => model_survives state bindings covered model valid⟩

/-- Coalescing retains two endpoints: a union of lowers and an intersection of
uppers. These terms still require actual source slots before child emission. -/
def merged (bindings : Bindings state) (name : Nat) :
    TyTerm (Fin state.slots) × TyTerm (Fin state.slots) :=
  ((CommonRoleCandidateConstraints.bounds bindings name).foldr (fun pair rest => .union (.var pair.1) rest) .bottom,
   (CommonRoleCandidateConstraints.bounds bindings name).foldr (fun pair rest => .inter (.var pair.2) rest) .top)

def MergeLinked (state : State) (bindings : Bindings state)
    (locations : Nat → Fin state.slots × Fin state.slots) : Prop :=
  ∀ name ∈ CommonRoleCandidateConstraints.names bindings, ∀ model, Models state model →
    Common.Equivalent (model (state.source (locations name).1)).1
      ((merged bindings name).1.eval Common.model (state.assignment model)) ∧
    Common.Equivalent (model (state.source (locations name).2)).1
      ((merged bindings name).2.eval Common.model (state.assignment model))

/-- Finite ordinary storage is a sufficient, independently checked connection
between merged endpoint terms and the source identities used by child demands. -/
def MergeRecorded (state : State) (bindings : Bindings state)
    (locations : Nat → Fin state.slots × Fin state.slots) : Prop :=
  ∀ name ∈ CommonRoleCandidateConstraints.names bindings,
    (∀ atom ∈ GeneralSourceState.equationAtoms (locations name).1 (merged bindings name).1,
      atom ∈ state.ordinary) ∧
    (∀ atom ∈ GeneralSourceState.equationAtoms (locations name).2 (merged bindings name).2,
      atom ∈ state.ordinary)

theorem merge_recorded_linked (state : State) (bindings : Bindings state)
    (locations : Nat → Fin state.slots × Fin state.slots)
    (recorded : MergeRecorded state bindings locations) :
    MergeLinked state bindings locations := by
  intro name named model models
  have stored := recorded name named
  constructor
  · exact (GeneralSourceState.equationAtoms_exact ..).mp
      (fun atom member => models.1 atom (stored.1 atom member))
  · exact (GeneralSourceState.equationAtoms_exact ..).mp
      (fun atom member => models.1 atom (stored.2 atom member))

theorem singleton_merge_linked (state : State) (name : Nat) (bounds : Fin state.slots × Fin state.slots) :
    MergeLinked state [(name, bounds)] (fun _ => bounds) := by
  intro other named model _
  have equal : other = name := by simpa [CommonRoleCandidateConstraints.names] using named
  subst other
  simp only [merged, CommonRoleCandidateConstraints.bounds, List.filterMap_cons, List.filterMap_nil, Common.model]
  refine ⟨⟨CommonBoundCoalescing.le_union_left _ _, ?_⟩, ⟨?_, CommonBoundCoalescing.inter_le_left _ _⟩⟩
  · exact (Common.common_union_is_join ..).mpr ⟨Common.subtype_refl _, CommonBoundCoalescing.bottom_le _⟩
  · exact (Common.common_inter_is_meet ..).mpr ⟨Common.subtype_refl _, CommonBoundCoalescing.le_top _⟩

/-- Recording checks for one alternative says nothing about another alternative.
The equivalence exposes precisely which conjunction a shared transaction adds. -/
theorem two_alternatives_models (state : State) (first last : Bindings state)
    (model : Assignment) :
    Models (GeneralDictionaryEquationRecording.append state (CommonRoleCandidateConstraints.generate first ++ CommonRoleCandidateConstraints.generate last)) model ↔
      Models state model ∧ CommonRoleCandidateConstraints.Compatible first (state.assignment model) ∧
        CommonRoleCandidateConstraints.Compatible last (state.assignment model) := by
  rw [GeneralDictionaryEquationRecording.append_models, PresenceNormalForm.all_append, CommonRoleCandidateConstraints.generate_exact, CommonRoleCandidateConstraints.generate_exact]

end Yulang.GeneralCandidateIntervals
