import Yulang.GeneralNominalVersionedMixedTerminalStable234
import Yulang.GeneralNominalCenteredHeadMatStepEnumeration
set_option backward.isDefEq.respectTransparency false
/-! Finite equality-only saturation in the existing mixed kernel. The pool is
exactly the current finite source list. Every added equation already holds in
all full journal models. No installation/refresh termination is asserted. -/
namespace Yulang.GeneralNominalVersionedMixedEqualityClosure235
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234
open GeneralNominalVersionedAdministrative232 (equate)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {state after : State roles}

theorem equate_models_iff (equal : Equal state first last) (model : Assignment) :
    Models (equate state first last) model ↔ Models state model := by
  constructor
  · exact GeneralNominalVersionedAdministrative232.equate_models
  · intro valid
    obtain ⟨legacy,plans,effects⟩ := valid
    refine ⟨?_,plans,?_⟩
    · refine ⟨?_,legacy.2.1,legacy.2.2.1,legacy.2.2.2.1,legacy.2.2.2.2.1,?_⟩
      · exact (GeneralNominalState.extend_models ..).mpr ⟨legacy.1,
          (GeneralNominalCaptureMerges.equations_exact ..).mpr (equal model ⟨legacy,plans,effects⟩)⟩
      · intro effect member
        have held := legacy.2.2.2.2.2 effect member
        refine ⟨held.1,?_⟩
        exact GeneralNominalCenteredHeadMatEffects.restrict
          (GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
            (before := (equate state first last).core) (after := state.core)
            (fun _ h => h) (fun _ h => h)) held.2
    · intro effect member
      have held := effects effect member
      exact ⟨held.1,live_restrict
        (GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
          (before := (equate state first last).core) (after := state.core)
          (fun _ h => h) (fun _ h => h)) held.2⟩

theorem equate_sources_iff
    (one : first ∈ GeneralNominalState.sources state.core.erased.current.context.state)
    (two : last ∈ GeneralNominalState.sources state.core.erased.current.context.state) :
    identity ∈ GeneralNominalState.sources (equate state first last).core.erased.current.context.state ↔
      identity ∈ GeneralNominalState.sources state.core.erased.current.context.state := by
  constructor
  · intro member
    exact GeneralNominalCenteredHeadMatStepEnumeration.equate_sources one two member
  · intro member
    change identity ∈ GeneralNominalState.sources (GeneralNominalState.extend state.core.erased.current.context.state [] _)
    simp only [GeneralNominalState.sources,GeneralNominalState.extend,List.append_nil,List.flatMap_append,List.mem_append] at member ⊢
    exact member.elim Or.inl (fun h => Or.inr (Or.inl h))

theorem raw_preserved (raw : GeneralNominalFeedbackSteps.RawEqual state.core.erased.current a b) :
    GeneralNominalFeedbackSteps.RawEqual (equate state first last).core.erased.current a b := by
  intro model valid
  exact raw model ((GeneralNominalState.extend_models ..).mp valid).1

inductive Trace : State roles → State roles → Prop
 | refl (value : State roles) : Trace value value
 | tail {before current : State roles} {first last : Nat} : Trace before current →
    first ∈ GeneralNominalState.sources current.core.erased.current.context.state →
    last ∈ GeneralNominalState.sources current.core.erased.current.context.state →
    Equal current first last → ¬ GeneralNominalFeedbackSteps.RawEqual current.core.erased.current first last →
    Trace before (equate current first last)

theorem trace_models (path : Trace state after) (model : Assignment) : Models after model ↔ Models state model := by
  induction path with
  | refl => rfl
  | tail path one two equal novel ih => exact (equate_models_iff equal model).trans ih

theorem trace_sources (path : Trace state after) :
    identity ∈ GeneralNominalState.sources after.core.erased.current.context.state ↔
      identity ∈ GeneralNominalState.sources state.core.erased.current.context.state := by
  induction path with
  | refl => rfl
  | tail path one two equal novel ih => exact (equate_sources_iff one two).trans ih

theorem trace_raw (path : Trace state after)
    (raw : GeneralNominalFeedbackSteps.RawEqual state.core.erased.current first last) :
    GeneralNominalFeedbackSteps.RawEqual after.core.erased.current first last := by
  induction path with
  | refl => exact raw
  | tail path one two equal novel ih => exact raw_preserved ih

theorem trace_trans (one : Trace state middle) (two : Trace middle after) : Trace state after := by
  induction two with
  | refl => exact one
  | tail path a b eq novel ih => exact .tail ih a b eq novel

theorem trace_steps (path : Trace state after) (registry : GeneralDeclarations.Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) : B4Target.Steps (Step registry root) state after := by
  induction path with
  | refl => exact .refl
  | tail path one two equal novel ih => exact .tail ih ⟨root,.root,.administrative (.equate root _ _ one two equal novel)⟩

def withOrdinary (state : State roles) (atoms : List (PresenceNormalForm.Atom Nat)) : State roles :=
  GeneralNominalVersionedAdministrative232.change state { state.core.erased.current with
    context := { state.core.erased.current.context with state := {
      state.core.erased.current.context.state with ordinary := atoms } } }

theorem trace_shape (path : Trace state after) :
    after = withOrdinary state after.core.erased.current.context.state.ordinary := by
  induction path with
  | refl => rfl
  | tail path one two equal novel ih =>
    rw [ih]
    simp only [equate,withOrdinary,GeneralNominalVersionedAdministrative232.change,
      GeneralNominalCenteredHeadMatStepJournal.change,GeneralNominalFeedbackSteps.equate,
      GeneralNominalState.extend,List.append_nil]
    rfl

theorem trace_known (path : Trace state after) :
    GeneralNominalState.Known after.core.erased.current.context.state identity ↔
      GeneralNominalState.Known state.core.erased.current.context.state identity := by
  rw [trace_shape path]
  rfl

theorem trace_pointClosed (path : Trace state after)
    (point : GeneralNominalReobservationSteps.PointClosed state.core.erased.current.context.state) :
    GeneralNominalReobservationSteps.PointClosed after.core.erased.current.context.state := by
  rw [trace_shape path]
  exact point

theorem close_pairs (pairs : List (Nat × Nat)) (state : State roles)
    (supported : ∀ pair ∈ pairs, pair.1 ∈ GeneralNominalState.sources state.core.erased.current.context.state ∧
      pair.2 ∈ GeneralNominalState.sources state.core.erased.current.context.state) :
    ∃ after, Trace state after ∧ ∀ pair ∈ pairs, Equal after pair.1 pair.2 →
      GeneralNominalFeedbackSteps.RawEqual after.core.erased.current pair.1 pair.2 := by
  classical
  induction pairs generalizing state with
  | nil => exact ⟨state,.refl _,by intro _ h; cases h⟩
  | cons pair pairs ih =>
    by_cases equal : Equal state pair.1 pair.2
    · by_cases raw : GeneralNominalFeedbackSteps.RawEqual state.core.erased.current pair.1 pair.2
      · obtain ⟨after,path,closed⟩ := ih state (fun p h => supported p (List.mem_cons_of_mem _ h))
        refine ⟨after,path,?_⟩
        intro p member eq
        rcases List.mem_cons.mp member with rfl | member
        · exact trace_raw path raw
        · exact closed p member eq
      · let next := equate state pair.1 pair.2
        have one := (supported pair List.mem_cons_self).1
        have two := (supported pair List.mem_cons_self).2
        have firstPath : Trace state next := .tail (.refl _) one two equal raw
        obtain ⟨after,path,closed⟩ := ih next (by
          intro p h
          have old := supported p (List.mem_cons_of_mem _ h)
          exact ⟨(trace_sources firstPath).mpr old.1,(trace_sources firstPath).mpr old.2⟩)
        refine ⟨after,trace_trans firstPath path,?_⟩
        intro p member eq
        rcases List.mem_cons.mp member with rfl | member
        · exact trace_raw path (GeneralNominalFeedbackSteps.equate_feedback state.core.erased.current p.1 p.2)
        · exact closed p member eq
    · obtain ⟨after,path,closed⟩ := ih state (fun p h => supported p (List.mem_cons_of_mem _ h))
      refine ⟨after,path,?_⟩
      intro p member eq
      rcases List.mem_cons.mp member with rfl | member
      · exact False.elim (equal (fun model valid => eq model ((trace_models path model).mpr valid)))
      · exact closed p member eq

theorem exists_closed (state : State roles) : ∃ after, Trace state after ∧
    GeneralNominalVersionedMixedTerminalStable234.EqualityClosed after := by
  let sources := GeneralNominalState.sources state.core.erased.current.context.state
  let pairs := sources.flatMap fun first => sources.map fun last => (first,last)
  have supported : ∀ pair ∈ pairs, pair.1 ∈ sources ∧ pair.2 ∈ sources := by
    intro pair member
    obtain ⟨first,one,lastMember⟩ := List.mem_flatMap.mp member
    obtain ⟨last,two,rfl⟩ := List.mem_map.mp lastMember
    exact ⟨one,two⟩
  obtain ⟨after,path,closed⟩ := close_pairs pairs state supported
  refine ⟨after,path,?_⟩
  intro first last one two equal
  exact closed (first,last)
    (List.mem_flatMap.mpr ⟨first,(trace_sources path).mp one,
      List.mem_map.mpr ⟨last,(trace_sources path).mp two,rfl⟩⟩) equal
end Yulang.GeneralNominalVersionedMixedEqualityClosure235
