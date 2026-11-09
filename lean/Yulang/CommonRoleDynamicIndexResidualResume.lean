import Yulang.CommonRoleDynamicIndexResidualSource

/-! Incremental continuation from finite string residuals. Discharged requests
are omitted; their derived facts remain seeds. New string constraints reactivate
pending work through the existing finite driver. This is not arbitrary state
refinement, a general role solver, or an in-place performance result. -/
namespace Yulang.CommonRoleDynamicIndexResidualResume
open CommonRoleSourceIdentity (Table Slot source)
open CommonRoleDynamicIndexSource (Requests WellScoped)
open CommonRoleDynamicIndexEqualitySource (Links saturate Derived)
open CommonRoleDynamicIndexSourceSemantics (SourceModel ForcesString)
open CommonRoleDynamicIndexResidualSource (Packet Models build residual)
open Core.PresenceGeneration (Comp)

def pendingNames (table : Table) (seeds : List (Slot table)) (links : Links table)
    (requests : Requests) : Requests :=
  (residual table seeds links requests).map fun p => (source table p.1, source table p.2)

/-- Projecting back to names neither revives a discharged alias occurrence nor
loses an unresolved occurrence. Source aliases share derived string evidence. -/
theorem pending_names_exact (table : Table) (seeds : List (Slot table)) (links : Links table)
    (requests : Requests) (i j : Slot table) :
    (source table i, source table j) ∈ pendingNames table seeds links requests ↔
      (i,j) ∈ residual table seeds links requests := by
  constructor
  · intro h
    obtain ⟨p,hp,he⟩ := List.mem_map.mp h
    obtain ⟨hr,hn⟩ := (CommonRoleDynamicIndexResidualSource.residual_exact ..).mp hp
    apply (CommonRoleDynamicIndexResidualSource.residual_exact ..).mpr
    refine ⟨?_, ?_⟩
    · simpa only [he] using hr
    · intro hi
      exact hn (.alias (congrArg Prod.fst he).symm hi)
  · intro h
    exact List.mem_map.mpr ⟨(i,j),h,rfl⟩

theorem pending_names_scoped (table : Table) (seeds : List (Slot table))
    (links : Links table) (requests : Requests) :
    WellScoped table (pendingNames table seeds links requests) := by
  intro r hr
  obtain ⟨p,_,rfl⟩ := List.mem_map.mp hr
  exact ⟨p.1,p.2,rfl,rfl⟩

def retainedSeeds (table : Table) (seeds extra : List (Slot table)) (links : Links table)
    (requests : Requests) : List (Slot table) :=
  seeds ++ (saturate table seeds links requests ++ extra)

/-- Retained facts plus only pending requests have exactly the models of the
original source with the extra seeds. No prior model or scope premise is needed;
the checked entrance remains responsible for reporting originally absent names. -/
theorem retained_source_exact (table : Table) (seeds extra : List (Slot table))
    (links : Links table) (requests : Requests) (a : Slot table → Comp Common.model) :
    SourceModel table (retainedSeeds table seeds extra links requests) links
      (pendingNames table seeds links requests) a ↔
      SourceModel table (seeds ++ extra) links requests a := by
  constructor
  · intro h
    refine ⟨?_,h.equalities,h.aliases,?_⟩
    · intro i hi
      apply h.seeds i
      simp only [List.mem_append] at hi
      rcases hi with hi | hi
      · exact List.mem_append_left _ hi
      · exact List.mem_append_right _ (List.mem_append_right _ hi)
    · intro i j hr hs
      by_cases hd : Derived table seeds links requests i
      · apply h.seeds j
        apply List.mem_append_right
        apply List.mem_append_left
        exact (CommonRoleDynamicIndexEqualitySource.saturate_exact ..).mpr (.index hr hd)
      · exact h.requests i j ((pending_names_exact ..).mpr
          ((CommonRoleDynamicIndexResidualSource.residual_exact ..).mpr ⟨hr,hd⟩)) hs
  · intro h
    have old : SourceModel table seeds links requests a :=
      ⟨fun i hi => h.seeds i (List.mem_append_left _ hi),h.equalities,h.aliases,h.requests⟩
    refine ⟨?_,h.equalities,h.aliases,?_⟩
    · intro i hi
      simp only [retainedSeeds, List.mem_append] at hi
      rcases hi with hi | hi | hi
      · exact old.seeds i hi
      · exact CommonRoleDynamicIndexSourceSemantics.derived_sound table seeds links requests i
          ((CommonRoleDynamicIndexEqualitySource.saturate_exact ..).mp hi) a old
      · exact h.seeds i (List.mem_append_right _ hi)
    · intro i j hr hs
      exact h.requests i j ((CommonRoleDynamicIndexResidualSource.residual_exact ..).mp
        ((pending_names_exact ..).mp hr)).1 hs

/-- Reuses the existing driver with retained facts and just the unresolved names. -/
def resume (table : Table) (seeds extra : List (Slot table)) (links : Links table)
    (requests : Requests) : Packet table :=
  build table (retainedSeeds table seeds extra links requests) links
    (pendingNames table seeds links requests)

theorem resume_models_exact (table : Table) (seeds extra : List (Slot table))
    (links : Links table) (requests : Requests) (a : Slot table → Comp Common.model) :
    Models table (resume table seeds extra links requests) a ↔
      Models table (build table (seeds ++ extra) links requests) a := by
  simp only [resume, CommonRoleDynamicIndexResidualSource.build_models_exact]
  exact retained_source_exact ..

/-- Real checked execution after residual continuation has precisely the full
rebuild's independent source forcing criterion. Atom lists need not be identical. -/
theorem resume_checked_exact (table : Table) (seeds extra : List (Slot table))
    (links : Links table) (requests : Requests) (i j : Slot table) :
    (∃ out, CommonRoleOrdinaryKnownness.checkedProduceIndex
      (resume table seeds extra links requests).state i j = some out) ↔
      ForcesString table (seeds ++ extra) links requests i := by
  change (∃ out, CommonRoleOrdinaryKnownness.checkedProduceIndex
    (CommonRoleDynamicIndexEqualitySource.output table
      (retainedSeeds table seeds extra links requests) links
      (pendingNames table seeds links requests)) i j = some out) ↔ _
  rw [CommonRoleDynamicIndexSourceSemantics.checked_source_exact]
  constructor
  · intro h a ha
    exact h a ((retained_source_exact ..).mpr ha)
  · intro h a ha
    exact h a ((retained_source_exact ..).mp ha)

theorem resume_pending_exact (table : Table) (seeds extra : List (Slot table))
    (links : Links table) (requests : Requests) (i j : Slot table) :
    CommonRoleOrdinaryKnownness.checkedProduceIndex
      (resume table seeds extra links requests).state i j = none ↔
      ∃ a b : Slot table → Comp Common.model,
        SourceModel table (seeds ++ extra) links requests a ∧
        SourceModel table (seeds ++ extra) links requests b ∧
        ¬ Common.Equivalent (a i).1 (b i).1 := by
  rw [CommonRoleDynamicIndexSourceSemantics.source_underdetermined_iff]
  constructor
  · intro hn hf
    obtain ⟨out,ho⟩ := (resume_checked_exact table seeds extra links requests i j).mpr hf
    rw [hn] at ho
    cases ho
  · intro hn
    cases h : CommonRoleOrdinaryKnownness.checkedProduceIndex
        (resume table seeds extra links requests).state i j with
    | none => rfl
    | some out => exact False.elim (hn ((resume_checked_exact ..).mp ⟨out,h⟩))

/-- Existing discharged work is stable: continuation without extra constraints
preserves the whole packet model class. It is not equality of serialized atoms. -/
theorem resume_empty_models (table : Table) (seeds : List (Slot table))
    (links : Links table) (requests : Requests) (a : Slot table → Comp Common.model) :
    Models table (resume table seeds [] links requests) a ↔
      Models table (build table seeds links requests) a := by
  simpa using resume_models_exact table seeds [] links requests a

/-- A previously entirely pending chain activates after one late receiver seed. -/
theorem delayed_chain_reactivates :
    (build [10,20,30] [] [] [(10,20),(20,30)]).pending = [(0,1),(1,2)] ∧
    (resume [10,20,30] [] [0] [] [(10,20),(20,30)]).pending = [] ∧
    ∃ out, CommonRoleOrdinaryKnownness.checkedProduceIndex
      (resume [10,20,30] [] [0] [] [(10,20),(20,30)]).state 1 2 = some out := by
  refine ⟨by decide, by decide, ?_⟩
  apply (resume_checked_exact ..).mpr
  apply (CommonRoleDynamicIndexSourceSemantics.source_forces_iff ..).mpr
  apply (CommonRoleDynamicIndexEqualitySource.saturate_exact ..).mp
  decide

end Yulang.CommonRoleDynamicIndexResidualResume
