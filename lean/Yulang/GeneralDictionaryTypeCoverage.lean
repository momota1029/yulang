import Yulang.GeneralDictionaryHeadlessLocations

/-!
# Finite type-source coverage for supplied snapshots

A certificate witnesses actual type slots, not membership in the nominal
state's mixed list of type IDs, row IDs, reservations and ordinary mentions.
The snapshot is supplied: this module neither allocates slots nor certifies
state extension. The demand list keeps every occurrence; coverage may use a
smaller list containing each needed ID only once.
-/
namespace Yulang.GeneralDictionaryTypeCoverage
open GeneralSourceState (State Demand)
open GeneralDictionaryHeadlessLocations (Available locate locate_success_iff locate_none_iff)
open GeneralDictionaryBinderLocations (sourceSlot sourceSlot_exact locateTerm)
open Core.PresenceGeneration (TyTerm)

/-- Only the type coordinate witnesses coverage. Row coordinates do not count. -/
def Covers (state : State) (neededTypeIDs : List Nat) : Prop :=
  ∀ source ∈ neededTypeIDs, ∃ slot, state.source slot = source

/-- Lower endpoints, upper endpoints, and output targets, without deduplication. -/
def demandTypeIDs (demand : Demand roles) : List Nat :=
  List.ofFn (fun index => (demand.arguments index).1) ++
  List.ofFn (fun index => (demand.arguments index).2) ++
  demand.outputs.map (·.target)

theorem demand_coverage_iff (state : State) (demand : Demand roles) :
    Covers state (demandTypeIDs demand) ↔ Available state demand := by
  constructor
  · intro covered
    refine ⟨?_, ?_, ?_⟩
    · intro index
      apply covered
      simp only [demandTypeIDs, List.mem_append, List.mem_ofFn, List.mem_map]
      exact Or.inl (Or.inl ⟨index, rfl⟩)
    · intro index
      apply covered
      simp only [demandTypeIDs, List.mem_append, List.mem_ofFn, List.mem_map]
      exact Or.inl (Or.inr ⟨index, rfl⟩)
    · intro index
      apply covered
      simp only [demandTypeIDs, List.mem_append, List.mem_ofFn, List.mem_map]
      exact Or.inr ⟨_, List.getElem_mem index.isLt, rfl⟩
  · rintro ⟨lower, upper, target⟩ source member
    simp only [demandTypeIDs, List.mem_append, List.mem_ofFn, List.mem_map] at member
    rcases member with (⟨index, rfl⟩ | ⟨index, rfl⟩) | ⟨output, member, rfl⟩
    · exact lower index
    · exact upper index
    · obtain ⟨index, bound, same⟩ := List.getElem_of_mem member
      have located := target ⟨index, bound⟩
      change ∃ slot, state.source slot = (demand.outputs[index]).target at located
      simpa only [same] using located

/-- A finite superset certificate discharges all endpoint and target obligations. -/
theorem available_of_coverage (state : State) (demand : Demand roles)
    (covered : Covers state neededTypeIDs)
    (included : ∀ source ∈ demandTypeIDs demand, source ∈ neededTypeIDs) :
    Available state demand :=
  (demand_coverage_iff state demand).mp (fun source member => covered source (included source member))

theorem locate_of_coverage (state : State) (demand : Demand roles)
    (covered : Covers state neededTypeIDs)
    (included : ∀ source ∈ demandTypeIDs demand, source ∈ neededTypeIDs) :
    ∃ inputs, locate state demand = some inputs :=
  (locate_success_iff state demand).mpr (available_of_coverage state demand covered included)

/-- Exact success requires no nominal linkage, model or interval premise. -/
theorem locate_success_coverage_iff (state : State) (demand : Demand roles) :
    (∃ inputs, locate state demand = some inputs) ↔ Covers state (demandTypeIDs demand) :=
  (locate_success_iff state demand).trans (demand_coverage_iff state demand).symm

/-- A missing actual type slot is exactly why endpoint localization defers. -/
theorem locate_none_missing_iff (state : State) (demand : Demand roles) :
    locate state demand = none ↔
      ∃ source ∈ demandTypeIDs demand, ∀ slot, state.source slot ≠ source := by
  rw [locate_none_iff, ← demand_coverage_iff]
  simp only [Covers, Classical.not_forall, not_exists, exists_prop]

/-- Explicit variable RHS localization has the same actual-slot requirement. -/
theorem locateTerm_variable_iff (state : State) (source : Nat) :
    (∃ term, locateTerm state (.var source) = some term) ↔ Covers state [source] := by
  constructor
  · rintro ⟨term, found⟩ candidate member
    have same : candidate = source := List.mem_singleton.mp member
    subst candidate
    obtain ⟨slot, found, _⟩ := Option.map_eq_some_iff.mp found
    exact ⟨slot, (sourceSlot_exact state source slot).mp found⟩
  · intro covered
    obtain ⟨slot, same⟩ := covered source (by simp)
    refine ⟨.var slot, ?_⟩
    simp only [locateTerm, (sourceSlot_exact state source slot).mpr same, Option.map_some]

end Yulang.GeneralDictionaryTypeCoverage
