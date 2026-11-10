import Yulang.CommonRoleWhereSourceModels
import Yulang.CommonRoleAllocatedGraph

/-! Compute finite original owners for all actual where endpoint occurrences.
The identity here is the ambient name in the original endpoint syntax, not a
local declaration binder or equality of observed types. Graphs remain explicit
inputs; this does not establish their ordinary-state adequacy or solve children. -/
namespace Yulang.CommonRoleWhereSourceAllocation
open CommonRoleSourceIdentity (Table Slot source retain)
open CommonRoleSourceDescent (representative representative_exists representative_source)
open CommonRoleCanonicalSourceGraph (canonical)
open CommonRoleCanonicalSourceGrowth (newRoot)
open CommonRoleAllocatedGraph (allocate retainSnapshot)
open CommonRoleGraphInspection (inspectSnapshot VisibleHead)
open CommonRoleRegularGraph (Graph)
open CommonRoleIntervalPaterson (Goal)
open CommonRoleStablePaterson (Declaration)
open CommonRoleSourceIntervalBatches (Demand)
open CommonRoleWhereSourceModels (goalSources)

/-- Resolve original endpoint names to their first parent occurrences. -/
def locate (table : Table) : List Nat → Option (List (Slot table))
  | [] => some []
  | name :: names => do
    let owner ← representative table name
    let owners ← locate table names
    pure (owner :: owners)

/-- Name inclusion, independent of the executable search. -/
def Included (table names : Table) : Prop := ∀ name ∈ names, name ∈ table

theorem representative_present (table : Table) (name : Nat) :
    (∃ owner, representative table name = some owner) ↔ name ∈ table := by
  constructor
  · rintro ⟨owner, found⟩
    rw [← representative_source table name owner found]
    exact List.getElem_mem owner.isLt
  · intro present
    obtain ⟨i, bound, equal⟩ := List.mem_iff_getElem.mp present
    have found := representative_exists table ⟨i, bound⟩
    simpa only [source, equal] using found

/-- The finite owner search succeeds exactly on the original source domain. -/
theorem locate_exact (table names : Table) :
    (∃ owners, locate table names = some owners) ↔ Included table names := by
  induction names with
  | nil => simp [locate, Included]
  | cons name names ih =>
    constructor
    · rintro ⟨owners, found⟩
      cases head : representative table name with
      | none => simp [locate, head] at found
      | some owner =>
        cases tail : locate table names with
        | none => simp [locate, head, tail] at found
        | some rest =>
          intro n present
          rcases List.mem_cons.mp present with rfl | present
          · exact (representative_present table _).mp ⟨owner, head⟩
          · exact ih.mp ⟨rest, tail⟩ n present
    · intro included
      obtain ⟨owner, head⟩ := (representative_present table name).mpr
        (included name List.mem_cons_self)
      obtain ⟨rest, tail⟩ := ih.mpr
        (fun n present => included n (List.mem_cons_of_mem _ present))
      exact ⟨owner :: rest, by simp [locate, head, tail]⟩

/-- Returned finite owners retain the complete ordered occurrence list. -/
theorem locate_sources (table names : Table) (owners : List (Slot table))
    (found : locate table names = some owners) : owners.map (source table) = names := by
  induction names generalizing owners with
  | nil => simpa [locate] using congrArg (Option.map (List.map (source table))) found.symm
  | cons name names ih =>
    cases head : representative table name with
    | none => simp [locate, head] at found
    | some owner =>
      cases tail : locate table names with
      | none => simp [locate, head, tail] at found
      | some rest =>
        have equal : owner :: rest = owners := by simpa [locate, head, tail] using found
        subst owners
        simp [representative_source table name owner head, ih rest tail]

/-- The computed owner is already the canonical original occurrence. -/
theorem representative_canonical (table : Table) (name : Nat) (owner : Slot table)
    (found : representative table name = some owner) : canonical table owner = owner := by
  simp [canonical, representative_source table name owner found, found]

theorem locate_canonical (table names : Table) (owners : List (Slot table))
    (found : locate table names = some owners) :
    ∀ owner ∈ owners, canonical table owner = owner := by
  induction names generalizing owners with
  | nil => have eq : [] = owners := by simpa [locate] using found
           subst owners
           simp
  | cons name names ih =>
    cases head : representative table name with
    | none => simp [locate, head] at found
    | some owner =>
      cases tail : locate table names with
      | none => simp [locate, head, tail] at found
      | some rest =>
        have equal : owner :: rest = owners := by simpa [locate, head, tail] using found
        subst owners
        intro i member
        rcases List.mem_cons.mp member with rfl | member
        · exact representative_canonical table _ _ head
        · exact ih rest tail i member

/-- Actual original-parent and generated-child tables, with multiplicity. -/
def parentTable (goal : Goal) : Table := goalSources goal.arguments

def childTable (result : CommonRoleWhereSourceModels.Result α) : Table :=
  result.children.flatMap fun child => goalSources child.arguments

/-- No model assumption: all actual generated names belong to the parent table. -/
theorem returned_included (slots : Nat → α) (old : List (Demand α))
    (declaration : Declaration) (goal : Goal) (bindingSource : Nat → Nat)
    (result : CommonRoleWhereSourceModels.Result α)
    (returned : CommonRoleWhereSourceModels.run slots old declaration goal bindingSource =
      some (some result)) : Included (parentTable goal) (childTable result) := by
  intro name present
  obtain ⟨child, member, present⟩ := List.mem_flatMap.mp present
  exact CommonRoleWhereSourceModels.returned_sources slots old declaration goal
    bindingSource result returned child member name present

/-- Every actual return has computable canonical finite owners. No additional
failure is introduced by allocation, even when the interval state has no model. -/
theorem returned_owners (slots : Nat → α) (old : List (Demand α))
    (declaration : Declaration) (goal : Goal) (bindingSource : Nat → Nat)
    (result : CommonRoleWhereSourceModels.Result α)
    (returned : CommonRoleWhereSourceModels.run slots old declaration goal bindingSource =
      some (some result)) :
    ∃ owners, locate (parentTable goal) (childTable result) = some owners ∧
      owners.map (source (parentTable goal)) = childTable result ∧
      ∀ owner ∈ owners, canonical (parentTable goal) owner = owner := by
  obtain ⟨owners, found⟩ := (locate_exact _ _).mpr
    (returned_included slots old declaration goal bindingSource result returned)
  exact ⟨owners, found, locate_sources _ _ _ found, locate_canonical _ _ _ found⟩

/-- Use the returned finite list in position order. The length equality is
proved from the actual search result, never supplied as an alias assumption. -/
def ownerAt (table names : Table) (owners : List (Slot table))
    (found : locate table names = some owners) (i : Slot names) : Slot table :=
  owners.get ⟨i.val, by
    have lengths := congrArg List.length (locate_sources table names owners found)
    simp only [List.length_map] at lengths
    omega⟩

theorem ownerAt_source (table names : Table) (owners : List (Slot table))
    (found : locate table names = some owners) (i : Slot names) :
    source table (ownerAt table names owners found i) = source names i := by
  have equal := locate_sources table names owners found
  have bound : i.val < owners.length := by
    have lengths := congrArg List.length equal
    simp only [List.length_map] at lengths
    omega
  have atIndex : (owners.map (source table))[i.val]'
      (by simpa only [List.length_map] using bound) = names[i.val] := by simp only [equal]
  simpa [ownerAt, source] using atIndex

theorem ownerAt_canonical (table names : Table) (owners : List (Slot table))
    (found : locate table names = some owners) (i : Slot names) :
    canonical table (ownerAt table names owners found i) = ownerAt table names owners found i :=
  locate_canonical table names owners found _ (List.get_mem ..)

/-- No caller-supplied equality: allocation uses the computed old owner exactly. -/
theorem allocated_root (table names : Table) (owners : List (Slot table))
    (found : locate table names = some owners) (i : Slot names) :
    newRoot table names i = retain table names (ownerAt table names owners found i) := by
  have root := (CommonRoleCanonicalSourceGrowth.newRoot_old_exact
    table names i (ownerAt table names owners found i)).mpr
      (ownerAt_source table names owners found i).symm
  simpa only [ownerAt_canonical] using root

/-- The exact full snapshot at each computed child source owner is preserved.
Arbitrary cyclic graphs, unknowns, visible order and capture payloads are covered. -/
theorem allocated_snapshot (table names : Table) (owners : List (Slot table))
    (found : locate table names = some owners) (i : Slot names)
    (graph : Graph table.length) (role : Nat) (visible : List VisibleHead) :
    inspectSnapshot (allocate table names graph) role (newRoot table names i) visible =
      retainSnapshot table names
        (inspectSnapshot graph role (ownerAt table names owners found i) visible) := by
  rw [allocated_root table names owners found i]
  exact CommonRoleAllocatedGraph.snapshot_allocated ..

/-- Actual capture-to-allocation bridge. The single return premise is executable;
all finite source ownership and graph-root preservation facts are derived. This
is local where allocation, not dictionary selection or recursive saturation. -/
theorem returned_allocation (slots : Nat → α) (old : List (Demand α))
    (declaration : Declaration) (goal : Goal) (bindingSource : Nat → Nat)
    (result : CommonRoleWhereSourceModels.Result α)
    (returned : CommonRoleWhereSourceModels.run slots old declaration goal bindingSource =
      some (some result)) :
    ∃ owners, ∃ found : locate (parentTable goal) (childTable result) = some owners,
      owners.map (source (parentTable goal)) = childTable result ∧
      ∀ i : Slot (childTable result),
        newRoot (parentTable goal) (childTable result) i =
          retain (parentTable goal) (childTable result)
            (ownerAt (parentTable goal) (childTable result) owners found i) ∧
        ∀ (graph : Graph (parentTable goal).length) (role : Nat) (visible : List VisibleHead),
          inspectSnapshot (allocate (parentTable goal) (childTable result) graph) role
            (newRoot (parentTable goal) (childTable result) i) visible =
              retainSnapshot (parentTable goal) (childTable result)
                (inspectSnapshot graph role
                  (ownerAt (parentTable goal) (childTable result) owners found i) visible) := by
  obtain ⟨owners, found, names, _⟩ := returned_owners slots old declaration goal
    bindingSource result returned
  exact ⟨owners, found, names, fun i => ⟨allocated_root _ _ _ found i,
    fun graph role visible => allocated_snapshot _ _ _ found i graph role visible⟩⟩

/-- The actual candidate and its computed finite endpoint owners travel together. -/
structure Prepared (α : Type) (goal : Goal) where
  candidate : CommonRoleWhereSourceModels.Result α
  owners : List (Slot (parentTable goal))

/-- Executable allocation after actual candidate inspection. The subsequent
conservativity theorem proves that the finite lookup adds no failure case. -/
def prepare (slots : Nat → α) (old : List (Demand α))
    (declaration : Declaration) (goal : Goal) (bindingSource : Nat → Nat) :
    Option (Option (Prepared α goal)) := do
  let answer ← CommonRoleWhereSourceModels.run slots old declaration goal bindingSource
  match answer with
  | none => pure none
  | some candidate =>
    let owners ← locate (parentTable goal) (childTable candidate)
    pure (some ⟨candidate, owners⟩)

/-- Erasing only the allocation payload recovers all three original outcomes
literally. No consistency, successful capture, or domain premise is assumed. -/
theorem prepare_conservative (slots : Nat → α) (old : List (Demand α))
    (declaration : Declaration) (goal : Goal) (bindingSource : Nat → Nat) :
    (prepare slots old declaration goal bindingSource).map
      (Option.map Prepared.candidate) =
        CommonRoleWhereSourceModels.run slots old declaration goal bindingSource := by
  cases returned : CommonRoleWhereSourceModels.run slots old declaration goal bindingSource with
  | none => simp [prepare, returned]
  | some answer =>
    cases answer with
    | none => simp [prepare, returned]
    | some candidate =>
      obtain ⟨owners, found, _, _⟩ := returned_owners slots old declaration goal
        bindingSource candidate returned
      simp [prepare, returned, found]

/-- Exact executable payload boundary, preserving the original candidate state
and child order while exposing the computed finite owner list. -/
theorem prepare_exact (slots : Nat → α) (old : List (Demand α))
    (declaration : Declaration) (goal : Goal) (bindingSource : Nat → Nat)
    (result : Prepared α goal) :
    prepare slots old declaration goal bindingSource = some (some result) ↔
      CommonRoleWhereSourceModels.run slots old declaration goal bindingSource =
        some (some result.candidate) ∧
      locate (parentTable goal) (childTable result.candidate) = some result.owners := by
  constructor
  · intro returned
    have original := prepare_conservative slots old declaration goal bindingSource
    rw [returned] at original
    have candidate := original.symm
    simp only [Option.map_some] at candidate
    refine ⟨candidate, ?_⟩
    cases found : locate (parentTable goal) (childTable result.candidate) with
    | none => simp [prepare, candidate, found] at returned
    | some owners =>
      have equal : (⟨result.candidate, owners⟩ : Prepared α goal) = result := by
        simpa [prepare, candidate, found] using returned
      have same := congrArg Prepared.owners equal
      exact congrArg some same
  · rintro ⟨candidate, found⟩
    cases result
    simp_all [prepare]

/-- At the executable public entry, the returned owners determine all original
source identities and preserve each complete graph snapshot. The graph and
visible heads are universally quantified, not selected from a favorable model. -/
theorem prepared_allocation (slots : Nat → α) (old : List (Demand α))
    (declaration : Declaration) (goal : Goal) (bindingSource : Nat → Nat)
    (result : Prepared α goal)
    (returned : prepare slots old declaration goal bindingSource = some (some result)) :
    ∃ found : locate (parentTable goal) (childTable result.candidate) = some result.owners,
      result.owners.map (source (parentTable goal)) = childTable result.candidate ∧
      ∀ i : Slot (childTable result.candidate),
        newRoot (parentTable goal) (childTable result.candidate) i =
          retain (parentTable goal) (childTable result.candidate)
            (ownerAt (parentTable goal) (childTable result.candidate) result.owners found i) ∧
        ∀ (graph : Graph (parentTable goal).length) (role : Nat) (visible : List VisibleHead),
          inspectSnapshot (allocate (parentTable goal) (childTable result.candidate) graph) role
            (newRoot (parentTable goal) (childTable result.candidate) i) visible =
              retainSnapshot (parentTable goal) (childTable result.candidate)
                (inspectSnapshot graph role
                  (ownerAt (parentTable goal) (childTable result.candidate)
                    result.owners found i) visible) := by
  have found := ((prepare_exact slots old declaration goal bindingSource result).mp returned).2
  exact ⟨found, locate_sources _ _ _ found, fun i => ⟨allocated_root _ _ _ found i,
    fun graph role visible => allocated_snapshot _ _ _ found i graph role visible⟩⟩

end Yulang.CommonRoleWhereSourceAllocation
