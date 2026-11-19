import Yulang.GeneralRebaseFreshSupport277
import Yulang.GeneralNominalVersionedMixedAdministrative236

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseOwnedSupport277
open GeneralDeclarations
open GeneralNominalState (State sources atomSources)
open GeneralNominalIdentities (Origin source)
open GeneralNominalSaturationState (Packet)
open GeneralNominalAllocation (Bindings occurrences cross lower upper equations)
open GeneralNominalAllocationSupport (Endpoints)
open GeneralNominalVersionedAllocation231 (capture merges keys reserved Fresh)
open GeneralRebaseFreshSupport277 (Support fresh_of_support)

def Owned (state : State) (id : Nat) : Prop :=
  id ≤ state.seed ∨ ∃ key ∈ state.allocated, source state.seed key = id

def Covered (state : State) : Prop :=
  ∀ id ∈ sources state, Owned state id

theorem allFresh (covered : Covered state) (reg : Registry) (root : Nat) (bs : Bindings) :
    Fresh state reg root bs := by
  apply fresh_of_support _ reg bs
  intro id known
  rcases covered id known with low | ⟨key,owned,same⟩
  · exact Or.inl low
  · exact Or.inr ⟨key,same,Or.inl owned⟩

theorem merge_sources (state : State) (visible : d ∈ reg.declarations)
    (endpoints : Endpoints bs pool)
    (reserve : reserved state reg root bs ⊆ pool)
    (atom : PresenceNormalForm.Atom Nat) (valid : atom ∈ merges state reg root d bs) :
    atomSources atom ⊆ pool := by
  obtain ⟨name,used,branch⟩ := List.mem_flatMap.mp valid
  have allocated := GeneralNominalVersionedAllocation231.aggregate_reserved
    (state := state) (root := root) (bindings := bs) visible used
  have low := reserve allocated.1
  have high := reserve allocated.2
  have contained := GeneralNominalAllocationSupport.occurrences_endpoints endpoints name
  cases exact : occurrences bs name with
  | nil =>
    change atom ∈ (match occurrences bs name with
      | [_] => []
      | bounds => equations ((capture state reg root d.id bs).inputs name).1 (lower bounds) ++
          equations ((capture state reg root d.id bs).inputs name).2 (upper bounds)) at branch
    rw [exact] at branch
    rcases List.mem_append.mp branch with first|last
    · exact GeneralNominalAllocationSupport.equation_sources _ _
        (by simpa only [capture,exact] using low)
        (GeneralNominalAllocationSupport.lower_sources _ (by rw [exact] at contained; exact contained)) atom first
    · exact GeneralNominalAllocationSupport.equation_sources _ _
        (by simpa only [capture,exact] using high)
        (GeneralNominalAllocationSupport.upper_sources _ (by rw [exact] at contained; exact contained)) atom last
  | cons first tail =>
    cases tail with
    | nil =>
      change atom ∈ (match occurrences bs name with
        | [_] => []
        | bounds => equations ((capture state reg root d.id bs).inputs name).1 (lower bounds) ++
            equations ((capture state reg root d.id bs).inputs name).2 (upper bounds)) at branch
      rw [exact] at branch
      cases branch
    | cons second rest =>
      change atom ∈ (match occurrences bs name with
        | [_] => []
        | bounds => equations ((capture state reg root d.id bs).inputs name).1 (lower bounds) ++
            equations ((capture state reg root d.id bs).inputs name).2 (upper bounds)) at branch
      rw [exact] at branch
      rcases List.mem_append.mp branch with lowEq|highEq
      · exact GeneralNominalAllocationSupport.equation_sources _ _
          (by simpa only [capture,exact] using low)
          (GeneralNominalAllocationSupport.lower_sources _ (by rw [exact] at contained; exact contained)) atom lowEq
      · exact GeneralNominalAllocationSupport.equation_sources _ _
          (by simpa only [capture,exact] using high)
          (GeneralNominalAllocationSupport.upper_sources _ (by rw [exact] at contained; exact contained)) atom highEq

theorem atoms_supported (p : Packet roles) (visible : p.declaration ∈ p.registry.declarations)
    (atom : PresenceNormalForm.Atom Nat)
    (added : atom ∈ GeneralNominalVersionedInstallation231.atoms p) :
    atomSources atom ⊆ sources p.context.state ++ GeneralNominalVersionedInstallation231.reserved p := by
  have old : sources p.context.state ⊆ sources p.context.state ++ GeneralNominalVersionedInstallation231.reserved p :=
    fun _ h => List.mem_append_left _ h
  have new : GeneralNominalVersionedInstallation231.reserved p ⊆
      sources p.context.state ++ GeneralNominalVersionedInstallation231.reserved p :=
    fun _ h => List.mem_append_right _ h
  have ep : Endpoints p.bindings (sources p.context.state ++ GeneralNominalVersionedInstallation231.reserved p) := by
    intro item present
    have known := GeneralNominalAllocationSupport.report_endpoints p.context.state
      (GeneralNominalPacketSupport.report p) item present
    exact ⟨old known.1,old known.2⟩
  unfold GeneralNominalVersionedInstallation231.atoms at added
  rcases List.mem_append.mp added with main|checks
  · rcases List.mem_append.mp main with cross|merge
    · exact GeneralNominalAllocationSupport.cross_sources ep atom cross
    · exact merge_sources p.context.state visible ep new atom merge
  · exact GeneralNominalAllocationSupport.checks_sources _ _ old atom checks

theorem replay_support (p : GeneralNominalCenters.Plan roles)
    (visible : p.packet.declaration ∈ p.packet.registry.declarations) :
    sources (GeneralNominalVersionedInstallation231.replayPlan p).packet.context.state ⊆
      sources p.packet.context.state ++ GeneralNominalVersionedInstallation231.reserved p.packet := by
  apply GeneralNominalAllocationSupport.extend_sources p.packet.context.state _ _
  · exact fun _ h => List.mem_append_left _ h
  · exact fun _ h => List.mem_append_right _ h
  · exact atoms_supported p.packet visible

theorem replay_owned (p : GeneralNominalCenters.Plan roles)
    (visible : p.packet.declaration ∈ p.packet.registry.declarations)
    (old : Covered p.packet.context.state) :
    Covered (GeneralNominalVersionedInstallation231.replayPlan p).packet.context.state := by
  intro id seen
  rcases List.mem_append.mp (replay_support p visible seen) with prior | added
  · rcases old id prior with low|⟨key,owned,same⟩
    · exact Or.inl low
    · exact Or.inr ⟨key,List.mem_append_left _ owned,same⟩
  · obtain ⟨key,owned,same⟩ := List.mem_map.mp added
    exact Or.inr ⟨key,List.mem_append_right _ owned,same⟩

theorem certified_refinement {a b : State} (refines : GeneralNominalRefinements.Refines a b)
    (support : sources b ⊆ sources a) (covered : Covered a) : Covered b := by
  intro id seen
  rcases covered id (support seen) with small | ⟨key,owned,same⟩
  · exact Or.inl (refines.seed.symm ▸ small)
  · exact Or.inr ⟨key,refines.allocated key owned,by rw [refines.seed]; exact same⟩

end Yulang.GeneralRebaseOwnedSupport277
