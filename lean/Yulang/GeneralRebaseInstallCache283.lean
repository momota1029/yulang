import Yulang.GeneralRebaseSortedCache283

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseInstallCache283
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralNominalVersionedInstall232 (install InstallationModels)
open GeneralNominalVersionedMixedSeedLedger237 (Recorded entries)
open GeneralNominalVersionedAggregateLedger236 (packetEntries)
open GeneralRebaseHistoryOrder282 (history decode ordered)
open GeneralRebaseProspective282 (recorded_install members)
open GeneralRebaseProspectiveDelta283 (ext_history coherent_history descending_history)
open GeneralRebaseSortedCache283 (Ascending push push_exact safe)
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralPresenceOrderedBlock247 (solve SafeOrder)
open GeneralRebaseIncrementalHistory283 (update)
open GeneralNominalAcyclicEquations237 (Coherent Descending)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (model)

structure Valid (cache : List (Entry Nat)) (state : State roles) : Prop where
  increasing : Ascending cache
  content : ∀ row, row ∈ cache ↔ row ∈ history state

def initial (state : State roles) : List (Entry Nat) := push (entries state) []

def add (cache : List (Entry Nat)) (effect : Effect roles) : List (Entry Nat) :=
  push (packetEntries effect.plan.packet) cache

def interpret (cache : List (Entry Nat)) (base : Assignment) := solve model cache base

def forward (cache : List (Entry Nat)) (effect : Effect roles) (values : Assignment) :=
  update cache (add cache effect) values

variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
  {state : State roles} {effect : Effect roles} {cache : List (Entry Nat)}

theorem initial_valid (recorded : Recorded state) : Valid (initial state) state := by
  obtain ⟨ordered,content⟩ := push_exact (entries state) [] List.Pairwise.nil
    (by simpa using GeneralNominalVersionedHistoryEquations237.coherent recorded)
  exact ⟨ordered,fun row => (show row ∈ initial state ↔ row ∈ entries state from by simpa only [initial,List.not_mem_nil,or_false] using content row).trans (members recorded row).symm⟩

theorem transport {after : State roles} (same : after.plans = state.plans)
    (valid : Valid cache state) : Valid cache after := by
  refine ⟨valid.increasing,?_⟩
  have steps : entries after = entries state := congrArg
    (fun plans : List (GeneralNominalCenters.Plan roles) => plans.flatMap fun p : GeneralNominalCenters.Plan roles => packetEntries p.packet) same
  intro row
  simpa only [history,steps] using valid.content row

theorem add_valid (valid : Valid cache state) (record : Recorded state)
    (snap : effect.snapshot = state.core) : Valid (add cache effect) (install state effect) := by
  have all (row) : row ∈ packetEntries effect.plan.packet ++ cache ↔
      row ∈ history (install state effect) := by
    rw [List.mem_append,valid.content,ext_history record snap]
  have complete := coherent_history _ (recorded_install record snap)
  have facts := push_exact (packetEntries effect.plan.packet) cache valid.increasing
    (fun a yes b other eq => complete a ((all a).mp yes) b ((all b).mp other) eq)
  exact ⟨facts.1,fun row => (facts.2 row).trans (List.mem_append.symm.trans (all row))⟩

theorem coherent (valid : Valid cache state) (record : Recorded state) : Coherent cache :=
  fun a one b two equal => coherent_history state record a ((valid.content a).mp one)
    b ((valid.content b).mp two) equal

theorem descending (valid : Valid cache state) (record : Recorded state) : Descending cache :=
  fun row present => descending_history state record row ((valid.content row).mp present)

theorem interpret_exact (valid : Valid cache state) (record : Recorded state) (base : Assignment) :
    interpret cache base = decode state base :=
  GeneralRebaseExactHistory283.order_independent valid.content (descending valid record)
    (safe _ valid.increasing (descending valid record)) (ordered state).2.2 base

theorem forward_exact (valid : Valid cache state) (record : Recorded state)
    (snap : effect.snapshot = state.core) (base : Assignment) :
    forward cache effect (interpret cache base) = interpret (add cache effect) base := by
  have next := add_valid valid record snap
  have new := recorded_install record snap
  apply GeneralRebaseIncrementalHistory283.exact_update
  · intro row member
    exact (next.content row).mpr ((ext_history record snap row).mpr (Or.inr ((valid.content row).mp member)))
  · exact coherent next new
  · exact descending next new
  · exact safe _ valid.increasing (descending valid record)
  · exact safe _ next.increasing (descending next new)

theorem lookup (valid : Valid cache state) (record : Recorded state)
    (snap : effect.snapshot = state.core) (base : Assignment) :
    forward cache effect (interpret cache base) = decode (install state effect) base :=
  (forward_exact valid record snap base).trans
    (interpret_exact (add_valid valid record snap) (recorded_install record snap) base)

theorem candidate (valid : Valid cache state) (reach : Reachable registry root state)
    (snap : effect.snapshot = state.core) :
    (∃ base, Models (install state effect) (forward cache effect (interpret cache base))) ↔
    ∃ a, InstallationModels state effect a := by
  have recorded := GeneralNominalVersionedMixedSeedLedger237.reachable reach
  have same (base : Assignment) :=
    (lookup valid recorded snap base).trans ((GeneralRebaseProspectiveDelta283.reachable_exact reach snap base).symm)
  exact (exists_congr (fun base => by rw [same])).trans (GeneralRebaseProspectiveDelta283.guard reach snap)

end Yulang.GeneralRebaseInstallCache283
