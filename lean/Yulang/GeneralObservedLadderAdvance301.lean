import Yulang.GeneralObservedLadderEnabled301
import Yulang.GeneralNominalVersionedInstallProperties232

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 8000000
namespace Yulang.GeneralObservedLadderAdvance301
open GeneralObservedLadderInitial301 (initial context)
open GeneralObservedLadderPlan301 (compiled)
open GeneralObservedLadderRoute301
open GeneralObservedLadderLedger301
open GeneralObservedLadderStage301 (stage_emits stage_children)
open GeneralObservedLadderEnabled301 (effect actual installation)
open GeneralDeclarationExamples (roles)
open GeneralNominalExamples (registry displayRoot)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedInstall232 (install)
open GeneralNominalVersionedInstallation231 (reserved atoms allocated)
open GeneralNominalIdentities (source)
open GeneralNominalCommonBridge (Assignment)

abbrev advanced (p : Phase n k) (hi : k ≤ n) := install p.state (effect p hi)

theorem reserved_exact (p : Phase n k) (hi : k ≤ n) :
    reserved (stagePlan p hi).packet =
      (allocated (stagePlan p hi).packet).map (source (n+1)) := rfl

theorem env_exact (p : Phase n k) (hi : k ≤ n) :
    (advanced p hi).core.erased.current.context =
      GeneralDictionaryOrdinaryTransport.extend (context n)
      ((p.keys ++ allocated (stagePlan p hi).packet).map (source (n+1)))
      (p.extraAtoms ++ atoms (stagePlan p hi).packet) (p.keys ++ allocated (stagePlan p hi).packet) := by
  change GeneralDictionaryOrdinaryTransport.extend (env p) (reserved (stagePlan p hi).packet)
      (atoms (stagePlan p hi).packet) (allocated (stagePlan p hi).packet) = _
  rw [reserved_exact,List.map_append]
  rfl

theorem edge_single (p : Phase n k) (hi : k ≤ n) :
    GeneralNominalVersionedChildren232.edges (stagePlan p hi) =
      [(focus n k,focus n (k+1))] := by
  unfold GeneralNominalVersionedChildren232.edges
  rw [stage_children]
  rfl

theorem new_models (p : Phase n k) (hi : k ≤ n) (m : Assignment) :
    Models (advanced p hi) m ↔ Models p.state m :=
  ⟨fun valid => GeneralNominalVersionedMixedSourceBoundary234.stepModels (actual p hi) valid,
    fun valid => (GeneralNominalVersionedInstall232.install_models (effect := effect p hi) rfl).mpr
      (installation p hi m valid)⟩

def advance (p : Phase n k) (hi : k ≤ n) : Phase n (k+1) where
  state := advanced p hi
  keys := p.keys ++ allocated (stagePlan p hi).packet
  extraAtoms := p.extraAtoms ++ atoms (stagePlan p hi).packet
  context_eq := env_exact p hi
  centers_eq := by
    change p.state.core.sites ++ GeneralNominalVersionedChildren232.emitted (stagePlan p hi) = _
    rw [p.centers_eq,stage_emits]
    rfl
  raw_eq := by
    change p.state.core.erased.current.sites ++ GeneralNominalVersionedChildren232.rawSites (stagePlan p hi) = _
    rw [p.raw_eq,GeneralNominalVersionedChildren232.rawSites,stage_emits,sites,List.map_append]
  edges_eq := by
    change p.state.core.erased.current.edges ++ GeneralNominalVersionedChildren232.edges (stagePlan p hi) = _
    rw [p.edges_eq,edge_single]
    rfl
  old_keys := by
    intro key member
    rcases List.mem_append.mp member with prior|recent
    · obtain ⟨i,before,owner⟩ := p.old_keys key prior
      exact ⟨i,by omega,owner⟩
    · exact ⟨k,Nat.lt_succ_self _,GeneralRebaseDisplayChildFresh276.keys_root recent⟩
  atom_support := by
    intro a occurs
    rw [List.flatMap_append] at occurs
    exact (List.mem_append.mp occurs).elim (p.atom_support a) (stage_supported p hi a)
  focus_generated := by
    exact GeneralNominalVersionedInstallProperties232.children_generated
      (plan := stagePlan p hi) p.focus_generated
      ((stage_children p hi).symm ▸ List.mem_singleton_self _)
  packets_display := by
    intro prior member
    rcases List.mem_cons.mp member with rfl|previous
    · rfl
    · exact p.packets_display prior previous
  legacy_empty := p.legacy_empty
  models := fun m => (new_models p hi m).trans (p.models m)
  reached := by
    obtain ⟨seed,label,prev⟩ := p.reached
    exact ⟨seed,label,.tail prev (actual p hi)⟩

def run (n : Nat) (k : Nat) (bound : k ≤ n+1) : Phase n k :=
  match k with
  | 0 => start n
  | k+1 => advance (run n k (by omega)) (by omega)

theorem phase_step (n k : Nat) (hi : k ≤ n) :
    (boundary roles).Step registry displayRoot (run n k (by omega)).state (run n (k+1) (by omega)).state :=
  actual (run n k (by omega)) hi

theorem path (n k : Nat) (bound : k ≤ n+1) :
    B4Target.Steps ((boundary roles).Step registry displayRoot) (initial n) (run n k bound).state := by
  induction k with
  | zero => exact .refl
  | succ k ih => exact .tail (ih (by omega)) (phase_step n k (by omega))

theorem terminal_reached (n : Nat) : ∃ s,
    B4Target.Steps ((boundary roles).Step registry displayRoot) (initial n) s ∧
    B4TargetV8.Reachable (boundary roles) registry displayRoot s ∧
    GeneralNominalSaturationState.Generated s.core.erased.current displayRoot (focus n (n+1)) ∧
    (∀ m, Models s m ↔ Models (initial n) m) ∧
    s.core.erased.current.edges = edges n (n+1) := by
  let p := run n (n+1) (Nat.le_refl _)
  exact ⟨p.state,path n (n+1) (Nat.le_refl _),p.reached,p.focus_generated,p.models,p.edges_eq⟩

end Yulang.GeneralObservedLadderAdvance301
