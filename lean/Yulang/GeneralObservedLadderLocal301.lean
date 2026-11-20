import Yulang.GeneralObservedLadderAvailability301
import Yulang.GeneralNominalVersionedDiagnosticLaws232

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 9000000
namespace Yulang.GeneralObservedLadderLocal301
open GeneralObservedLadderInitial301 (context)
open GeneralObservedLadderPlan301 (compiled)
open GeneralObservedLadderReport301 (point list_as_int int_as_list)
open GeneralObservedLadderRoute301
open GeneralObservedLadderLedger301
open GeneralObservedLadderEvidence301
open GeneralObservedLadderStage301 (current_requests model)
open GeneralObservedLadderEnabled301 (separates)
open GeneralDeclarationExamples (roles display display_checked)
open GeneralNominalExamples (registry intDisplay int_display_checked)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedCandidates231
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedPlans231 (Holds)
open GeneralNominalCenters (Plan)
open GeneralNominalOutputGrowth (finiteModel)
open GeneralNominalIdentities (source source_identity source_above_seed)
open GeneralDeclarations (Declaration)

theorem arbitrary_fresh (p : Phase n k) (id : Nat) (bs) :
    GeneralNominalVersionedAllocation231.Fresh (env p).state compiled id bs := by
  intro key _ collision
  rcases support p _ collision with low|old
  · exact False.elim (Nat.not_lt_of_ge low (source_above_seed (n+1) key))
  · obtain ⟨other,inKeys,eq⟩ := List.mem_map.mp old
    have sameKey := (source_identity (n+1) other key).mp eq
    exact sameKey ▸ inKeys

theorem administrative (n i : Nat) (bound : i ≤ n+1) :
    GeneralNominalVersionedDiagnostic232.AdministrativeReady (final n).state (focus n i) := by
  let p := final n
  constructor
  · refine ⟨site n i,?_,rfl⟩
    rw [p.centers_eq]
    exact (sites_exact ..).mpr ⟨i,bound,rfl⟩
  · intro a first id b second same
    rw [p.centers_eq] at first second
    rw [unique_row n (n+1) i a first id] at same ⊢
    obtain ⟨j,le,rfl⟩ := (sites_exact ..).mp second
    have eq := separates p bound le same
    subst j
    exact .refl _

theorem failed_int (n i : Nat) (hi : i ≤ n) :
    Failed compiled (final n).state.core.erased.current.context (focus n i) intDisplay := by
  let p := final n
  rw [p.context_eq]
  refine ⟨GeneralObservedLadderStage301.metadata p,[point n i (by omega)],
    GeneralObservedLadderSelection301.located n i (invocation n i) (by omega),
    arbitrary_fresh p _ _,?_,?_,.inl ?_⟩
  all_goals rw [GeneralDictionaryOrdinaryTransport.candidate_report_extended,list_as_int n i hi]
  all_goals try rfl
  intro bad
  cases bad

theorem safe (n i : Nat) (bound : i ≤ n+1) (d : Declaration)
    (right : Prepared compiled (final n).state.core.erased.current.context (focus n i) d)
    (checked : ∀ e ∈ compiled.declarations, e.role = (focus n i).demand.role →
      e = d ∨ Failed compiled (final n).state.core.erased.current.context (focus n i) e) :
    B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) compiled (final n).state (focus n i) := by
  let p := final n
  have held := model p
  have semantic := GeneralObservedLadderSafety301.semantic n held
  have raw : ∀ s, ¬ GeneralNominalCycleK2.RecursAt p.state.core.erased.current.context.state s := by
    have transfer : ∀ s, ¬ GeneralNominalCycleK2.RecursAt (env p).state s := by
      have valid := held.1.1
      rw [p.context_eq] at valid
      exact GeneralObservedLadderSafety301.raw_acyclic n _ rfl valid
    rw [p.context_eq]
    exact transfer
  refine ⟨?_,?_,?_,?_⟩
  · change ¬ GeneralNominalState.RootPending p.state.core.erased.current.context.state (focus n i).demand
    rw [p.context_eq]
    exact GeneralObservedLadderSelection301.known n i (invocation n i) bound
  · rintro (rawCycle | (⟨i,cyclic⟩ | ⟨s,_,_,i,cyclic⟩))
    · obtain ⟨_,_,_,slot,_,cyclic⟩ := rawCycle
      exact raw slot cyclic
    · exact semantic _ cyclic
    · exact semantic _ cyclic
  · rintro (rawCycle | ⟨plan,_,entry,_,cyclic⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cyclic⟩ := rawCycle
      exact raw visited.1 cyclic
    · exact semantic _ cyclic
  · rintro (⟨_,e,visible,role,notFailed,notPrepared⟩ | pending)
    rcases checked e visible role with rfl|bad
    · exact notPrepared right
    · exact notFailed bad
    · exact pending (administrative n i bound)

theorem unique_list (n i : Nat) (hi : i ≤ n) :
    Unique compiled (final n).state.core.erased.current.context (focus n i) 1 [focus n (i+1)] := by
  let p := final n
  have owned := keys_installed n (n+1) (Nat.le_refl _) i (by omega)
  have belongs := replay_prepared p i hi owned
  rw [p.context_eq]
  have chosen : Survivor compiled (env p) (focus n i) 1 [focus n (i+1)] :=
    ⟨GeneralObservedLadderSelection301.known n i (invocation n i) (by omega),display,
      List.mem_cons_of_mem _ (List.mem_cons_self ..),display_checked,rfl,rfl,[point n i (by omega)],
      GeneralObservedLadderSelection301.located n i (invocation n i) (by omega),
      belongs,(replay_children p i hi).symm⟩
  refine ⟨chosen,?_⟩
  intro key children other
  have kept := other
  obtain ⟨_,d,visible,_,eq,role,_,_,good,_⟩ := other
  rcases GeneralRebaseCompiledDisplay277.compiled_members visible role with rfl|rfl
  · have denies := GeneralObservedLadderOnlyInstall301.wrong_int_at p i hi
    rw [p.context_eq] at denies
    exact False.elim (denies good)
  · subst key
    exact ⟨rfl,survivor_children_functional GeneralRebaseCompiledDisplay277.compiled_checked kept chosen⟩

theorem not_merged (n i : Nat) :
    ¬ GeneralNominalVersionedMergedConflict232.MergedOutputConflict (final n).state (focus n i) := by
  let p := final n
  apply GeneralNominalVersionedMergedConflict232.models_exclude_conflict (model p)
  · intro target _ out taken
    rw [current_requests p] at taken
    cases taken
  · intro out taken
    rw [current_requests p] at taken
    cases taken

theorem local_of (n i : Nat) {key kids} (q : Plan roles)
    (frame : Frame compiled (final n).state.core (focus n i) key q)
    (holds : Holds q (finiteModel n))
    (safeHere : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) compiled
      (final n).state (focus n i))
    (only : Unique compiled (final n).state.core.erased.current.context (focus n i) key kids) :
    B4TargetV8.Local (boundary roles) registry (final n).state (focus n i) (.selected key kids) := by
  let p := final n
  have ready : GeneralNominalCenteredHeadMatEffects.Ready p.state.core (focus n i) q := by
    intro out taken
    rw [current_requests p] at taken
    cases taken
  apply GeneralNominalVersionedMixedSourceBoundary234.local_iff.mpr
  apply GeneralNominalVersionedMixedBoundary234.local_iff.mpr
  exact GeneralNominalVersionedDiagnosticLaws232.selected_of_model safeHere only (model p) frame ready holds
    (GeneralRebaseDisplayFrame276.classes_empty (current_requests p _) q _) (not_merged n i)

theorem list_local (n i : Nat) (hi : i ≤ n) :
    B4TargetV8.Local (boundary roles) registry (final n).state (focus n i) (.selected 1 [focus n (i+1)]) := by
  let p := final n
  let q := replay p i hi
  have f : Frame compiled p.state.core (focus n i) 1 q :=
    replay_frame n (n+1) (Nat.le_refl _) i (by omega)
  refine local_of n i q f (replay_held p i hi _ (model p)) ?_ (unique_list n i hi)
  exact safe n i (by omega) display f.prepared (by
    intro d visible role
    rcases GeneralRebaseCompiledDisplay277.compiled_members visible role with rfl|rfl
    · exact .inr (failed_int n i hi)
    · exact .inl rfl)

theorem leaf_local (n : Nat) :
    B4TargetV8.Local (boundary roles) registry (final n).state (focus n (n+1)) (.selected 3 []) := by
  let p := final n
  let q := GeneralObservedLadderLeaf301.terminalPlan p
  have f : Frame compiled p.state.core (focus n (n+1)) 3 q :=
    GeneralObservedLadderLeaf301.frame p
  have only : Unique compiled p.state.core.erased.current.context (focus n (n+1)) 3 [] := by
    rw [p.context_eq]
    exact GeneralObservedLadderLeaf301.unique p
  refine local_of n (n+1) q f (GeneralObservedLadderLeaf301.holds p _ (model p)) ?_ only
  exact safe n (n+1) (Nat.le_refl _) intDisplay f.prepared (by
    intro d visible role
    rcases GeneralRebaseCompiledDisplay277.compiled_members visible role with rfl|rfl
    · exact .inl rfl
    · right
      rw [p.context_eq]
      exact GeneralObservedLadderStage301.wrong_list p)

end Yulang.GeneralObservedLadderLocal301
