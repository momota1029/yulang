import Yulang.GeneralDeferredLadderFirstPromotion302

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 8000000
namespace Yulang.GeneralDeferredLadderAfterVariants302
open GeneralDeferredLadderLedger302 (Phase)
open GeneralDeferredLadderAdvance302 (run)
open GeneralDeferredLadderBranch302 (variant successor padding models_preserved actual)
open GeneralDeferredLadderRefresh302 (promotedPhase promotedContext)
open GeneralDeferredLadderCompiler302 (certified_promotion_table)
open GeneralObservedLadderInitial301 (context)
open GeneralObservedLadderRoute301 (focus invocation)
open GeneralObservedLadderAdvance301 (advance)
open GeneralNominalIdentities (source)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalExamples (registry displayRoot)
open GeneralDeclarationExamples (roles)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedInstallation231 (allocated)
open GeneralNominalSaturationState (Generated Alias)
open GeneralObservedLadderBudget301 (Counted)
open B4Target (Steps)

theorem generated (p : Phase n k) (ctx : GeneralNominalCandidates.Context)
    {root endpoint : GeneralSourceDictionaries.Occurrence roles}
    (old : Generated p.state.core.erased.current root endpoint) :
    Generated (refresh p.state ctx).core.erased.current root endpoint := by
  have same {a b} (rel : Alias p.state.core.erased.current a b) : Alias (refresh p.state ctx).core.erased.current a b := by
    induction rel with
    | refl => exact .refl _
    | edge yes => exact .edge yes
    | symm _ ih => exact .symm ih
    | trans _ _ one two => exact .trans one two
  induction old with
  | root => exact .root
  | child _ edge ih => exact .child ih edge
  | alias _ one two link ih => exact .alias ih one two (same link)

theorem variant_context (p : Phase n k) (count : Nat) :
    (successor p count).core.erased.current.context =
      GeneralDictionaryOrdinaryTransport.extend (context n) (p.keys.map (source (n+1)))
        ((promotedPhase p).extraAtoms ++ padding n count) p.keys := by
  change GeneralDictionaryOrdinaryTransport.extend (promotedContext p) [] (padding n count) [] = _
  simp [GeneralDeferredLadderRefresh302.promotedContext,GeneralDictionaryOrdinaryTransport.extend,
    GeneralDictionaryOrdinaryTransport.extendState,List.append_assoc,GeneralDeferredLadderRefresh302.promotedPhase]

def variantPhase (p : Phase n k) (count : Nat) : GeneralObservedLadderLedger301.Phase n k where
  state := successor p count
  keys := p.keys
  extraAtoms := (promotedPhase p).extraAtoms ++ padding n count
  context_eq := variant_context p count
  centers_eq := p.centers_eq
  raw_eq := p.raw_eq
  edges_eq := p.edges_eq
  old_keys := p.old_keys
  atom_support := by
    intro id member
    rw [List.flatMap_append] at member
    rcases List.mem_append.mp member with old|added
    · exact (promotedPhase p).atom_support id old
    · obtain ⟨atom,rep,inAtom⟩ := List.mem_flatMap.mp added
      cases List.eq_of_mem_replicate rep
      exact Nat.le_of_eq (by simpa [GeneralNominalState.atomSources,GeneralNominalState.typeSources] using inAtom)
  focus_generated := generated p _ p.focus_generated
  packets_display := p.packets_display
  legacy_empty := p.legacy_empty
  models := fun m => (models_preserved p count m).trans (GeneralDeferredLadderNoAdmin302.same_observed_models p m)
  reached := by
    obtain ⟨s,ini,path⟩ := p.reached
    exact ⟨s,ini,.tail path (actual p count)⟩

def Owns (p : GeneralObservedLadderLedger301.Phase n k) : Prop :=
  ∀ i < k, GeneralNominalVersionedAllocation231.keys GeneralObservedLadderPlan301.compiled
    (invocation n i) [(0,(i+1,i+1))] ⊆ p.keys

theorem variant_owns (n k : Nat) (cap : k ≤ n+1) (count : Nat) :
    Owns (variantPhase (run n k cap) count) :=
  GeneralDeferredLadderFrames302.keys_installed n k cap

theorem owns_advance (p : GeneralObservedLadderLedger301.Phase n k) (old : Owns p) (hi : k ≤ n) :
    Owns (advance p hi) := by
  intro i hi' key seen
  change key ∈ p.keys ++ allocated (GeneralObservedLadderLedger301.stagePlan p hi).packet
  by_cases was : i < k
  · exact List.mem_append_left _ (old i was seen)
  · have row : i = k := by omega
    subst i
    apply List.mem_append_right
    unfold allocated
    rw [GeneralObservedLadderLedger301.stage_bindings p hi]
    exact seen

structure OwnedPhase (n k : Nat) extends GeneralObservedLadderLedger301.Phase n k where
  all_owned : Owns toPhase

def variantOwned (n k : Nat) (cap : k ≤ n+1) (padding : Nat) : OwnedPhase n k :=
  ⟨variantPhase (run n k cap) padding,variant_owns n k cap padding⟩

def step (p : OwnedPhase n k) (hi : k ≤ n) : OwnedPhase n (k+1) :=
  ⟨advance p.toPhase hi,owns_advance p.toPhase p.all_owned hi⟩

def advanceFrom (p : OwnedPhase n k) (count : Nat) (fit : k+count ≤ n+1) : OwnedPhase n (k+count) :=
  match count with
  | 0 => p
  | d+1 =>
    have b : k+d+1 ≤ n+1 := fit
    have ok : k+d ≤ n := by omega
    step (advanceFrom p d (Nat.le_succ_of_le ok)) ok

theorem path_count (p : OwnedPhase n k) (count : Nat) (fit : k+count ≤ n+1) :
    Counted count p.state (advanceFrom p count fit).state := by
  induction count with
  | zero => exact .refl _
  | succ t ih =>
    have b : k+t+1 ≤ n+1 := fit
    exact .tail (ih (by omega))
      (GeneralObservedLadderEnabled301.actual (advanceFrom p t (by omega)).toPhase (show k+t ≤ n by omega))

theorem raw_after (p : OwnedPhase n k) (count : Nat) (fit : k+count ≤ n+1) :
    Steps ((boundary roles).Step registry displayRoot) p.state (advanceFrom p count fit).state :=
  GeneralObservedLadderBudget301.erase (path_count p count fit)

end Yulang.GeneralDeferredLadderAfterVariants302
