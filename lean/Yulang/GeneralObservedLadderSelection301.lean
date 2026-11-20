import Yulang.GeneralObservedLadderSemantics301
import Yulang.GeneralRebaseCompiledDisplay277

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralObservedLadderSelection301
open GeneralObservedLadderSource301 (snapshot nominal_at endpoint)
open GeneralObservedLadderInitial301 (context formed support)
open GeneralObservedLadderReport301
open GeneralObservedLadderPlan301
open GeneralObservedLadderSemantics301 (holds)
open GeneralDeclarationExamples (roles display display_checked)
open GeneralNominalExamples (intDisplay)
open GeneralNominalOutputGrowth (finiteModel)
open GeneralNominalVersionedCandidates231
open GeneralNominalVersionedFrame231 (children)
open GeneralNominalRecursiveCandidates (arguments report Metadata)

theorem metadata (n : Nat) : Metadata compiled (context n) :=
  ⟨rfl,(formed n).metadata.2⟩

theorem linked (n i id : Nat) (hi : i ≤ n+1) :
    GeneralNominalState.Linked (snapshot n) (inputs (occurrence i id)).demand := by
  constructor
  · intro _
    have seen := GeneralNominalAllocationSupport.slot_source (snapshot n) (pos n i hi)
    exact ⟨seen,seen⟩
  · intro _ impossible; cases impossible

theorem known (n i id : Nat) (hi : i ≤ n+1) :
    ¬ GeneralNominalState.RootPending (snapshot n) (inputs (occurrence i id)).demand := by
  rintro ⟨j,absent⟩
  apply absent
  refine ⟨pos n i hi,rfl,?_⟩
  by_cases inside : i ≤ n
  · exact .inr ⟨_,nominal_at n i inside⟩
  · left
    have equal : i = n+1 := by omega
    subst i
    change (snapshot n).view.graph (endpoint n) ≠ .unresolved
    change ((snapshot n).view.heads (endpoint n)).node ≠ .unresolved
    rw [GeneralObservedLadderSource301.scalar_at]
    intro impossible
    cases impossible

theorem fresh (n id : Nat) (bs) : GeneralNominalVersionedAllocation231.Fresh (snapshot n) compiled id bs := by
  intro key _ overlaps
  have high := GeneralNominalIdentities.source_above_seed (snapshot n).seed key
  have low := support n _ overlaps
  exact False.elim (Nat.not_lt_of_ge low high)

theorem located (n i id : Nat) (hi : i ≤ n+1) :
    arguments (context n) (inputs (occurrence i id)) = some [point n i hi] := by
  change GeneralCandidateBoundaryParts.locate (snapshot n).base (List.ofFn (fun _ : Fin 1 => (i,i))) = _
  have lookup : GeneralDictionaryBinderLocations.sourceSlot (snapshot n).base i = some (pos n i hi) :=
    (GeneralDictionaryBinderLocations.sourceSlot_exact _ _ _).mpr rfl
  simp [List.ofFn_succ,GeneralCandidateBoundaryParts.locate,lookup]

theorem prepared (n i id : Nat) (hi : i ≤ n) : Prepared compiled (context n) (occurrence i id) display := by
  refine ⟨metadata n,linked n i id (by omega),[point n i (by omega)],located n i id (by omega),fresh n id _,?_,
    finiteModel n,?_⟩
  · exact (exact_at n i (by omega)).1.mpr hi
  · exact GeneralNominalVersionedPlans231.head_models (holds n i id hi _ (GeneralObservedLadderSource301.model_exists n))

theorem failed_int (n i id : Nat) (hi : i ≤ n) :
    Failed compiled (context n) (occurrence i id) intDisplay := by
  refine ⟨metadata n,[point n i (by omega)],located n i id (by omega),fresh n id _,?_,?_,.inl ?_⟩
  all_goals rw [list_as_int n i hi]
  · intro impossible; cases impossible

theorem int_not_prepared (n i id : Nat) (hi : i ≤ n) :
    ¬ Prepared compiled (context n) (occurrence i id) intDisplay := by
  rintro ⟨_,_,bs,matching,_,done,_⟩
  cases Option.some.inj (matching.symm.trans (located n i id (by omega)))
  have last := (exact_at n i (by omega)).2.mp done
  omega

theorem child_occurrence (n i id : Nat) (hi : i ≤ n) :
    (child n i id hi).occurrence = occurrence (i+1) (child n i id hi).occurrence.identity := by
  apply congrArg (fun args : Fin 1 → Nat × Nat => (⟨(child n i id hi).occurrence.identity,⟨0,args,[],by intro _ impossible; cases impossible⟩⟩ : GeneralSourceDictionaries.Occurrence roles))
  funext k
  exact child_args n i id hi k

theorem one_child (n i id : Nat) (hi : i ≤ n) :
    children (packet n i id hi) = [(child n i id hi).occurrence] := by
  rw [← GeneralNominalVersionedChildren232.emitted_occurrences (plan n i id hi),emitted_sites]
  rfl

theorem unique (n i id : Nat) (hi : i ≤ n) :
    Unique compiled (context n) (occurrence i id) 1 [(child n i id hi).occurrence] := by
  have selected : Survivor compiled (context n) (occurrence i id) 1 [(child n i id hi).occurrence] :=
    ⟨known n i id (by omega),display,List.mem_cons_of_mem _ (List.mem_cons_self ..),display_checked,rfl,rfl,
      [point n i (by omega)],located n i id (by omega),prepared n i id hi,(one_child n i id hi).symm⟩
  refine ⟨selected,?_⟩
  intro k kids other
  have copy := other
  obtain ⟨_,d,visible,_,key,role,_,_,ready,_⟩ := other
  rcases GeneralRebaseCompiledDisplay277.compiled_members visible role with rfl|rfl
  · exact False.elim (int_not_prepared n i id hi ready)
  · subst k
    exact ⟨rfl,survivor_children_functional GeneralRebaseCompiledDisplay277.compiled_checked copy selected⟩

end Yulang.GeneralObservedLadderSelection301
