import Yulang.GeneralObservedLadderSource301
import Yulang.GeneralNominalGroundAccessibility
import Yulang.GeneralNominalVersionedMixedSourceBoundary234
import Yulang.GeneralNominalCenteredHeadWFFixtures

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralObservedLadderInitial301
open GeneralObservedLadderSource301
open GeneralDeclarationExamples (roles constructors)
open GeneralNominalExamples (registry displayRoot interpretation)
open GeneralDeclarationPatterns (Pattern normalize normalizeArgs)
open GeneralNominalOriginTerms
open GeneralNominalRecursiveInspection
open GeneralNominalCompoundReadback
open GeneralNominalGroundAccessibility (ClosedTerm GroundRoots)
open GeneralNominalFiniteMeaning (denote)
open GeneralNominalOutputGrowth (tower finiteModel)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedJournal232 (Models)
open CommonNominalFullCarrier

abbrev context (n : Nat) : GeneralNominalCandidates.Context := ⟨snapshot n,interpretation⟩

def pattern : Nat → Pattern
  | 0 => .app 2 []
  | k+1 => .app 0 [pattern k]

def term : Nat → Expr Nat
  | 0 => .node (.scalar .int) Fin.elim0
  | k+1 => .node (.nominal 0 1) (fun _ => term k)

theorem translated (k : Nat) :
    GeneralNominalInspection.translate constructors interpretation (normalize (pattern k)) = quote (term k) := by
  induction k with
  | zero => simp [pattern,normalize,normalizeArgs,GeneralNominalInspection.translate,interpretation,term,quote]
  | succ k ih =>
    simpa [pattern,normalize,normalizeArgs,GeneralNominalInspection.translate,interpretation,constructors,
      term,quote,List.ofFn_succ,arity] using congrArg (fun x => GeneralNominalInspection.Query.nominal 0 [x]) ih

theorem leafless (k : Nat) : (term k).leaves = [] := by
  induction k with
  | zero => rfl
  | succ k ih => simp [term,Expr.leaves,List.ofFn_succ,arity,ih]

theorem canonical (k : Nat) : GeneralNominalReadbackFunctionality.Canonical (term k) := by
  induction k with
  | zero => exact ⟨trivial,fun i => Fin.elim0 i⟩
  | succ k ih => exact ⟨trivial,fun _ => ih⟩

theorem denotes (k : Nat) : denote (fun _ => .bottom) (term k) = tower k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [term,denote,tower,GeneralNominalFiniteMeaning.build,List.ofFn_succ,ih]

abbrev labels (n : Nat) : List Pattern := [pattern (n+1)]
abbrev initial (n : Nat) := GeneralNominalVersionedJournal232.initial (context n) displayRoot

theorem support (n i : Nat) (member : i ∈ GeneralNominalState.sources (snapshot n)) :
    i ≤ n+1 := by
  change i ∈ List.ofFn (Fin.val : Fin (n+2) → Nat) ++ List.ofFn (Fin.val : Fin (n+2) → Nat) ++ [] ++ [] at member
  simp only [List.append_nil,List.mem_append,or_self] at member
  obtain ⟨slot,same⟩ := List.mem_ofFn.mp member
  exact same ▸ Nat.le_of_lt_succ slot.isLt

theorem formed (n : Nat) : GeneralNominalSourceFormation.InitialSource registry (context n) displayRoot := by
  refine ⟨rfl,⟨rfl,GeneralDictionarySupportRecursiveExample.initial_source.metadata.2⟩,?_,
    (by intro _ _ _; exact subtype_refl _),support n,rfl⟩
  constructor
  · intro index
    have present := GeneralNominalAllocationSupport.slot_source (snapshot n)
      (⟨0,by change 0 < n+2; omega⟩ : Fin (snapshot n).base.slots)
    exact ⟨present,present⟩
  · intro _ impossible; cases impossible

theorem ground (n : Nat) : GroundRoots (context n) displayRoot (labels n) := by
  refine ⟨rfl,?_⟩
  intro index
  have zero : index.val = 0 := by have bounded := index.isLt; change index.val < 1 at bounded; omega
  simp only [zero]
  refine ⟨term (n+1),⟨translated _,leafless _,canonical _⟩,?_⟩
  intro m valid
  change Equivalent (m 0).1 (denote (fun _ => .bottom) (term (n+1)))
  rw [denotes]
  simpa only [Nat.sub_self] using slot_model n m valid (n+1) (Nat.le_refl _)

theorem actual_initial (n : Nat) : (boundary roles).Initial registry displayRoot (initial n) := by
  refine ⟨_,⟨context n,labels n,formed n,(fun _ => rfl),ground n,
    GeneralNominalCenteredHeadWFFixtures.display_coverage,rfl⟩,rfl⟩

theorem models (n : Nat) : Models (initial n) (finiteModel n) := by
  apply (GeneralNominalVersionedJournal232.initial_models ..).mpr
  exact ⟨model_exists n,GeneralNominalCenters.point_root_holds _ _ (fun _ => rfl) _⟩

theorem reached (n : Nat) :
    B4TargetV8.Reachable (boundary roles) registry displayRoot (initial n) ∧ Models (initial n) (finiteModel n) :=
  ⟨⟨initial n,actual_initial n,.refl⟩,models n⟩

end Yulang.GeneralObservedLadderInitial301
