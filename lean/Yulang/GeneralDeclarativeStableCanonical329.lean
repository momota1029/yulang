import Yulang.GeneralDeclarativeStableTies329

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStableCanonical329
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeStableTies329 (Use pairOf rows model_batch)
open GeneralDeclarativeOpaqueCapture328 (choose)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_symm eqv_trans)

def Representative (selected : Nat → Capture) (spans : List (Nat × Capture)) : Prop :=
  ∀ key ∈ spans.map Prod.fst, ∃ a, (key,a) ∈ spans ∧ a.center = (selected key).center

def EqualUses (m : Assignment) (spans : List (Nat × Capture)) : Prop :=
  ∀ key a b, (key,a) ∈ spans → (key,b) ∈ spans → Equivalent (m a.center).1 (m b.center).1

theorem found {spans : List (Nat × Capture)} (h : key ∈ spans.map Prod.fst) :
    (key,choose base key spans) ∈ spans := by
  induction spans with
  | nil => cases h
  | cons item rest ih =>
    obtain ⟨k,a⟩ := item
    by_cases same : key = k
    · subst k
      simpa only [choose,ite_true] using
        (show (key,a) ∈ (key,a) :: rest from List.mem_cons_self)
    · simp only [choose,same,ite_false]
      exact List.mem_cons_of_mem _ (ih ((List.mem_cons.mp h).resolve_left same))

theorem uses_existing (spans : List (Nat × Capture)) (base) :
    Representative (fun key => choose base key spans) spans :=
  fun _key h => ⟨_,found h,rfl⟩

/-- No true equality is imposed on an unrelated old logical name.
A representative from the actual occurrences makes the finite star
equivalent to the symmetric source sharing condition, independently of
which occurrence is used as representative. -/
theorem exact (s : State) (selected : Nat → Capture) (spans : List (Nat × Capture))
    (actual : Representative selected spans) (m) :
    Models (appendFacts s (rows selected (spans.map pairOf))) m ↔ Models s m ∧ EqualUses m spans := by
  rw [model_batch]
  refine and_congr_right fun _ => ⟨?_,?_⟩
  · intro equal key a b first last
    exact eqv_trans (equal (key,a.center) (List.mem_map.mpr ⟨(key,a),first,rfl⟩))
      (eqv_symm (equal (key,b.center) (List.mem_map.mpr ⟨(key,b),last,rfl⟩)))
  · intro shared use actualUse
    obtain ⟨⟨key,a⟩,present,rfl⟩ := List.mem_map.mp actualUse
    obtain ⟨b,witness,linked⟩ := actual key (List.mem_map.mpr ⟨_,present,rfl⟩)
    change Equivalent (m a.center).1 (m (selected key).center).1
    rw [← linked]
    exact shared key a b present witness

theorem model_independent {s : State} (a b : Nat → Capture)
    (repA : Representative a spans) (repB : Representative b spans) (m) :
    Models (appendFacts s (rows a (spans.map pairOf))) m ↔
      Models (appendFacts s (rows b (spans.map pairOf))) m := by
  rw [exact s a spans repA,exact s b spans repB]

theorem permutation {s : State} (a b : Nat → Capture)
    (repA : Representative a spans) (repB : Representative b others)
    (same : spans.Perm others) (m) :
    Models (appendFacts s (rows a (spans.map pairOf))) m ↔
      Models (appendFacts s (rows b (others.map pairOf))) m := by
  rw [exact s a spans repA,exact s b others repB]
  refine and_congr_right fun _ => ⟨?_,?_⟩
  · intro all k l r left right
    exact all _ _ _ (same.mem_iff.mpr left) (same.mem_iff.mpr right)
  · intro all k l r left right
    exact all _ _ _ (same.mem_iff.mp left) (same.mem_iff.mp right)

/-- Actual source identities may have more than one spelling, but
ordinary ties are not needed when no binder repeats. -/
theorem distinct_redundant {s : State} (nodup : (spans.map Prod.fst).Nodup)
    (actual : Representative selected spans) (m) :
    Models (appendFacts s (rows selected (spans.map pairOf))) m ↔ Models s m := by
  rw [exact s selected spans actual]
  refine ⟨And.left,fun old => ⟨old,?_⟩⟩
  intro key a b first last
  have equal := (GeneralDeclarativeOpaqueCapture328.choice_exact (fallback := selected) nodup first).symm.trans
    (GeneralDeclarativeOpaqueCapture328.choice_exact (fallback := selected) nodup last)
  cases equal
  exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_refl _

end Yulang.GeneralDeclarativeStableCanonical329
