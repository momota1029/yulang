import Yulang.GeneralObservedLadderRoot301

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralObservedLadderRoute301
open GeneralObservedLadderSource301 (snapshot)
open GeneralObservedLadderPlan301 (occurrence child plan)
open GeneralObservedLadderPlan301
open GeneralObservedLadderSelection301 (child_occurrence)
open GeneralNominalIdentities (source source_above_invocation)
open GeneralDeclarationExamples (roles displayChild display_checked)
open GeneralNominalCenters (Site rootSite point_center)
open GeneralNominalVersionedFrame231 (childSite)
open GeneralSourceDictionaries (Occurrence)

def invocation (n : Nat) : Nat → Nat
  | 0 => 100
  | k+1 => source (n+1) (invocation n k,1,6,10,0)

theorem climbs (n k : Nat) : invocation n k < invocation n (k+1) :=
  source_above_invocation (n+1) (invocation n k,1,6,10,0)

theorem strictly_monotone (n : Nat) : ∀ {i j}, i < j → invocation n i < invocation n j := by
  intro i j
  induction j with
  | zero => omega
  | succ j ih =>
    intro lt
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ lt) with earlier | equal
    · exact Nat.lt_trans (ih earlier) (climbs n j)
    · subst i
      exact climbs n j

theorem injective (n : Nat) : Function.Injective (invocation n) := by
  intro i j eq
  rcases Nat.lt_trichotomy i j with less|same|more
  · exact False.elim (Nat.ne_of_lt (strictly_monotone n less) eq)
  · exact same
  · exact False.elim (Nat.ne_of_lt (strictly_monotone n more) eq.symm)

abbrev focus (n i : Nat) : Occurrence roles := occurrence i (invocation n i)

abbrev site (n i : Nat) : Site roles := rootSite (snapshot n).seed (focus n i)

theorem child_id (n i : Nat) (hi : i ≤ n) :
    (child n i (invocation n i) hi).occurrence.identity = invocation n (i+1) := rfl

theorem child_site (n i : Nat) (hi : i ≤ n) :
    child n i (invocation n i) hi = site n (i+1) := by
  have eq : (child n i (invocation n i) hi).occurrence = focus n (i+1) :=
    (child_occurrence n i (invocation n i) hi).trans (by rw [child_id n i hi])
  have data := child_center n i (invocation n i) hi
  generalize h : child n i (invocation n i) hi = c at eq data ⊢
  rcases c with ⟨root,center⟩
  change root = focus n (i+1) at eq
  subst root
  change (⟨focus n (i+1),center⟩ : Site roles) = ⟨focus n (i+1),(site n (i+1)).center⟩
  congr 1
  funext k
  exact (data k).trans (point_center (snapshot n).seed (focus n (i+1)) k rfl).symm

theorem observed (n i : Nat) : (site n i).observed = GeneralNominalDemandMerging.pointSite (focus n i) := by
  unfold GeneralNominalDemandMerging.pointSite GeneralNominalCenters.Site.observed
  congr 1
  congr 1
  funext k
  rw [point_center _ _ _ rfl]
  change some (GeneralNominalRecursiveInspection.Origin.source i) = (if i = i then some (.source i) else none)
  simp

theorem inputs (n i : Nat) : (site n i).observed.inputs = [some (.source i)] := by
  change List.ofFn (fun k : Fin 1 => some (GeneralNominalRecursiveInspection.Origin.source ((site n i).center k))) = _
  simp only [List.ofFn_succ,List.ofFn_zero,List.cons.injEq,Option.some.injEq,GeneralNominalRecursiveInspection.Origin.source.injEq,and_true]
  exact point_center (snapshot n).seed (focus n i) _ rfl

def sites (n : Nat) : Nat → List (Site roles)
  | 0 => [site n 0]
  | k+1 => sites n k ++ [site n (k+1)]

theorem sites_exact (n k : Nat) (s : Site roles) :
    s ∈ sites n k ↔ ∃ i, i ≤ k ∧ s = site n i := by
  induction k with
  | zero =>
    constructor
    · intro found
      exact ⟨0,Nat.le_refl _,List.mem_singleton.mp found⟩
    · rintro ⟨i,le,eq⟩
      have z : i = 0 := by omega
      subst i
      exact List.mem_singleton.mpr eq
  | succ k ih =>
    rw [sites,List.mem_append,ih,List.mem_singleton]
    constructor
    · rintro (⟨i,le,eq⟩|eq)
      · exact ⟨i,by omega,eq⟩
      · exact ⟨k+1,Nat.le_refl _,eq⟩
    · rintro ⟨i,le,eq⟩
      by_cases before : i ≤ k
      · exact .inl ⟨i,before,eq⟩
      · have same : i = k+1 := by omega
        subst i
        exact .inr eq

theorem unique_row (n k i : Nat) (s : Site roles)
    (member : s ∈ sites n k) (matchId : s.occurrence = focus n i) : s = site n i := by
  obtain ⟨j,_,rfl⟩ := (sites_exact n k s).mp member
  have same : invocation n j = invocation n i := congrArg (fun x => x.identity) matchId
  cases injective n same
  rfl

def edges (n : Nat) : Nat → List (Occurrence roles × Occurrence roles)
  | 0 => []
  | k+1 => edges n k ++ [(focus n k,focus n (k+1))]

theorem edge_exact (n k : Nat) (edge : Occurrence roles × Occurrence roles) :
    edge ∈ edges n k ↔ ∃ i, i < k ∧ edge = (focus n i,focus n (i+1)) := by
  induction k with
  | zero => simp [edges]
  | succ k ih =>
    rw [edges,List.mem_append,ih,List.mem_singleton]
    constructor
    · rintro (⟨i,le,eq⟩|eq)
      · exact ⟨i,by omega,eq⟩
      · exact ⟨k,Nat.lt_succ_self _,eq⟩
    · rintro ⟨i,le,eq⟩
      by_cases before : i < k
      · exact .inl ⟨i,before,eq⟩
      · have same : i = k := by omega
        subst i
        exact .inr eq

end Yulang.GeneralObservedLadderRoute301
