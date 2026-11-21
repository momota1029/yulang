import Yulang.GeneralLadderCompiledPresentation306

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralLadderCompiledMinimal306
open GeneralDeferredLadderControl304 (Control view successors successors_exact Edge remaining edge_consumes_one)
open GeneralDeferredLadderControlCover304 (allStates)
open GeneralDeferredLadderExact302 (RawStep)
open GeneralNominalVersionedJournal232 (State)
open GeneralDeclarationExamples (roles)
open GeneralLadderCompiledPresentation306 (Reach closure present level_bound all_levels level_bisim any_bisim_level possible)
open GeneralFiniteColoredQuotient306 (fastQuotient fast_exact in_domain projection_total projection_sound
  projection_respects representative_fixed exact_edges)
open GeneralFiniteColoredEquivalence306 (test test_exact)
open GeneralFiniteQuotientRepresentatives306 (distinct)
open GeneralFiniteColoredRounds306 (On)

def compile (n : Nat) := fastQuotient (successors n) (fun _ => ()) (allStates n)

theorem test_levels (n : Nat) {x y : Control} (xm : x ∈ allStates n) (ym : y ∈ allStates n) :
    test (successors n) (fun _ => ()) (allStates n) x y = true ↔ remaining n x = remaining n y := by
  rw [test_exact (closure n) xm ym]
  exact ⟨fun ⟨_,valid,h⟩ => any_bisim_level n valid x y xm ym h,
    fun same => ⟨_,level_bisim n,same⟩⟩

theorem abstract_exact (n : Nat) {x y : Control} (xm : x ∈ allStates n) (ym : y ∈ allStates n) :
    (compile n).project x = (compile n).project y ↔ remaining n x = remaining n y := by
  unfold compile
  rw [fast_exact]
  exact (projection_respects (observe := fun _ => ()) (closure n) xm ym).trans (test_levels n xm ym)

theorem raw_exact (n : Nat) {s t : State roles} (hs : Reach n s) (ht : Reach n t) :
    (compile n).project (view n s) = (compile n).project (view n t) ↔
      remaining n (view n s) = remaining n (view n t) :=
  abstract_exact n ((present n).inside s hs) ((present n).inside t ht)

theorem raw_edges (n : Nat) {s : State roles} (hs : Reach n s) {a b : Control}
    (marked : (compile n).project (view n s) = some a) :
    b ∈ (compile n).edges a ↔ ∃ t, RawStep s t ∧ (compile n).project (view n t) = some b :=
  GeneralFiniteRawPresentation306.raw_edges (present n) hs marked

theorem reps_permutation (n : Nat) :
    List.Perm ((compile n).representatives.map (remaining n)) (List.range (n+3)) := by
  let rel := test (successors n) (fun _ => ()) (allStates n)
  let q := GeneralFiniteColoredQuotient306.quotient (successors n) (fun _ => ()) (allStates n)
  have eq : compile n = q := fast_exact ..
  rw [eq]
  have reps : q.representatives.Pairwise (fun x y => rel x y = false) := distinct rel (allStates n)
  have levelDistinct : q.representatives.Pairwise (fun x y => remaining n x ≠ remaining n y) :=
    reps.imp_of_mem (fun {a b} am bm no equal => by
      have yes := (test_levels n (in_domain am) (in_domain bm)).mpr equal
      change rel a b = true at yes
      rw [yes] at no
      cases no)
  have nd : (q.representatives.map (remaining n)).Nodup := levelDistinct.map _ (fun _ _ h => h)
  apply (List.perm_ext_iff_of_nodup nd List.nodup_range).mpr
  intro k
  rw [List.mem_map,List.mem_range]
  constructor
  · rintro ⟨c,mem,rfl⟩
    have high := level_bound n (in_domain mem)
    omega
  · intro fits
    obtain ⟨c,here,level⟩ := all_levels n k (by omega)
    obtain ⟨representative,chosen⟩ := projection_total (observe := fun _ => ()) (closure n) here
    have sound := projection_sound chosen
    have same := (test_levels n here (in_domain sound.1)).mp sound.2
    exact ⟨representative,sound.1,same.symm.trans level⟩

theorem exact_count (n : Nat) : (compile n).representatives.length = n+3 := by
  have result := (reps_permutation n).length_eq
  simpa only [List.length_map,List.length_range] using result

theorem countdown_edges (n : Nat) {a b : Control}
    (am : a ∈ (compile n).representatives) (bm : b ∈ (compile n).representatives) :
    b ∈ (compile n).edges a ↔ remaining n b + 1 = remaining n a := by
  unfold compile at am bm ⊢
  rw [fast_exact] at am bm ⊢
  have aq := representative_fixed (closure n) am
  have bq := representative_fixed (closure n) bm
  have here := in_domain am
  have there := in_domain bm
  rw [exact_edges (closure n) here aq]
  constructor
  · rintro ⟨z,edge,chosen⟩
    have chosenCorrect := projection_sound chosen
    have eq := (test_levels n (closure n a here z edge) there).mp chosenCorrect.2
    have gain := edge_consumes_one ((successors_exact ..).mp edge)
    omega
  · intro count
    obtain ⟨z,edge,_⟩ := (possible n a here).mpr (by omega)
    have gain := edge_consumes_one ((successors_exact ..).mp edge)
    have level : remaining n z = remaining n b := by omega
    have same := (projection_respects (observe := fun _ => ()) (closure n)
      (closure n a here z edge) there).mpr ((test_levels n (closure n a here z edge) there).mpr level)
    exact ⟨z,edge,same.trans bq⟩

end Yulang.GeneralLadderCompiledMinimal306
