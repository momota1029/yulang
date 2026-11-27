import Yulang.GeneralDeclarativeI65I74PreparationBoundReplay467
import Yulang.GeneralDeclarativeI65I74CheckedPreparationObservations467

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.PreparedBoundRetraction467
open GeneralDeclarativeI65.I72.PreparationBoundReplay467
open GeneralDeclarativeI65.I72.PreparationFootprint467
open GeneralDeclarativeI65.I72.PreparationTagScope467
open GeneralDeclarativeI65.I72.CheckedPreparedRetraction467
open GeneralDeclarativeI65.I72.CheckedPreparationObservations467
open GeneralDeclarativeI65.I72.NamedProjection464 (exactOrdinaryState exact_ordinary_snapshot_iff)
open GeneralDeclarativeWitnessBound349 (Path check sound)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeLowerKnown321 (Knows)
open PresenceNormalForm (Atom)
private abbrev Raw := GeneralDeclarativeHead320.State

def pathsForPairs (s : Raw) (p : Nat → Nat) :
    List (Nat × Nat) → List Path → Bool
  | [],[] => true
  | (a,b)::xs,w::ws => check s (p a) (p b) w && pathsForPairs s p xs ws
  | _,_ => false

theorem checked_projected_pairs_prove_actual_old_bounds (s : Raw) (p : Nat → Nat)
    (pairs : List (Nat × Nat)) (paths : List Path)
    (accepted : pathsForPairs s p pairs paths = true) :
    ∀ a b, (a,b) ∈ pairs → Bound s.normal (p a) (p b) := by
  induction pairs generalizing paths with
  | nil => simp
  | cons head rest ih =>
    rcases head with ⟨x,y⟩
    cases paths with
    | nil => cases accepted
    | cons first later =>
      have passes := Bool.and_eq_true_iff.mp accepted
      intro a b got
      rcases List.mem_cons.mp got with fromHead|fromRest
      · cases fromHead
        exact sound passes.1
      · exact ih later passes.2 a b fromRest

theorem every_list_of_independent_projected_bounds_reifies (s : Raw) (p : Nat → Nat)
    (pairs : List (Nat × Nat))
    (all : ∀ a b, (a,b) ∈ pairs → Bound s.normal (p a) (p b)) :
    ∃ paths, pathsForPairs s p pairs paths = true := by
  induction pairs with
  | nil => exact ⟨[],rfl⟩
  | cons head rest ih =>
    rcases head with ⟨a,b⟩
    obtain ⟨first,proof⟩ := (finite_literal_bound_wire_is_equivalent_to_independent_bound s _ _).mpr
      (all a b List.mem_cons_self)
    obtain ⟨later,passed⟩ := ih (fun a b mem => all a b (List.mem_cons_of_mem _ mem))
    exact ⟨first::later,Bool.and_eq_true_iff.mpr ⟨proof,passed⟩⟩

def checkProjectedPreparation (s t : Raw) (wire : List (Nat × Nat)) (root : Nat)
    (paths : List Path) : Bool :=
  checkOrdinaryObservationRetraction s s wire root &&
    exactOrdinaryState (withMoreAtoms s (appendingSuffix s t)) t &&
    pathsForPairs s (explicitProject wire) ((appendingSuffix s t).filterMap boundsIn) paths

def ExactProjectedPreparation (s t : Raw) (wire : List (Nat × Nat)) (root : Nat) : Prop :=
  ExactPreparedRetraction s s wire root ∧
  (∀ n ∈ tagFootprint s, explicitProject wire n = n) ∧
  ∃ added : List (Atom Nat), t = withMoreAtoms s added ∧
    ∀ a b, Atom.tyLe (.var a) (.var b) ∈ added →
      Bound s.normal (explicitProject wire a) (explicitProject wire b)

theorem projected_preparation_has_finite_wire_exactly_for_independent_old_bounds
    (s t : Raw) (wire : List (Nat × Nat)) (root : Nat) :
    (∃ paths, checkProjectedPreparation s t wire root paths = true) ↔
      ExactProjectedPreparation s t wire root := by
  constructor
  · rintro ⟨paths,passed⟩
    have ok := Bool.and_eq_true_iff.mp passed
    have old := Bool.and_eq_true_iff.mp ok.1
    obtain ⟨base,tags⟩ := (same_phase_retention_wire_checks_both_original_footprints ..).mp old.1
    refine ⟨base,tags,_,((exact_ordinary_snapshot_iff ..).mp old.2).symm,?_⟩
    intro a b row
    exact checked_projected_pairs_prove_actual_old_bounds _ _ _ _ ok.2 _ _
      (bounded_atom_pair_is_exact.mpr row)
  · rintro ⟨base,tags,added,same,proj⟩
    have before := (same_phase_retention_wire_checks_both_original_footprints ..).mpr ⟨base,tags⟩
    have suffix : appendingSuffix s t = added := by simp [appendingSuffix,same,withMoreAtoms]
    obtain ⟨paths,accepted⟩ := every_list_of_independent_projected_bounds_reifies s
      (explicitProject wire) (added.filterMap boundsIn) (fun a b mem =>
        proj a b (bounded_atom_pair_is_exact.mp mem))
    have equal := (exact_ordinary_snapshot_iff (withMoreAtoms s added) t).mpr same.symm
    exact ⟨paths,by simp [checkProjectedPreparation,before,suffix,equal,accepted]⟩

theorem checked_projected_preparation_preserves_original_raw_k2_and_tags
    {s t : Raw} {wire : List (Nat × Nat)} {root : Nat} {paths : List Path}
    (checked : checkProjectedPreparation s t wire root paths = true) :
    (AliasCycle s (observed s) root ↔ AliasCycle t (observed t) root) ∧
      (∀ tag, Knows s root tag ↔ Knows t root tag) := by
  obtain ⟨base,tags,added,same,proof⟩ :=
    (projected_preparation_has_finite_wire_exactly_for_independent_old_bounds ..).mp ⟨paths,checked⟩
  obtain ⟨_,_,intvs,ordinary,aliases,_,pins⟩ := base
  have rows : s.equations = t.equations := by rw [same]; rfl
  have intervals : s.normal.intervals = t.normal.intervals := by rw [same]; rfl
  have atoms : t.normal.ordinary = s.normal.ordinary ++ added := by rw [same]; rfl
  let p := explicitProject wire
  have retraction : OrdinaryRetraction s t p := by
    constructor
    · intro a b found
      rw [← intervals] at found
      obtain ⟨ha,hb⟩ := intvs _ found
      simpa [p,ha,hb] using (Bound.interval found)
    · intro a b found
      rw [atoms,List.mem_append] at found
      cases found with
      | inl old =>
        obtain ⟨ha,hb⟩ := ordinary a b old
        simpa [p,ha,hb] using (Bound.constraint old)
      | inr new => exact proof a b new
    · intro a b found
      rw [← rows] at found
      obtain ⟨ha,hb⟩ := aliases a b found
      simpa [p,ha,hb] using (GeneralDeclarativeLowerKnown321.Alias.forward found)
    · intro a b found
      exact .interval (intervals ▸ found)
    · intro a b found
      apply Bound.constraint
      rw [atoms,List.mem_append]
      exact Or.inl found
    · intro a b found
      exact .forward (rows ▸ found)
  apply finite_combined_graph_and_tag_scope_preserves_K2_and_knowledge retraction rows
  apply List.all_eq_true.mpr
  intro n mem
  cases List.mem_append.mp mem with
  | inl old => exact decide_eq_true (pins n old)
  | inr tag => exact decide_eq_true (tags n tag)

end Yulang.GeneralDeclarativeI65.I72.PreparedBoundRetraction467
