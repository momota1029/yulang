import Yulang.GeneralRebaseCompactEvidenceAt279

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseEdgeLedger279
open GeneralDeclarations GeneralSourceDictionaries
open GeneralRebaseInstallNovelty279 (Edge)
open GeneralRebaseEdgeReceipt279 (edgeKnown edgeKnown_exact freshEdges mem_freshEdges)
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralRebaseCompactEdgeInstall279 (replaceEdges)
open GeneralRebaseCompactAvailability279 (SameEdges)
open GeneralNominalVersionedChildren232 (edges)
open GeneralNominalVersionedInstall232 (install)

def normalize : List (Edge roles) → List (Edge roles)
  | [] => []
  | edge::rest =>
    if edgeKnown rest edge then normalize rest else edge :: normalize rest

theorem normalize_members (xs : List (Edge roles)) (edge : Edge roles) :
    edge ∈ normalize xs ↔ edge ∈ xs := by
  induction xs with
  | nil => rfl
  | cons front tail ih =>
    by_cases repeats : edgeKnown tail front = true
    · have found := (edgeKnown_exact tail front).mp repeats
      rw [normalize,ite_eq_left repeats,ih,List.mem_cons]
      exact ⟨Or.inr,fun h => h.elim (fun eq => eq.symm ▸ found) id⟩
    · rw [normalize,ite_eq_right repeats,List.mem_cons,ih,List.mem_cons]

theorem normalize_nodup (xs : List (Edge roles)) : (normalize xs).Nodup := by
  induction xs with
  | nil => exact .nil
  | cons edge tail ih =>
    by_cases repeats : edgeKnown tail edge = true
    · rwa [normalize,ite_eq_left repeats]
    · have notIn : edge ∉ tail := (not_congr (edgeKnown_exact tail edge)).mp repeats
      rw [normalize,ite_eq_right repeats,List.nodup_cons,normalize_members]
      exact ⟨notIn,ih⟩

theorem normalize_order (xs : List (Edge roles)) : (normalize xs).Sublist xs := by
  induction xs with
  | nil => exact .slnil
  | cons edge tail ih =>
    by_cases repeats : edgeKnown tail edge = true
    · rw [normalize,ite_eq_left repeats]
      exact .cons _ ih
    · rw [normalize,ite_eq_right repeats]
      exact .cons_cons _ ih

theorem normalize_eq (xs : List (Edge roles)) (exact : xs.Nodup) : normalize xs = xs := by
  induction xs with
  | nil => rfl
  | cons edge tail ih =>
    have bound := List.nodup_cons.mp exact
    have unique := (not_congr (edgeKnown_exact tail edge)).mpr bound.1
    rw [normalize,ite_eq_right unique,ih bound.2]

theorem normalize_idempotent (xs : List (Edge roles)) : normalize (normalize xs) = normalize xs :=
  normalize_eq _ (normalize_nodup _)

def advance (old requested : List (Edge roles)) : List (Edge roles) :=
  old ++ freshEdges old (normalize requested)

theorem advance_members (old requested : List (Edge roles)) (edge : Edge roles) :
    edge ∈ advance old requested ↔ edge ∈ old ++ requested := by
  rw [advance,GeneralRebaseEdgeReceipt279.append_delta_membership]
  simp only [List.mem_append,normalize_members]

theorem advance_nodup (old requested : List (Edge roles)) (unique : old.Nodup) :
    (advance old requested).Nodup := by
  rw [advance,List.nodup_append]
  refine ⟨unique,(List.Nodup.sublist (List.filter_sublist) (normalize_nodup requested)),?_⟩
  intro front was rear added same
  exact ((mem_freshEdges ..).mp added).2 (same ▸ was)

theorem advance_limit (old requested : List (Edge roles)) :
    (advance old requested).length ≤ old.length + requested.length := by
  rw [advance,List.length_append]
  exact Nat.add_le_add_left ((List.filter_sublist.trans (normalize_order requested)).length_le) _

theorem advance_repeated (old requested : List (Edge roles)) :
    advance (advance old requested) requested = advance old requested := by
  unfold advance at ⊢
  have empty : freshEdges (advance old requested) (normalize requested) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro edge h
    have info := (mem_freshEdges ..).mp h
    exact info.2 ((advance_members ..).mpr (List.mem_append_right _ ((normalize_members ..).mp info.1)))
  change advance old requested ++ freshEdges (advance old requested) (normalize requested) = advance old requested
  rw [empty,List.append_nil]

def normalizedInstall (start : State roles) (effect : Effect roles) : State roles :=
  replaceEdges (install start effect) (advance (normalize start.core.erased.current.edges) (edges effect.plan))

theorem normalized_members (start : State roles) (effect : Effect roles) :
    SameEdges (install start effect) (advance (normalize start.core.erased.current.edges) (edges effect.plan)) := by
  intro edge
  rw [advance_members,List.mem_append,normalize_members]
  exact List.mem_append.symm

theorem normalized_nodup (start : State roles) (effect : Effect roles) :
    (normalizedInstall start effect).core.erased.current.edges.Nodup :=
  advance_nodup _ _ (normalize_nodup _)

end Yulang.GeneralRebaseEdgeLedger279
