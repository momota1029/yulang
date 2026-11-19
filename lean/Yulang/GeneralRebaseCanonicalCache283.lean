import Yulang.GeneralRebaseCachedFixtures283

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseCanonicalCache283
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralRebaseSortedCache283 (Ascending)
open GeneralRebaseInstallCache283 (Valid)
open GeneralRebaseCachedDriver283 (Snapshot Move Initial raw valid_next)
open GeneralRebaseMixedCounts277 (Actual)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)

theorem sorted_unique (a b : List (Entry Nat)) (sa : Ascending a) (sb : Ascending b)
    (same : ∀ row, row ∈ a ↔ row ∈ b) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons head rest =>
      exact False.elim (List.not_mem_nil ((same head).mpr List.mem_cons_self))
  | cons head rest ih =>
    cases b with
    | nil => exact False.elim (List.not_mem_nil ((same head).mp List.mem_cons_self))
    | cons next tail =>
      obtain ⟨amin,saTail⟩ := List.pairwise_cons.mp sa
      obtain ⟨bmin,bt⟩ := List.pairwise_cons.mp sb
      have headSame : head = next := by
        apply Classical.byContradiction
        intro ne
        have a : head ∈ tail := (List.mem_cons.mp ((same head).mp List.mem_cons_self)).resolve_left ne
        have b : next ∈ rest := (List.mem_cons.mp ((same next).mpr List.mem_cons_self)).resolve_left (Ne.symm ne)
        exact Nat.lt_asymm (bmin head a) (amin next b)
      subst next
      congr
      apply ih tail saTail bt
      intro row
      constructor
      · intro mem
        refine (List.mem_cons.mp ((same row).mp (List.mem_cons_of_mem _ mem))).resolve_left ?_
        intro eq
        exact Nat.lt_irrefl _ (eq ▸ amin row mem)
      · intro mem
        refine (List.mem_cons.mp ((same row).mpr (List.mem_cons_of_mem _ mem))).resolve_left ?_
        intro eq
        exact Nat.lt_irrefl _ (eq ▸ bmin row mem)

theorem valid_unique {s : GeneralNominalVersionedJournal232.State roles} {a b : List (Entry Nat)}
    (va : Valid a s) (vb : Valid b s) : a = b :=
  sorted_unique a b va.increasing vb.increasing (fun row => (va.content row).trans (vb.content row).symm)

theorem snapshot_unique {p q : Snapshot roles} (vp : Valid p.defs p.raw) (vq : Valid q.defs q.raw)
    (same : p.raw = q.raw) : p = q := by
  cases p with | mk pa pc =>
  cases q with | mk qa qc =>
  change pa = qa at same
  subst qa
  exact congrArg (Snapshot.mk pa) (valid_unique vp vq)

theorem next_unique {p q q' : Snapshot roles}
    (first : Move r root p q) (second : Move r root p q') (same : q.raw = q'.raw) : q = q' :=
  snapshot_unique (valid_next first) (valid_next second) same

theorem next_initial {p q : Snapshot roles} (act : Move r root p q) : q = Initial q.raw :=
  snapshot_unique (valid_next act) (GeneralRebaseInstallCache283.initial_valid
    (GeneralNominalVersionedMixedSeedLedger237.reachable
      (GeneralNominalVersionedMixedProgressSplit236.reachable_step act.1 (raw act)))) rfl

theorem raw_next_exact {p : Snapshot roles} (seen : Reachable r root p.raw) (cached : Valid p.defs p.raw)
    (next : GeneralNominalVersionedJournal232.State roles) :
    Move r root p (Initial next) ↔ Actual r root p.raw next := by
  constructor
  · exact raw
  · intro action
    obtain ⟨q,eq,h⟩ := GeneralRebaseCachedDriver283.lift_one seen cached action
    have pair := (next_initial h).trans (congrArg Initial eq)
    exact pair ▸ h

end Yulang.GeneralRebaseCanonicalCache283
