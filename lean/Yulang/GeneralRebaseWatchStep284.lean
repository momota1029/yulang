import Yulang.GeneralRebaseFutureWatch284

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseWatchStep284
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralRebaseFutureWatch284 (Closed Covers trim member_exact)
open GeneralRebaseSortedCache283 (Ascending push push_exact)
open GeneralNominalAcyclicEquations237 (Coherent Descending)

def NoReveal (before after : List Nat) (old : List (Entry Nat)) : Prop :=
  ∀ row ∈ old, row.1 ∈ after → row.1 ∈ before

def next (watch : List Nat) (stored delta : List (Entry Nat)) :=
  trim watch (push delta stored)

theorem advance {first last : List Nat} {old stored delta full : List (Entry Nat)}
    (haveOld : Covers first old stored) (ascending : Ascending stored)
    (allRows : ∀ row, row ∈ full ↔ row ∈ delta ∨ row ∈ old)
    (coherent : Coherent full) (closed : Closed last full)
    (safe : NoReveal first last old) :
    Covers last full (next last stored delta) ∧ Ascending (next last stored delta) := by
  have included (row : Entry Nat) (seen : row ∈ delta ++ stored) : row ∈ full := by
    apply (allRows row).mpr
    exact (List.mem_append.mp seen).imp id (fun m => haveOld.sound m)
  obtain ⟨ordered,bump⟩ := push_exact delta stored ascending
    (fun a ha b hb same => coherent a (included a ha) b (included b hb) same)
  have forward (row : Entry Nat) (present : row ∈ next last stored delta) : row ∈ full := by
    exact included row (List.mem_append.mpr ((bump row).mp ((member_exact ..).mp present).1))
  have rear (row : Entry Nat) (present : row ∈ full) (asked : row.1 ∈ last) : row ∈ next last stored delta := by
    refine (member_exact ..).mpr ⟨(bump row).mpr ?_,asked⟩
    exact ((allRows row).mp present).imp id (fun h => haveOld.enough row h (safe row h asked))
  exact ⟨⟨closed,fun {_} => forward _,rear⟩,List.Pairwise.sublist List.filter_sublist ordered⟩

theorem noReveal_same (watch : List Nat) (old : List (Entry Nat)) : NoReveal watch watch old :=
  fun _ _ h => h

theorem noReveal_subsets {first last : List Nat} (sub : last ⊆ first) (old : List (Entry Nat)) :
    NoReveal first last old := fun _ _ h => sub h

theorem watches_only (watch : List Nat) (stored delta : List (Entry Nat)) (row : Entry Nat)
    (seen : row ∈ next watch stored delta) : row.1 ∈ watch :=
  ((member_exact ..).mp seen).2

theorem length_limit {watch : List Nat} {stored delta : List (Entry Nat)}
    (ascending : Ascending (next watch stored delta)) :
    (next watch stored delta).length ≤ watch.length := by
  have watchOnly : (next watch stored delta).map Prod.fst ⊆ watch := by
    intro n known
    obtain ⟨row,seen,rfl⟩ := List.mem_map.mp known
    exact watches_only watch stored delta row seen
  have unique : ((next watch stored delta).map Prod.fst).Nodup := by
    have noRepeats := List.pairwise_map.mpr ascending
    exact noRepeats.imp (fun hit => Nat.ne_of_lt hit)
  have size := List.Nodup.length_le_of_subset unique watchOnly
  simpa using size

end Yulang.GeneralRebaseWatchStep284
