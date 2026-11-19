import Yulang.GeneralRebaseVersionWindow284
import Yulang.GeneralRebaseLooseWindow284

namespace Yulang.GeneralRebaseWindowMinimum284
open GeneralRebaseRoundMicro278 (Tick Phase)
open GeneralRebaseEpochWindow284 (Window view canInstall latestKnown previousKnown table)

def witness (s : Window) : Tick := ⟨if s.later then 1 else 0,s.phase⟩

theorem witness_exact (s : Window) : view (witness s) = s := by
  rcases s with ⟨b,p⟩; cases b <;> rfl

theorem distinguish (s t : Window) (earlier : previousKnown s = previousKnown t)
    (fresh : latestKnown s = latestKnown t) (enabled : canInstall s = canInstall t) : s = t := by
  rcases s with ⟨b,p⟩
  rcases t with ⟨c,q⟩
  have bits : b = c := earlier
  subst c
  cases p <;> cases q <;> simp [latestKnown,canInstall] at fresh enabled ⊢

theorem minimum (encode : Tick → Q) (pool : List Q) (covers : ∀ t, encode t ∈ pool)
    (seesPrev : ∀ a b, encode a = encode b → previousKnown (view a) = previousKnown (view b))
    (seesFresh : ∀ a b, encode a = encode b → latestKnown (view a) = latestKnown (view b))
    (seesInstall : ∀ a b, encode a = encode b → canInstall (view a) = canInstall (view b)) :
    6 ≤ pool.length := by
  let values := table.map (fun s => encode (witness s))
  have unique : values.Nodup := by
    change (table.map (fun s => encode (witness s))).Pairwise (· ≠ ·)
    rw [List.pairwise_map]
    apply GeneralRebaseEpochWindow284.table_distinct.imp
    intro a b diff same
    have prev := seesPrev _ _ same
    have last := seesFresh _ _ same
    have install := seesInstall _ _ same
    simp only [witness_exact] at prev last install
    exact diff (distinguish a b prev last install)
  have subset : values ⊆ pool := by
    intro x present
    obtain ⟨s,_,rfl⟩ := List.mem_map.mp present
    exact covers _
  simpa [values,GeneralRebaseEpochWindow284.table_size] using List.Nodup.length_le_of_subset unique subset

end Yulang.GeneralRebaseWindowMinimum284
