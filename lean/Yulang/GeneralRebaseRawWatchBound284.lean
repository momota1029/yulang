import Yulang.GeneralRebaseFutureCounter284

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseRawWatchBound284
open GeneralNominalVersionedJournal232 (State)
open GeneralRebaseSliceJournal283 (journalReads)
open GeneralNominalRebaseJournalView243 (compile)
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralNominalVersionedAggregateLedger236 (packetEntries)
open GeneralNominalVersionedInstallation231 (atoms)
open Core.PresenceGeneration (TyTerm CompTerm)
open PresenceNormalForm (Atom)

def raw (state : State roles) := state.core.erased.current.context.state

theorem atom_in_packet (p : GeneralNominalSaturationState.Packet roles) (e : Entry Nat)
    (stored : e ∈ packetEntries p) :
    Atom.tyLe (.var e.1) e.2 ∈ atoms p := by
  have eq := GeneralNominalVersionedAggregateEntries236.atoms_eq p.context.state p.registry
    p.site.occurrence.identity p.declaration p.bindings
  unfold atoms
  apply List.mem_append_left
  apply List.mem_append_right
  rw [eq]
  exact List.mem_flatMap.mpr ⟨e,stored,List.mem_cons_self ..⟩

theorem raw_target_read (s : State roles) (name : Nat) (term : TyTerm Nat)
    (present : Atom.tyLe (.var name) term ∈ (raw s).ordinary) :
    name ∈ journalReads s := by
  unfold journalReads GeneralNominalJournalSupport249.support
  apply List.mem_flatten.mpr
  refine ⟨GeneralNominalViewSupport249.support (compile s CompTerm.var).current,List.mem_cons_self,?_⟩
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨.tyLe (.var name) (term.subst CompTerm.var),?_,?_⟩
  · apply List.mem_append_right
    exact List.mem_map.mpr ⟨_,present,rfl⟩
  · exact List.mem_append_left _ (List.mem_singleton_self _)

theorem watch_must_count (states : Nat → State roles) (lo : Nat → Nat)
    (strict : ∀ {i j}, lo i = lo j → i = j)
    (seen : ∀ n i, i < n → lo (i+1) ∈ journalReads (states n))
    (n : Nat) (watch : List Nat) (covered : journalReads (states n) ⊆ watch) :
    n ≤ watch.length := by
  let names := (List.range n).map (fun i => lo (i+1))
  have distinct : names.Nodup := by
    change ((List.range n).map (fun i => lo (i+1))).Pairwise (· ≠ ·)
    rw [List.pairwise_map]
    exact List.nodup_range.imp (fun distinct hit => distinct (Nat.succ.inj (strict hit)))
  have inside : names ⊆ watch := by
    intro name wanted
    obtain ⟨i,mem,rfl⟩ := List.mem_map.mp wanted
    exact covered (seen n i (List.mem_range.mp mem))
  simpa [names] using List.Nodup.length_le_of_subset distinct inside


theorem all_keys_required {defs : List (Entry Nat)} {n a b : Nat} {lo hi up : Nat → Nat}
    (family : GeneralRebaseAliasFamily283.Family defs n a b lo hi up)
    (distinct : GeneralRebaseTwoWrites283.Distinct lo hi) (state : State roles) (watch : List Nat)
    (readable : journalReads state ⊆ watch)
    (stored : ∀ row ∈ defs, Atom.tyLe (.var row.1) row.2 ∈ (raw state).ordinary) :
    2*n ≤ watch.length := by
  have noRepeats := GeneralRebaseArchiveUnbounded283.nodup distinct n
  have covered : GeneralRebaseArchiveUnbounded283.keys lo hi n ⊆ watch := by
    intro k h
    have listed := (GeneralRebaseArchiveUnbounded283.key_member lo hi n k).mp h
    obtain ⟨row,mem,same⟩ := List.mem_map.mp ((GeneralRebaseTwoWrites283.known family).mpr listed)
    exact readable (same ▸ raw_target_read state row.1 row.2 (stored row mem))
  have count := List.Nodup.length_le_of_subset noRepeats covered
  rw [GeneralRebaseArchiveUnbounded283.key_count] at count
  exact count

end Yulang.GeneralRebaseRawWatchBound284
