import Yulang.GeneralRebaseCertifiedWatchFixtures284

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseSingleQueryObstruction284
open GeneralRebaseRoundMicro278 (Tick)
open GeneralRebaseInstallTimeline278 (installedCount observedCount)
open GeneralRebaseWindowNoFinite284 (threshold_left threshold_right)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalState (Known)
open GeneralRebaseEpochWindow284 (view)

theorem impossibility {Q : Type} (encode : Tick → Q) (pool : List Q)
    (distinct : ∀ a b : Nat, encode ⟨a,.enter⟩ = encode ⟨b,.enter⟩ → a = b) :
    ¬ ∀ t, encode t ∈ pool := by
  intro all
  let n := pool.length+1
  let row := (List.range n).map (fun k => encode ⟨k,.enter⟩)
  have uniq : row.Nodup := by
    change ((List.range n).map (fun k => encode ⟨k,.enter⟩)).Pairwise (· ≠ ·)
    rw [List.pairwise_map]
    exact List.nodup_range.imp (fun {a b} diff eq => diff (distinct a b eq))
  have members : row ⊆ pool := by
    intro key found
    obtain ⟨n,_,rfl⟩ := List.mem_map.mp found
    exact all ⟨n,.enter⟩
  have wrong := List.Nodup.length_le_of_subset uniq members
  simp [row,n] at wrong
  omega

theorem by_models {Q : Type} (encode : Tick → Q) (pool : List Q) (query : Q → Nat → Prop)
    (correct : ∀ t i, query (encode t) i ↔ installedCount t ≤ i) :
    ¬ ∀ t, encode t ∈ pool := by
  apply impossibility encode pool
  intro a b same
  apply threshold_right
  intro k
  exact (correct ⟨a,.enter⟩ k).symm.trans (same ▸ correct ⟨b,.enter⟩ k)

theorem by_known {Q : Type} (encode : Tick → Q) (pool : List Q) (query : Q → Nat → Prop)
    (correct : ∀ t i, query (encode t) i ↔ i < observedCount t) :
    ¬ ∀ t, encode t ∈ pool := by
  apply impossibility encode pool
  intro a b same
  apply threshold_left
  intro k
  exact (correct ⟨a,.enter⟩ k).symm.trans (same ▸ correct ⟨b,.enter⟩ k)

namespace Version
open GeneralDictionaryVersionLoopFamilyNovel239 (bad)
open GeneralDictionaryVersionLoopNames238 (lower)
open GeneralRebaseVersionMicro278 (raw)

theorem no_finite_models {Q : Type} (encode : Tick → Q) (pool : List Q) (query : Q → Nat → Prop)
    (correct : ∀ t i, query (encode t) i ↔ Models (raw t) (bad i)) :
    ¬ ∀ t, encode t ∈ pool :=
  by_models encode pool query (fun t i => (correct t i).trans (GeneralRebaseInstallTimeline278.Version.patch_exact t i))

theorem no_finite_known {Q : Type} (encode : Tick → Q) (pool : List Q) (query : Q → Nat → Prop)
    (correct : ∀ t i, query (encode t) i ↔ Known (raw t).core.erased.current.context.state (lower (i+1))) :
    ¬ ∀ t, encode t ∈ pool :=
  by_known encode pool query (fun t i => (correct t i).trans (GeneralRebaseVersionKnown278.prefix_known t i))

theorem same_window_distinct_models :
    view ⟨1,.enter⟩ = view ⟨2,.enter⟩ ∧
    Models (raw ⟨1,.enter⟩) (bad 1) ∧ ¬ Models (raw ⟨2,.enter⟩) (bad 1) :=
  ⟨rfl,(GeneralRebaseInstallTimeline278.Version.patch_exact ⟨1,.enter⟩ 1).mpr (by decide),
    fun impossible => Nat.not_succ_le_self 1 ((GeneralRebaseInstallTimeline278.Version.patch_exact ⟨2,.enter⟩ 1).mp impossible)⟩

end Version

namespace Loose
open GeneralDictionaryLooseFamilyNovel240 (bad)
open GeneralDictionaryLooseFamilyNames240 (lower)
open GeneralRebaseLooseMicro278 (raw)

theorem no_finite_models {Q : Type} (encode : Tick → Q) (pool : List Q) (query : Q → Nat → Prop)
    (correct : ∀ t i, query (encode t) i ↔ Models (raw t) (bad i)) :
    ¬ ∀ t, encode t ∈ pool :=
  by_models encode pool query (fun t i => (correct t i).trans (GeneralRebaseInstallTimeline278.Loose.patch_exact t i))

theorem no_finite_known {Q : Type} (encode : Tick → Q) (pool : List Q) (query : Q → Nat → Prop)
    (correct : ∀ t i, query (encode t) i ↔ Known (raw t).core.erased.current.context.state (lower (i+1))) :
    ¬ ∀ t, encode t ∈ pool :=
  by_known encode pool query (fun t i => (correct t i).trans (GeneralRebaseLooseKnown278.prefix_known t i))

theorem same_window_distinct_models :
    view ⟨1,.enter⟩ = view ⟨2,.enter⟩ ∧
    Models (raw ⟨1,.enter⟩) (bad 1) ∧ ¬ Models (raw ⟨2,.enter⟩) (bad 1) :=
  ⟨rfl,(GeneralRebaseInstallTimeline278.Loose.patch_exact ⟨1,.enter⟩ 1).mpr (by decide),
    fun impossible => Nat.not_succ_le_self 1 ((GeneralRebaseInstallTimeline278.Loose.patch_exact ⟨2,.enter⟩ 1).mp impossible)⟩

end Loose
end Yulang.GeneralRebaseSingleQueryObstruction284
