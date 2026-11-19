import Yulang.GeneralRebaseWindowPaths284

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseWindowNoFinite284
open GeneralRebaseRoundMicro278 (Tick Phase)
open GeneralRebaseInstallTimeline278 (installedCount observedCount)

structure Faithful (encode : Tick → Q) where
  models : Q → Nat → Prop
  known : Q → Nat → Prop
  ready : Q → Prop
  model_eq : ∀ t i, models (encode t) i ↔ installedCount t ≤ i
  known_eq : ∀ t i, known (encode t) i ↔ i < observedCount t
  ready_eq : ∀ t, ready (encode t) ↔ t.phase = .enter

theorem threshold_right {a b : Nat} (same : ∀ i, a ≤ i ↔ b ≤ i) : a = b :=
  Nat.le_antisymm ((same b).mpr (Nat.le_refl _)) ((same a).mp (Nat.le_refl _))

theorem threshold_left {a b : Nat} (same : ∀ i, i < a ↔ i < b) : a = b := by
  apply Nat.le_antisymm
  · apply Nat.le_of_not_gt
    exact fun h => Nat.lt_irrefl b ((same b).mp h)
  · apply Nat.le_of_not_gt
    exact fun h => Nat.lt_irrefl a ((same a).mpr h)

theorem counts {encode : Tick → Q} (h : Faithful encode) {a b : Tick} (eq : encode a = encode b) :
    installedCount a = installedCount b ∧ observedCount a = observedCount b ∧
    (a.phase = .enter ↔ b.phase = .enter) := by
  exact ⟨threshold_right (fun i => (h.model_eq a i).symm.trans (eq ▸ h.model_eq b i)),
    threshold_left (fun i => (h.known_eq a i).symm.trans (eq ▸ h.known_eq b i)),
    (h.ready_eq a).symm.trans (eq ▸ h.ready_eq b)⟩

theorem all_ticks {encode : Tick → Q} (h : Faithful encode) {a b : Tick} (eq : encode a = encode b) :
    a = b := by
  obtain ⟨wired,known,ready⟩ := counts h eq
  rcases a with ⟨i,pa⟩
  rcases b with ⟨j,pb⟩
  cases pa <;> cases pb <;> simp [installedCount,observedCount] at *
  all_goals first | congr 1 <;> omega | omega

theorem not_finite {encode : Tick → Q} (proof : Faithful encode) (pool : List Q) :
    ¬ ∀ tick, encode tick ∈ pool := by
  intro finite
  let n := pool.length+1
  let data := (List.range n).map (fun i => encode ⟨i,.enter⟩)
  have unique : data.Nodup := by
    change ((List.range n).map (fun i => encode ⟨i,.enter⟩)).Pairwise (· ≠ ·)
    rw [List.pairwise_map]
    exact List.nodup_range.imp (fun ne eq => ne (congrArg Tick.round (all_ticks proof eq)))
  have inside : data ⊆ pool := by
    intro x found
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp found
    exact finite ⟨i,.enter⟩
  have length := List.Nodup.length_le_of_subset unique inside
  simp [data,n] at length
  omega

end Yulang.GeneralRebaseWindowNoFinite284
