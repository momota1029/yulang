import Yulang.GeneralSourceMetadataCoverageFixture291

/-! A checked finite association lookup has exactly its listed graph.
The forward direction works even before duplicate-key validation. -/
namespace Yulang.GeneralSourceMetadataFiniteLookup291

def get {α : Type} (key : Nat) : List (Nat × α) → Option α
  | [] => none
  | (name,value) :: rest => if key = name then some value else get key rest

theorem some_sound {α : Type} {key : Nat} {value : α} {data : List (Nat × α)}
    (h : get key data = some value) : (key,value) ∈ data := by
  induction data with
  | nil => cases h
  | cons first rest ih =>
    rcases first with ⟨name,a⟩
    by_cases seen : key = name
    · rw [get,ite_eq_left seen] at h
      rcases seen with rfl
      cases Option.some.inj h
      exact List.mem_cons_self
    · rw [get,ite_eq_right seen] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem some_complete {α : Type} {key : Nat} {value : α} {data : List (Nat × α)}
    (unique : (data.map Prod.fst).Nodup) (h : (key,value) ∈ data) : get key data = some value := by
  induction data with
  | nil => cases h
  | cons first rest ih =>
    rcases first with ⟨name,a⟩
    rcases List.mem_cons.mp h with exactPair | tail
    · cases exactPair
      simp [get]
    · have distinct := List.nodup_cons.mp unique
      have keyAway : key ≠ name := by
        intro same
        apply distinct.1
        rw [←same]
        exact List.mem_map.mpr ⟨(key,value),tail,rfl⟩
      rw [get,ite_eq_right keyAway]
      exact ih distinct.2 tail

theorem some_iff {α : Type} (data : List (Nat × α)) (unique : (data.map Prod.fst).Nodup)
    (key : Nat) (value : α) : get key data = some value ↔ (key,value) ∈ data :=
  ⟨some_sound,some_complete unique⟩

end Yulang.GeneralSourceMetadataFiniteLookup291
