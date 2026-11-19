import Yulang.GeneralRebaseFreshDelta283
import Yulang.GeneralPresencePersistentSnapshot250

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseTwoWrites283
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralPresenceUsedSupport245 (typedReads)
open GeneralRebaseFreshDelta283 (NoBackReads)
open GeneralRebaseIncrementalHistory283 (changes)
open GeneralRebaseAliasFamily283 (Family lowerRow upperRow lower_one upper_one)
open GeneralRebaseOneSource283 (reads_exact)

variable {n a b : Nat} {lo hi upRead : Nat → Nat} {old next : List (Entry Nat)}

structure Distinct (lo hi : Nat → Nat) : Prop where
  monotone : ∀ {i j}, i < j → lo i < lo j
  hi_unique : ∀ {i j}, hi i = hi j → i = j
  split : ∀ i j, lo i ≠ hi j

theorem known {k v : Nat} {defs : List (Entry Nat)} (f : Family defs k a b lo hi upRead) :
    v ∈ defs.map Prod.fst ↔ ∃ i < k, v = lo (i+1) ∨ v = hi i := by
  constructor
  · intro seen
    obtain ⟨row,found,hit⟩ := List.mem_map.mp seen
    obtain ⟨i,bound,rfl|rfl⟩ := (f.cover row).mp found
    · exact ⟨i,bound,Or.inl hit.symm⟩
    · exact ⟨i,bound,Or.inr hit.symm⟩
  · rintro ⟨i,limit,hit|hit⟩
    · exact List.mem_map.mpr ⟨lowerRow lo i,(f.cover _).mpr ⟨i,limit,Or.inl rfl⟩,hit.symm⟩
    · exact List.mem_map.mpr ⟨upperRow hi upRead i,(f.cover _).mpr ⟨i,limit,Or.inr rfl⟩,hit.symm⟩

theorem fresh (family : Family old n a b lo hi upRead) (sep : Distinct lo hi) :
    lo (n+1) ∉ old.map Prod.fst ∧ hi n ∉ old.map Prod.fst := by
  constructor
  · intro found
    obtain ⟨i,bound,eq|eq⟩ := (known family).mp found
    · have high := sep.monotone (i := i+1) (j := n+1) (by omega)
      omega
    · exact sep.split _ _ eq
  · intro found
    obtain ⟨i,bound,eq|eq⟩ := (known family).mp found
    · exact sep.split _ _ eq.symm
    · have same := sep.hi_unique eq
      omega

theorem old_member (prior : Family old n a b lo hi upRead) (nextF : Family next (n+1) a b lo hi upRead)
    (sep : Distinct lo hi) (row : Entry Nat) (seen : row ∈ next)
    (already : row.1 ∈ old.map Prod.fst) : row ∈ old := by
  obtain ⟨i,lim,rfl|rfl⟩ := (nextF.cover row).mp seen
  · by_cases les : i < n
    · exact (prior.cover _).mpr ⟨i,les,Or.inl rfl⟩
    · have eq : i = n := by omega
      subst i; exact False.elim ((fresh prior sep).1 already)
  · by_cases les : i < n
    · exact (prior.cover _).mpr ⟨i,les,Or.inr rfl⟩
    · have eq : i = n := by omega
      subst i; exact False.elim ((fresh prior sep).2 already)

theorem future_rows (prior : Family old n a b lo hi upRead) (nextF : Family next (n+1) a b lo hi upRead)
    (row : Entry Nat) (seen : row ∈ next) (unseen : row.1 ∉ old.map Prod.fst) :
    row = lowerRow lo n ∨ row = upperRow hi upRead n := by
  obtain ⟨i,bound,eq|eq⟩ := (nextF.cover row).mp seen
  · subst row
    have no : ¬ i < n := fun h => unseen ((known prior).mpr ⟨i,h,Or.inl rfl⟩)
    have same : i = n := by omega
    exact Or.inl (same ▸ rfl)
  · subst row
    have no : ¬ i < n := fun h => unseen ((known prior).mpr ⟨i,h,Or.inr rfl⟩)
    have same : i = n := by omega
    exact Or.inr (same ▸ rfl)

theorem no_old_reads (prior : Family old n a b lo hi upRead) (nextF : Family next (n+1) a b lo hi upRead)
    (sep : Distinct lo hi) : NoBackReads (old.map Prod.fst) next := by
  intro before used known after listed unseen
  have pre := old_member prior nextF sep before used known
  obtain ⟨i,lim,kind⟩ := (prior.cover before).mp pre
  have future := future_rows prior nextF after listed unseen
  have upperRead := prior.upper_reads i lim
  have loNot (j : Nat) (h : j < n+1) :
      lo (n+1) ≠ lo j := Nat.ne_of_gt (sep.monotone h)
  have hiNot (j : Nat) : hi n ≠ lo j := (sep.split _ _).symm
  have noHigh : lo (n+1) ≠ b ∧ hi n ≠ b := by
    exact ⟨nextF.high_fresh _ ((nextF.cover _).mpr ⟨n,by omega,Or.inl rfl⟩),
      nextF.high_fresh _ ((nextF.cover _).mpr ⟨n,by omega,Or.inr rfl⟩)⟩
  rcases kind with rfl|rfl <;> rcases future with rfl|rfl
  · exact fun h => loNot i (by omega) ((reads_exact (lower_one lo i)).mp h)
  · exact fun h => hiNot i ((reads_exact (lower_one lo i)).mp h)
  · intro h
    have equal := (reads_exact (upper_one hi upRead i)).mp h
    exact upperRead.elim (fun e => loNot i (by omega) (equal.trans e)) (fun e => noHigh.1 (equal.trans e))
  · intro h
    have equal := (reads_exact (upper_one hi upRead i)).mp h
    exact upperRead.elim (fun e => hiNot i (equal.trans e)) (fun e => noHigh.2 (equal.trans e))

theorem exactly_two (prior : Family old n a b lo hi upRead) (nextF : Family next (n+1) a b lo hi upRead)
    (sep : Distinct lo hi) (row : Entry Nat) :
    row ∈ changes old next ↔ row = lowerRow lo n ∨ row = upperRow hi upRead n := by
  rw [GeneralRebaseFreshDelta283.member_exact (no_old_reads prior nextF sep)]
  constructor
  · rintro ⟨listed,no⟩; exact future_rows prior nextF row listed no
  · rintro (rfl|rfl)
    · exact ⟨(nextF.cover _).mpr ⟨n,by omega,Or.inl rfl⟩,(fresh prior sep).1⟩
    · exact ⟨(nextF.cover _).mpr ⟨n,by omega,Or.inr rfl⟩,(fresh prior sep).2⟩

theorem two_count (prior : Family old n a b lo hi upRead) (nextF : Family next (n+1) a b lo hi upRead)
    (sep : Distinct lo hi) : (changes old next).length = 2 := by
  have safe := GeneralRebaseDirtyHistory283.safe (old.map Prod.fst) next [] nextF.safe
  have nodup : ((changes old next).map Prod.fst).Nodup :=
    GeneralPresencePersistentSnapshot250.safe_nodup _ safe
  have pair : ([lo (n+1),hi n] : List Nat).Nodup := by simp [sep.split]
  have permutation : ((changes old next).map Prod.fst).Perm [lo (n+1),hi n] := by
    apply (List.perm_ext_iff_of_nodup nodup pair).mpr
    intro id
    constructor
    · intro present
      obtain ⟨row,member,equal⟩ := List.mem_map.mp present
      rcases (exactly_two prior nextF sep row).mp member with rfl|rfl
      · simp [← equal,lowerRow]
      · simp [← equal,upperRow]
    · intro present
      simp only [List.mem_cons,List.not_mem_nil,or_false] at present
      rcases present with rfl|rfl
      · exact List.mem_map.mpr ⟨lowerRow lo n,(exactly_two prior nextF sep _).mpr (Or.inl rfl),rfl⟩
      · exact List.mem_map.mpr ⟨upperRow hi upRead n,(exactly_two prior nextF sep _).mpr (Or.inr rfl),rfl⟩
  simpa using permutation.length_eq

end Yulang.GeneralRebaseTwoWrites283
