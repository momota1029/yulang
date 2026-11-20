import Yulang.GeneralRebaseQuestionFootprint298
import Yulang.GeneralFiniteAssignment246

namespace Yulang.GeneralRebasePackedAnswers298
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty)
open GeneralRebaseQuestionFootprint298 (Footprint agrees question question_exact prior prior_exact)
open GeneralRebaseSymbolicQuestions298 (Body)
open GeneralNominalRebaseJournalView243 (Journal)

def unique : List Nat → List Nat
 | [] => []
 | n :: rest =>
   let tail := unique rest
   if n ∈ tail then tail else n :: tail

theorem unique_mem (names : List Nat) (n : Nat) : n ∈ unique names ↔ n ∈ names := by
  induction names with
  | nil => rfl
  | cons a tail ih =>
    by_cases present : a ∈ unique tail
    · simp only [unique,present,ite_true,List.mem_cons]
      exact ⟨fun h => Or.inr (ih.mp h),fun h => h.elim (fun e => e.symm ▸ present) ih.mpr⟩
    · simp only [unique,present,ite_false,List.mem_cons,ih]

theorem unique_nodup (names : List Nat) : (unique names).Nodup := by
  induction names with
  | nil => exact List.nodup_nil
  | cons a tail ih =>
    by_cases inTail : a ∈ unique tail
    · simpa only [unique,inTail,ite_true] using ih
    · simpa only [unique,inTail,ite_false] using List.nodup_cons.mpr ⟨inTail,ih⟩

theorem key_injective (names : List Nat) : Function.Injective (unique names).get := by
  intro i j equal
  apply Fin.ext
  exact (List.Nodup.getElem_inj (unique_nodup names)).mp equal

structure Vector (f : Footprint) where
  types : Fin (unique f.types).length → Ty
  rows : Fin (unique f.rows).length → Common.Row

def pack (f : Footprint) (a : Assignment) : Vector f :=
  ⟨fun i => (a ((unique f.types).get i)).1,fun i => (a ((unique f.rows).get i)).2⟩

def fill (f : Footprint) (x : Vector f) (fallback : Assignment) : Assignment :=
  fun n => ⟨GeneralFiniteAssignment246.finite (unique f.types).get x.types (fun k => (fallback k).1) n,
            GeneralFiniteAssignment246.finite (unique f.rows).get x.rows (fun k => (fallback k).2) n⟩

theorem type_at (f : Footprint) (x : Vector f) (fallback : Assignment) (i : Fin (unique f.types).length) :
    (fill f x fallback ((unique f.types).get i)).1 = x.types i :=
  GeneralFiniteAssignment246.finite_at _ (key_injective f.types) x.types _ i

theorem row_at (f : Footprint) (x : Vector f) (fallback : Assignment) (i : Fin (unique f.rows).length) :
    (fill f x fallback ((unique f.rows).get i)).2 = x.rows i :=
  GeneralFiniteAssignment246.finite_at _ (key_injective f.rows) x.rows _ i

theorem unpack_pack (f : Footprint) (x : Vector f) (fallback : Assignment) : pack f (fill f x fallback) = x := by
  cases x with
  | mk tc rc =>
    unfold pack
    congr 1
    · funext i; exact type_at f _ fallback i
    · funext i; exact row_at f _ fallback i

theorem retain (f : Footprint) (a fallback : Assignment) :
    agrees f (fill f (pack f a) fallback) a := by
  constructor
  · intro n seen
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp ((unique_mem f.types n).mpr seen)
    exact type_at f _ fallback i
  · intro n seen
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp ((unique_mem f.rows n).mpr seen)
    exact row_at f _ fallback i

theorem fallback_irrelevant (f : Footprint) (x : Vector f) (a b : Assignment) :
    agrees f (fill f x a) (fill f x b) := by
  constructor
  · intro n seen
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp ((unique_mem f.types n).mpr seen)
    exact (type_at f x a i).trans (type_at f x b i).symm
  · intro n seen
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp ((unique_mem f.rows n).mpr seen)
    exact (row_at f x a i).trans (row_at f x b i).symm

theorem check_same (j : Journal) (q : Body) (a fallback : Assignment) :
    q.Holds j (fill (question j q) (pack (question j q) a) fallback) ↔ q.Holds j a :=
  question_exact j q _ _ (retain _ _ _)

theorem same_vector (j : Journal) (q : Body) (a b : Assignment)
    (same : pack (question j q) a = pack (question j q) b) : q.Holds j a ↔ q.Holds j b := by
  have x := check_same j q a a
  rw [same] at x
  exact x.symm.trans (check_same j q b a)

theorem asked_iff (j : Journal) (q : Body) (fallback : Assignment) :
    (∃ a, q.Holds j a) ↔
    ∃ v : Vector (question j q), q.Holds j (fill (question j q) v fallback) :=
  ⟨fun ⟨a,held⟩ => ⟨pack _ a,(check_same j q a fallback).mpr held⟩,
    fun ⟨v,held⟩ => ⟨fill _ v fallback,held⟩⟩

theorem valid_prior_iff (j : Journal) (fallback : Assignment) :
    (∃ a, j.Models a) ↔ ∃ v : Vector (prior j), j.Models (fill (prior j) v fallback) :=
  ⟨fun ⟨a,held⟩ => ⟨pack _ a,(prior_exact j _ _ (retain _ _ _)).mpr held⟩,
    fun ⟨v,held⟩ => ⟨fill _ v fallback,held⟩⟩

end Yulang.GeneralRebasePackedAnswers298
