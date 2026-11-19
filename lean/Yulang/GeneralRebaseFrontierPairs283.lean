import Yulang.GeneralRebaseArchiveUnbounded283

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseFrontierPairs283
open GeneralSourceState (Output)
open GeneralRebaseClassFrontier283 (fresh fresh_exact pairs pairs_exact pairAtoms)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters (Plan)
open GeneralNominalRebaseClassView243 (View equations)
open GeneralNominalRebaseRawView243 (read)
open GeneralRebaseClassDelta283 (Growth)
open Core.PresenceGeneration (CompTerm)

local instance : DecidableEq Output := fun a b =>
  if h : a.name = b.name ∧ a.target = b.target then
    isTrue (by cases a; cases b; cases h; congr)
  else isFalse (fun eq => h ⟨congrArg Output.name eq,congrArg Output.target eq⟩)

def old (prev next : List Output) := next.filter (fun o => o ∈ prev)

def products (left right : List Output) : List (Output × Output) :=
  left.flatMap (fun a => right.map (a,·))

def fast (prev next : List Output) : List (Output × Output) :=
  let arrived := fresh prev next
  if arrived.isEmpty then []
  else products arrived next ++ products (old prev next) arrived

theorem product_exact (left right : List Output) (a b : Output) :
    (a,b) ∈ products left right ↔ a ∈ left ∧ b ∈ right := by simp [products]

theorem exact_pairs (prev next : List Output) (a b : Output) :
    (a,b) ∈ fast prev next ↔ (a,b) ∈ pairs prev next := by
  unfold fast
  cases seen : fresh prev next with
  | nil =>
    simp only [List.isEmpty_nil,ite_true,List.not_mem_nil,false_iff]
    intro pair
    have h := (pairs_exact prev next a b).mp pair
    rcases h.2.2 with left|right
    · have some := (fresh_exact prev next a).mpr ⟨h.1,left⟩
      rw [seen] at some; cases some
    · have some := (fresh_exact prev next b).mpr ⟨h.2.1,right⟩
      rw [seen] at some; cases some
  | cons head tail =>
    simp only [List.isEmpty_cons,Bool.false_eq_true,ite_false]
    rw [← seen]
    simp only [List.mem_append,product_exact,fresh_exact,pairs_exact]
    have old_exact : a ∈ old prev next ↔ a ∈ next ∧ a ∈ prev := by simp [old]
    rw [old_exact]
    constructor
    · rintro (⟨⟨ha,notA⟩,hb⟩|⟨⟨ha,_⟩,hb,notB⟩)
      · exact ⟨ha,hb,Or.inl notA⟩
      · exact ⟨ha,hb,Or.inr notB⟩
    · rintro ⟨ha,hb,notA|notB⟩
      · exact Or.inl ⟨⟨ha,notA⟩,hb⟩
      · by_cases seenA : a ∈ prev
        · exact Or.inr ⟨⟨ha,seenA⟩,hb,notB⟩
        · exact Or.inl ⟨⟨ha,seenA⟩,hb⟩

theorem product_count (left right : List Output) : (products left right).length = left.length * right.length := by
  induction left with
  | nil => simp [products]
  | cons head tail ih =>
    change (right.map (head,·) ++ products tail right).length = (tail.length+1)*right.length
    rw [List.length_append,List.length_map,ih,Nat.succ_mul,Nat.add_comm]

theorem fast_count (prev next : List Output) :
    (fast prev next).length ≤ (fresh prev next).length * (2 * next.length) := by
  have atMost := List.length_filter_le (fun o : Output => decide (o ∈ prev)) next
  simp only [fast]
  split
  · exact Nat.zero_le _
  · rw [List.length_append,product_count,product_count,Nat.mul_comm (old prev next).length]
    have small : (old prev next).length ≤ next.length := atMost
    apply Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left (fresh prev next).length small) _)
    rw [← Nat.mul_add]
    exact Nat.le_of_eq (by congr 1; omega)

def compile (plan : Plan roles) (mapping : Nat → CompTerm Nat) (prev next : List Output) : View :=
  ⟨equations plan mapping (fresh prev next),(fast prev next).flatMap (pairAtoms mapping)⟩

theorem exact (plan : Plan roles) (mapping : Nat → CompTerm Nat) (prev next : List Output) (base : Assignment) :
    (compile plan mapping prev next).Holds base ↔ Growth plan (read mapping base) (· ∈ prev) (· ∈ next) := by
  refine Iff.trans ?_ (GeneralRebaseClassFrontier283.exact plan mapping prev next base)
  unfold View.Holds compile GeneralRebaseClassFrontier283.compile PresenceNormalForm.All
  apply and_congr Iff.rfl
  simp only [List.forall_mem_flatMap]
  constructor <;> intro held pair used <;> obtain ⟨a,b⟩ := pair
  · exact held _ ((exact_pairs prev next a b).mpr used)
  · exact held _ ((exact_pairs prev next a b).mp used)


noncomputable def actual (before next : GeneralNominalCenteredSteps.State roles)
    (prior : GeneralNominalVersionedJournal232.Effect roles) (mapping : Nat → CompTerm Nat) : View :=
  compile prior.plan mapping
    (GeneralNominalCenteredHeadOutputs.requests before prior.plan.packet.site.occurrence)
    (GeneralNominalCenteredHeadOutputs.requests next prior.plan.packet.site.occurrence)

theorem actual_iff (before next : GeneralNominalCenteredSteps.State roles)
    (prior : GeneralNominalVersionedJournal232.Effect roles) (mapping : Nat → CompTerm Nat) (base : Assignment) :
    (actual before next prior mapping).Holds base ↔
      (GeneralRebaseClassMutation283.frontier before next prior mapping).Holds base :=
  (exact prior.plan mapping _ _ base).trans (GeneralRebaseClassFrontier283.exact prior.plan mapping _ _ base).symm

end Yulang.GeneralRebaseFrontierPairs283
