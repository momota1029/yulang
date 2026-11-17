import Yulang.GeneralPresencePersistentSnapshot250
/-! A finite fixed target reservation uses bottom only as an unobservable
initial value. It is not a constraint on public types or a bound on owners. -/
namespace Yulang.GeneralPresenceReserveBlock250
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedDedup247 GeneralPresenceUsedSupport245
variable {Name : Type} [DecidableEq Name]

def reserve (names : List Name) : List (Entry Name) := dedup (names.map (fun name => (name,.bottom)))

omit [DecidableEq Name] in
theorem coherent (names : List Name) : GeneralPresenceOwnerRewrite244.Coherent (names.map (fun name => (name,TyTerm.bottom))) := by
 intro first one last two _
 obtain ⟨a,_,rfl⟩ := List.mem_map.mp one
 obtain ⟨b,_,rfl⟩ := List.mem_map.mp two
 rfl

theorem member_iff (names : List Name) (entry : Entry Name) : entry ∈ reserve names ↔ entry.1 ∈ names ∧ entry.2 = .bottom := by
 constructor
 · intro member
   obtain ⟨name,present,rfl⟩ := List.mem_map.mp (dedup_subset _ member)
   exact ⟨present,rfl⟩
 · rintro ⟨member,equal⟩
   apply member_preserved _ (coherent names)
   exact List.mem_map.mpr ⟨entry.1,member,Prod.ext rfl equal.symm⟩

theorem safe (names : List Name) : SafeOrder (reserve names) := by
 apply GeneralPresenceOrderedSupport247.safe_independent _ (targets_nodup _)
 intro target _ rhs member
 rw [(member_iff names rhs).mp member |>.2]
 simp [typedReads]

omit [DecidableEq Name] in
theorem safe_append (old fresh : List (Entry Name)) (oldSafe : SafeOrder old) (freshSafe : SafeOrder fresh)
 (distinct : ∀ a ∈ old, ∀ b ∈ fresh, b.1 ≠ a.1)
 (unread : ∀ a ∈ old, ∀ b ∈ fresh, b.1 ∉ typedReads a.2) : SafeOrder (old ++ fresh) := by
 induction old with
 | nil => exact freshSafe
 | cons head rest ih =>
   refine ⟨oldSafe.1,?_,?_,?_⟩
   · intro later member
     rcases List.mem_append.mp member with member | member
     · exact oldSafe.2.1 later member
     · exact distinct head (by simp) later member
   · intro later member
     rcases List.mem_append.mp member with member | member
     · exact oldSafe.2.2.1 later member
     · exact unread head (by simp) later member
   · exact ih oldSafe.2.2.2
       (fun a am => distinct a (List.mem_cons_of_mem _ am))
       (fun a am => unread a (List.mem_cons_of_mem _ am))

def support (old : List (Entry Name)) : List Name := old.flatMap (fun e => e.1 :: typedReads e.2)

theorem append_safe (old : List (Entry Name)) (oldSafe : SafeOrder old) (names : List Name)
 (fresh : ∀ name ∈ names, name ∉ support old) : SafeOrder (old ++ reserve names) := by
 apply safe_append old _ oldSafe (safe names)
 · intro a am b bm equal
   exact fresh b.1 ((member_iff names b).mp bm).1
     (List.mem_flatMap.mpr ⟨a,am,by simp [equal]⟩)
 · intro a am b bm read
   exact fresh b.1 ((member_iff names b).mp bm).1
     (List.mem_flatMap.mpr ⟨a,am,List.mem_cons_of_mem _ read⟩)
end Yulang.GeneralPresenceReserveBlock250
