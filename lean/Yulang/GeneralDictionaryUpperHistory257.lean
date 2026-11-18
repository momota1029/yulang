import Yulang.GeneralDictionaryAggregateHistory256
namespace Yulang.GeneralDictionaryUpperHistory257
open Core.PresenceGeneration
open GeneralDictionaryLooseFamilyNames240 (lower upper)
open GeneralDictionaryLooseIterationBook240 (atoms packet)
open GeneralPresenceDefinitionRewrite244 (Entry block)
open GeneralPresenceOrderedSubstitution247 (mapping)

def upperEntry (n : Nat) : Entry Nat := (upper n,.inter (.var 4) (.var 4))
def lowerEntry (n : Nat) : Entry Nat := GeneralDictionaryAggregateHistory256.entry n

def history : Nat → List (Entry Nat)
 | 0 => []
 | n+1 => history n ++ [lowerEntry n,upperEntry n]

theorem upper_equations (n : Nat) :
 GeneralNominalAllocation.equations (upper n) (.inter (.var 4) (.var 4)) ⊆ atoms (n+1) := by
 intro atom member
 change atom ∈ atoms n ++ GeneralNominalVersionedInstallation231.atoms (packet n)
 apply List.mem_append_right
 apply List.mem_append_left
 apply List.mem_append_right
 rw [GeneralDictionaryLooseFamilyPacket240.bindings_exact]
 change atom ∈ ((GeneralNominalAllocation.equations (lower (n+1)) (.union (.var (lower n)) (.var (lower n))) ++
   GeneralNominalAllocation.equations (upper n) (.inter (.var 4) (.var 4))) ++
   (GeneralNominalAllocation.equations (lower (n+1)) (.union (.var (lower n)) (.var (lower n))) ++
   GeneralNominalAllocation.equations (upper n) (.inter (.var 4) (.var 4))))
 exact List.mem_append_left _ (List.mem_append_right _ member)

theorem block_in_source (n : Nat) : block (history n) ⊆ atoms n := by
 induction n with
 | zero => intro atom member; cases member
 | succ n ih =>
   intro atom member
   change atom ∈ (history n ++ [lowerEntry n,upperEntry n]).flatMap _ at member
   rw [List.flatMap_append] at member
   rcases List.mem_append.mp member with old | fresh
   · exact GeneralDictionaryReachableAggregate256.old_atoms n (ih old)
   · change atom ∈ GeneralNominalAllocation.equations (lower (n+1)) (.union (.var (lower n)) (.var (lower n))) ++
       GeneralNominalAllocation.equations (upper n) (.inter (.var 4) (.var 4)) ++ [] at fresh
     rw [List.append_nil] at fresh
     rcases List.mem_append.mp fresh with lo | hi
     · exact GeneralDictionaryReachableAggregate256.lower_equations n lo
     · exact upper_equations n hi

theorem targets_above (n : Nat) (e : Entry Nat) (member : e ∈ history n) : 4 < e.1 := by
 induction n with
 | zero => cases member
 | succ n ih =>
   rcases List.mem_append.mp member with old | fresh
   · exact ih old
   · simp only [List.mem_cons,List.not_mem_nil,or_false] at fresh
     rcases fresh with rfl | rfl
     · exact GeneralDictionaryLooseFamilyNames240.lower_above n
     · exact GeneralDictionaryLooseFamilyNames240.upper_above n

theorem initial_fixed (n name : Nat) (small : name ≤ 4) :
 (mapping (history n) name).ty = .var name := by
 apply GeneralPresenceOrderedSyntax247.mapping_outside
 intro e member
 have above := targets_above n e member
 omega
end Yulang.GeneralDictionaryUpperHistory257
