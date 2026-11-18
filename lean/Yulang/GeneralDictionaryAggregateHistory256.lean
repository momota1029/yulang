import Yulang.GeneralDictionaryReachableAggregate256
import Yulang.GeneralPresenceOrderedAppend256
namespace Yulang.GeneralDictionaryAggregateHistory256
open Core.PresenceGeneration
open GeneralPresenceDefinitionRewrite244 (Entry block)
open GeneralPresenceOrderedSubstitution247 (mapping)
open GeneralDictionaryLooseFamilyNames240 (lower)
open GeneralDictionaryLooseIterationBook240 (atoms plan)
open GeneralDictionaryReachableAggregate256

def tree : Nat → TyTerm Nat
 | 0 => .var 2
 | n+1 => .union (tree n) (tree n)

def entry (n : Nat) : Entry Nat :=
 (lower (n+1),.union (.var (lower n)) (.var (lower n)))

/-- Projection of the actually retained lower equations, in replay order.
It is not asserted to be the entire materialized owner frame. -/
def history : Nat → List (Entry Nat)
 | 0 => []
 | n+1 => history n ++ [entry n]

theorem block_in_source (n : Nat) : block (history n) ⊆ atoms n := by
 induction n with
 | zero => intro atom member; cases member
 | succ n ih =>
   intro atom member
   change atom ∈ (history n ++ [entry n]).flatMap _ at member
   rw [List.flatMap_append] at member
   rcases List.mem_append.mp member with prior | added
   · exact old_atoms n (ih prior)
   · have inEquation : atom ∈ GeneralNominalAllocation.equations (lower (n+1))
       (.union (.var (lower n)) (.var (lower n))) := by
       simpa only [List.flatMap_cons,List.flatMap_nil,List.append_nil,entry,GeneralPresenceDefinitionRewrite244.equations,GeneralNominalAllocation.equations] using added
     exact lower_equations n inEquation

theorem current_expansion (n : Nat) : (mapping (history n) (lower n)).ty = tree n := by
 induction n with
 | zero => rfl
 | succ n ih =>
   change (mapping (history n ++ [entry n]) (entry n).1).ty = tree (n+1)
   rw [GeneralPresenceOrderedAppend256.mapping_snoc]
   change TyTerm.union (mapping (history n) (lower n)).ty (mapping (history n) (lower n)).ty = _
   rw [ih]
   rfl

theorem targets_above (n : Nat) (e : Entry Nat) (member : e ∈ history n) : 4 < e.1 := by
 induction n with
 | zero => cases member
 | succ n ih =>
   rcases List.mem_append.mp member with prior | added
   · exact ih prior
   · cases List.mem_singleton.mp added
     exact GeneralDictionaryLooseFamilyNames240.lower_above n

theorem upper_fixed (n : Nat) : (mapping (history n) 4).ty = .var 4 := by
 apply GeneralPresenceOrderedSyntax247.mapping_outside
 intro e member
 have above := targets_above n e member
 omega

theorem tree_atoms (n : Nat) (atom : TyTerm Nat) :
 atom ∈ GeneralPresenceUnionNormal252.atoms (tree n) ↔ atom = .var 2 := by
 induction n with
 | zero => simp [tree,GeneralPresenceUnionNormal252.atoms]
 | succ n ih => simp [tree,GeneralPresenceUnionNormal252.atoms,ih]

def pool : List (TyTerm Nat) := [.var 2,.var 4]

theorem tree_normal (n : Nat) : GeneralPresenceUnionNormal252.normalize pool (tree n) = .var 2 := by
 have same := GeneralPresenceNormalFinite252.union_atoms_same pool (tree n) (.var 2)
   (fun atom => (tree_atoms n atom).trans (by simp [GeneralPresenceUnionNormal252.atoms]))
 exact same

theorem endpoint_supported (n : Nat) :
 GeneralNominalHistoricalAggregate256.EndpointSupported pool (history n)
   (GeneralNominalFrameAggregate256.pairs (plan n) 0) := by
 rw [pairs_exact]
 constructor
 · intro pair member atom present
   have equal : pair = (lower n,4) := by simpa only [List.mem_cons,List.not_mem_nil,or_false,or_self] using member
   subst pair
   change atom ∈ GeneralPresenceUnionNormal252.atoms (mapping (history n) (lower n)).ty at present
   rw [current_expansion] at present
   cases (tree_atoms n atom).mp present
   exact List.mem_cons_self ..
 · intro pair member atom present
   have equal : pair = (lower n,4) := by simpa only [List.mem_cons,List.not_mem_nil,or_false,or_self] using member
   subst pair
   change atom ∈ GeneralPresenceInterNormal252.atoms (mapping (history n) 4).ty at present
   rw [upper_fixed] at present
   cases List.mem_singleton.mp present
   exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

theorem rewritten (n : Nat) :
 GeneralNominalHistoricalAggregate256.rewrite pool (history n)
   (GeneralNominalFrameAggregate256.pairs (plan n) 0) = representative := by
 rw [pairs_exact]
 change GeneralNominalRebaseProjectionView243.Bounds.mk
   (GeneralPresenceUnionNormal252.normalize pool (.union (mapping (history n) (lower n)).ty (mapping (history n) (lower n)).ty))
   (GeneralPresenceInterNormal252.normalize pool (.inter (mapping (history n) 4).ty (mapping (history n) 4).ty)) = _
 rw [current_expansion,upper_fixed]
 change GeneralNominalRebaseProjectionView243.Bounds.mk
   (GeneralPresenceUnionNormal252.normalize pool (tree (n+1))) _ = _
 rw [tree_normal]
 rfl

theorem prepared (n : Nat) :
 GeneralNominalHistoricalAggregate256.prepare pool (history n)
   (GeneralNominalFrameAggregate256.pairs (plan n) 0) = some representative := by
 apply (GeneralNominalHistoricalAggregate256.prepare_exact ..).mpr
 refine ⟨?_,endpoint_supported n,(rewritten n).symm⟩
 rw [pairs_exact]
 simp
end Yulang.GeneralDictionaryAggregateHistory256
