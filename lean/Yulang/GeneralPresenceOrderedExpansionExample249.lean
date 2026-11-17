import Yulang.GeneralPresenceOrderedExpansion249
import Yulang.GeneralPresenceOrderedCheck247

/-! A finite compiled-block regression with a genuinely new target. This is
not a reachable source execution. Row-only reads of the new target remain
permitted because solve preserves every row component. -/
namespace Yulang.GeneralPresenceOrderedExpansionExample249
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedSubstitution247 GeneralPresenceOrderedDependence247
open GeneralPresenceOrderedExpansion249 GeneralPresenceConsumerSupport246

def old : List (Entry Nat) := [(2,.var 0)]
def fresh : List (Entry Nat) := [(2,.var 1),(3,.pair (.var 2) (.var 0))]
def consumers : List (Atom Nat) :=
 [.tyLe (.var 2) (.var 1),.rowLe (.var 3) (.join (.var 3) .empty)]
def sharedNames (name : Nat) : Prop := name ≠ 2 ∧ name ≠ 3

theorem old_safe : SafeOrder old := by
 simp [old,SafeOrder,GeneralPresenceUsedSupport245.typedReads]

theorem fresh_safe : SafeOrder fresh := by
 simp [fresh,SafeOrder,GeneralPresenceUsedSupport245.typedReads]

theorem not_within : ¬ TargetsWithin fresh old := by
 intro within
 obtain ⟨entry,present,equal⟩ := within (3,.pair (.var 2) (.var 0)) (by simp [fresh])
 have found : entry = (2,TyTerm.var 0) := by simpa [old] using present
 subst entry
 cases equal

theorem rewritten : rewrite old consumers =
 [.tyLe (.var 0) (.var 1),.rowLe (.var 3) (.join (.var 3) .empty)] := rfl

theorem protected_reads : Protected old fresh consumers := by
 intro name member entry present
 rw [rewritten] at member
 simp only [listTypedReads,List.flatMap_cons,List.flatMap_nil,atomTypedReads,
   GeneralPresenceUsedSupport245.typedReads,List.append_nil,List.singleton_append,
   List.mem_cons,List.not_mem_nil,or_false] at member
 have targets : entry.1 = 2 ∨ entry.1 = 3 := by
   simp only [fresh,List.mem_cons,List.not_mem_nil,or_false] at present
   rcases present with rfl | rfl <;> simp
 rcases member with rfl | rfl <;> rcases targets with equal | equal <;> omega

theorem old_private : ∀ name, sharedNames name → ∀ entry ∈ old, entry.1 ≠ name := by
 intro name shared entry member
 have found : entry = (2,TyTerm.var 0) := by simpa [old] using member
 subst entry
 exact Ne.symm shared.1

theorem fresh_private : ∀ name, sharedNames name → ∀ entry ∈ fresh, entry.1 ≠ name := by
 intro name shared entry member
 simp only [fresh,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl
 · exact Ne.symm shared.1
 · exact Ne.symm shared.2

theorem public_models_iff (boundary : Nat → Comp CommonNominalFullCarrier.model) :
 (∃ assignment, All CommonNominalFullCarrier.model assignment (consumers ++ block old) ∧
   GeneralPresenceOrderedRebase247.Agrees CommonNominalFullCarrier.model sharedNames assignment boundary) ↔
 (∃ assignment, All CommonNominalFullCarrier.model assignment (rewrite old consumers ++ block fresh) ∧
   GeneralPresenceOrderedRebase247.Agrees CommonNominalFullCarrier.model sharedNames assignment boundary) :=
 common_public_models_iff old fresh old_safe fresh_safe consumers protected_reads sharedNames old_private fresh_private boundary
end Yulang.GeneralPresenceOrderedExpansionExample249
