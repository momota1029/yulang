import Yulang.GeneralDeclarativeNestedSiblingsFrame332
import Yulang.GeneralCanonicalChildOrder

set_option maxRecDepth 16000
set_option maxHeartbeats 12000000
namespace Yulang.C334OrderedRawCut
open GeneralDeclarations (Declaration DeclarationChecked Clause)
open GeneralDeclarativeNestedSiblingsDecl332 (impl clauseTwo impl_checked registry)
open GeneralDeclarativeNestedSiblingsFrame332 (stage keep targets)
open GeneralDeclarativeNestedDecl332 (root)
open GeneralDeclarativeNestedExample332 (interpretation)
open GeneralDeclarativeNestedFrame332 (spans fallback)
open GeneralDeclarativePairDecl326 (clause)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarationExamples (constructors roles)
open GeneralDeclarativeNestedBody332 (compileBody)
open GeneralCanonicalChildOrder (canonicalDeclaration canonicalRequirements canonicalRequirements_eq)

abbrev backwards : Declaration := {impl with requirements := [clauseTwo,clause]}

theorem backwards_checked : DeclarationChecked constructors roles backwards :=
  GeneralRegistryReordering.checked_permute_requirements impl _ (.swap _ _ []) impl_checked

def targetsIn (xs : List Demand) : List (List Nat) := xs.map (fun d => d.outputs.map (·.target))

def emittedTargets (d : Declaration) : Option (List (List Nat)) :=
  (compileBody registry interpretation root d stage spans keep fallback targets).map (targetsIn ∘ Prod.snd)

theorem original_order : canonicalDeclaration impl = impl := by
  have sorted : List.Pairwise (fun a b : Clause => decide (a.id ≤ b.id) = true) impl.requirements := by
    refine List.pairwise_cons.mpr ⟨?_,.cons (fun _ h => (List.not_mem_nil h).elim) .nil⟩
    intro a member
    cases List.mem_singleton.mp member
    decide +kernel
  unfold canonicalDeclaration canonicalRequirements
  rw [List.mergeSort_of_pairwise sorted]

theorem restored_order : canonicalDeclaration backwards = impl := by
  have same : canonicalRequirements impl.requirements = canonicalRequirements backwards.requirements :=
    canonicalRequirements_eq _ _ impl_checked.identified.1 (.swap _ _ [])
  calc
    canonicalDeclaration backwards = canonicalDeclaration impl := by
      unfold canonicalDeclaration
      change {backwards with requirements := canonicalRequirements backwards.requirements} =
        {impl with requirements := canonicalRequirements impl.requirements}
      rw [← same]
    _ = impl := original_order

/-- Actual declared-order compilation swaps two same-role requests that
have distinct fixed targets. This projection doesn't assume allocated span
names are equal across each compile. -/
theorem actual_order_cut :
  emittedTargets impl = some [[5],[10]] ∧
  emittedTargets backwards = some [[10],[5]] ∧
  canonicalDeclaration backwards = impl ∧ canonicalDeclaration impl = impl :=
  ⟨rfl,rfl,restored_order,original_order⟩

theorem raw_canonical_input_repairs_this_order :
    emittedTargets (canonicalDeclaration backwards) = some [[5],[10]] := by
  rw [restored_order]
  rfl

def boundsIn (xs : List Demand) : List (List (Nat × Nat × Nat)) :=
  xs.map (fun d => d.arguments.map fun a => (a.lower,a.center,a.upper))

def emittedBounds (d : Declaration) : Option (List (List (Nat × Nat × Nat))) :=
  (compileBody registry interpretation root d stage spans keep fallback targets).map (boundsIn ∘ Prod.snd)

/-- In this fixture, the allocator keeps each complete child request,
including the exact endpoint and center names; only the two visits
exchange position. This is a computed case, not a general permutation law. -/
theorem actual_names_follow_order :
    emittedBounds impl = some [[(18,3,19)],[(20,11,21)]] ∧
    emittedBounds backwards = some [[(20,11,21)],[(18,3,19)]] :=
  ⟨rfl,rfl⟩

def emittedChildren (d : Declaration) : Option (List Demand) :=
  (compileBody registry interpretation root d stage spans keep fallback targets).map Prod.snd

theorem fixture_reverses_full_requests :
    emittedChildren backwards = (emittedChildren impl).map List.reverse := rfl

end Yulang.C334OrderedRawCut

#print axioms Yulang.C334OrderedRawCut.backwards_checked
#print axioms Yulang.C334OrderedRawCut.actual_order_cut
#print axioms Yulang.C334OrderedRawCut.raw_canonical_input_repairs_this_order
#print axioms Yulang.C334OrderedRawCut.actual_names_follow_order
#print axioms Yulang.C334OrderedRawCut.fixture_reverses_full_requests
