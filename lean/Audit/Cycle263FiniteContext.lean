import Yulang.GeneralRebaseFiniteStates263
import Yulang.GeneralRebaseSourceLocalMeaning263
namespace Yulang.Cycle263FiniteContext
open GeneralRebaseSourceRepresentatives263 (RegisteredAt)
open GeneralRebaseSourceLocalHeads263 (RepresentativeHeads)
open GeneralRebaseUniversalObserver263 (Current)

/-- The inspector-wide part of the local context is exactly a finite image
quantifier. Semantic satisfaction and source reachability remain separate. -/
theorem context_exact (base : GeneralNominalCommonBridge.Assignment → Prop)
 (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence roles)
 (start : GeneralNominalVersionedJournal232.State roles)
 (inhabited : ∃ owner plan, RegisteredAt registry root start owner plan)
 (owners : List Nat) (pool : List GeneralSourceState.Output)
 (inspect : Current owners pool → GeneralNominalVersionedJournal232.State roles)
 (assignment : GeneralNominalCommonBridge.Assignment) :
 GeneralRebaseSourceLocalMeaning263.Context base registry root start inhabited owners inspect assignment ↔
 base assignment ∧ RepresentativeHeads registry root start inhabited owners assignment ∧
 ∀ snapshot ∈ (GeneralRebaseFiniteStates263.states (GeneralRebaseUniversalBasis263.basis owners pool)).map inspect,
 GeneralRebaseSourceCenters263.Heads snapshot assignment := by
 unfold GeneralRebaseSourceLocalMeaning263.Context
 rw [GeneralRebaseFiniteStates263.heads_image_iff]
#print axioms context_exact
end Yulang.Cycle263FiniteContext
