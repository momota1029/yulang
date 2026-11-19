import Yulang.GeneralRebaseOneOutputFacts270
import Yulang.GeneralRebaseCompression266

namespace Yulang.GeneralRebaseOneOutputProjection270
open GeneralNominalCenters (Plan)
open GeneralSourceState (Output)
open GeneralRebaseStep258 (Fact)
open GeneralRebaseCompression266 (Basis)
open GeneralRebaseUniversalBasis263 (bodyKey)
open GeneralRebaseOneOutputFacts270 (pairKey synchronized)
open GeneralRebaseLiveProjection264 (project liveFacts)
open GeneralRebaseMultiSelection263 (ofPlan)
open GeneralRebaseBodyTable261 (schema)
open GeneralNominalVersionedJournal232 (State)

theorem basis_two (owner : Nat) (output : Output) :
 Basis [owner] [output] = [bodyKey owner output,pairKey owner output] := by
 simp [Basis,GeneralRebaseUniversalBasis263.basis,GeneralRebaseUniversalBasis263.ownerFacts,
   GeneralRebasePairKeys261.facts,pairKey]

theorem remaining_cases (state : State roles) (owner : Nat) (output : Output)
 (equations : ∀ p ∈ state.plans, (ofPlan p).owner = owner → (schema p output).equations.length = 1) :
 (project [owner] [output] state).remaining = [] ∨
 (project [owner] [output] state).remaining = Basis [owner] [output] := by
 have synchronization := synchronized state owner output equations
 change (Basis [owner] [output]).filter (fun f => !(liveFacts state).contains f) = [] ∨
   (Basis [owner] [output]).filter (fun f => !(liveFacts state).contains f) = _
 rw [basis_two]
 by_cases present : bodyKey owner output ∈ liveFacts state
 · have pairs := synchronization.mp present
   left
   simp [present,pairs]
 · have noPairs : pairKey owner output ∉ liveFacts state := fun pair => present (synchronization.mpr pair)
   right
   simp [present,noPairs]

end Yulang.GeneralRebaseOneOutputProjection270
