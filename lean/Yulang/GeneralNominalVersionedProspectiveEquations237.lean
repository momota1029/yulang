import Yulang.GeneralNominalVersionedHistoryEquations237
/-! The actual historical and one current packet's aggregate equations admit
one common assignment. No full Models, selected success, or install is claimed. -/
namespace Yulang.GeneralNominalVersionedProspectiveEquations237
open GeneralNominalVersionedJournal232 GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedMixedSeedLedger237 (Recorded)
variable {roles : Roles.RoleDecls}
/-- An auxiliary equation ledger, explicitly NOT an operational successor. -/
def ledger (state : State roles) (plan : Plan roles) : State roles :=
 {state with plans := plan :: state.plans}

theorem recorded (previous : Recorded state)
 (current : plan.packet.context = state.core.erased.current.context) : Recorded (ledger state plan) := by
 intro prior member
 rcases List.mem_cons.mp member with rfl | member
 · exact congrArg (fun context => context.state.seed) current
 · exact previous prior member

noncomputable def solution (state : State roles) (plan : Plan roles) (base : Assignment) : Assignment :=
 GeneralNominalVersionedHistoryEquations237.solution (ledger state plan) base

theorem simultaneous (previous : Recorded state)
 (current : plan.packet.context = state.core.erased.current.context) (base : Assignment) :
 PresenceNormalForm.All CommonNominalFullCarrier.model (solution state plan base)
   (GeneralNominalVersionedAllocation231.merges plan.packet.context.state plan.packet.registry
     plan.packet.site.occurrence.identity plan.packet.declaration plan.packet.bindings) ∧
 (∀ prior ∈ state.plans, PresenceNormalForm.All CommonNominalFullCarrier.model (solution state plan base)
   (GeneralNominalVersionedAllocation231.merges prior.packet.context.state prior.packet.registry
     prior.packet.site.occurrence.identity prior.packet.declaration prior.packet.bindings)) := by
 have all := GeneralNominalVersionedHistoryEquations237.all_merges (recorded previous current) base
 exact ⟨all plan (List.mem_cons_self ..),fun prior member => all prior (List.mem_cons_of_mem _ member)⟩

theorem source_simultaneous
 (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (current : plan.packet.context = state.core.erased.current.context) (base : Assignment) :
 PresenceNormalForm.All CommonNominalFullCarrier.model (solution state plan base)
   (GeneralNominalVersionedAllocation231.merges plan.packet.context.state plan.packet.registry
     plan.packet.site.occurrence.identity plan.packet.declaration plan.packet.bindings) ∧
 (∀ prior ∈ state.plans, PresenceNormalForm.All CommonNominalFullCarrier.model (solution state plan base)
   (GeneralNominalVersionedAllocation231.merges prior.packet.context.state prior.packet.registry
     prior.packet.site.occurrence.identity prior.packet.declaration prior.packet.bindings)) :=
 simultaneous (GeneralNominalVersionedMixedSeedLedger237.reachable path) current base

theorem rows (state : State roles) (plan : Plan roles) (base : Assignment) (identity : Nat) :
 (solution state plan base identity).2 = (base identity).2 := rfl
end Yulang.GeneralNominalVersionedProspectiveEquations237
