import Yulang.GeneralNominalCenters

/-! Syntactic center coherence, separate from candidate compatibility.
Equal historical/current child arguments force equal variable centers when
allocation metadata and the declaration agree. -/
namespace Yulang.GeneralNominalCenterCoherence184
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters

variable {roles : Roles.RoleDecls}

theorem binder_equal (first last : Plan roles)
    (seed : first.packet.context.state.seed = last.packet.context.state.seed)
    (invocation : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
    (declaration : first.packet.declaration = last.packet.declaration) (name : Nat)
    (inputs : (GeneralNominalPacketSupport.capture first.packet).inputs name =
      (GeneralNominalPacketSupport.capture last.packet).inputs name) :
    first.binder name = last.binder name := by
  unfold Plan.binder
  dsimp only
  rw [declaration,inputs]
  split
  · change fresh first.packet.context.state.seed first.packet.site.occurrence.identity
      first.packet.declaration.id 2 name 0 = fresh last.packet.context.state.seed
      last.packet.site.occurrence.identity last.packet.declaration.id 2 name 0
    rw [seed,invocation,declaration]
  · split
    · rfl
    · rw [seed,invocation]

theorem emitted_equal (first last : Plan roles)
    (seed : first.packet.context.state.seed = last.packet.context.state.seed)
    (invocation : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
    (declaration : first.packet.declaration = last.packet.declaration)
    (clause position : Nat) (pattern : GeneralDeclarationPatterns.Pattern)
    (inputs : GeneralDeclarationDemands.inputInterval (GeneralNominalPacketSupport.capture first.packet)
        firstAllocated pattern =
      GeneralDeclarationDemands.inputInterval (GeneralNominalPacketSupport.capture last.packet)
        lastAllocated pattern) :
    first.emittedCenter clause position pattern = last.emittedCenter clause position pattern := by
  unfold Plan.emittedCenter
  split
  · rename_i name normalized
    have captures : (GeneralNominalPacketSupport.capture first.packet).inputs name =
        (GeneralNominalPacketSupport.capture last.packet).inputs name := by
      simpa only [GeneralDeclarationDemands.inputInterval,normalized] using inputs
    exact binder_equal first last seed invocation declaration name captures
  all_goals rw [seed,invocation,declaration]

theorem child_center_equal (first last : Plan roles)
    (seed : first.packet.context.state.seed = last.packet.context.state.seed)
    (invocation : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
    (declaration : first.packet.declaration = last.packet.declaration)
    (clause : Clause) (signature : clause.Signature roles)
    (index : Fin (roles clause.role).arity)
    (arguments : ((first.childSite clause signature).occurrence.demand.arguments index) =
      ((last.childSite clause signature).occurrence.demand.arguments index)) :
    (first.childSite clause signature).center index = (last.childSite clause signature).center index := by
  exact emitted_equal first last seed invocation declaration clause.id index.val _ arguments

end Yulang.GeneralNominalCenterCoherence184
