import Yulang.GeneralVersionedSiteOrigins312
import Yulang.GeneralNominalChildCoherence184

set_option backward.isDefEq.respectTransparency false
/-! This is equality of center names for exact versioned occurrences, not
equality of names for all observations of one numeric invocation. -/
namespace Yulang.GeneralVersionedEqualChildCenters312
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedFrame231 (capture binder emittedCenter childSite)
variable {roles : Roles.RoleDecls}

theorem binder_equal (first last : Plan roles)
    (seed : first.packet.context.state.seed = last.packet.context.state.seed)
    (invocation : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
    (declaration : first.packet.declaration = last.packet.declaration) (name : Nat)
    (inputs : (capture first.packet).inputs name =
      (capture last.packet).inputs name) :
    binder first name = binder last name := by
  unfold binder
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
    (inputs : GeneralDeclarationDemands.inputInterval (capture first.packet)
        firstAllocated pattern =
      GeneralDeclarationDemands.inputInterval (capture last.packet)
        lastAllocated pattern) :
    emittedCenter first clause position pattern = emittedCenter last clause position pattern := by
  unfold emittedCenter
  split
  · rename_i name normalized
    have captures : (capture first.packet).inputs name =
        (capture last.packet).inputs name := by
      simpa only [GeneralDeclarationDemands.inputInterval,normalized] using inputs
    exact binder_equal first last seed invocation declaration name captures
  all_goals rw [seed,invocation,declaration]

theorem child_center_equal (first last : Plan roles)
    (seed : first.packet.context.state.seed = last.packet.context.state.seed)
    (invocation : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
    (declaration : first.packet.declaration = last.packet.declaration)
    (clause : Clause) (signature : clause.Signature roles)
    (index : Fin (roles clause.role).arity)
    (arguments : ((childSite first clause signature).occurrence.demand.arguments index) =
      ((childSite last clause signature).occurrence.demand.arguments index)) :
    (childSite first clause signature).center index = (childSite last clause signature).center index := by
  exact emitted_equal first last seed invocation declaration clause.id index.val _ arguments


theorem same_clause_site (first last : Plan roles)
    (seed : first.packet.context.state.seed = last.packet.context.state.seed)
    (invocation : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
    (declaration : first.packet.declaration = last.packet.declaration)
    (clause : Clause) (signature : clause.Signature roles)
    (same : (childSite first clause signature).occurrence = (childSite last clause signature).occurrence) :
    childSite first clause signature = childSite last clause signature := by
  apply GeneralNominalChildCoherence184.site_eq_of_centers _ _ same
  apply congrArg List.ofFn
  funext index
  apply child_center_equal first last seed invocation declaration
  have args := congrArg (fun occurrence : Occurrence roles => List.ofFn occurrence.demand.arguments) same
  have atIndex := congrArg (fun values : List GeneralSourceState.Interval => values[index.val]?) args
  have l : index.val < (roles (childSite first clause signature).occurrence.demand.role).arity := index.isLt
  have r : index.val < (roles (childSite last clause signature).occurrence.demand.role).arity := index.isLt
  simp only [List.getElem?_ofFn,dite_eq_left l,dite_eq_left r,Option.some.injEq] at atIndex
  exact atIndex

theorem child_site (registry : Registry) (checked : Checked registry)
    (first last : Plan roles)
    (seed : first.packet.context.state.seed = last.packet.context.state.seed)
    (firstVisible : first.packet.declaration ∈ registry.declarations)
    (lastVisible : last.packet.declaration ∈ registry.declarations)
    (one two : Clause) (oneMember : one ∈ first.packet.declaration.requirements)
    (twoMember : two ∈ last.packet.declaration.requirements)
    (oneSignature : one.Signature roles) (twoSignature : two.Signature roles)
    (same : (childSite first one oneSignature).occurrence = (childSite last two twoSignature).occurrence) :
    childSite first one oneSignature = childSite last two twoSignature := by
  have ids : (first.childSite one oneSignature).occurrence.identity =
      (last.childSite two twoSignature).occurrence.identity := by
    rw [← GeneralNominalVersionedFrame231.childSite_identity_eq,← GeneralNominalVersionedFrame231.childSite_identity_eq]
    exact congrArg Occurrence.identity same
  obtain ⟨invocation,declaration,clauses⟩ := GeneralNominalChildCoherence184.producer_declarations
    registry checked first last seed firstVisible lastVisible one two oneMember twoMember oneSignature twoSignature
    ids
  subst two
  exact same_clause_site first last seed invocation declaration one oneSignature same

end Yulang.GeneralVersionedEqualChildCenters312
