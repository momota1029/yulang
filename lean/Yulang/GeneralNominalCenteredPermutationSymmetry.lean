import Yulang.GeneralNominalCenteredPermutationExtension

set_option backward.isDefEq.respectTransparency false

/-! The finite rebasing table is reversible. Original metadata enumeration is
recovered on reversal, while all retained ledger pairings reverse together. -/
namespace Yulang.GeneralNominalCenteredPermutationSymmetry
open GeneralDeclarations GeneralRegistryReordering GeneralNominalSaturationState
open GeneralNominalCenteredPermutationRepresentation
variable {roles : Roles.RoleDecls}

theorem rebased_symm {packet other : Packet roles} (paired : RebasedPacket first last packet other) :
    RebasedPacket last first other packet := by
  obtain ⟨registry,decl,order,pair,allocated,reserved,keys,names,rfl⟩ := paired
  subst first
  refine ⟨rfl,packet.declaration,GeneralRegistryChildOrder.reorders_symm order,
    declarationReorders_symm pair,packet.context.state.allocated,packet.context.state.reserved,
    fun key => (keys key).symm,fun name => (names name).symm,?_⟩
  rcases packet with ⟨registry,⟨state,interpretation⟩,site,declaration,checked,bounds⟩
  cases state
  rfl

def reverse (table : List (Packet roles × Packet roles)) : List (Packet roles × Packet roles) :=
  table.map (fun entry => (entry.2,entry.1))

theorem reversed_member (table : List (Packet roles × Packet roles)) (one two : Packet roles) :
    paired (reverse table) one two ↔ paired table two one := by
  change (one,two) ∈ table.map (fun entry => (entry.2,entry.1)) ↔ (two,one) ∈ table
  constructor
  · intro member
    obtain ⟨⟨a,b⟩,member,equal⟩ := List.mem_map.mp member
    have one := congrArg Prod.fst equal
    have two := congrArg Prod.snd equal
    dsimp at one two
    cases one; cases two
    exact member
  · intro member
    exact List.mem_map.mpr ⟨(two,one),member,rfl⟩

theorem corresponds_symm {left right : GeneralNominalCenteredSteps.State roles}
    (same : Corresponds first last left right) : Corresponds last first right left := by
  obtain ⟨table,rebased,recorded,related⟩ := same
  refine ⟨reverse table,?_,?_,?_⟩
  · intro one two member
    exact rebased_symm (rebased two one ((reversed_member table one two).mp member))
  · intro one two member
    have original := recorded two one ((reversed_member table one two).mp member)
    exact ⟨original.2,original.1⟩
  · have relationEq : (fun a b => paired table b a) = paired (reverse table) :=
      funext (fun one => funext (fun two => propext (reversed_member table one two).symm))
    exact relationEq ▸ GeneralNominalCenteredPermutationSafety.symm related

end Yulang.GeneralNominalCenteredPermutationSymmetry
