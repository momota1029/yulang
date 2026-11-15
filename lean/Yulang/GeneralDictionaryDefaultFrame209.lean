import Yulang.GeneralDictionaryDefaultRecorded208

set_option backward.isDefEq.respectTransparency false

/-! Current-frame coherence does not assume a historical stored plan has the
current context. Ordered children are independent of the chosen witness model. -/
namespace Yulang.GeneralDictionaryDefaultFrame209
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadOutputs (Frame)
variable {roles : Roles.RoleDecls}

 theorem frame_children (checked : Checked registry)
    (one : Frame registry state focus key first)
    (two : Frame registry state focus key last) :
    first.packet.children = last.packet.children := by
  have declarations : first.packet.declaration = last.packet.declaration :=
    GeneralDictionaryEmissionPlans.declaration_key_unique registry checked _ _
      one.visible two.visible (one.key_eq.trans two.key_eq.symm)
  have contexts := one.context_eq.trans two.context_eq.symm
  have registries := one.registry_eq.trans two.registry_eq.symm
  have occurrences := one.occurrence_eq.trans two.occurrence_eq.symm
  rcases first with ⟨first,input₁,exact₁⟩
  rcases last with ⟨last,input₂,exact₂⟩
  rcases first with ⟨reg₁,ctx₁,site₁,decl₁,checked₁,bounds₁⟩
  rcases last with ⟨reg₂,ctx₂,site₂,decl₂,checked₂,bounds₂⟩
  dsimp at declarations contexts registries occurrences
  cases registries
  cases contexts
  cases declarations
  have bounds : bounds₁ = bounds₂ := Option.some.inj (one.located.symm.trans two.located)
  cases bounds
  simp only [GeneralNominalSaturationState.Packet.children, GeneralNominalSaturationState.Packet.bindings,occurrences]

 theorem certificate_children (checked : Checked registry)
    (one : GeneralDictionaryTotalEvidence206.Certificate registry state model focus key children first)
    (two : GeneralDictionaryTotalEvidence206.Certificate registry state otherModel focus key otherChildren last) :
    children = otherChildren :=
  one.children_eq.trans ((frame_children checked one.frame two.frame).trans two.children_eq.symm)

 theorem instance_children (checked : Checked registry)
    (one : GeneralDictionaryTotalEvidence206.Instance registry state model focus key children)
    (two : GeneralDictionaryTotalEvidence206.Instance registry state otherModel focus key otherChildren) :
    children = otherChildren := by
  obtain ⟨first,one⟩ := one
  obtain ⟨last,two⟩ := two
  exact certificate_children checked one two

 theorem childrenFunctional (checked : Checked registry) :
    GeneralDictionaryReadback.ChildrenFunctional
      (GeneralDictionaryTotalEvidence206.Instance registry state model) :=
  fun _ _ _ _ one two => instance_children checked one two

end Yulang.GeneralDictionaryDefaultFrame209
