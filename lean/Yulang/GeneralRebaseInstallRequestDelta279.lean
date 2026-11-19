import Yulang.GeneralNominalVersionedMixedKernel234

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseInstallRequestDelta279
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedInstall232 (installCore requests_included)
open GeneralNominalVersionedChildren232 (rawSites)
open GeneralNominalCenteredHeadOutputs (requests mem_requests_iff EqualOutputs)
open GeneralNominalVersionedEffects231 (ClassEffects BodyHolds)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryAssociatedProvenance (lookup)
open CommonNominalFullCarrier (Equivalent)

variable {roles : Roles.RoleDecls}
abbrev Core (roles : Roles.RoleDecls) := GeneralNominalCenteredSteps.State roles
abbrev Output := GeneralSourceState.Output

def EmittedRequest (core : Core roles) (added : Plan roles) (root : Occurrence roles)
    (output : Output) : Prop :=
  ∃ site ∈ rawSites added,
    GeneralNominalSaturationState.Alias core.erased.current root.identity site.occurrence.identity ∧
    output ∈ site.occurrence.demand.outputs

def FreshRequest (core : Core roles) (added : Plan roles) (root : Occurrence roles)
    (output : Output) : Prop :=
  EmittedRequest core added root output ∧ output ∉ requests core root

theorem append_requests (core : Core roles) (added : Plan roles) (root : Occurrence roles) (output : Output) :
    output ∈ requests (installCore core added) root ↔
      output ∈ requests core root ∨ EmittedRequest core added root output := by
  constructor
  · intro present
    obtain ⟨site,member,aliases,within⟩ := mem_requests_iff.mp present
    change site ∈ core.erased.current.sites ++ rawSites added at member
    have aliasOld := GeneralNominalVersionedInstallProperties232.alias_iff.mp aliases
    rcases List.mem_append.mp member with old | new
    · exact Or.inl (mem_requests_iff.mpr ⟨site,old,aliasOld,within⟩)
    · exact Or.inr ⟨site,new,aliasOld,within⟩
  · rintro (old | ⟨site,new,aliases,within⟩)
    · exact requests_included core added _ old
    · exact mem_requests_iff.mpr ⟨site,List.mem_append_right _ new,GeneralNominalVersionedInstallProperties232.alias_iff.mpr aliases,within⟩

theorem split_requests (core : Core roles) (added : Plan roles) (root : Occurrence roles) (output : Output) :
    output ∈ requests (installCore core added) root ↔
      output ∈ requests core root ∨ FreshRequest core added root output := by
  rw [append_requests]
  classical
  by_cases old : output ∈ requests core root <;> simp [FreshRequest,old]

theorem fresh_exact (core : Core roles) (added : Plan roles) (root : Occurrence roles) (output : Output) :
    FreshRequest core added root output ↔
      output ∈ requests (installCore core added) root ∧ output ∉ requests core root := by
  rw [append_requests]
  classical
  by_cases old : output ∈ requests core root <;> simp [FreshRequest,old]

def EffectDelta (core : Core roles) (added : Plan roles) (root : Occurrence roles)
    (recipient : Plan roles) (m : Assignment) : Prop :=
  (∀ output, FreshRequest core added root output → ∀ body,
    lookup roles recipient.packet.declaration output.name = some body →
    BodyHolds recipient output.target m body) ∧
  (∀ first, first ∈ requests (installCore core added) root → ∀ last,
    last ∈ requests (installCore core added) root →
    (FreshRequest core added root first ∨ FreshRequest core added root last) →
    first.name = last.name → Equivalent (m first.target).1 (m last.target).1)

theorem class_iff (core : Core roles) (added : Plan roles) (root : Occurrence roles)
    (recipient : Plan roles) (m : Assignment) :
    ClassEffects (installCore core added) root recipient m ↔
      ClassEffects core root recipient m ∧ EffectDelta core added root recipient m := by
  constructor
  · intro valid
    refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
    · exact fun o mem => valid.1 o (requests_included core added o mem)
    · exact fun a ha b hb => valid.2 a (requests_included core added a ha) b
        (requests_included core added b hb)
    · exact fun o mem => valid.1 o ((fresh_exact core added root o).mp mem).1
    · exact fun a ha b hb _ => valid.2 a ha b hb
  · rintro ⟨old,delta⟩
    constructor
    · intro o mem
      rcases (split_requests core added root o).mp mem with was | new
      · exact old.1 o was
      · exact delta.1 o new
    · intro a ha b hb equal
      rcases (split_requests core added root a).mp ha with oldA | newA
      · rcases (split_requests core added root b).mp hb with oldB | newB
        · exact old.2 a oldA b oldB equal
        · exact delta.2 a ha b hb (.inr newB) equal
      · exact delta.2 a ha b hb (.inl newA) equal

end Yulang.GeneralRebaseInstallRequestDelta279
