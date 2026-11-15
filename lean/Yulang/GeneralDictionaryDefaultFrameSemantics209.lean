import Yulang.GeneralDictionaryDefaultPointTransport209

set_option backward.isDefEq.respectTransparency false

/-! Current witness frames agree on binders even when their input-center names
are different. Point arguments then give representative-independent meanings
for all explicit/default bodies and whole current alias classes. -/
namespace Yulang.GeneralDictionaryDefaultFrameSemantics209
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadOutputs (Frame)
open GeneralNominalCenteredHeadMatEffects
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls} {first last : Plan roles}
variable {model : GeneralNominalCommonBridge.Assignment}

 theorem declaration (checked : Checked registry)
    (one : Frame registry state focus key first) (two : Frame registry state focus key last) :
    first.packet.declaration = last.packet.declaration :=
  GeneralDictionaryEmissionPlans.declaration_key_unique registry checked _ _
    one.visible two.visible (one.key_eq.trans two.key_eq.symm)

 theorem binder (checked : Checked registry)
    (one : Frame registry state focus key first) (two : Frame registry state focus key last) (name : Nat) :
    first.binder name = last.binder name := by
  have decl := declaration checked one two
  have ctx := one.context_eq.trans two.context_eq.symm
  have reg := one.registry_eq.trans two.registry_eq.symm
  have occurrence := one.occurrence_eq.trans two.occurrence_eq.symm
  rcases first with ⟨first,input₁,exact₁⟩
  rcases last with ⟨last,input₂,exact₂⟩
  rcases first with ⟨reg₁,ctx₁,site₁,decl₁,checked₁,bounds₁⟩
  rcases last with ⟨reg₂,ctx₂,site₂,decl₂,checked₂,bounds₂⟩
  dsimp at decl ctx reg occurrence
  cases reg
  cases ctx
  cases decl
  have bounds : bounds₁ = bounds₂ := Option.some.inj (one.located.symm.trans two.located)
  cases bounds
  simp only [Plan.binder,GeneralNominalPacketSupport.capture,GeneralNominalSaturationState.Packet.bindings,
    occurrence]

 theorem body_iff (checked : Checked registry)
    (one : Frame registry state focus key first) (two : Frame registry state focus key last)
    (point : ∀ index, (focus.demand.arguments index).1 = (focus.demand.arguments index).2)
    (firstHolds : first.input.Holds model) (lastHolds : last.input.Holds model) :
    BodyHolds first target model body ↔ BodyHolds last target model body := by
  apply GeneralDictionaryDefaultBodyTransport209.body_transport
  · exact congrArg Registry.constructors (one.registry_eq.trans two.registry_eq.symm)
  · exact congrArg GeneralNominalCandidates.Context.interpretation (one.context_eq.trans two.context_eq.symm)
  · intro name
    rw [binder checked one two name]
    exact GeneralDictionaryDefaultExpression209.equivalent_refl _
  · have firstFocus := first.input_exact.trans one.occurrence_eq
    have lastFocus := last.input_exact.trans two.occurrence_eq
    exact GeneralDictionaryDefaultPointTransport209.centers_equivalent first.input last.input
      (firstFocus.trans lastFocus.symm) (firstFocus.symm ▸ point) firstHolds lastHolds

 theorem class_iff (checked : Checked registry)
    (one : Frame registry state focus key first) (two : Frame registry state focus key last)
    (point : ∀ index, (focus.demand.arguments index).1 = (focus.demand.arguments index).2)
    (firstHolds : first.input.Holds model) (lastHolds : last.input.Holds model) :
    ClassEffects state focus first model ↔ ClassEffects state focus last model := by
  have decl := declaration checked one two
  have bodies : ∀ target body, BodyHolds first target model body ↔ BodyHolds last target model body :=
    fun _ _ => body_iff checked one two point firstHolds lastHolds
  simp only [ClassEffects,decl,bodies]

 theorem model_class_iff
    (checked : (GeneralDictionaryDefaultBoundary208.boundary roles).Checked value)
    (one : Frame (GeneralNominalCenteredHeadAllocEncoding.registry value) state.core focus key first)
    (two : Frame (GeneralNominalCenteredHeadAllocEncoding.registry value) state.core focus key last)
    (point : ∀ index, (focus.demand.arguments index).1 = (focus.demand.arguments index).2)
    (valid : GeneralNominalCenteredHeadMatStepJournal.Models state model) :
    ClassEffects state.core focus first model ↔ ClassEffects state.core focus last model :=
  class_iff (GeneralNominalCenteredHeadAllocBoundary.checked_compiled checked).2 one two point
    (valid.2.2.2.1 first.input one.center_recorded) (valid.2.2.2.1 last.input two.center_recorded)

end Yulang.GeneralDictionaryDefaultFrameSemantics209
