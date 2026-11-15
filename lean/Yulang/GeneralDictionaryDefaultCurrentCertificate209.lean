import Yulang.GeneralDictionaryDefaultSemanticReplay209
import Yulang.GeneralDictionaryDefaultReadback209

set_option backward.isDefEq.respectTransparency false

/-! At point inputs, the choice of current frame does not affect certificates.
This concerns already witnessed evidence, not existence for every selection. -/
namespace Yulang.GeneralDictionaryDefaultCurrentCertificate209
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCenteredHeadOutputs (Frame)
open GeneralDictionaryDefaultSemanticReplay209 (recenter)
open GeneralDictionaryDefaultBoundary208 (boundary)
open GeneralNominalCenteredHeadAllocEncoding (registry)
variable {roles : Roles.RoleDecls} {first last : Plan roles}

 theorem frame_data {reg : Registry} (checked : Checked reg)
    (one : Frame reg state focus key first) (two : Frame reg state focus key last)
    (same : first.input.occurrence = last.packet.site.occurrence) :
    GeneralNominalCenteredHeadMatPlanData.Same first (recenter last first.input same) := by
  have decl := GeneralDictionaryDefaultFrameSemantics209.declaration checked one two
  have ctx := one.context_eq.trans two.context_eq.symm
  have reg := one.registry_eq.trans two.registry_eq.symm
  rcases first with ⟨first,input₁,exact₁⟩
  rcases last with ⟨last,input₂,exact₂⟩
  rcases first with ⟨reg₁,ctx₁,site₁,decl₁,checked₁,bounds₁⟩
  rcases last with ⟨reg₂,ctx₂,site₂,decl₂,checked₂,bounds₂⟩
  dsimp at decl ctx reg
  cases reg
  cases ctx
  cases decl
  have bounds : bounds₁ = bounds₂ := Option.some.inj (one.located.symm.trans two.located)
  cases bounds
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

 theorem transport {state : State roles}
    (checked : (boundary roles).Checked value)
    (frame : Frame (registry value) state.core focus key first)
    (point : ∀ index, (focus.demand.arguments index).1 = (focus.demand.arguments index).2)
    (valid : Models state model)
    (old : GeneralDictionaryTotalEvidence206.Certificate (registry value) state.core model focus key children last) :
    GeneralDictionaryTotalEvidence206.Certificate (registry value) state.core model focus key children first := by
  have checkedRegistry := (GeneralNominalCenteredHeadAllocBoundary.checked_compiled checked).2
  have same := first.input_exact.trans (frame.occurrence_eq.trans old.frame.occurrence_eq.symm)
  have data := frame_data checkedRegistry frame old.frame same
  have one := valid.2.2.2.1 first.input frame.center_recorded
  have two := valid.2.2.2.1 last.input old.frame.center_recorded
  have oldPoint := (last.input_exact.trans old.frame.occurrence_eq).symm ▸ point
  have packet := GeneralDictionaryDefaultSemanticReplay209.recenter_holds first.input same oldPoint one old.packet
  refine ⟨frame,old.children_eq.trans
    (GeneralDictionaryDefaultFrame209.frame_children checkedRegistry old.frame frame),
    GeneralDictionaryDefaultReinspection209.packet_reinspect data frame valid packet,?_⟩
  intro output member
  obtain ⟨body,supplied,⟨expression,compiled⟩,held⟩ := old.outputs output member
  refine ⟨body,?_,⟨expression,?_⟩,?_⟩
  · exact (GeneralDictionaryDefaultFrameSemantics209.declaration checkedRegistry frame old.frame).symm ▸ supplied
  · exact (GeneralDictionaryDefaultBodyTransport209.compile_equal
      (congrArg Registry.constructors (frame.registry_eq.trans old.frame.registry_eq.symm))
      (congrArg GeneralNominalCandidates.Context.interpretation (frame.context_eq.trans old.frame.context_eq.symm)) body).trans compiled
  · exact (GeneralDictionaryDefaultFrameSemantics209.body_iff checkedRegistry frame old.frame point one two).mpr held

 theorem instance_iff {state : State roles}
    (checked : (boundary roles).Checked value)
    (frame : Frame (registry value) state.core focus key first)
    (point : ∀ index, (focus.demand.arguments index).1 = (focus.demand.arguments index).2)
    (valid : Models state model) :
    GeneralDictionaryTotalEvidence206.Instance (registry value) state.core model focus key children ↔
      GeneralDictionaryTotalEvidence206.Certificate (registry value) state.core model focus key children first := by
  constructor
  · rintro ⟨other,certificate⟩
    exact transport checked frame point valid certificate
  · exact fun certificate => ⟨first,certificate⟩

 theorem node_iff {state : State roles}
    (checked : (boundary roles).Checked value)
    (frame : Frame (registry value) state.core focus key first)
    (point : ∀ index, (focus.demand.arguments index).1 = (focus.demand.arguments index).2)
    (valid : Models state model) :
    GeneralDictionaryTotalEvidence206.Evidence (registry value) state.core model focus (.node key dictionaries) ↔
      GeneralDictionaryTotalEvidence206.Certificate (registry value) state.core model focus key first.packet.children first ∧
        CommonRoleOutermostResolver.All₂
          (GeneralDictionaryTotalEvidence206.Evidence (registry value) state.core model) first.packet.children dictionaries := by
  rw [GeneralDictionaryDefaultReadback209.node_current_frame_iff
    (GeneralNominalCenteredHeadAllocBoundary.checked_compiled checked).2 frame,
    instance_iff checked frame point valid]

end Yulang.GeneralDictionaryDefaultCurrentCertificate209
