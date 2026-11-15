import Yulang.GeneralDictionaryDefaultTerminalOutputs210
import Yulang.GeneralDictionaryDefaultBodyGlue212

/-! For a terminal current frame, full snapshot class bodies already imply
all emitted packet outputs. Defaults stay in ClassEffects; explicit root
materialization is not a separate existential witness. -/
namespace Yulang.GeneralDictionaryDefaultTerminalOutput212
open GeneralNominalCenters GeneralNominalCenteredHeadMatEffects
open GeneralNominalCenteredHeadMatSchemas
open GeneralNominalCenteredHeadOutputs (requests)
variable {roles : Roles.RoleDecls} {plan : Plan roles}
variable {model : GeneralNominalCommonBridge.Assignment}

 theorem generated_holds {variables : GeneralNominalMaterialization.Mode → Nat → CommonNominalFullCarrier.Ty} (list : List GeneralNominalMaterialization.Request)
     (each : ∀ request ∈ list, (materialize catalogue interpretation request).Holds variables model) :
     (generated catalogue interpretation list).Holds variables model := by
  induction list with
  | nil => intro equation member; cases member
  | cons first rest ih =>
    exact append_holds.mpr ⟨each first (List.mem_cons_self ..),
      ih (fun request member => each request (List.mem_cons_of_mem _ member))⟩

 theorem outputs_of_bodies
     (terminal : plan.packet.declaration.requirements = [])
     (recorded : plan.packet.site ∈ state.erased.current.sites)
     (bodies : ∀ output ∈ requests state plan.packet.site.occurrence, ∀ body,
       GeneralDictionaryAssociatedProvenance.lookup roles plan.packet.declaration output.name = some body →
         BodyHolds plan output.target model body) :
     GeneralNominalCenteredHeadMatStepPackets.Outputs plan model := by
  unfold GeneralNominalCenteredHeadMatStepPackets.Outputs GeneralNominalCenteredHeadMatPlans.emittedSchema
  rw [GeneralDictionaryDefaultTerminalOutputs210.terminal_requests plan terminal]
  apply generated_holds
  intro request member
  obtain ⟨output,within,member⟩ := List.mem_flatMap.mp member
  obtain ⟨equation,found,rfl⟩ := List.mem_map.mp member
  have found := Option.mem_toList.mp found
  have inClass := GeneralNominalCenteredHeadOutputs.request_retained plan.packet.site recorded (.refl _) within
  have held := bodies output inClass (.explicit equation) (by
    simp only [GeneralDictionaryAssociatedProvenance.lookup,found])
  exact held

 theorem outputs_of_class
     (terminal : plan.packet.declaration.requirements = [])
     (recorded : plan.packet.site ∈ state.erased.current.sites)
     (effects : ClassEffects state plan.packet.site.occurrence plan model) :
     GeneralNominalCenteredHeadMatStepPackets.Outputs plan model :=
  outputs_of_bodies terminal recorded effects.1

 theorem outputs_of_effect (effect : GeneralNominalCenteredHeadMatStepJournal.Effect roles)
     (terminal : effect.plan.packet.declaration.requirements = [])
     (held : effect.Holds model) :
     GeneralNominalCenteredHeadMatStepPackets.Outputs effect.plan model :=
  outputs_of_class terminal effect.frame.raw_recorded held.2

end Yulang.GeneralDictionaryDefaultTerminalOutput212
