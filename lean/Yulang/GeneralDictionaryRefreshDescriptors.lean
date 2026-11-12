import Yulang.GeneralDictionaryRecordedRefresh

/-! On the fixed carrier of reobservation, an actual refinement fixes every
source slot and retains every previously recorded nominal descriptor. This
turns descriptor-preservation obligations into checkable occupancy conditions;
it says nothing about previously absent descriptors or changed views. -/
namespace Yulang.GeneralDictionaryRefreshDescriptors
open GeneralDictionaryInspectionTransport
open GeneralNominalRefinements
open GeneralNominalRecursiveCandidates (Context)

theorem embed_identity (context : Context) (next : Observation context.state)
    (refinement : Refines context.state (reobserve context next).state) :
    refinement.base.embed = id := by
  funext slot
  exact context.state.base.source_injective (refinement.base.source slot)

theorem rename_descriptor_identity (descriptor : GeneralNominalState.Descriptor slots) :
    renameDescriptor id descriptor = descriptor := by
  have identity : renameParameter (id : Fin slots → Fin slots) = id := by
    funext parameter; cases parameter <;> rfl
  cases descriptor
  simp [renameDescriptor,identity]

theorem descriptor_preserved (context : Context) (next : Observation context.state)
    (refinement : Refines context.state (reobserve context next).state)
    (slot : Fin context.state.base.slots) (descriptor : GeneralNominalState.Descriptor context.state.base.slots)
    (recorded : context.state.nominals slot = some descriptor) :
    next.nominals slot = some descriptor := by
  have retained := refinement.nominals slot descriptor recorded
  rw [embed_identity context next refinement,rename_descriptor_identity] at retained
  exact retained

end Yulang.GeneralDictionaryRefreshDescriptors
