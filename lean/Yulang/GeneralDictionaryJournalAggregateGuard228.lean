import Yulang.GeneralDictionaryDefaultMergeRevisionProbe210
import Yulang.GeneralDictionaryDefaultKernel208
import Yulang.CommonNominalFullConstructors

namespace Yulang.GeneralDictionaryJournalAggregateGuard228
open GeneralDeclarations GeneralNominalCenters GeneralNominalAllocation
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionaryDefaultMergeRevisionProbe210
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls} {state : State roles} {effect : Effect roles}
variable {model : Assignment} {first last upper nextUpper name : Nat}

/-- Repeated lower merges at a reused key require equivalence even across
raw-state revisions with the same seed. The carrier values are arbitrary. -/
theorem reused_lower_equivalent
    (sameSeed : firstState.seed = lastState.seed)
    (named : name ∈ declaration.inputNames)
    (one : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (merges firstState registry root declaration (twice name first upper)))
    (two : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (merges lastState registry root declaration (twice name last nextUpper))) :
    Equivalent (model first).1 (model last).1 := by
  rw [← GeneralNominalPacketCodes.merges_seed firstState lastState sameSeed] at two
  exact reused_lower_forces_equivalence named one two

theorem packet_equivalent
    {old current : Plan roles} {model : Assignment}
    (registryEq : old.packet.registry = current.packet.registry)
    (rootEq : old.packet.site.occurrence.identity = current.packet.site.occurrence.identity)
    (declarationEq : old.packet.declaration = current.packet.declaration)
    (sameSeed : old.packet.context.state.seed = current.packet.context.state.seed)
    (named : name ∈ old.packet.declaration.inputNames)
    (oldBindings : old.packet.bindings = twice name first upper)
    (newBindings : current.packet.bindings = twice name last nextUpper)
    (oldValid : GeneralNominalCenteredHeadMatStepPackets.Holds old model)
    (newValid : GeneralNominalCenteredHeadMatStepPackets.Holds current model) :
    Equivalent (model first).1 (model last).1 := by
  have one := oldValid.2.1.1.2.1
  have two := newValid.2.1.1.2.1
  rw [oldBindings] at one
  rw [newBindings,← registryEq,← rootEq,← declarationEq] at two
  exact reused_lower_equivalent sameSeed named one two

/-- A concrete journal model separating the old/new endpoints rules out the
current packet in that model, even if raw Prepared has some other model. -/
theorem journal_blocks_packet
    {old current : Plan roles} {model : Assignment}
    (registered : old ∈ state.core.plans)
    (valid : Models state model)
    (registryEq : old.packet.registry = current.packet.registry)
    (rootEq : old.packet.site.occurrence.identity = current.packet.site.occurrence.identity)
    (declarationEq : old.packet.declaration = current.packet.declaration)
    (sameSeed : old.packet.context.state.seed = current.packet.context.state.seed)
    (named : name ∈ old.packet.declaration.inputNames)
    (oldBindings : old.packet.bindings = twice name first upper)
    (newBindings : current.packet.bindings = twice name last nextUpper)
    (separated : ¬ Equivalent (model first).1 (model last).1) :
    ¬ GeneralNominalCenteredHeadMatStepPackets.Holds current model := by
  intro packet
  exact separated (packet_equivalent registryEq rootEq declarationEq sameSeed named oldBindings newBindings
    (valid.2.2.2.2.1 old registered) packet)

/-- When the separation holds for every journal model, the real installation
criterion cannot hold. This is an obstruction lemma, not a reachable refutation. -/
theorem no_installable
    (blocked : ∀ model, Models state model → ¬ GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan model) :
    ¬ GeneralDictionaryDefaultKernel208.Installable registry state effect := by
  intro enabled
  obtain ⟨model,valid,packet,_⟩ := enabled.common
  exact blocked model valid packet
end Yulang.GeneralDictionaryJournalAggregateGuard228
