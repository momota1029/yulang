import Yulang.GeneralDictionaryCenteredJournalPoint180

/-! Real Candidate consumer for a nonempty or empty centered journal.
The leaf shape is recovered from finished inspection, not postulated. -/
namespace Yulang.GeneralDictionaryCenteredJournalCandidate180
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralDictionaryCenteredCandidate176 GeneralDictionaryLinearLeaf
open GeneralNominalRawFrame179 (fullSources)
variable {roles : Roles.RoleDecls} {registry : Registry} {focus : Occurrence roles}
  {state : State roles} {key : Nat} {children : List (Occurrence roles)} {plan : Plan roles}

/-- Exact syntactic freshness requirement: only genuinely allocated input binders
must be absent from the complete old raw and centered footprint. -/
 def FreshInputs (state : State roles) (plan : Plan roles) : Prop :=
  ∀ name ∈ plan.packet.declaration.inputNames,
    ((GeneralNominalPacketSupport.capture plan.packet).inputs name).1 ≠
      ((GeneralNominalPacketSupport.capture plan.packet).inputs name).2 →
    plan.binder name ∉ fullSources state

/-- Point captures reuse old names and require no freshness, even if every input
center is already present in the journal. -/
 theorem freshInputs_of_points
    (points : ∀ name ∈ plan.packet.declaration.inputNames,
      ((GeneralNominalPacketSupport.capture plan.packet).inputs name).1 =
        ((GeneralNominalPacketSupport.capture plan.packet).inputs name).2) :
    FreshInputs state plan := by
  intro name member different
  exact False.elim (different (points name member))

/-- A concrete overlap outside the point case is exactly a failed side condition,
not evidence that the old journal or candidate is inconsistent. -/
 theorem not_freshInputs_of_overlap
    (name : Nat) (input : name ∈ plan.packet.declaration.inputNames)
    (different : ((GeneralNominalPacketSupport.capture plan.packet).inputs name).1 ≠
      ((GeneralNominalPacketSupport.capture plan.packet).inputs name).2)
    (present : plan.binder name ∈ fullSources state) : ¬ FreshInputs state plan := by
  intro freshInputs
  exact freshInputs name input different present

 theorem joint
    (candidate : Candidate registry state focus key children plan)
    (named : plan.input.PointNames)
    (freshInputs : FreshInputs state plan)
    (slot : Fin plan.packet.context.state.base.slots) (name : Nat)
    (names : Fin n → Nat) (distinct : Function.Injective names)
    (inputs : plan.packet.declaration.inputNames = List.ofFn names)
    (query : GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation
      plan.packet.declaration = [.nominal name (List.ofFn fun i => .variables [names i])])
    (located : arguments plan.packet.context plan.packet.site.occurrence = some [(slot,slot)])
    (terminal : plan.packet.declaration.requirements = [])
    (outputs : plan.packet.site.occurrence.demand.outputs = [])
    (previous : GeneralNominalCommonBridge.Assignment)
    (valid : Models state previous) :
    ∃ extended, Models state extended ∧ plan.Holds extended ∧
      ∀ name ∈ fullSources state, extended name = previous name := by
  obtain ⟨shape⟩ := GeneralDictionaryCenteredPointCandidate179.discovered_shape
    candidate slot name names distinct inputs query located terminal outputs
  have packetLocated : plan.packet.bounds = [(shape.slot,shape.slot)] :=
    Option.some.inj (candidate.located.symm.trans shape.located)
  apply GeneralDictionaryCenteredJournalPoint180.joint_model state plan shape
    candidate.context_eq packetLocated named ?_ previous valid
  intro i different
  apply freshInputs (shape.names i)
  · rw [shape.inputs]
    exact List.mem_ofFn.mpr ⟨i,rfl⟩
  · rw [GeneralDictionaryCenteredPointJoint179.capture_exact plan shape packetLocated i]
    exact different

end Yulang.GeneralDictionaryCenteredJournalCandidate180
