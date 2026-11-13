import Yulang.GeneralNominalReobservationSteps

/-! The exact boundary of descriptor-preserving transport. A genuine improving
reobservation cannot be a Refines update: it has the same source carrier, whose
identities force the embedding to be identity, but changes a nonpoint descriptor
to a point descriptor. This does not refute a different semantic transport rule. -/
namespace Yulang.GeneralDictionaryReobservationRefinementGap
open GeneralNominalReobservationSteps GeneralNominalRefinements
variable {roles : Roles.RoleDecls}
variable {state : GeneralNominalSaturationState.State roles}

theorem embedding_identity (revision : Revision state)
    (refinement : Refines state.context.state revision.snapshot) :
    refinement.base.embed = id := by
  funext slot
  apply state.context.state.base.source_injective
  exact refinement.base.source slot

private theorem rename_identity (descriptor : GeneralNominalState.Descriptor slots) :
    renameDescriptor id descriptor = descriptor := by
  have parameter : renameParameter (id : Fin slots → Fin slots) = id := by
    funext p; cases p <;> rfl
  cases descriptor
  simp [renameDescriptor,parameter]

theorem point_preserved_backwards (revision : Revision state)
    (refinement : Refines state.context.state revision.snapshot) (slot : Fin state.context.state.base.slots)
    (point : PointAt revision.snapshot slot) : PointAt state.context.state slot := by
  obtain ⟨descriptor,recorded,point⟩ := point
  cases old : state.context.state.nominals slot with
  | none =>
    have absent := (revision.domain slot).mpr old
    change revision.entries slot = some descriptor at recorded
    rw [absent] at recorded
    cases recorded
  | some prior =>
    have retained := refinement.nominals slot prior old
    rw [embedding_identity revision refinement] at retained
    simp only [id_eq] at retained
    have same := Option.some.inj (retained.symm.trans recorded)
    subst descriptor
    refine ⟨prior,old,?_⟩
    have eq : renameDescriptor (id : Fin state.context.state.base.slots → Fin state.context.state.base.slots) prior = prior := rename_identity prior
    exact eq ▸ point

theorem improving_not_refines (revision : Revision state) (improves : Improves revision) :
    ¬ Nonempty (Refines state.context.state revision.snapshot) := by
  rintro ⟨refinement⟩
  obtain ⟨_,slot,old,new⟩ := improves
  exact old (point_preserved_backwards revision refinement slot new)
end Yulang.GeneralDictionaryReobservationRefinementGap
