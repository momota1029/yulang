import Yulang.GeneralDeclarativeWhereCurrent346

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 19000000
namespace Yulang.GeneralDeclarativeWhereRevisionCut346
open GeneralWherePhysicalPast319 (loose point)
open GeneralWherePhysicalPointLift319 (historically_loose closed)
open GeneralWherePhysicalIndex319 (old)
open GeneralNominalRefinements (Refines renameDescriptor)
open GeneralNominalReobservationSteps (PointAt)
open GeneralWhereOriginSingleSource318 (registry sourceRegistry)
open GeneralWherePhysicalOldInstall319 (installed)
open GeneralWherePhysicalReobserve319 (updated underlying_step)
open GeneralDictionaryJournalRefinement228Source (root)
open GeneralDeclarativeWhereStore346 (Store)

theorem same_basis : point.base = loose.base := rfl

/-- This *actual* nominal improvement changes the descriptor, even
though slot identities and both histories stay. It therefore cannot
satisfy the old literal descriptor-preservation contract. -/
theorem not_literal_refinement (ref : Refines loose point) : False := by
  have identity : ref.base.embed = (id : Fin 7 → Fin 7) := by
    funext i
    apply loose.base.source_injective
    exact ref.base.source i
  let i : Fin 7 := old 2 (0 : Fin 5)
  let d := renameDescriptor (old 2) (GeneralDictionaryJournalRefinement228Source.descriptor (4,2))
  have recorded : loose.nominals i = some d := rfl
  have kept := ref.nominals i d recorded
  rw [identity] at kept
  have exact := closed (id i) (renameDescriptor id d) kept
  have oldStored : loose.nominals (id i) = some (renameDescriptor id d) :=
    (GeneralNominalRefinements.refl loose).nominals i d recorded
  exact historically_loose ⟨_,oldStored,exact⟩

theorem actual_cut :
    GeneralNominalVersionedMixedKernel234.Step registry root installed.mixed updated.mixed ∧
    Store sourceRegistry updated ∧ (Refines loose point → False) :=
  ⟨underlying_step,GeneralDeclarativeWhereCurrent346.actual_revision,not_literal_refinement⟩

end Yulang.GeneralDeclarativeWhereRevisionCut346
