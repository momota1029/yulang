import Yulang.GeneralDeclarativeNominalIntervals347
import Yulang.GeneralDeclarativeWhereNominalFixture346

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 19000000
namespace Yulang.GeneralDeclarativeNominalRevision347
open GeneralDeclarativeNominalIntervals347 (Named observes FitList)
open GeneralWherePhysicalPast319 (point loose two four point_models)
open GeneralWherePhysicalCurrentRead319 (zero desc nominal0)
open GeneralWherePhysicalCommit319 (final)
open GeneralWherePhysicalActive319 (active refines)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryBinderLocations (sourceSlot sourceSlot_exact)
open GeneralNominalState (Models Descriptor)
open CommonNominalFullCarrier (Equivalent nominal)

abbrev get := GeneralDeclarativeNominalIntervals347.read

abbrev historic : Descriptor 7 :=
  GeneralNominalRefinements.renameDescriptor (GeneralWherePhysicalIndex319.old 2)
    (GeneralDictionaryJournalRefinement228Source.descriptor (4,2))

theorem prior_read : get loose 0 = some (0,[.type 4 2,.type 4 2]) := by
  apply GeneralDeclarativeNominalIntervals347.read_exact.mpr
  refine ⟨zero,historic,(sourceSlot_exact ..).mpr rfl,rfl,rfl,rfl⟩

theorem current_read : get point 0 = some (0,[.type 2 2,.type 2 2]) := by
  apply GeneralDeclarativeNominalIntervals347.read_exact.mpr
  exact ⟨zero,desc,(sourceSlot_exact ..).mpr rfl,nominal0,rfl,rfl⟩

theorem not_current (h : get point 0 = some (0,[.type 4 2,.type 4 2])) : False := by
  rw [current_read] at h
  cases h

/-- The same physical root and the same final raw model allow both
recorded observations at their own times. The earlier bound is genuinely
nonpoint in *every* actual final model; it is not an alternative exact
current literal even when nominal denotations agree. -/
theorem exact_times (m : Assignment) (valid : GeneralWhereVersionInstall317.Models final m) :
    get loose 0 = some (0,[.type 4 2,.type 4 2]) ∧
    get point 0 = some (0,[.type 2 2,.type 2 2]) ∧
    (∃ vals, FitList m [.type 4 2,.type 4 2] vals ∧ Equivalent (m 0).1 (nominal 0 vals)) ∧
    (∃ vals, FitList m [.type 2 2,.type 2 2] vals ∧ Equivalent (m 0).1 (nominal 0 vals)) ∧
    ¬ Equivalent (m 4).1 (m 2).1 := by
  have live : Models point m := GeneralNominalRefinements.models refines m valid.1.1.1
  exact ⟨prior_read,current_read,observes prior_read m ((point_models m).mp live),
    observes current_read m live,GeneralDeclarativeVersionedSeparation342.unequal_operands m valid⟩

end Yulang.GeneralDeclarativeNominalRevision347
