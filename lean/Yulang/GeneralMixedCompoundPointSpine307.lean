import Yulang.GeneralMixedCompoundRefreshBound307

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 18000
namespace Yulang.GeneralMixedCompoundPointSpine307
open GeneralDictionaryJournalRefinement228Source (roles root snapshot constructors interpretation)
open GeneralDictionaryCompoundPoint238 (point)
open GeneralDictionaryCompoundSource238 (registry sourceRegistry)
open GeneralMixedCompoundRefreshBound307 (Run models support)
open GeneralMixedCompoundUpperRefresh307 (upperState)
open GeneralMixedCompoundUpperSnapshot307 (snap)
open GeneralMixedCompoundUpperTypes307 (classifierModel classifier_model model_class)
open GeneralMixedCompoundAnyRefresh307 (nominal_class)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalRecursiveCandidates (Context)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalCommonBridge (Assignment)

abbrev descriptor (slot : Fin n) : GeneralNominalState.Descriptor n :=
  ⟨0,⟨[.type,.type],0⟩,[.type (slot,slot),.type (slot,slot)],rfl⟩

structure Slots (ctx : Context) where
  a : Fin ctx.state.base.slots
  b : Fin ctx.state.base.slots
  c : Fin ctx.state.base.slots
  name_a : ctx.state.base.source a = 0
  name_b : ctx.state.base.source b = 1
  name_c : ctx.state.base.source c = 2
  read_a : ctx.state.nominals a = some (descriptor c)
  read_b : ctx.state.nominals b = some (descriptor c)
  interpretation_eq : ctx.interpretation = interpretation
  catalogue_eq : ctx.state.constructors = constructors
  seed_eq : ctx.state.seed = snapshot.seed

noncomputable def initial : Slots point.core.erased.current.context :=
  ⟨(0 : Fin 5),(1 : Fin 5),(2 : Fin 5),rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

def advance {s : State roles} {ctx : Context} (cert : Refresh s ctx) (old : Slots s.core.erased.current.context) :
    Slots ctx :=
  let r := cert.refines
  ⟨r.base.embed old.a,r.base.embed old.b,r.base.embed old.c,
    (r.base.source old.a).trans old.name_a,(r.base.source old.b).trans old.name_b,
    (r.base.source old.c).trans old.name_c,r.nominals _ _ old.read_a,r.nominals _ _ old.read_b,
    cert.interpretation.trans old.interpretation_eq,r.constructors.trans old.catalogue_eq,r.seed.trans old.seed_eq⟩

theorem spine (p : Run n s) : Nonempty (Slots s.core.erased.current.context) := by
  induction p with
  | zero => exact ⟨initial⟩
  | more _ ctx cert _ _ _ _ ih =>
    obtain ⟨prev⟩ := ih
    exact ⟨advance cert prev⟩

theorem raw_base (p : Run n s) (m : Assignment)
    (valid : GeneralNominalState.Models s.core.erased.current.context.state m) :
    GeneralNominalState.Models point.core.erased.current.context.state m := by
  induction p with
  | zero => exact valid
  | more _ ctx cert _ _ _ _ ih =>
    exact ih (GeneralNominalRefinements.models cert.refines m valid)

theorem reach (p : Run n s) : B4TargetV8.Reachable (boundary roles) sourceRegistry root s := by
  induction p with
  | zero => exact GeneralDictionaryCompoundPoint238.reachable
  | more _ ctx cert i present unknown known ih =>
    obtain ⟨start,source,prior⟩ := ih
    exact ⟨start,source,.tail prior ⟨root,.root,.refresh root ctx cert i present unknown known⟩⟩

theorem sites (p : Run n s) : s.core.erased.current.sites = point.core.erased.current.sites := by
  induction p with
  | zero => rfl
  | more _ _ _ _ _ _ _ ih => exact ih

theorem centers (p : Run n s) : s.core.sites = point.core.sites := by
  induction p with
  | zero => rfl
  | more _ _ _ _ _ _ _ ih => exact ih

theorem nominal_location (p : Run n s) (slot : Fin s.core.erased.current.context.state.base.slots)
    (d) (found : s.core.erased.current.context.state.nominals slot = some d) :
    s.core.erased.current.context.state.base.source slot = 0 ∨
    s.core.erased.current.context.state.base.source slot = 1 := by
  let name := s.core.erased.current.context.state.base.source slot
  have nameIn := support p (GeneralNominalAllocationSupport.slot_source s.core.erased.current.context.state slot)
  have witnessed := (models p _).mpr classifier_model
  have head := GeneralDictionaryInspectionHeads215.nominal_slot witnessed.1.1 found
  have category := model_class name nameIn
  exact nominal_class name nameIn (GeneralDictionaryInspectionHeads215.tagged_equivalent ⟨category.2,category.1⟩ head)

theorem point_closed (p : Run n s) : GeneralNominalReobservationSteps.PointClosed s.core.erased.current.context.state := by
  obtain ⟨whereAt⟩ := spine p
  intro i d found
  have loc := nominal_location p i d found
  have eq : d = descriptor whereAt.c := by
    rcases loc with a|b
    · have eq := s.core.erased.current.context.state.base.source_injective (a.trans whereAt.name_a.symm)
      rw [eq,whereAt.read_a] at found
      exact (Option.some.inj found).symm
    · have eq := s.core.erased.current.context.state.base.source_injective (b.trans whereAt.name_b.symm)
      rw [eq,whereAt.read_b] at found
      exact (Option.some.inj found).symm
  subst d
  intro param member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl <;> rfl

end Yulang.GeneralMixedCompoundPointSpine307
