import Yulang.GeneralVersionedTraceDomain313
import Yulang.GeneralVersionedEssentialSupport313
import Yulang.GeneralNominalInspectionFiniteValues
import Yulang.GeneralNominalVersionedMixedObservations233

set_option backward.isDefEq.respectTransparency false
/-! A genuine constructor observation imposes a nontrivial constraint on
its source coordinate. In an inhabited journal it cannot turn an inert
reservation into a known constructor merely by moving it into the cache. -/
namespace Yulang.GeneralVersionedObservedEssential313
open GeneralNominalVersionedJournal232 (State Models)
open GeneralVersionedEssentialSupport313 (Apart Essential Inert)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalFiniteMeaning (build)
open GeneralVersionedTraceDomain313 (context)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedRefresh232 (refresh)

def replaceType (m : Assignment) (id : Nat) (ty : Ty) : Assignment :=
  fun n => if n = id then (ty,(m n).2) else m n

theorem unchanged (m : Assignment) (id : Nat) (ty : Ty) : Apart id m (replaceType m id ty) := by
  intro n away; simp [replaceType,away]

theorem cannot_substitute {s : State roles} {id : Nat} {m : Assignment}
    (valid : Models s m) (ty : Ty) (bad : ¬ Models s (replaceType m id ty)) :
    Essential s id := by
  intro inert
  exact bad ((inert m _ (unchanged m id ty)).mp valid)

theorem scalar {s : State roles} {m : Assignment} (valid : Models s m)
    (slot : Fin (context s).state.base.slots) (base : Inference.Base)
    (recorded : (context s).state.view.heads slot = .scalar base) :
    Essential s ((context s).state.base.source slot) := by
  let other : Inference.Base := if base = .int then .bool else .int
  have diff : other ≠ base := by
    by_cases h : base = .int
    · subst base; decide
    · simpa [other,h] using Ne.symm h
  apply cannot_substitute valid (.base other)
  intro patched
  have equal := GeneralNominalInspectionFiniteValues.scalar_slot (context s).state _ patched.1.1 slot recorded
  change Equivalent (replaceType m ((context s).state.base.source slot) (.base other) ((context s).state.base.source slot)).1 (.base base) at equal
  simp only [replaceType,ite_true] at equal
  have heads := GeneralNominalFiniteBracket.subtype_head (.scalar other) (.scalar base) Fin.elim0 Fin.elim0 equal.1
  exact diff (CommonNominalFullDemand.Head.base.inj heads)

theorem structural {s : State roles} {m : Assignment} (valid : Models s m)
    (slot : Fin (context s).state.base.slots) (kind : Fin (context s).state.view.kinds)
    (fields : Fin ((context s).state.view.shapes kind).arity → Fin (context s).state.base.slots)
    (recorded : (context s).state.view.heads slot = .structural kind fields) :
    Essential s ((context s).state.base.source slot) := by
  apply cannot_substitute valid (.base .int)
  intro patched
  have equal := GeneralNominalFiniteBracket.structural_slot (context s).state _ patched.1.1 slot kind fields recorded rfl
  have contra := GeneralNominalFiniteBracket.subtype_head (.scalar .int) (.structural ((context s).state.view.shapes kind))
    Fin.elim0 _ (show Subtype (.base .int) _ from by
      simpa only [replaceType,ite_true] using equal.1)
  cases h : (context s).state.view.shapes kind <;>
    simp only [h,GeneralNominalFiniteHeadInversion.head] at contra <;> contradiction

theorem scalar_not_nominal (name : Nat) (args : List Argument) :
    ¬ Subtype (.base .int) (nominal name args) := by
  intro below
  let env : CommonNominalFullDemand.Environment Row := ⟨fun _ => .bottom,fun _ => [.nominal name args.length]⟩
  have accept : CommonNominalFullDemand.ProbeAt Common.rowLe 0 env (observeTy 0 (nominal name args)) (.role 0) := by
    rw [observe_nominal]
    change CommonNominalFullDemand.Head.nominal name (args.map (argumentAt 0)).length ∈ env.roles 0
    simp [env]
  have impossible := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0 env (.role 0) accept
  change CommonNominalFullDemand.Head.base .int ∈ env.roles 0 at impossible
  simp [env] at impossible

theorem nominal {s : State roles} {m : Assignment} (valid : Models s m)
    (slot : Fin (context s).state.base.slots) (descriptor : GeneralNominalState.Descriptor (context s).state.base.slots)
    (recorded : (context s).state.nominals slot = some descriptor) :
    Essential s ((context s).state.base.source slot) := by
  apply cannot_substitute valid (.base .int)
  intro patched
  obtain ⟨values,_,equal⟩ := patched.1.1.2.1 slot descriptor recorded
  change Equivalent (replaceType m ((context s).state.base.source slot) (.base .int) ((context s).state.base.source slot)).1
    (CommonNominalFullCarrier.nominal descriptor.declaration.name values) at equal
  simp only [replaceType,ite_true] at equal
  exact scalar_not_nominal _ _ equal.1

theorem known {s : State roles} {m : Assignment} {id : Nat} (valid : Models s m)
    (observed : GeneralNominalState.Known (context s).state id) : Essential s id := by
  obtain ⟨slot,equal,head|⟨descriptor,recorded⟩⟩ := observed
  · cases recorded : (context s).state.view.heads slot with
    | scalar src => exact equal ▸ scalar valid slot src recorded
    | structural kind fields => exact equal ▸ structural valid slot kind fields recorded
    | deferred source => simp [GeneralNormalizedObservation.Snapshot.graph,GeneralNormalizedObservation.Head.node,recorded] at head
  · exact equal ▸ nominal valid slot descriptor recorded

theorem refreshed_essential {s : State roles} {m : Assignment} {id : Nat}
    (valid : Models s m) (certificate : Refresh s ctx)
    (observed : GeneralNominalState.Known ctx.state id) : Essential s id := by
  have after := (GeneralNominalVersionedMixedObservations233.refresh_models certificate).mpr valid
  exact (GeneralVersionedEssentialSupport313.observation
    (.refresh s ctx certificate)).mp (known after observed)

end Yulang.GeneralVersionedObservedEssential313
