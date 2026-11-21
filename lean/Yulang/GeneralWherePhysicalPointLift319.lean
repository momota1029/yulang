import Yulang.GeneralWherePhysicalPast319

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 26000000
namespace Yulang.GeneralWherePhysicalPointLift319
open GeneralWherePhysicalPast319
open GeneralDictionaryJournalRefinement228Source (roles snapshot descriptor)
open GeneralDictionaryJournalRefinement228Reobserve (pointSnapshot exactCopy)
open GeneralWherePhysicalDeferred319 (observations_from_old)
open GeneralWherePhysicalNominal319 (nominal_old nominal_new)
open GeneralWherePhysicalIndex319 (old new)
open GeneralNominalReobservationSteps (Revision Improves PointAt PointClosed PointDescriptor)
open GeneralNominalRefinements (renameDescriptor renameParameter)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalSaturationState (State)

theorem domain (i : Fin 7) : point.nominals i = none ↔ loose.nominals i = none := by
  refine Fin.addCases (m := 5) (n := 2) ?_ ?_ i
  · intro j
    change GeneralWherePhysicalNominal319.nominals pointSnapshot 2 (old 2 j) = none ↔
      GeneralWherePhysicalNominal319.nominals snapshot 2 (old 2 j) = none
    rw [nominal_old,nominal_old]
    change ((if j = 0 ∨ j = 1 then some exactCopy else none).map _) = none ↔
      ((if j = 0 then some (descriptor (4,2)) else if j = 1 then some exactCopy else none).map _) = none
    by_cases a : j = 0 <;> by_cases b : j = 1 <;> simp [a,b]
  · intro j
    change GeneralWherePhysicalNominal319.nominals pointSnapshot 2 (new 5 j) = none ↔
      GeneralWherePhysicalNominal319.nominals snapshot 2 (new 5 j) = none
    rw [nominal_new,nominal_new]

theorem point_map {d : GeneralNominalState.Descriptor 5} (exact : PointDescriptor d) :
    PointDescriptor (renameDescriptor (old 2) d) := by
  intro p used
  obtain ⟨q,member,rfl⟩ := List.mem_map.mp used
  have eq := exact q member
  cases q with
  | type param => exact congrArg (old 2) eq
  | row param => exact congrArg (old 2) eq

theorem closed : PointClosed point := by
  intro i d found
  refine Fin.addCases (m := 5) (n := 2) (fun j h => ?_) (fun j h => ?_) i found
  · change GeneralWherePhysicalNominal319.nominals pointSnapshot 2 (old 2 j) = some d at h
    rw [nominal_old] at h
    cases idx : pointSnapshot.nominals j with
    | none => rw [idx] at h; cases h
    | some prior =>
      rw [idx] at h
      cases Option.some.inj h
      exact point_map (GeneralDictionaryJournalRefinement228Reobserve.point_closed [] [] [] j prior idx)
  · change GeneralWherePhysicalNominal319.nominals pointSnapshot 2 (new 5 j) = some d at h
    rw [nominal_new] at h
    cases h

theorem historically_loose : ¬ PointAt loose (old 2 (0 : Fin 5)) := by
  rintro ⟨d,defined,exact⟩
  have name : renameDescriptor (old 2) (descriptor (4,2)) = d := Option.some.inj defined
  subst d
  have member : GeneralNominalState.Parameter.type (four,two) ∈
      (renameDescriptor (old 2) (descriptor (4,2))).arguments := List.mem_cons_self
  have bad : four = two := exact _ member
  have false' : (4:Nat) = 2 := congrArg (fun i : Fin 7 => i.val) bad
  cases false'

def revisionFor (s : State roles) (same : s.context.state = loose) : Revision s := by
  rcases s with ⟨⟨data,interp⟩,packets,sites,edges,aliases⟩
  dsimp only at same
  subst data
  exact ⟨point.nominals,point.catalogue,point.bodies_opaque,domain⟩

theorem snapshot_eq (s : State roles) (same : s.context.state = loose) :
    (revisionFor s same).snapshot = point := by
  rcases s with ⟨⟨data,interp⟩,packets,sites,edges,aliases⟩
  dsimp only at same
  subst data
  rfl

theorem improves (s : State roles) (same : s.context.state = loose) : Improves (revisionFor s same) := by
  rcases s with ⟨⟨data,interp⟩,packets,sites,edges,aliases⟩
  dsimp only at same
  subst data
  change (∀ i : Fin 7, PointAt loose i → PointAt point i) ∧
    ∃ i : Fin 7, ¬ PointAt loose i ∧ PointAt point i
  constructor
  · intro i ⟨oldEntry,recorded,_⟩
    cases r : point.nominals i with
    | none =>
      have oldNone := (domain i).mp r
      rw [recorded] at oldNone
      cases oldNone
    | some d => exact ⟨d,r,closed i d r⟩
  · have named : point.nominals (old 2 (0 : Fin 5)) = some (renameDescriptor (old 2) exactCopy) := rfl
    exact ⟨old 2 (0 : Fin 5),historically_loose,_,named,closed _ _ named⟩

theorem certificate (s : GeneralNominalCenteredHeadMatStepJournal.State roles)
    (sourceAt : s.core.erased.source.state = snapshot) (same : s.core.erased.current.context.state = loose) :
    GeneralNominalCenteredHeadMatStepRefresh.Reobserve s (revisionFor s.core.erased.current same) := by
  constructor
  · intro m valid
    rw [snapshot_eq] at valid
    rw [same]
    exact (point_models m).mp valid
  · rw [snapshot_eq]
    intro observation actual
    refine ⟨[],.source,?_⟩
    intro m valid
    exact observations_from_old layout extra m
      ((GeneralDictionaryJournalRefinement228Reobserve.point_models_iff m).mpr (sourceAt ▸ valid.1)) actual

end Yulang.GeneralWherePhysicalPointLift319
