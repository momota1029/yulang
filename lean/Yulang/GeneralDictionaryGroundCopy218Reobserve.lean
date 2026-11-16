import Yulang.GeneralDictionaryGroundCopy218Install

/-! Pointifying the loose descriptor is justified by the original source alone.
Allocation ownership, reservations, and ordinary journal extensions are retained. -/
namespace Yulang.GeneralDictionaryGroundCopy218Reobserve
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryLooseVariant217
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open Core.PresenceGeneration (TyTerm)

abbrev pointSnapshot : GeneralNominalState.State :=
  { snapshot with
    nominals := fun slot => if slot = 6 ∨ slot = 7 then some exactCopy else none
    catalogue := by
      intro slot descriptor found
      split at found
      · cases Option.some.inj found; rfl
      · cases found
    bodies_opaque := by
      intro slot descriptor found
      split at found
      · rename_i either
        rcases either with rfl | rfl <;> rfl
      · cases found }

private theorem base_equation (model : Assignment) (valid : GeneralNominalCommonBridge.Models base model)
    (slot : Fin 8) (term : TyTerm (Fin 8)) (member : (slot,term) ∈ equations) :
    Equivalent (model slot.val).1 (term.eval CommonNominalFullCarrier.model
      (GeneralNominalCommonBridge.assignment base model)) := by
  constructor
  · exact valid.1 _ (List.mem_flatMap.mpr ⟨(slot,term),member,List.mem_cons_self⟩)
  · exact valid.1 _ (List.mem_flatMap.mpr ⟨(slot,term),member,List.mem_cons_of_mem _ (List.mem_singleton_self _)⟩)

theorem envelope (model : Assignment) (valid : GeneralNominalCommonBridge.Models base model) :
    Equivalent (model 2).1 low ∧ Equivalent (model 3).1 high := by
  have bottom := base_equation model valid 0 .bottom (by simp [equations])
  have top := base_equation model valid 1 .top (by simp [equations])
  have lower := base_equation model valid 2 (.variant 0 (.var 0)) (by simp [equations])
  have upper := base_equation model valid 3 (.variant 0 (.var 1)) (by simp [equations])
  exact ⟨⟨subtype_trans lower.1 ((common_variant_iff ..).mpr bottom.1),
      subtype_trans ((common_variant_iff ..).mpr bottom.2) lower.2⟩,
    ⟨subtype_trans upper.1 ((common_variant_iff ..).mpr top.1),
      subtype_trans ((common_variant_iff ..).mpr top.2) upper.2⟩⟩

theorem endpoint_bounds (model : Assignment) (valid : GeneralNominalCommonBridge.Models base model) :
    GeneralNominalCaptureMerges.Fits model (2,3) (model 4).1 ∧
      GeneralNominalCaptureMerges.Fits model (2,3) (model 5).1 := by
  have limits := envelope model valid
  have a := base_equation model valid 4 (.variant 0 (.base .int)) (by simp [equations])
  have b := base_equation model valid 5 (.variant 0 (.base .bool)) (by simp [equations])
  exact ⟨⟨subtype_trans limits.1.1 (subtype_trans fits_first.1 a.2),
      subtype_trans a.1 (subtype_trans fits_first.2 limits.2.2)⟩,
    ⟨subtype_trans limits.1.1 (subtype_trans fits_second.1 b.2),
      subtype_trans b.1 (subtype_trans fits_second.2 limits.2.2)⟩⟩

theorem weaken_descriptor (model : Assignment) (valid : GeneralNominalCommonBridge.Models base model)
    (denotes : GeneralNominalState.Denotes base model slot exactCopy) :
    GeneralNominalState.Denotes base model slot loose := by
  obtain ⟨values,fits,equal⟩ := denotes
  have bounds := endpoint_bounds model valid
  refine ⟨values,?_,equal⟩
  change GeneralNominalState.FitsAll base model [.type (4,4),.type (5,5)] values at fits
  cases fits with
  | @cons _ a _ rest fitA remaining =>
      cases remaining with
      | @cons _ b _ tail fitB remaining =>
          cases remaining
          cases a with
          | inr => cases fitA
          | inl a =>
              cases b with
              | inr => cases fitB
              | inl b =>
                  exact .cons ⟨subtype_trans bounds.1.1 fitA.1,subtype_trans fitA.2 bounds.1.2⟩
                    (.cons ⟨subtype_trans bounds.2.1 fitB.1,subtype_trans fitB.2 bounds.2.2⟩ .nil)

theorem point_models_iff (model : Assignment) :
    GeneralNominalState.Models pointSnapshot model ↔ GeneralNominalState.Models snapshot model := by
  constructor
  · intro valid
    refine ⟨valid.1,?_,valid.2.2⟩
    intro slot descriptor found
    change (if slot = 6 then some loose else if slot = 7 then some exactCopy else none) = some descriptor at found
    split at found
    · rename_i same
      subst slot
      cases Option.some.inj found
      exact weaken_descriptor model valid.1 (valid.2.1 6 exactCopy rfl)
    · split at found
      · rename_i same
        subst slot
        cases Option.some.inj found
        exact valid.2.1 7 exactCopy rfl
      · cases found
  · intro valid
    refine ⟨valid.1,?_,valid.2.2⟩
    intro slot descriptor found
    change (if slot = 6 ∨ slot = 7 then some exactCopy else none) = some descriptor at found
    split at found
    · rename_i either
      cases Option.some.inj found
      rcases either with rfl | rfl
      · obtain ⟨values,fits,equal⟩ := valid.2.1 7 exactCopy rfl
        have copies := copy_equal model valid
        exact ⟨values,fits,⟨subtype_trans copies.1 equal.1,subtype_trans equal.2 copies.2⟩⟩
      · exact valid.2.1 7 exactCopy rfl
    · cases found

abbrev looseExtended (allocated : List GeneralNominalIdentities.Origin)
    (reserved : List Nat) (ordinary : List (PresenceNormalForm.Atom Nat)) : GeneralNominalState.State :=
  { snapshot with allocated := allocated, reserved := reserved, ordinary := ordinary }

abbrev pointExtended (allocated : List GeneralNominalIdentities.Origin)
    (reserved : List Nat) (ordinary : List (PresenceNormalForm.Atom Nat)) : GeneralNominalState.State :=
  { pointSnapshot with allocated := allocated, reserved := reserved, ordinary := ordinary }

theorem extended_models_iff (allocated reserved ordinary) (model : Assignment) :
    GeneralNominalState.Models (pointExtended allocated reserved ordinary) model ↔
      GeneralNominalState.Models (looseExtended allocated reserved ordinary) model := by
  constructor
  · intro valid
    have original := (point_models_iff model).mp ⟨valid.1,valid.2.1,by intro _ impossible; cases impossible⟩
    exact ⟨original.1,original.2.1,valid.2.2⟩
  · intro valid
    have updated := (point_models_iff model).mpr ⟨valid.1,valid.2.1,by intro _ impossible; cases impossible⟩
    exact ⟨updated.1,updated.2.1,valid.2.2⟩

theorem point_closed (allocated reserved ordinary) :
    GeneralNominalReobservationSteps.PointClosed (pointExtended allocated reserved ordinary) := by
  intro slot descriptor found
  change (if slot = 6 ∨ slot = 7 then some exactCopy else none) = some descriptor at found
  split at found
  · cases Option.some.inj found
    intro parameter member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> rfl
  · cases found

theorem recorded_source (allocated reserved ordinary) (model : Assignment)
    (valid : GeneralNominalState.Models snapshot model)
    (recorded : GeneralCanonicalObservations.Recorded (pointExtended allocated reserved ordinary) observation) :
    observation.Holds model := by
  have point := (point_models_iff model).mpr valid
  have original : GeneralCanonicalObservations.Recorded pointSnapshot observation := by
    cases recorded with
    | scalar slot scalar found => exact GeneralCanonicalObservations.Recorded.scalar (snapshot := pointSnapshot) slot scalar found
    | structural slot kind children found => exact GeneralCanonicalObservations.Recorded.structural (snapshot := pointSnapshot) slot kind children found
    | nominal slot descriptor found => exact GeneralCanonicalObservations.Recorded.nominal (snapshot := pointSnapshot) slot descriptor found
  exact GeneralCanonicalObservations.recorded_sound pointSnapshot model point original

theorem source_cache (state : GeneralNominalCenteredHeadMatStepJournal.State roles)
    (source : state.core.erased.source.state = snapshot) (allocated reserved ordinary) :
    GeneralNominalCenteredHeadMatStepObservations.CacheSound state (pointExtended allocated reserved ordinary) := by
  intro observation recorded
  refine ⟨[],.source,?_⟩
  intro model valid
  exact recorded_source allocated reserved ordinary model (source ▸ valid.1) recorded

def revisionFor (prior : GeneralNominalSaturationState.State roles) (allocated reserved ordinary)
    (same : prior.context.state = looseExtended allocated reserved ordinary) :
    GeneralNominalReobservationSteps.Revision prior := by
  rcases prior with ⟨⟨data,interpretation⟩,packets,sites,edges,aliases⟩
  dsimp only at same
  subst data
  refine ⟨pointSnapshot.nominals,pointSnapshot.catalogue,pointSnapshot.bodies_opaque,?_⟩
  intro slot
  change (if slot = 6 ∨ slot = 7 then some exactCopy else none) = none ↔
    (if slot = 6 then some loose else if slot = 7 then some exactCopy else none) = none
  by_cases six : slot = 6 <;> by_cases seven : slot = 7 <;> simp [six,seven]

theorem revision_snapshot (prior : GeneralNominalSaturationState.State roles) (allocated reserved ordinary)
    (same : prior.context.state = looseExtended allocated reserved ordinary) :
    (revisionFor prior allocated reserved ordinary same).snapshot = pointExtended allocated reserved ordinary := by
  rcases prior with ⟨⟨data,interpretation⟩,packets,sites,edges,aliases⟩
  dsimp only at same
  subst data
  rfl

theorem revision_improves (prior : GeneralNominalSaturationState.State roles) (allocated reserved ordinary)
    (same : prior.context.state = looseExtended allocated reserved ordinary) :
    GeneralNominalReobservationSteps.Improves (revisionFor prior allocated reserved ordinary same) := by
  rcases prior with ⟨⟨data,interpretation⟩,packets,sites,edges,aliases⟩
  dsimp only at same
  subst data
  constructor
  · intro slot old
    obtain ⟨descriptor,found,_⟩ := old
    change (if slot = 6 then some loose else if slot = 7 then some exactCopy else none) = some descriptor at found
    have domain : slot = 6 ∨ slot = 7 := by
      split at found
      · exact Or.inl (by assumption)
      · split at found
        · exact Or.inr (by assumption)
        · cases found
    refine ⟨exactCopy,?_,?_⟩
    · change (if slot = 6 ∨ slot = 7 then some exactCopy else none) = some exactCopy
      simp [domain]
    · exact point_closed allocated reserved ordinary slot exactCopy (by simp [domain])
  · refine ⟨(6 : Fin 8),?_,exactCopy,rfl,?_⟩
    · rintro ⟨descriptor,found,point⟩
      have equal : loose = descriptor := Option.some.inj found
      subst descriptor
      have impossible := point (.type (2,3)) (by simp)
      cases impossible
    · exact point_closed allocated reserved ordinary 6 exactCopy rfl

theorem revision_certificate (state : GeneralNominalCenteredHeadMatStepJournal.State roles)
    (source : state.core.erased.source.state = snapshot) (allocated reserved ordinary)
    (same : state.core.erased.current.context.state = looseExtended allocated reserved ordinary) :
    GeneralNominalCenteredHeadMatStepRefresh.Reobserve state
      (revisionFor state.core.erased.current allocated reserved ordinary same) := by
  constructor
  · intro model valid
    rw [revision_snapshot] at valid
    rw [same]
    exact (extended_models_iff allocated reserved ordinary model).mp valid
  · rw [revision_snapshot]
    exact source_cache state source allocated reserved ordinary

theorem revision_step (state : GeneralNominalCenteredHeadMatStepJournal.State roles)
    (source : state.core.erased.source.state = snapshot) (allocated reserved ordinary)
    (same : state.core.erased.current.context.state = looseExtended allocated reserved ordinary)
    (value : GeneralDeclarations.Registry) (focus : GeneralSourceDictionaries.Occurrence roles) :
    GeneralDictionaryDefaultKernel208.Step value focus state
      (GeneralNominalCenteredHeadMatStepJournal.change state
        (revisionFor state.core.erased.current allocated reserved ordinary same).result) :=
  ⟨focus,.root,.administrative (.reobserve focus _
    (revision_certificate state source allocated reserved ordinary same)
    (revision_improves state.core.erased.current allocated reserved ordinary same))⟩

theorem revision_models (state : GeneralNominalCenteredHeadMatStepJournal.State roles)
    (source : state.core.erased.source.state = snapshot) (allocated reserved ordinary)
    (same : state.core.erased.current.context.state = looseExtended allocated reserved ordinary) (model : Assignment) :
    GeneralNominalCenteredHeadMatStepJournal.Models
      (GeneralNominalCenteredHeadMatStepJournal.change state
        (revisionFor state.core.erased.current allocated reserved ordinary same).result) model ↔
      GeneralNominalCenteredHeadMatStepJournal.Models state model :=
  GeneralNominalCenteredHeadMatStepRefresh.reobserve_models
    (revision_certificate state source allocated reserved ordinary same)

open GeneralDictionaryGroundCopy218Install (installed packet plan effect)
open GeneralNominalCenteredHeadMatStepJournal (Models change)

abbrev installedAllocation := packet.privateContext.state.allocated
abbrev installedReservation := packet.privateContext.state.reserved
abbrev installedOrdinary := packet.privateContext.state.ordinary

theorem installed_snapshot : installed.core.erased.current.context.state =
    looseExtended installedAllocation installedReservation installedOrdinary := rfl

abbrev revision := revisionFor installed.core.erased.current
  installedAllocation installedReservation installedOrdinary installed_snapshot

abbrev reobserved := change installed revision.result

theorem certificate : GeneralNominalCenteredHeadMatStepRefresh.Reobserve installed revision :=
  revision_certificate installed rfl installedAllocation installedReservation installedOrdinary installed_snapshot

theorem reobserve_step : GeneralDictionaryDefaultBoundary208.Step sourceRegistry root installed reobserved :=
  revision_step installed rfl installedAllocation installedReservation installedOrdinary installed_snapshot registry root

theorem reobserved_models (model : Assignment) : Models reobserved model ↔ Models installed model :=
  GeneralNominalCenteredHeadMatStepRefresh.reobserve_models certificate

theorem reobserved_model : Models reobserved GeneralDictionaryGroundCopy218Install.model :=
  (reobserved_models _).mpr GeneralDictionaryGroundCopy218Install.installed_models

theorem reobserved_reachable :
    B4TargetV7.Reachable (GeneralDictionaryDefaultBoundary208.boundary roles) sourceRegistry root reobserved := by
  obtain ⟨start,initial,path⟩ := GeneralDictionaryGroundCopy218Install.installed_reachable
  exact ⟨start,initial,.tail path reobserve_step⟩

theorem reobserved_snapshot : reobserved.core.erased.current.context.state =
    pointExtended installedAllocation installedReservation installedOrdinary :=
  revision_snapshot installed.core.erased.current installedAllocation installedReservation installedOrdinary installed_snapshot

theorem reobserved_point_closed :
    GeneralNominalReobservationSteps.PointClosed reobserved.core.erased.current.context.state := by
  rw [reobserved_snapshot]
  exact point_closed installedAllocation installedReservation installedOrdinary

theorem retained : reobserved.core.sites = installed.core.sites ∧
    reobserved.core.erased.current.sites = installed.core.erased.current.sites ∧
    reobserved.core.plans = installed.core.plans ∧
    reobserved.core.erased.current.edges = installed.core.erased.current.edges ∧
    reobserved.core.erased.current.aliases = installed.core.erased.current.aliases ∧
    reobserved.effects = installed.effects := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

end Yulang.GeneralDictionaryGroundCopy218Reobserve
