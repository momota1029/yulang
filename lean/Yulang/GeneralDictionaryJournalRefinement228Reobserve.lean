import Yulang.GeneralDictionaryJournalRefinement228Source
import Yulang.GeneralNominalCenteredHeadMatStepRefresh
import Yulang.GeneralDictionaryDefaultKernel208

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryJournalRefinement228Reobserve
open GeneralDictionaryJournalRefinement228Source
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
abbrev loose := descriptor (4,2)
abbrev exactCopy := descriptor (2,2)

abbrev pointSnapshot : GeneralNominalState.State :=
  { snapshot with
    nominals := fun slot => if slot = 0 ∨ slot = 1 then some exactCopy else none
    catalogue := by
      intro slot d found
      split at found
      · cases Option.some.inj found; rfl
      · cases found
    bodies_opaque := by
      intro slot d found
      split at found
      · rename_i either
        rcases either with rfl | rfl <;> rfl
      · cases found }

theorem weaken_descriptor (m : Assignment) (valid : GeneralNominalCommonBridge.Models base m)
    (denotes : GeneralNominalState.Denotes base m slot exactCopy) :
    GeneralNominalState.Denotes base m slot loose := by
  obtain ⟨values,fits,equal⟩ := denotes
  have low : Subtype (m 4).1 (m 2).1 :=
    valid.1 (.tyLe (.var 4) (.var 2)) (by simp [base,GeneralSourceState.equationAtoms])
  refine ⟨values,?_,equal⟩
  change GeneralNominalState.FitsAll base m [.type (2,2),.type (2,2)] values at fits
  cases fits with
  | @cons _ a _ rest first tail =>
    cases tail with
    | @cons _ b _ tail second rest =>
      cases rest
      cases a with
      | inr => cases first
      | inl a =>
        cases b with
        | inr => cases second
        | inl b =>
          exact .cons ⟨subtype_trans low first.1,first.2⟩
            (.cons ⟨subtype_trans low second.1,second.2⟩ .nil)

theorem point_models_iff (m : Assignment) :
    GeneralNominalState.Models pointSnapshot m ↔ GeneralNominalState.Models snapshot m := by
  constructor
  · intro valid
    refine ⟨valid.1,?_,valid.2.2⟩
    intro slot d found
    change (if slot = 0 then some loose else if slot = 1 then some exactCopy else none) = some d at found
    split at found
    · rename_i same
      subst slot
      cases Option.some.inj found
      exact weaken_descriptor m valid.1 (valid.2.1 0 exactCopy rfl)
    · split at found
      · rename_i same
        subst slot
        cases Option.some.inj found
        exact valid.2.1 1 exactCopy rfl
      · cases found
  · intro valid
    refine ⟨valid.1,?_,valid.2.2⟩
    intro slot d found
    change (if slot = 0 ∨ slot = 1 then some exactCopy else none) = some d at found
    split at found
    · rename_i either
      cases Option.some.inj found
      rcases either with rfl | rfl
      · obtain ⟨values,fits,equal⟩ := valid.2.1 1 exactCopy rfl
        have copies := alias_zero m valid
        exact ⟨values,fits,⟨subtype_trans copies.1 equal.1,subtype_trans equal.2 copies.2⟩⟩
      · exact valid.2.1 1 exactCopy rfl
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
  change (if slot = 0 ∨ slot = 1 then some exactCopy else none) = some descriptor at found
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
  change (if slot = 0 ∨ slot = 1 then some exactCopy else none) = none ↔
    (if slot = 0 then some loose else if slot = 1 then some exactCopy else none) = none
  by_cases six : slot = 0 <;> by_cases seven : slot = 1 <;> simp [six,seven]

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
    change (if slot = 0 then some loose else if slot = 1 then some exactCopy else none) = some descriptor at found
    have domain : slot = 0 ∨ slot = 1 := by
      split at found
      · exact Or.inl (by assumption)
      · split at found
        · exact Or.inr (by assumption)
        · cases found
    refine ⟨exactCopy,?_,?_⟩
    · change (if slot = 0 ∨ slot = 1 then some exactCopy else none) = some exactCopy
      simp [domain]
    · exact point_closed allocated reserved ordinary slot exactCopy (by simp [domain])
  · refine ⟨(0 : Fin 5),?_,exactCopy,rfl,?_⟩
    · rintro ⟨descriptor,found,point⟩
      have equal : loose = descriptor := Option.some.inj found
      subst descriptor
      have impossible := point (.type (4,2)) (by simp)
      cases impossible
    · exact point_closed allocated reserved ordinary 0 exactCopy rfl

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


end Yulang.GeneralDictionaryJournalRefinement228Reobserve
