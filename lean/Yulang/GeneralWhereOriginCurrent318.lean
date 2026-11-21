import Yulang.GeneralWhereOriginInstall318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 18000000
namespace Yulang.GeneralWhereOriginCurrent318
open GeneralNominalCenters (Plan)
open GeneralNominalCenteredHeadMatPlanData (Same)
open GeneralWhereOriginReady318 (HeadReady)
open GeneralWhereVersionSemantics317 (Holds)
open GeneralWhereVersionCompiler317 (schema children child)
open GeneralWhereVersionInstall317 (Journal Models)
open GeneralNominalVersionedPlans231 (variables childSchema)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatEffects (Ready)
open GeneralNominalCenteredHeadOutputs (request_retained)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalSaturationState (Alias Generated)

/-- A genuine current frame with equal erased observation may use a prior
record's children and rows. Its *current* head/captures/classes are checked
separately; an arbitrary changed report cannot be replayed this way. -/
theorem reread_holds {j : Journal rs} {p q : Plan rs} {m : Assignment}
    (old : p ∈ j.versionedWhere) (state : Models j m)
    (same : Same p q) (current : HeadReady j q m) :
    Holds q m ∧ children q = children p := by
  have record := (state.2 p old).1
  have out := GeneralWhereVersionRecompile317.schema_eq same
  have values := GeneralWhereVersionReobserved317.variables_eq same m
  refine ⟨⟨current.head,current.input,current.captures,current.schema,?_,?_,?_⟩,
    (GeneralWhereVersionRecompile317.children_eq same).symm⟩
  · rw [← out]
    exact record.materialized
  · rw [← out,← values]
    exact record.rows
  · intro c currentMem sig
    have stored := record.childSemantics c (same.declaration.symm ▸ currentMem) sig
    have site := GeneralWhereVersionCurrentCert317.child_site_eq same c sig
    have priorSchema : childSchema p c sig = childSchema q c sig := by
      rw [GeneralNominalVersionedPlans231.childSchema_eq,
        GeneralNominalVersionedPlans231.childSchema_eq,GeneralNominalCenteredHeadMatPlanData.child_schema same]
    exact ⟨site ▸ stored.1,by rw [← priorSchema,← values]; exact stored.2⟩

theorem current_output {j : Journal rs} {q : Plan rs} {m : Assignment}
    (framed : Frame registry j.mixed.core focus key q)
    (ready : Ready j.mixed.core focus q) (current : HeadReady j q m)
    (seen : output ∈ focus.demand.outputs) :
    GeneralDictionaryDefaultEvidence204.OutputWitness q m output := by
  have effects := current.effects
  rw [framed.occurrence_eq] at effects
  exact GeneralDictionaryDefaultEvidence204Laws.output_of_class_effects ready
    ((GeneralNominalVersionedEffects231.class_effects_iff ..).mp effects)
    (request_retained q.packet.site framed.raw_recorded
      (by rw [framed.occurrence_eq]; exact Alias.refl _) (framed.occurrence_eq.symm ▸ seen))

end Yulang.GeneralWhereOriginCurrent318
