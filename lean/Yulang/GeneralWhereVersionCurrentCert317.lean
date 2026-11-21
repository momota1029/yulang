import Yulang.GeneralWhereVersionReobserved317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 33000
set_option maxHeartbeats 51000000
namespace Yulang.GeneralWhereVersionCurrentCert317
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralLiveCompoundRegistry316 (registry declaration otherChild)
open GeneralLiveCompoundChildSite316 (signature)
open GeneralWhereVersionRootReport317 (plan same)
open GeneralWhereVersionCase317 (site occ)
open GeneralWhereVersionCommit317 (core)
open GeneralWhereVersionWitness317 (ParentHolds)
open GeneralWhereVersionCompiler317 (schema children child emit)
open GeneralWhereVersionInstall317 (fixed Models)
open GeneralWhereVersionSemantics317 (Holds full)
open GeneralNominalVersionedPlans231 (variables childSchema SchemaHolds)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalCenteredHeadMatPlanData (needed occurrence)
open GeneralDeferredLadderTransport302 (binder_eq capture_eq frame_eq)

theorem child_site_eq {a b : GeneralNominalCenters.Plan rs}
    (view : GeneralNominalCenteredHeadMatPlanData.Same a b) (clause : GeneralDeclarations.Clause)
    (sig : clause.Signature rs) : child a clause sig = child b clause sig := by
  rcases a with ⟨⟨ra,ca,sa,da,ha,ba⟩,ia,ja⟩
  rcases b with ⟨⟨rb,cb,sb,db,hb,bb⟩,ib,jb⟩
  have reg : ra = rb := view.registry
  have decl : da = db := view.declaration
  subst rb; subst db
  have alloc := congrFun (GeneralWhereVersionRecompile317.allocation_eq view) clause
  unfold child emit
  rw [frame_eq view,alloc,occurrence view,capture_eq view]
  congr 1
  funext i
  rw [GeneralNominalVersionedFrame231.emittedCenter_eq,
    GeneralNominalVersionedFrame231.emittedCenter_eq,
    GeneralNominalCenteredHeadMatPlanData.emitted_center view]

theorem child_site : child plan otherChild signature = site := (child_site_eq same _ _).symm

theorem all_rows_and_sites (m : Assignment) (valid : Models fixed m) : Holds plan m := by
  have p := (GeneralWhereVersionJournal317.fixed_iff m).mp valid
  have old := full m p
  have reread := GeneralWhereVersionReobserved317.rows_live m valid
  refine ⟨GeneralWhereVersionRootHead317.model_head m p,old.input,?_,
    GeneralWhereVersionRootHead317.schema_hold m p,reread.1,reread.2,?_⟩
  · intro name used
    rw [← capture_eq same,← binder_eq same]
    apply old.captures name
    rcases used with member|needs
    · exact .inl (same.declaration.symm ▸ member)
    · exact .inr ((needed same name).mpr needs)
  · intro clause member proof
    have exactly : clause = otherChild := List.mem_singleton.mp member
    subst clause
    exact ⟨child_site.symm ▸ GeneralWhereVersionCommit317.corrected_site m p,
      GeneralWhereVersionReobserved317.child_same_model m valid⟩

theorem outputs (m : Assignment) (valid : Models fixed m) :
    ∀ out ∈ root.demand.outputs, GeneralDictionaryDefaultEvidence204.OutputWitness plan m out := by
  intro out belongs
  have p := (GeneralWhereVersionJournal317.fixed_iff m).mp valid
  have framed := GeneralWhereVersionRootHead317.frame m p
  exact GeneralDictionaryDefaultEvidence204Laws.output_of_class_effects
    GeneralWhereVersionRootRegistry317.ready
    ((GeneralNominalVersionedEffects231.class_effects_iff ..).mp (GeneralWhereVersionRootRegistry317.classes m p))
    (GeneralNominalCenteredHeadOutputs.request_retained plan.packet.site framed.raw_recorded
      (GeneralNominalSaturationState.Alias.refl _) belongs)

theorem current_certified (m : Assignment) (valid : Models fixed m) :
    Frame registry core root declaration.id plan ∧ Holds plan m ∧
    (∀ out ∈ root.demand.outputs, GeneralDictionaryDefaultEvidence204.OutputWitness plan m out) ∧
    (∀ d ∈ children plan, GeneralNominalSaturationState.Generated core.erased.current root d) := by
  have p := (GeneralWhereVersionJournal317.fixed_iff m).mp valid
  refine ⟨GeneralWhereVersionRootHead317.frame m p,all_rows_and_sites m valid,outputs m valid,?_⟩
  intro d present
  rw [GeneralWhereVersionReobserved317.rows_and_occurrence.2] at present
  exact (List.mem_singleton.mp present).symm ▸ GeneralWhereVersionCommit317.produced

end Yulang.GeneralWhereVersionCurrentCert317
