import Yulang.GeneralWherePhysicalChildCert319

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 34000
set_option maxHeartbeats 39000000
namespace Yulang.GeneralWherePhysicalEvidence319
open GeneralWhereOriginSingleSource318 (registry declaration sourceRegistry)
open GeneralWherePhysicalCommit319 (final newChild emission step models produced)
open GeneralWherePhysicalReobserve319 (updated)
open GeneralWherePhysicalCurrentRead319 (plan)
open GeneralWherePhysicalCurrentFrame319 (frame)
open GeneralWherePhysicalPatch319 (n)
open GeneralWhereVersionInstall317 (Models)
open GeneralWhereVersionCompiler317 (children)
open GeneralWhereVersionSemantics317 (Holds)
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralLiveCompoundRegistry316 (leaf)
open GeneralNominalCenters GeneralSourceDictionaries
open GeneralDictionaryReadback (Payload erased_evidence_node)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedEffects231 (ClassEffects)
open GeneralNominalCenteredHeadMatEffects (Ready)
open CommonRoleOutermostResolver (All₂)

theorem compiled_child : children plan = [newChild.occurrence] := by
  rw [← GeneralWhereVersionInstall317.ordered,emission]
  rfl

theorem recorded : plan ∈ final.versionedWhere :=
  List.mem_cons_of_mem _ (List.mem_singleton_self _)

theorem ready : Ready final.mixed.core root plan := by
  intro out present
  apply GeneralWherePhysicalCurrentPick319.ready out
  exact (GeneralWhereOriginSuccessor318.requests_unchanged _ _ _
    GeneralWherePhysicalCommit319.silent root out).mp present

theorem outputs (m : Assignment) (valid : Models final m) :
    ∀ out ∈ root.demand.outputs, GeneralDictionaryDefaultEvidence204.OutputWitness plan m out := by
  intro out request
  apply GeneralDictionaryDefaultEvidence204Laws.output_of_class_effects ready
    ((GeneralNominalVersionedEffects231.class_effects_iff ..).mp (valid.2 plan recorded).2)
  exact GeneralNominalCenteredHeadOutputs.request_retained plan.packet.site
    (List.mem_append_left _ frame.raw_recorded)
    (GeneralNominalSaturationState.Alias.refl _) request

structure RootCertificate (m : Assignment) : Prop where
  entry : plan ∈ final.versionedWhere
  transaction : GeneralWhereVersionInstall317.InstallStep sourceRegistry updated final
  before : Frame registry updated.mixed.core root declaration.id plan
  typed : Holds plan m
  effects : ClassEffects final.mixed.core root plan m
  output : ∀ out ∈ root.demand.outputs, GeneralDictionaryDefaultEvidence204.OutputWitness plan m out
  ordered : ∀ d ∈ children plan, GeneralNominalSaturationState.Generated final.mixed.core.erased.current root d

def Instance (m : Assignment) : LocalInstance roles :=
  fun focus key kids =>
    (focus = root ∧ key = declaration.id ∧ kids = children plan ∧ RootCertificate m) ∨
    GeneralNominalVersionedEvidence231.Instance registry final.mixed.core m focus key kids

def Evidence (m : Assignment) (focus : Occurrence roles) (payload : Payload) : Prop :=
  ErasedEvidence (Instance m) focus payload

theorem recursive (m : Assignment) (valid : Models final m) :
    Evidence m root (.node declaration.id [.node leaf.id []]) := by
  have rootOk : Instance m root declaration.id [newChild.occurrence] := by
    refine .inl ⟨rfl,rfl,compiled_child.symm,recorded,step,frame,(valid.2 plan recorded).1,
      (valid.2 plan recorded).2,outputs m valid,?_⟩
    intro d member
    rw [compiled_child] at member
    cases List.mem_singleton.mp member
    exact produced
  have kid : Instance m newChild.occurrence leaf.id [] :=
    .inr ⟨_,GeneralWherePhysicalChildCert319.certificate m valid⟩
  exact erased_evidence_node _ _ _ _ _ rootOk
    (.cons (erased_evidence_node _ _ _ _ _ kid .nil) .nil)

theorem same_model : Models final n ∧ Evidence n root (.node declaration.id [.node leaf.id []]) :=
  ⟨models,recursive n models⟩

end Yulang.GeneralWherePhysicalEvidence319
