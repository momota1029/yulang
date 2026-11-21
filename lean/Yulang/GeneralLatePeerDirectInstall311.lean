import Yulang.GeneralLatePeerFresh311

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 16500000
namespace Yulang.GeneralLatePeerDirectInstall311
open GeneralLatePeerSource311 (compiled root initial receiver registry checked initial_source)
open GeneralLatePeerRoot311 (direct branch z direct_args direct_output)
open GeneralLatePeerDirectPlan311 (plan packet report ctx two body no_children emitted_exact)
open GeneralLatePeerFirst311 (after reached generated_direct centers raw)
open GeneralLatePeerFresh311 (direct_different distinct_child)
open GeneralGeneratedNestedSource299 (model snapshot context snapshot_model)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarationExamples (roles)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedCandidates231 (inputs Prepared)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedInstall232 (install install_models)
open GeneralNominalVersionedMixedKernel234 (Step Committed)
open GeneralNominalRecursiveCandidates (arguments)
open GeneralNominalCenteredHeadOutputs (requests mem_requests_iff)
open GeneralNominalSaturationState (Generated)
open CommonNominalFullCarrier (Equivalent subtype_refl)

theorem located : arguments ctx (inputs direct.occurrence) = some [(two,two)] := by
  decide +kernel

theorem known : GeneralLatePeerGuard311.Known after direct.occurrence := by
  rintro ⟨i,unknown⟩
  exact unknown ⟨two,(congrArg Prod.fst (direct_args i)).symm,Or.inl (by decide +kernel)⟩

theorem linked : GeneralNominalState.Linked ctx.state (inputs direct.occurrence).demand := by
  refine ⟨?_,?_⟩
  · intro i
    change (direct.occurrence.demand.arguments i).1 ∈ GeneralNominalState.sources ctx.state ∧
      (direct.occurrence.demand.arguments i).2 ∈ GeneralNominalState.sources ctx.state
    rw [direct_args]
    exact ⟨GeneralNominalAllocationSupport.slot_source ctx.state two,GeneralNominalAllocationSupport.slot_source ctx.state two⟩
  · intro _ h; cases h

theorem initial_z : Equivalent (model z).1 (.base .int) := by
  have notZero : z ≠ 0 := by decide +kernel
  have notOne : z ≠ 1 := by decide +kernel
  change Equivalent (if z = 0 then GeneralGeneratedNestedSource299.nestedTy else
    if z = 1 then GeneralGeneratedNestedSource299.listTy else GeneralGeneratedNestedSource299.intTy) _
  simp only [ite_eq_right notZero,ite_eq_right notOne]
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem prepared : Prepared compiled ctx direct.occurrence receiver := by
  refine ⟨⟨rfl,initial_source.metadata.2⟩,linked,[(two,two)],located,?_,?_,model,?_⟩
  · exact GeneralLatePeerFresh311.fresh GeneralLatePeerFresh311.before compiled direct.occurrence.identity
      (fun h => direct_different (List.mem_singleton.mp h)) _
  · change GeneralNominalRecursiveInspection.Finished (GeneralNominalPacketSupport.report packet)
    rw [report]
    exact ⟨rfl,rfl,rfl⟩
  · exact (GeneralNominalVersionedCandidates231.headModels_packet_iff packet model).mpr
      (GeneralNominalVersionedPlans231.head_models (plan := plan)
        (GeneralLatePeerDirectPlan311.holds model GeneralLatePeerFirst311.inhabited initial_z))

theorem frame : Frame compiled after.core direct.occurrence 2 plan :=
  ⟨rfl,rfl,rfl,rfl,raw ▸ List.mem_cons_of_mem _ List.mem_cons_self,
    centers ▸ List.mem_cons_of_mem _ List.mem_cons_self,
    List.mem_cons_of_mem _ List.mem_cons_self,rfl,located,prepared⟩

theorem admin : GeneralNominalVersionedDiagnostic232.AdministrativeReady after direct.occurrence := by
  refine ⟨⟨direct,frame.center_recorded,rfl⟩,?_⟩
  intro a one identity b two equal
  rw [centers] at one two
  simp only [List.mem_cons,List.not_mem_nil,or_false] at one two
  rcases one with rfl|rfl|rfl
  · exact False.elim (direct_different (congrArg Occurrence.identity identity).symm)
  · rcases two with rfl|rfl|rfl
    · cases equal.1
    · exact .refl _
    · cases equal.1
  · exact False.elim (distinct_child (congrArg Occurrence.identity identity))

theorem request (out : GeneralSourceState.Output) (member : out ∈ requests after.core direct.occurrence) :
    out = ⟨1,z⟩ := by
  obtain ⟨site,present,alias,within⟩ := mem_requests_iff.mp member
  rw [raw] at present
  simp only [List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl|rfl|rfl
  · cases within
  · exact List.mem_singleton.mp (direct_output ▸ within)
  · cases within

theorem classes (m : Assignment) (out : Equivalent (m z).1 (.base .int)) :
    GeneralNominalVersionedEffects231.ClassEffects after.core direct.occurrence plan m := by
  constructor
  · intro target mem found given
    cases request target mem
    have eq : found = .explicit body := (Option.some.inj given).symm
    subst found
    intro atom seen
    cases List.mem_singleton.mp seen
    exact out
  · intro a one b two _
    cases request a one
    cases request b two
    exact ⟨subtype_refl _,subtype_refl _⟩

theorem picked :
    Local registry after direct.occurrence (.selected 2 (GeneralLatePeerGuard311.children plan)) :=
  GeneralLatePeerGuard311.select reached frame known rfl GeneralLatePeerFirst311.inhabited admin
    (GeneralLatePeerDirectPlan311.holds model GeneralLatePeerFirst311.inhabited initial_z) (classes model initial_z)
    (GeneralLatePeerGuard311.no_merged rfl)

abbrev effect := GeneralLatePeerGuard311.effect (p := plan) reached frame known
abbrev recorded := install after effect

theorem enabled : GeneralNominalVersionedMixedKernel234.Installable compiled after effect :=
  GeneralLatePeerGuard311.enabled (p := plan) reached frame known picked GeneralLatePeerFirst311.inhabited
    (GeneralLatePeerDirectPlan311.holds model GeneralLatePeerFirst311.inhabited initial_z) (classes model initial_z)

def bad : Assignment := fun n => if n = z then (.base .bool,(model n).2) else model n

theorem bad_before : Models after bad := by
  apply (GeneralLatePeerFirst311.models _).mpr
  apply (GeneralNominalVersionedJournal232.initial_models ..).mpr
  refine ⟨?_,GeneralNominalCenters.point_root_holds _ _ (fun _ => rfl) _⟩
  apply (GeneralNominalSemanticRawFrame236.source_models_same snapshot (first := model) (last := bad) ?_).mp snapshot_model
  intro n seen
  have ne : n ≠ z := by
    intro equal
    subst n
    have small := initial_source.below_seed z (GeneralNominalSemanticRawFrame236.contained snapshot seen)
    exact (by decide +kernel : ¬ z ≤ snapshot.seed) small
  simp only [bad,ite_eq_right ne]

theorem packet_implies (m : Assignment) (held : GeneralNominalVersionedPlans231.Holds plan m) :
    Equivalent (m z).1 (.base .int) := by
  have outs := held.2.2
  unfold GeneralNominalVersionedPlans231.Outputs at outs
  rw [emitted_exact] at outs
  exact outs _ List.mem_cons_self

theorem novel : ¬ Committed after plan := by
  intro committed
  have output := packet_implies bad (committed.1 bad bad_before).1
  apply GeneralNominalRepeatedLocal190.bool_not_below_int
  have bz : (bad z).1 = (.base .bool : CommonNominalFullCarrier.Ty) := by simp [bad]
  exact bz ▸ output.1

theorem step : Step compiled root after recorded := ⟨direct.occurrence,generated_direct,.install effect enabled novel⟩

theorem reached_recorded : B4TargetV8.Reachable (boundary roles) registry root recorded := by
  obtain ⟨start,ini,walk⟩ := reached
  exact ⟨start,ini,.tail walk step⟩

theorem models (m : Assignment) : Models recorded m ↔ Models after m ∧ Equivalent (m z).1 (.base .int) :=
  ⟨fun valid => ⟨GeneralNominalVersionedMixedKernel234.step_models step valid,
      packet_implies m (valid.2.1 plan List.mem_cons_self)⟩,
    fun ⟨valid,value⟩ => (install_models rfl).mpr
      ((GeneralNominalVersionedMixedCommon235.installation_models_iff ⟨rfl,checked⟩ reached rfl rfl).mpr
        ⟨valid,GeneralLatePeerDirectPlan311.holds m valid value,classes m value⟩)⟩

theorem model_now : Models recorded model := (models _).mpr ⟨GeneralLatePeerFirst311.inhabited,initial_z⟩

theorem centers_same : recorded.core.sites = after.core.sites := by
  change after.core.sites ++ GeneralNominalVersionedChildren232.emitted plan = _
  have n : (GeneralNominalVersionedChildren232.emitted plan).length = 0 := by
    rw [← List.length_map (f := GeneralNominalCenters.Site.occurrence),
      GeneralNominalVersionedChildren232.emitted_occurrences,no_children]
    rfl
  rw [List.length_eq_zero_iff.mp n,List.append_nil]

theorem alias_empty : recorded.core.erased.current.aliases = [] := rfl

end Yulang.GeneralLatePeerDirectInstall311
