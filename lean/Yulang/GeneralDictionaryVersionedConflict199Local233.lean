import Yulang.GeneralDictionaryVersionedConflict199233
import Yulang.GeneralNominalVersionedDiagnosticLaws232
import Yulang.B4SkeletonV8
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionedConflict199Local233
open GeneralDictionaryMatPriorConflictSource199
open GeneralDictionaryVersionedConflict199233
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open CommonNominalFullCarrier
open GeneralNominalVersionedJournal232

theorem survivor : GeneralNominalVersionedCandidates231.Survivor registry context root 37 [] :=
  ⟨GeneralDictionaryMatPriorConflictLocal199.known,declaration,List.mem_singleton_self _,declaration_checked,
    rfl,rfl,[(1,1)],rfl,prepared,children_empty.symm⟩

theorem unique : GeneralNominalVersionedCandidates231.Unique registry context root 37 [] := by
  refine ⟨survivor,?_⟩
  intro key kids found
  have copy := found
  obtain ⟨_,d,visible,_,identity,_⟩ := found
  cases List.mem_singleton.mp visible
  have same : key = 37 := identity.symm
  subst key
  exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional checked copy survivor⟩

theorem frame_plan {candidate : Plan roles}
    (framed : GeneralNominalVersionedEvidence231.Frame registry current.core root key candidate) : candidate = plan :=
  GeneralNominalVersionedFrameFunctional232.frame_plan_unique rfl rfl rfl framed frame

theorem scalar_no_edge (last : GeneralNominalRecursiveInspection.Origin) :
    ¬ GeneralNominalVersionedCycles232.Edge current (.source 1) last := by
  rintro ⟨parent,test,index,headed,equal,_⟩
  have same := equal model current_model
  obtain ⟨actual,seen⟩ := same.2.1
  have value := same.2.2 _ actual (.source 1) seen
  have shape := (headed model current_model).2 actual seen
  change Equivalent (.base .int) actual at value
  cases test with
  | scalar => exact Fin.elim0 index
  | nominal name count =>
    obtain ⟨values,_,head⟩ := shape
    exact GeneralNominalPeelingOrigins.base_not_nominal .int name values (subtype_trans value.1 head.1)
  | structural kind =>
    obtain ⟨values,length,head⟩ := shape
    exact GeneralNominalCenteredHeadMatPairCycles.scalar_no_shape length
      ⟨subtype_trans value.1 head.1,subtype_trans head.2 value.2⟩

theorem scalar_acyclic : ¬ GeneralNominalVersionedCycles232.Cyclic current (.source 1) := by
  rintro ⟨⟨last,edge,_⟩,_⟩
  exact scalar_no_edge last edge

theorem administrative_ready : GeneralNominalVersionedDiagnostic232.AdministrativeReady current root := by
  refine ⟨⟨_,List.mem_singleton_self _,rfl⟩,?_⟩
  intro first one same last two _
  cases List.mem_singleton.mp one
  cases List.mem_singleton.mp two
  exact .refl _

theorem safe : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) registry current root := by
  refine ⟨GeneralDictionaryMatPriorConflictLocal199.known,?_,?_,?_⟩
  · rintro (old | (⟨index,cycle⟩ | ⟨site,present,same,index,cycle⟩))
    · obtain ⟨_,_,_,slot,_,cycle⟩ := old
      exact GeneralNominalCenteredHeadWFJoinLocal.no_raw_recurs slot cycle
    · exact scalar_acyclic cycle
    · cases List.mem_singleton.mp present; exact scalar_acyclic cycle
  · rintro (old | ⟨candidate,framed,entry,member,cycle⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := old
      exact GeneralNominalCenteredHeadWFJoinLocal.no_raw_recurs visited.1 cycle
    · cases frame_plan framed
      rw [GeneralDictionaryMatPriorConflictLocal199.inspection_exact] at member
      cases List.mem_singleton.mp member
      exact scalar_acyclic cycle
  · rintro (⟨_,d,visible,_,_,unprepared⟩ | unclosed)
    · cases List.mem_singleton.mp visible; exact unprepared prepared
    · exact unclosed administrative_ready


theorem no_effects (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models snapshot assignment) :
    ¬ GeneralNominalVersionedEffects231.ClassEffects current.core root plan assignment :=
  fun held => GeneralDictionaryMatPriorConflict199.no_effects assignment valid
    ((GeneralNominalVersionedEffects231.class_effects_iff ..).mp held)

theorem output_conflict : GeneralNominalVersionedDiagnostic232.OutputConflict registry current root 37 := by
  constructor
  · exact ⟨model,current_model,⟨[],unique⟩,plan,frame,GeneralDictionaryMatPriorConflict199.ready,
      head_equations model source_model⟩
  · rintro ⟨assignment,valid,_,candidate,framed,_,_,effects⟩
    rw [frame_plan framed] at effects
    exact no_effects assignment valid.1.1 effects

theorem rejected : GeneralNominalVersionedSourceBoundary232.Local registry current root .rejected := by
  classical
  apply GeneralNominalVersionedSourceBoundary232.local_iff.mpr
  apply GeneralNominalVersionedBoundary232.local_iff.mpr
  by_cases sharing : GeneralNominalVersionedDiagnostic232.SharingConflict registry current root
  · exact B4TargetV8.sharing_unique_rejected sharing unique
  · apply B4TargetV8.Local.ordinary sharing
    by_cases merged : GeneralNominalVersionedMergedConflict232.MergedOutputConflict current root
    · exact B4TargetV7.merged_unique_rejected merged unique
    · exact .ordinary merged (B4TargetV6.output_conflict_rejected safe unique output_conflict)


theorem stable : GeneralNominalVersionedKernel232.Stable registry current root := by
  intro focus generated after action
  have same := GeneralDictionaryMatPriorConflict199.generated_only_root focus generated
  cases action with
  | administrative action =>
    cases action with
    | enqueue linked absent => exact absent _ (List.mem_singleton_self _) same.symm
    | refresh context certificate source member unknown known =>
      exact unknown (GeneralNominalCenteredTerminalForkSource.all_known _ source member)
    | equate first last one two equal novel =>
      apply novel
      intro assignment sourceModels
      exact equal assignment ((lift_models ..).mpr
        ((GeneralNominalCenteredHeadMatStepJournal.point_initial_models (fun _ => rfl)).mpr sourceModels))
    | reobserve revision certificate improved =>
      exact GeneralNominalReobservationSteps.pointClosed_no_revision
        (GeneralNominalCenteredTerminalForkSource.point_closed false) revision improved
  | refresh focus context certificate source member unknown known =>
    exact unknown (GeneralNominalCenteredTerminalForkSource.all_known _ source member)
  | install candidate enabled novel =>
    have framed := same ▸ enabled.snapshot_eq ▸ enabled.registry_eq ▸ candidate.frame
    have planEq := frame_plan framed
    obtain ⟨assignment,_,packet,_⟩ := enabled.common
    rw [planEq] at packet
    exact no_packet assignment packet
  | merge first last one two inputs novel =>
    have a := List.mem_singleton.mp one
    have b := List.mem_singleton.mp two
    subst first; subst last
    exact novel (.refl _)


theorem no_selected (key children) :
    ¬ GeneralNominalVersionedSourceBoundary232.Local registry current root (.selected key children) := by
  intro chosen
  have same := B4TargetV8.local_functional chosen rejected
  cases same

theorem evidenceAt : B4SkeletonV8.EvidenceAt (GeneralNominalVersionedSourceBoundary232.boundary roles) registry current root := by
  intro assignment valid demand key children dictionaries reached _stable _childStable chosen given
  have same : demand = root := reached.elim id (GeneralDictionaryMatPriorConflict199.generated_only_root demand)
  subst demand
  exact False.elim (no_selected key children chosen)

theorem regression :
    (GeneralNominalVersionedSourceBoundary232.boundary roles).Checked registry ∧
    (GeneralNominalVersionedSourceBoundary232.boundary roles).Initial registry root current ∧
    Models current model ∧ (GeneralNominalVersionedSourceBoundary232.boundary roles).Stable registry current root ∧
    GeneralNominalVersionedSourceBoundary232.Local registry current root .rejected ∧
    B4SkeletonV8.EvidenceAt (GeneralNominalVersionedSourceBoundary232.boundary roles) registry current root :=
  ⟨⟨rfl,checked⟩,initial,current_model,stable,rejected,evidenceAt⟩

end Yulang.GeneralDictionaryVersionedConflict199Local233
