import Yulang.GeneralDictionaryVersionedGap206233
import Yulang.GeneralNominalVersionedDiagnosticLaws232
import Yulang.B4SkeletonV8
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionedGap206Safety233
open GeneralDictionaryDefaultGap206Source
open GeneralDictionaryVersionedGap206233
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open CommonNominalFullCarrier
open GeneralNominalVersionedJournal232

theorem survivor : GeneralNominalVersionedCandidates231.Survivor registry context root 37 [] :=
  ⟨GeneralDictionaryDefaultGap206Local.known,declaration,List.mem_singleton_self _,declaration_checked,
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
  refine ⟨GeneralDictionaryDefaultGap206Local.known,?_,?_,?_⟩
  · rintro (old | (⟨index,cycle⟩ | ⟨site,present,same,index,cycle⟩))
    · obtain ⟨_,_,_,slot,_,cycle⟩ := old
      exact GeneralDictionaryDefaultGap206Local.no_raw_recurs slot cycle
    · exact scalar_acyclic cycle
    · cases List.mem_singleton.mp present; exact scalar_acyclic cycle
  · rintro (old | ⟨candidate,framed,entry,member,cycle⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := old
      exact GeneralDictionaryDefaultGap206Local.no_raw_recurs visited.1 cycle
    · cases frame_plan framed
      rw [GeneralDictionaryDefaultGap206Local.inspection_exact] at member
      cases List.mem_singleton.mp member
      exact scalar_acyclic cycle
  · rintro (⟨_,d,visible,_,_,unprepared⟩ | unclosed)
    · cases List.mem_singleton.mp visible; exact unprepared prepared
    · exact unclosed administrative_ready

end Yulang.GeneralDictionaryVersionedGap206Safety233
