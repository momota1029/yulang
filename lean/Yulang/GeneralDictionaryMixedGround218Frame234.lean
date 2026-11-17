import Yulang.GeneralDictionaryMixedGround218Packet234
import Yulang.GeneralNominalVersionedMixedKernel234
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
namespace Yulang.GeneralDictionaryMixedGround218Frame234
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryGroundCopy218Install
open GeneralDictionaryMixedGround218Packet234 (initial initial_model packet_holds)
open GeneralNominalVersionedJournal232

theorem fresh : GeneralNominalVersionedAllocation231.Fresh snapshot registry root.identity packet.bindings := by
  intro key _ member
  have lower := source.below_seed _ member
  have upper := GeneralNominalIdentities.source_above_seed snapshot.seed key
  exact False.elim (Nat.not_le_of_lt upper lower)

theorem prepared : GeneralNominalVersionedCandidates231.Prepared registry context root declaration :=
  ⟨GeneralDictionaryGroundCopy218Install.prepared.1,source.linked,[(6,6)],rfl,fresh,
    (by rw [report_exact]; exact ⟨rfl,rfl,rfl⟩),model,
    GeneralNominalVersionedPlans231.head_models packet_holds⟩

theorem frame : GeneralNominalVersionedEvidence231.Frame registry initial.core root 0 plan :=
  ⟨rfl,rfl,rfl,rfl,List.mem_singleton_self _,List.mem_singleton_self _,List.mem_cons_self,rfl,rfl,prepared⟩

theorem children_eq : GeneralNominalVersionedFrame231.children packet = children := by
  unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
    GeneralCanonicalChildOrder.canonicalEmit
  simp only [canonical_declaration]
  rw [children_exact]
  change [GeneralNominalVersionedFrame231.clauseChild packet clause _] = [childSite.occurrence]
  apply congrArg List.singleton
  apply congrArg (fun arguments : Fin 2 → GeneralSourceState.Interval =>
    (⟨GeneralNominalCenters.fresh 7 0 0 6 0 0,⟨1,arguments,[],by intro _ h; cases h⟩⟩ : GeneralSourceDictionaries.Occurrence roles))
  funext i
  change Fin 2 at i
  have positions : i = 0 ∨ i = 1 := by omega
  rcases positions with rfl | rfl
  · change (GeneralNominalVersionedFrame231.capture packet).inputs 0 = (GeneralNominalPacketSupport.capture packet).inputs 0
    rw [GeneralDictionaryMixedGround218Packet234.capture 0 (Or.inl rfl),capture_exact 0 (Or.inl rfl)]
  · change (GeneralNominalVersionedFrame231.capture packet).inputs 1 = (GeneralNominalPacketSupport.capture packet).inputs 1
    rw [GeneralDictionaryMixedGround218Packet234.capture 1 (Or.inr rfl),capture_exact 1 (Or.inr rfl)]

theorem unique : GeneralNominalVersionedCandidates231.Unique registry context root 0 children := by
  have survivor : GeneralNominalVersionedCandidates231.Survivor registry context root 0 children :=
    ⟨known,declaration,List.mem_cons_self,declaration_checked,rfl,rfl,[(6,6)],rfl,prepared,children_eq.symm⟩
  refine ⟨survivor,?_⟩
  intro key kids found
  have copy := found
  obtain ⟨_,d,visible,_,identity,role,_⟩ := found
  cases parent_only visible role
  cases identity
  exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional checked copy survivor⟩

theorem edge_old (edge : GeneralNominalVersionedCycles232.Edge initial first last) :
    GeneralNominalCenteredHeadMatStepCycles.Edge start first last := by
  obtain ⟨parent,test,index,head,one,two⟩ := edge
  exact ⟨parent,test,index,
    fun model valid => head model ((lift_models start model).mpr valid),
    fun model valid => one model ((lift_models start model).mpr valid),
    fun model valid => two model ((lift_models start model).mpr valid)⟩

theorem path_old {first last : GeneralNominalRecursiveInspection.Origin}
    (path : GeneralNominalVersionedCycles232.Path initial first last) :
    GeneralNominalCenteredHeadMatStepCycles.Path start first last := by
  induction path with
  | nil => exact .nil _
  | cons edge path ih => exact .cons (edge_old edge) ih

theorem acyclic (origin) : ¬ GeneralNominalVersionedCycles232.Cyclic initial origin := by
  rintro ⟨⟨next,edge,path⟩,model,valid⟩
  exact GeneralDictionaryGroundCopy218Install.acyclic origin
    ⟨⟨next,edge_old edge,path_old path⟩,model,valid.1⟩

theorem administrative_ready : GeneralNominalVersionedDiagnostic232.AdministrativeReady initial root := by
  refine ⟨⟨_,List.mem_singleton_self _,rfl⟩,?_⟩
  intro first one same last two _
  cases List.mem_singleton.mp one
  cases List.mem_singleton.mp two
  exact .refl _

theorem safe : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) registry initial root := by
  refine ⟨known,?_,?_,?_⟩
  · rintro (old | (⟨index,cycle⟩ | ⟨site,present,same,index,cycle⟩))
    · obtain ⟨_,_,_,slot,_,cycle⟩ := old; exact no_raw_recurs slot cycle
    · exact acyclic _ cycle
    · exact acyclic _ cycle
  · rintro (old | ⟨candidate,framed,entry,member,cycle⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := old; exact no_raw_recurs visited.1 cycle
    · exact acyclic _ cycle
  · rintro (⟨_,d,visible,role,_,unprepared⟩ | unclosed)
    · cases parent_only visible role; exact unprepared prepared
    · exact unclosed administrative_ready
end Yulang.GeneralDictionaryMixedGround218Frame234
