import Yulang.GeneralDictionaryAllocDefaultSource202
import Yulang.GeneralNominalCenteredHeadWFJoinLocal
import Yulang.GeneralNominalCenteredHeadMatPairCycles

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDictionaryAllocDefaultLocal202
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalCenters GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalCenteredHeadOutputs CommonNominalFullCarrier
open GeneralDictionaryAllocDefaultSource202
open GeneralNominalCenteredHeadMatStepBoundary (boundary)

theorem known : ¬ GeneralNominalState.RootPending snapshot root.demand :=
  by
    rintro ⟨index,unknown⟩
    exact unknown ⟨(1 : Fin 3),rfl,Or.inl (by decide +kernel)⟩

theorem survivor : GeneralNominalCenteredHeadCandidates.Survivor registry context root 37 children :=
  ⟨known,declaration,List.mem_singleton_self _,declaration_checked,rfl,rfl,[(1,1)],rfl,prepared,rfl⟩

theorem unique : GeneralNominalCenteredHeadCandidates.Unique registry context root 37 children := by
  refine ⟨survivor,?_⟩
  intro key kids found
  have copy := found
  obtain ⟨_,d,visible,_,identity,_⟩ := found
  cases List.mem_singleton.mp visible
  have same : key = 37 := identity.symm
  subst key
  exact ⟨rfl,GeneralNominalCenteredHeadCandidates.survivor_children_functional checked copy survivor⟩

theorem frame : Frame registry start.core root 37 plan :=
  ⟨rfl,rfl,rfl,rfl,List.mem_singleton_self _,List.mem_singleton_self _,List.mem_singleton_self _,rfl,rfl,prepared⟩

theorem frame_plan {candidate : Plan roles} (framed : Frame registry start.core root key candidate) :
    candidate = plan := by
  rcases candidate with ⟨⟨reg,ctx,site,decl,check,bounds⟩,input,inputEq⟩
  have regEq : reg = registry := framed.registry_eq
  have ctxEq : ctx = context := framed.context_eq
  have declEq : decl = declaration := List.mem_singleton.mp framed.visible
  have siteEq : site = GeneralNominalDemandMerging.pointSite root := List.mem_singleton.mp framed.raw_recorded
  have inputSame : input = rootSite snapshot.seed root := List.mem_singleton.mp framed.center_recorded
  subst reg; subst ctx; subst decl; subst site; subst input
  have boundsEq : [(1,1)] = bounds := Option.some.inj framed.located
  subst bounds
  rfl

theorem head_schema : plan.headSchema = { tests := [(.source 1,.scalar .int)] } := by
  unfold Plan.headSchema
  rw [query]
  simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,plan,rootSite,List.ofFn_succ]

theorem head_equations : HeadEquations plan model := by
  refine ⟨point_root_holds _ root (fun _ => rfl) model,?_,?_⟩
  · intro name member
    simp [Declaration.inputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables] at member
  · rw [head_schema]
    constructor
    · intro test member
      cases List.mem_singleton.mp member
      exact ⟨⟨_,.source _⟩,by intro actual seen; cases seen; exact ⟨subtype_refl _,subtype_refl _⟩⟩
    · intro entry member; cases member

theorem scalar_no_edge (last : Origin) : ¬ GeneralNominalCenteredHeadMatStepCycles.Edge start (.source 1) last := by
  rintro ⟨parent,test,index,headed,equal,_⟩
  have same := equal model inhabited
  obtain ⟨actual,seen⟩ := same.2.1
  have value := same.2.2 _ actual (.source 1) seen
  have shape := (headed model inhabited).2 actual seen
  change Equivalent (.base .int) actual at value
  cases test with
  | scalar => exact Fin.elim0 index
  | nominal name count =>
      obtain ⟨values,_,head⟩ := shape
      exact GeneralNominalPeelingOrigins.base_not_nominal .int name values
        (subtype_trans value.1 head.1)
  | structural kind =>
      obtain ⟨values,length,head⟩ := shape
      exact GeneralNominalCenteredHeadMatPairCycles.scalar_no_shape length
        ⟨subtype_trans value.1 head.1,subtype_trans head.2 value.2⟩

theorem scalar_acyclic : ¬ GeneralNominalCenteredHeadMatStepCycles.Cyclic start (.source 1) := by
  rintro ⟨⟨last,edge,_⟩,_⟩
  exact scalar_no_edge last edge

theorem inspection_exact : (GeneralNominalCenteredSteps.inspection plan).tests = [(.source 1,.scalar .int)] := by
  unfold GeneralNominalCenteredSteps.inspection
  rw [query]
  simp [inspectMany,inspect,Report.visit,Report.append,Site.observed,rootSite,List.ofFn_succ]

theorem administrative_ready : GeneralNominalCenteredHeadMatStepLocal.AdministrativeReady start root := by
  refine ⟨⟨_,List.mem_singleton_self _,rfl⟩,?_⟩
  intro first one same last two _
  cases List.mem_singleton.mp one
  cases List.mem_singleton.mp two
  exact .refl _

theorem safe : B4TargetV6.SafeKnown (boundary roles) registry start root := by
  refine ⟨known,?_,?_,?_⟩
  · rintro (old | (⟨index,cycle⟩ | ⟨site,present,same,index,cycle⟩))
    · obtain ⟨_,_,_,slot,_,cycle⟩ := old
      exact GeneralNominalCenteredHeadWFJoinLocal.no_raw_recurs slot cycle
    · exact scalar_acyclic cycle
    · cases List.mem_singleton.mp present
      exact scalar_acyclic cycle
  · rintro (old | ⟨candidate,framed,entry,member,cycle⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := old
      exact GeneralNominalCenteredHeadWFJoinLocal.no_raw_recurs visited.1 cycle
    · cases frame_plan framed
      rw [inspection_exact] at member
      cases List.mem_singleton.mp member
      exact scalar_acyclic cycle
  · rintro (⟨_,d,visible,_,_,unprepared⟩ | unclosed)
    · cases List.mem_singleton.mp visible
      exact unprepared prepared
    · exact unclosed administrative_ready


end Yulang.GeneralDictionaryAllocDefaultLocal202
