import Yulang.GeneralDictionaryOutputDepthCycles252
import Yulang.GeneralNominalVersionedTerminal232
import Yulang.GeneralDictionaryDefaultCache208
import Yulang.GeneralNominalPointSourceBoundary240
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryOutputDepthInstall252
open GeneralDictionaryOutputDepth252
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open CommonNominalFullCarrier GeneralNominalRecursiveInspection
open GeneralDictionaryOutputDepthCycles252
open GeneralNominalVersionedMixedKernel234

def smallModel : GeneralNominalCommonBridge.Assignment := fun name => (if name = 2 then F else S,Common.rowEmpty)
theorem small_source : GeneralNominalState.Models snapshot smallModel := by
 refine ⟨⟨?_,(by intro _ _ h; cases h),(by intro _ h; cases h)⟩,?_,(by intro _ h; cases h)⟩
 · intro atom member
   simp only [atoms,List.flatMap_cons,List.flatMap_nil,List.cons_append,List.nil_append,
     GeneralSourceState.equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl <;> exact subtype_refl _
 · intro slot d found
   change (if slot = 2 then some foo else none) = some d at found
   split at found
   · rename_i same; subst slot; cases Option.some.inj found
     exact ⟨[.inl S],.cons ⟨subtype_refl _,subtype_refl _⟩ .nil,⟨subtype_refl _,subtype_refl _⟩⟩
   · cases found
theorem small_initial : GeneralNominalVersionedJournal232.Models initial smallModel :=
 (GeneralNominalVersionedJournal232.initial_models context root smallModel).mpr
   ⟨small_source,fun _ => ⟨subtype_refl _,subtype_refl _⟩⟩
def form (name : Nat) : Form := if name=2 then .foo else .scalar
theorem form_value (name : Nat) : (smallModel name).1 = (form name).value := by
 simp only [smallModel,form]; split <;> rfl
theorem no_cycle (origin) : ¬ GeneralNominalVersionedCycles232.Cyclic initial origin :=
 acyclic small_initial (fun n => ⟨form n,form_value n⟩) origin

theorem raw_smaller {a b : Fin 4} (edge : GeneralNominalMixedRecurrence.Edge snapshot a b) :
 (form b.val).rank < (form a.val).rank := by
 rcases edge with structural | nominal
 · obtain ⟨kind,children,recorded,index,child⟩ := structural
   cases recorded
 · obtain ⟨descriptor,recorded,index,actual,seen,same⟩ :=
     GeneralNominalMixedRecurrence.actual_edge_sound snapshot a b nominal smallModel small_source
   have observation := GeneralNominalRecursiveInspection.embed_observation smallModel _ actual seen
   cases observation with
   | nominal parent equal found =>
     cases parent
     change Equivalent (smallModel a.val).1 _ at equal
     rw [form_value] at equal
     obtain ⟨child,smaller,meaning⟩ := nominal_child (form a.val) equal found
     change Equivalent actual (smallModel b.val).1 at same
     rw [form_value] at same
     have ranks := equivalent_rank child (form b.val)
       ⟨subtype_trans meaning.2 same.1,subtype_trans same.2 meaning.1⟩
     omega

theorem no_raw (slot : Fin 4) : ¬ GeneralNominalCycleK2.RecursAt snapshot slot := by
 have paths : ∀ a b, GeneralNominalMixedRecurrence.Path snapshot a b → (form b.val).rank ≤ (form a.val).rank := by
   intro a b path
   induction path with
   | nil => exact Nat.le_refl _
   | cons edge path ih => exact Nat.le_trans ih (Nat.le_of_lt (raw_smaller edge))
 intro cycle
 obtain ⟨next,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle _ _ cycle
 have smaller := raw_smaller edge
 have larger := paths _ _ path
 omega

theorem frame_plan {candidate : Plan roles} {key}
 (framed : GeneralNominalVersionedEvidence231.Frame registry initial.core root key candidate) : candidate = plan := by
 rcases candidate with ⟨⟨reg,ctx,site,decl,check,bounds⟩,input,inputEq⟩
 have regEq : reg = registry := framed.registry_eq
 have ctxEq : ctx = context := framed.context_eq
 have declEq : decl = declaration := List.mem_singleton.mp framed.visible
 have siteEq : site = GeneralNominalDemandMerging.pointSite root := List.mem_singleton.mp framed.raw_recorded
 have inputSame : input = rootSite snapshot.seed root := List.mem_singleton.mp framed.center_recorded
 subst reg; subst ctx; subst decl; subst site; subst input
 have boundsEq : [(2,2)] = bounds := Option.some.inj framed.located
 subst bounds; rfl

theorem positions : GeneralNominalVersionedCycles232.Safe initial plan :=
 by
 refine ⟨by decide +kernel,?_⟩
 have empty : (GeneralNominalCenteredSteps.inspection plan).tests = [] := by decide +kernel
 intro entry member
 rw [empty] at member
 cases member
theorem administrative_ready : GeneralNominalVersionedDiagnostic232.AdministrativeReady initial root := by
 refine ⟨⟨_,List.mem_singleton_self _,rfl⟩,?_⟩
 intro first one same last two _
 cases List.mem_singleton.mp one
 cases List.mem_singleton.mp two
 exact .refl _
theorem safe : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) registry initial root := by
 refine ⟨known,?_,?_,?_⟩
 · rintro (old | (⟨index,cycle⟩ | ⟨site,present,same,index,cycle⟩))
   · obtain ⟨_,_,_,slot,_,cycle⟩ := old; exact no_raw slot cycle
   · exact no_cycle _ cycle
   · exact no_cycle _ cycle
 · rintro (old | ⟨candidate,framed,entry,member,cycle⟩)
   · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := old; exact no_raw visited.1 cycle
   · exact no_cycle _ cycle
 · rintro (⟨_,d,visible,role,_,unprepared⟩ | unclosed)
   · cases List.mem_singleton.mp visible; exact unprepared prepared
   · exact unclosed administrative_ready


theorem request_single {output : GeneralSourceState.Output}
 (member : output ∈ GeneralNominalCenteredHeadOutputs.requests initial.core root) : output = ⟨0,3⟩ := by
 obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
 cases List.mem_singleton.mp present
 exact List.mem_singleton.mp within

theorem ready : GeneralNominalCenteredHeadMatEffects.Ready initial.core root plan := by
 intro output member
 cases request_single member
 exact ⟨.explicit ⟨0,0,.app 0 [.app 0 [.var 0]]⟩,rfl,rfl⟩

noncomputable def effect : GeneralNominalVersionedJournal232.Effect roles :=
 ⟨registry,initial.core,plan,frame,children_empty ▸ unique,ready⟩
noncomputable def installed := GeneralNominalVersionedInstall232.install initial effect

theorem classes : GeneralNominalVersionedEffects231.ClassEffects initial.core root plan model := by
 constructor
 · intro output member body found
   cases request_single member
   have equal : body = .explicit ⟨0,0,.app 0 [.app 0 [.var 0]]⟩ := Option.some.inj found.symm
   subst body
   change ∀ equation ∈ ([⟨3,.actual,rhs⟩] : List GeneralNominalCenteredHeadMatSchemas.Equation), equation.Holds _ _
   intro equation member
   cases List.mem_singleton.mp member
   change Equivalent P (GeneralNominalCenteredHeadMatExpressions.value _ .actual rhs)
   simp only [GeneralNominalVersionedEffects231.bodyVariables]
   rw [rhs_value]
   exact ⟨subtype_refl _,subtype_refl _⟩
 · intro first one last two _
   cases request_single one
   cases request_single two
   exact ⟨subtype_refl _,subtype_refl _⟩

theorem installation_models : GeneralNominalVersionedInstall232.InstallationModels initial effect model := by
 refine ⟨initial_model,packet_holds,⟨head_model,classes⟩,?_,?_,?_⟩
 · exact (GeneralNominalVersionedFrameTransport232.class_effects_iff
     (fun _ => GeneralNominalVersionedTerminal232.requests_iff children_empty)).mpr classes
 · intro prior member; cases member
 · intro prior member; cases member

theorem installed_model : GeneralNominalVersionedJournal232.Models installed model :=
 (GeneralNominalVersionedInstall232.install_models rfl).mpr installation_models

theorem installable : Installable registry initial effect := by
 refine ⟨rfl,rfl,safe,?_,?_,?_,positions,?_,model,installation_models⟩
 · exact GeneralNominalVersionedMixedObservations233.legacy_cache
     (GeneralDictionaryDefaultCache208.initial_valid context root)
 · change (GeneralNominalVersionedPlans231.emittedSchema plan).unknown = false
   rw [emitted_exact]
 · intro packet member; cases member
 · intro candidate input framed
   change GeneralNominalVersionedEvidence231.Frame registry initial.core root candidate.packet.declaration.id candidate at framed
   cases frame_plan framed
   exact positions


theorem small_rhs : GeneralNominalCenteredHeadMatExpressions.value
 (GeneralNominalVersionedPlans231.variables plan smallModel) .actual rhs = P := by
 simp only [GeneralNominalCenteredHeadMatExpressions.value,GeneralNominalCenteredHeadMatExpressions.values]
 change nominal 0 [.inl (nominal 0 [.inl (smallModel (GeneralNominalVersionedFrame231.binder plan 0)).1])] = P
 rw [binder_exact]
 rfl

theorem novel : ¬ Committed initial plan := by
 intro committed
 have outputs := (committed.1 smallModel small_initial).1.2.2
 unfold GeneralNominalVersionedPlans231.Outputs at outputs
 rw [emitted_exact] at outputs
 have equal := outputs ⟨3,.actual,rhs⟩ (List.mem_singleton_self _)
 change Equivalent S (GeneralNominalCenteredHeadMatExpressions.value _ .actual rhs) at equal
 rw [small_rhs] at equal
 have tags := GeneralDictionaryInspectionHeads215.tag_subtype
   (GeneralDictionaryInspectionHeads215.tagged_scalar .int)
   (GeneralDictionaryInspectionHeads215.tagged_nominal 0 [.inl (nominal 0 [.inl F])]) equal.1
 cases tags

theorem step : Step registry root initial installed := ⟨root,.root,.install effect installable novel⟩
theorem reachable_installed : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles)
 sourceRegistry root installed := ⟨initial,initial_source,.tail .refl step⟩

/-- The deep output is forced by the installed packet, not chosen freely in
one convenient model of an otherwise unconstrained output slot. -/
theorem output_forced (assignment : GeneralNominalCommonBridge.Assignment)
 (valid : GeneralNominalVersionedJournal232.Models installed assignment) : Equivalent (assignment 3).1 P := by
 have packetValid := valid.2.1 plan List.mem_cons_self
 have inputFixed := foo_fixed assignment packetValid.1
 have outputs := packetValid.2.2
 unfold GeneralNominalVersionedPlans231.Outputs at outputs
 rw [emitted_exact] at outputs
 have equation := outputs ⟨3,.actual,rhs⟩ (List.mem_singleton_self _)
 change Equivalent (assignment 3).1
   (nominal 0 [.inl (nominal 0 [.inl (assignment (GeneralNominalVersionedFrame231.binder plan 0)).1])]) at equation
 rw [binder_exact] at equation
 have inner := GeneralNominalCenteredHeadMatCompilerSemantics.nominal_congr 0 (.cons inputFixed .nil)
 have outer := GeneralNominalCenteredHeadMatCompilerSemantics.nominal_congr 0 (.cons inner .nil)
 exact ⟨subtype_trans equation.1 outer.1,subtype_trans outer.2 equation.2⟩

/-- One actual source installation produces the associated output whose ground
readback exceeds the maximum of the ground input and declaration-template depths.
The raw journal may keep references: the claim concerns their expanded readback,
not growth of the literal stored template and not nontermination. -/
theorem actual_expanded_depth_obstruction :
 Checked sourceRegistry ∧
 B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) sourceRegistry root installed ∧
 GeneralNominalVersionedJournal232.Models installed model ∧
 plan ∈ installed.plans ∧
 GeneralNominalVersionedPlans231.emittedSchema plan = ⟨[⟨3,.actual,rhs⟩],false⟩ ∧
 GeneralNominalCenteredHeadMatExpressions.value (GeneralNominalVersionedPlans231.variables plan model) .actual rhs = P ∧
 max (depth rootPattern) (depth template) < depth expanded :=
 ⟨source_checked,reachable_installed,installed_model,List.mem_cons_self,emitted_exact,rhs_value,exceeds_max⟩
/-- I45 is retained: this is installation, not descriptor-changing reobservation. -/
theorem point_step : GeneralNominalPointKernel240.Step registry root initial installed :=
 ⟨root,.root,.install effect installable novel⟩
theorem point_reachable : B4TargetV8.Reachable (GeneralNominalPointSourceBoundary240.boundary roles)
 sourceRegistry root installed := ⟨initial,initial_source,.tail .refl point_step⟩
theorem point_expanded_depth_obstruction :
 B4TargetV8.Reachable (GeneralNominalPointSourceBoundary240.boundary roles) sourceRegistry root installed ∧
 GeneralNominalVersionedJournal232.Models installed model ∧
 (∀ assignment, GeneralNominalVersionedJournal232.Models installed assignment → Equivalent (assignment 3).1 P) ∧
 max (depth rootPattern) (depth template) < depth expanded :=
 ⟨point_reachable,installed_model,output_forced,exceeds_max⟩
/-- Complete I45 source witness. Pure nominal constructors are unchanged by
union-duplicate or hidden-field normalization. No language nontermination claim. -/
theorem point_public_readback_exceeds_max :
 Checked sourceRegistry ∧
 (GeneralNominalPointSourceBoundary240.boundary roles).Initial sourceRegistry root initial ∧
 GeneralNominalPointKernel240.Step registry root initial installed ∧
 B4TargetV8.Reachable (GeneralNominalPointSourceBoundary240.boundary roles) sourceRegistry root installed ∧
 GeneralNominalVersionedJournal232.Models installed model ∧
 (∀ assignment, GeneralNominalVersionedJournal232.Models installed assignment → Equivalent (assignment 3).1 P) ∧
 GeneralNominalCenteredHeadMatPatternSemantics.eval
   (GeneralNominalCenteredHeadMatCompilerSemantics.algebra GeneralDeclarationExamples.constructors interpretation)
   (fun _ => S) expanded = P ∧
 GeneralNominalCenteredHeadMatExpressions.value (GeneralNominalVersionedPlans231.variables plan model) .actual rhs = P ∧
 max (depth rootPattern) (depth template) < depth expanded :=
 ⟨source_checked,initial_source,point_step,point_reachable,installed_model,output_forced,expanded_value,rhs_value,exceeds_max⟩
end Yulang.GeneralDictionaryOutputDepthInstall252
