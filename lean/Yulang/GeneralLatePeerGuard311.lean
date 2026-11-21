import Yulang.GeneralLatePeerRoot311

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 25500
set_option maxHeartbeats 15500000
namespace Yulang.GeneralLatePeerGuard311
open GeneralLatePeerSource311 (registry compiled checked parentCode receiver route)
open GeneralGeneratedNestedSource299 (model)
open GeneralDeclarationExamples (roles)
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedCandidates231 (Unique)
open GeneralNominalVersionedMixedKernel234 (Installable)
open GeneralNominalVersionedPlans231 (Holds)
open GeneralNominalVersionedEffects231 (ClassEffects)
open GeneralNominalVersionedDiagnostic232 (AdministrativeReady)
open GeneralNominalSaturationState (Alias)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters

abbrev children (p : Plan roles) := GeneralNominalVersionedFrame231.children p.packet

theorem one_per_role (a : Declaration) (one : a ∈ compiled.declarations)
    (b : Declaration) (two : b ∈ compiled.declarations) (same : a.role = b.role) :
    a = b := by
  change a ∈ [parentCode,receiver,route] at one
  change b ∈ [parentCode,receiver,route] at two
  simp only [List.mem_cons,List.not_mem_nil,or_false] at one two
  rcases one with rfl|rfl|rfl <;> rcases two with rfl|rfl|rfl <;> first | rfl | cases same

variable {s : State roles} {p : Plan roles} {d root : Occurrence roles} {key : Nat}

def Known (s : State roles) (d : Occurrence roles) : Prop :=
  ¬ GeneralNominalState.RootPending s.core.erased.current.context.state
    (GeneralNominalVersionedCandidates231.inputs d).demand

theorem unique (frame : Frame compiled s.core d key p) (known : Known s d) :
    Unique compiled s.core.erased.current.context d key (children p) := by
  have survives := GeneralNominalVersionedMixedFrameSelection235.frame_survivor frame known
  refine ⟨survives,?_⟩
  intro k kids alternative
  have original := alternative
  obtain ⟨_,other,present,_,tag,role,_⟩ := alternative
  cases one_per_role other present p.packet.declaration frame.visible (role.trans frame.role_eq.symm)
  have same := tag.symm.trans frame.key_eq
  rw [same] at original
  exact ⟨same,GeneralNominalVersionedCandidates231.survivor_children_functional
    (GeneralNominalCenteredHeadAllocEncoding.registry_checked checked) original survives⟩

theorem safe (frame : Frame compiled s.core d key p) (known : Known s d)
    (shape : s.core.erased.current.context.state.view.kinds = 0) (valid : Models s model)
    (admin : AdministrativeReady s d) :
    B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) compiled s d := by
  refine ⟨known,?_,?_,?_⟩
  · rintro (raw| (⟨i,cycle⟩ | ⟨site,_,_,i,cycle⟩))
    · obtain ⟨_,_,_,slot,_,cycle⟩ := raw
      exact GeneralDepthTwoSafety300.raw_acyclic _ shape valid.1.1 slot cycle
    · exact GeneralDepthTwoSafety300.semantic valid _ cycle
    · exact GeneralDepthTwoSafety300.semantic valid _ cycle
  · rintro (raw | ⟨candidate,_,entry,_,cycle⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := raw
      exact GeneralDepthTwoSafety300.raw_acyclic _ shape valid.1.1 visited.1 cycle
    · exact GeneralDepthTwoSafety300.semantic valid _ cycle
  · rintro (⟨_,other,visible,role,_,absent⟩ | noAdmin)
    · cases one_per_role other visible p.packet.declaration frame.visible (role.trans frame.role_eq.symm)
      exact absent frame.prepared
    · exact noAdmin admin

theorem no_merged (absent : s.core.erased.current.aliases = []) :
    ¬ GeneralNominalVersionedMergedConflict232.MergedOutputConflict s d := by
  rintro ⟨⟨a,b,linked,_,_⟩,_⟩
  rw [absent] at linked
  cases linked

theorem select (path : B4TargetV8.Reachable (boundary roles) registry root s)
    (frame : Frame compiled s.core d key p) (known : Known s d)
    (shape : s.core.erased.current.context.state.view.kinds = 0) (valid : Models s model)
    (admin : AdministrativeReady s d) (held : Holds p model) (classes : ClassEffects s.core d p model)
    (clear : ¬ GeneralNominalVersionedMergedConflict232.MergedOutputConflict s d) :
    Local registry s d (.selected key (children p)) := by
  apply GeneralNominalVersionedMixedSourceBoundary234.local_iff.mpr
  apply GeneralNominalVersionedMixedBoundary234.local_iff.mpr
  exact GeneralNominalVersionedDiagnosticLaws232.selected_of_model
    (safe frame known shape valid admin) (unique frame known) valid frame
    (GeneralNominalVersionedMixedReady235.ready ⟨rfl,checked⟩ path frame) held classes clear

def effect (path : B4TargetV8.Reachable (boundary roles) registry root s)
    (frame : Frame compiled s.core p.packet.site.occurrence p.packet.declaration.id p)
    (known : Known s p.packet.site.occurrence) : Effect roles :=
  ⟨compiled,s.core,p,frame,unique frame known,
    GeneralNominalVersionedMixedReady235.ready ⟨rfl,checked⟩ path frame⟩

theorem enabled (path : B4TargetV8.Reachable (boundary roles) registry root s)
    (frame : Frame compiled s.core p.packet.site.occurrence p.packet.declaration.id p)
    (known : Known s p.packet.site.occurrence)
    (chosen : Local registry s p.packet.site.occurrence (.selected p.packet.declaration.id (children p)))
    (valid : Models s model) (held : Holds p model) (currentClasses : ClassEffects s.core p.packet.site.occurrence p model) :
    Installable compiled s (effect path frame known) := by
  apply (GeneralNominalVersionedMixedSelectedEffect235.source_installable_iff path chosen rfl rfl).mpr
  refine ⟨GeneralNominalVersionedMixedChoice236.choice_of_role_unique ⟨rfl,checked⟩ path chosen
    frame.visible frame.role_eq (fun a ma b mb same => congrArg Declaration.id (one_per_role a ma b mb same)),model,?_⟩
  exact (GeneralNominalVersionedMixedCommon235.installation_models_iff ⟨rfl,checked⟩ path rfl rfl).mpr
    ⟨valid,held,currentClasses⟩

end Yulang.GeneralLatePeerGuard311
