import Yulang.GeneralRebaseRefreshSafety275

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27500
set_option maxHeartbeats 9200000
namespace Yulang.GeneralRebaseRefreshSelected275
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryOptionalInitial229 (registry sourceRegistry declaration checked)
open GeneralDictionaryVersionedSecondInstall233 (installed)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseRefreshClosure275 (Gates)
open GeneralRebaseRefreshEvidence275 (Validated all_histories leaves)
open GeneralRebaseRefreshSafety275 (known model safe)
open GeneralNominalVersionedCandidates231 (Survivor Unique)
open GeneralNominalVersionedMixedKernel234 (Step)

variable {state : State roles}

theorem no_children (ctx : GeneralNominalCandidates.Context)
 (valid : GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
 (bounds : List (GeneralNominalInspection.Bounds ctx.state)) :
 GeneralNominalVersionedCandidates231.children registry ctx root declaration valid bounds = [] := by
 unfold GeneralNominalVersionedCandidates231.children GeneralNominalVersionedFrame231.children
   GeneralDictionaryEmissionPlans.children
 rw [GeneralRebaseRetarget275.no_emission _ _ _ _ _ (show declaration.requirements = [] from rfl)]
 rfl

theorem survivor (gates : Gates state) (valid : Validated state) :
 Survivor registry state.core.erased.current.context root declaration.id [] := by
 obtain ⟨p,frame,_,_,_⟩ := valid
 have whereAt := GeneralRebaseRefreshFrame275.of_frame frame
 rcases p with ⟨⟨reg,ctx,site,decl,dcheck,bounds⟩,center,centerDef⟩
 have regEq : reg = registry := frame.registry_eq
 have ctxEq : ctx = state.core.erased.current.context := frame.context_eq
 have declEq : decl = declaration := whereAt.declaration_eq
 subst reg; subst ctx; subst decl
 exact ⟨known gates,declaration,frame.visible,dcheck,frame.key_eq,frame.role_eq,bounds,
   frame.located,frame.prepared,(no_children _ dcheck bounds).symm⟩

theorem unique (gates : Gates state) (valid : Validated state) :
 Unique registry state.core.erased.current.context root declaration.id [] := by
 have chosen := survivor gates valid
 refine ⟨chosen,?_⟩
 intro key kids other
 have copy := other
 obtain ⟨_,d,visible,_,identity,_⟩ := other
 cases List.mem_singleton.mp visible
 have same : key = declaration.id := identity.symm
 subst key
 exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional checked copy chosen⟩

theorem equal_outputs (gates : Gates state) (m : Assignment) (focus : GeneralSourceDictionaries.Occurrence roles) :
 GeneralNominalCenteredHeadOutputs.EqualOutputs state.core focus m := by
 intro first one last two _
 obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp one
 rw [gates.sites] at present
 cases List.mem_singleton.mp present
 cases List.mem_singleton.mp within
 obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp two
 rw [gates.sites] at present
 cases List.mem_singleton.mp present
 cases List.mem_singleton.mp within
 exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩

theorem selected (gates : Gates state) (valid : Validated state) :
 GeneralNominalVersionedMixedSourceBoundary234.Local sourceRegistry state root (.selected declaration.id []) := by
 have witness := model gates
 have invariant := valid
 obtain ⟨p,frame,_,committed,ready⟩ := valid
 have total := committed.1 _ witness
 have effects : GeneralNominalVersionedEffects231.ClassEffects state.core root p _ :=
   frame.occurrence_eq ▸ total.2
 apply GeneralNominalVersionedMixedSourceBoundary234.local_iff.mpr
 apply GeneralNominalVersionedMixedBoundary234.local_iff.mpr
 apply GeneralNominalVersionedDiagnosticLaws232.selected_of_model (safe gates invariant) (unique gates invariant)
   witness frame ready total.1 effects
 exact GeneralNominalVersionedMergedConflict232.models_exclude_conflict witness
   (fun focus _ => equal_outputs gates _ focus) (equal_outputs gates _ root)

theorem evidenceAt (gates : Gates state) (good : Validated state) :
 B4SkeletonV8.EvidenceAt (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) sourceRegistry state root := by
 intro assignment valid demand key children dictionaries reached _stable _childStable chosen given
 have generated_only (any : GeneralNominalSaturationState.Generated state.core.erased.current root demand) :
   demand = root := GeneralNominalVersionedMixedTerminalStable234.generated_only gates.sites gates.edges any
 have same : demand = root := reached.elim id generated_only
 subst demand
 have same := B4TargetV8.local_functional chosen (selected gates good)
 cases same
 cases given
 exact leaves good assignment valid

theorem all_post_install (path : B4Target.Steps (Step registry root) installed state) :
 GeneralNominalVersionedMixedSourceBoundary234.Local sourceRegistry state root (.selected declaration.id []) ∧
 B4SkeletonV8.EvidenceAt (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) sourceRegistry state root :=
 let ⟨gates,good⟩ := all_histories path
 ⟨selected gates good,evidenceAt gates good⟩

end Yulang.GeneralRebaseRefreshSelected275
