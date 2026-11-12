import Yulang.GeneralNominalSaturationBoundary

/-! Reachability properties of the transition journal. These are derived from
initialization and updates, rather than assumptions about arbitrary records.
Context completeness remains a distinct feedback obligation. -/
namespace Yulang.GeneralNominalSaturationInvariants

open GeneralNominalSaturationState GeneralNominalSaturationSteps
open GeneralNominalDemandMerging (Site pointSite)
open GeneralSourceDictionaries (Occurrence)

variable {roles : Roles.RoleDecls}

def Canonical (state : State roles) : Prop :=
  ∀ site ∈ state.sites, site = pointSite site.occurrence

def EdgesRecorded (state : State roles) : Prop :=
  ∀ parent child, (parent,child) ∈ state.edges →
    (∃ packet ∈ state.packets, packet.site.occurrence = parent ∧ child ∈ packet.children) ∧
      ∃ site ∈ state.sites, site.occurrence = child

def Reachable (registry : GeneralDeclarations.Registry) (context : GeneralNominalCandidates.Context)
    (root : Occurrence roles) (state : State roles) : Prop :=
  B4Target.Steps (Step registry root) (initial context root) state

theorem canonical_update {before after : State roles}
    (canonical : Canonical before) (update : At registry before focus after) : Canonical after := by
  cases update with
  | enqueue focus _ _ =>
      intro site member
      rcases List.mem_append.mp member with old | new
      · exact canonical site old
      · have same := List.mem_singleton.mp new; subst site; rfl
  | install packet emitted _ _ =>
      intro site member
      rcases List.mem_append.mp member with old | new
      · exact canonical site old
      · rw [emitted.canonical] at new
        obtain ⟨child,_,rfl⟩ := List.mem_map.mp new
        rfl
  | merge _ _ _ _ _ _ => exact canonical
  | refresh _ _ _ _ _ _ _ => exact canonical

theorem edges_update {before after : State roles}
    (recorded : EdgesRecorded before) (update : At registry before focus after) : EdgesRecorded after := by
  have growth := at_extends update
  cases update with
  | enqueue focus _ _ =>
      intro parent child member
      obtain ⟨packet,site⟩ := recorded parent child member
      exact ⟨packet,by obtain ⟨site,member,equal⟩ := site; exact ⟨site,growth.sites site member,equal⟩⟩
  | install packet emitted _ _ =>
      intro parent child member
      rcases List.mem_append.mp member with old | new
      · obtain ⟨⟨prior,present,equal,member⟩,⟨site,found,same⟩⟩ := recorded parent child old
        exact ⟨⟨prior,List.mem_cons_of_mem _ present,equal,member⟩,⟨site,growth.sites site found,same⟩⟩
      · obtain ⟨actual,member,equal⟩ := List.mem_map.mp new
        have parentSame := congrArg Prod.fst equal
        have childSame := congrArg Prod.snd equal
        change packet.site.occurrence = parent at parentSame
        change actual = child at childSame
        subst parent; subst actual
        refine ⟨⟨packet,by simp [install],rfl,member⟩,?_⟩
        rw [← emitted.exact] at member
        obtain ⟨site,found,same⟩ := List.mem_map.mp member
        exact ⟨site,List.mem_append_right _ found,same⟩
  | merge first last _ _ _ _ => exact recorded
  | refresh focus context _ _ _ _ _ => exact recorded

theorem reachable_journal {state : State roles}
    (path : Reachable registry context root state) :
    Canonical state ∧ EdgesRecorded state ∧ ∃ site ∈ state.sites, site.occurrence = root := by
  induction path with
  | refl =>
      refine ⟨?_,?_,pointSite root,by simp [initial],rfl⟩
      · intro site member
        have same := List.mem_singleton.mp member; subst site; rfl
      · intro parent child member; cases member
  | tail path update ih =>
      obtain ⟨focus,generated,action⟩ := update
      obtain ⟨site,member,same⟩ := ih.2.2
      exact ⟨canonical_update ih.1 action,edges_update ih.2.1 action,
        site,(at_extends action).sites site member,same⟩

theorem generated_recorded {state : State roles}
    (path : Reachable registry context root state) (generated : Generated state root child) :
    ∃ site ∈ state.sites, site.occurrence = child := by
  have journal := reachable_journal path
  induction generated with
  | root => exact journal.2.2
  | child _ member _ => exact (journal.2.1 _ _ member).2
  | alias _ _ member _ _ => exact ⟨_,member,rfl⟩

theorem merged_outputs_retained (state : State roles) (first last : Site roles)
    (one : first ∈ state.sites) (two : last ∈ state.sites) :
    first ∈ (merge state first last).sites ∧ last ∈ (merge state first last).sites := ⟨one,two⟩

theorem complete_consistency (state : State roles) (complete : ContextComplete state)
    (registry : GeneralDeclarations.Registry) (root : Occurrence roles) (declaration : GeneralDeclarations.Declaration)
    (checked : GeneralDeclarations.DeclarationChecked registry.constructors roles declaration)
    (bounds : List (GeneralNominalInspection.Bounds state.context.state)) :
    GeneralNominalRecursiveCandidates.Consistent registry state.context root declaration checked bounds ↔
      ∃ model, Models state model ∧
        GeneralNominalRecursiveCandidates.BranchModels registry state.context root declaration checked bounds model := by
  constructor
  · rintro ⟨model,valid⟩
    exact ⟨model,complete model (GeneralNominalRecursiveCandidates.branch_interval_sound _ _ _ _ _ _ _ valid).1,valid⟩
  · rintro ⟨model,_,valid⟩; exact ⟨model,valid⟩

end Yulang.GeneralNominalSaturationInvariants
