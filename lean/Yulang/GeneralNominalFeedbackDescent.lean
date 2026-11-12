import Yulang.GeneralNominalFeedbackAdministrative

/-! Formation excludes unrecorded child enqueue updates. Administrative
accessibility reduces full progress to an installation budget that must still
be constructed from interval-sensitive Paterson descent and source data. -/
namespace Yulang.GeneralNominalFeedbackDescent

open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalFeedbackSteps
open GeneralNominalSaturationInvariants (EdgesRecorded)

variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

theorem edges_update {before after : State roles}
    (recorded : EdgesRecorded before) (update : At registry before focus after) : EdgesRecorded after := by
  have growth := (GeneralNominalFeedbackProgress.at_extends update).journal
  cases update with
  | enqueue focus _ _ =>
      intro parent child member
      obtain ⟨packet,site⟩ := recorded parent child member
      exact ⟨packet,by obtain ⟨site,member,equal⟩ := site; exact ⟨site,growth.sites site member,equal⟩⟩
  | install packet _ _ =>
      let emitted := GeneralNominalFeedbackSites.emitted packet
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
        refine ⟨⟨packet,by simp [GeneralNominalFeedbackSites.install],rfl,member⟩,?_⟩
        rw [← emitted.exact] at member
        obtain ⟨site,found,same⟩ := List.mem_map.mp member
        exact ⟨site,List.mem_append_right _ found,same⟩
  | merge first last _ _ _ _ => exact recorded
  | refresh focus context _ _ _ _ _ => exact recorded
  | equate _ _ _ _ _ _ _ => exact recorded

theorem formed_journal {state : State roles} (formed : SourceFormed registry root state) :
    EdgesRecorded state ∧ ∃ site ∈ state.sites, site.occurrence = root := by
  induction formed with
  | initial context _ =>
      exact ⟨(by intro parent child member; cases member),GeneralNominalDemandMerging.pointSite root,by simp [initial],rfl⟩
  | update _ step ih =>
      obtain ⟨site,member,same⟩ := ih.2
      exact ⟨edges_update ih.1 step.choose_spec.2,site,
        (GeneralNominalFeedbackProgress.at_extends step.choose_spec.2).journal.sites site member,same⟩

theorem generated_registered {state : State roles} (formed : SourceFormed registry root state)
    (generated : Generated state root child) : ∃ site ∈ state.sites, site.occurrence = child := by
  have journal := formed_journal formed
  induction generated with
  | root => exact journal.2
  | child _ member _ => exact (journal.1 _ _ member).2
  | alias _ _ member _ _ => exact ⟨_,member,rfl⟩

theorem formed_step_cases {before after : State roles} (formed : SourceFormed registry root before)
    (step : Step registry root before after) :
    GeneralNominalFeedbackAdministrative.Update registry before after ∨
      ∃ packet : Packet roles, Installable registry before packet ∧ ¬ Committed before packet ∧
        after = GeneralNominalFeedbackSites.install before packet (GeneralNominalFeedbackSites.emitted packet) := by
  obtain ⟨focus,generated,action⟩ := step
  cases action with
  | enqueue focus _ absent =>
      obtain ⟨site,member,same⟩ := generated_registered formed generated
      exact False.elim (absent site member same)
  | install packet enabled novel => exact Or.inr ⟨packet,enabled,novel,rfl⟩
  | merge first last one two same novel => exact Or.inl (.merge first last one two same novel)
  | refresh focus context cert source member unknown known => exact Or.inl (.refresh focus context cert source member unknown known)
  | equate focus first last one two equal novel => exact Or.inl (.equate focus first last one two equal novel)

structure InstallationDescent (registry : Registry) (root : Occurrence roles) where
  rank : State roles → Nat
  administrative : ∀ before after, SourceFormed registry root before →
    GeneralNominalFeedbackAdministrative.Update registry before after → rank after ≤ rank before
  installation : ∀ before, SourceFormed registry root before → ∀ packet : Packet roles,
    Installable registry before packet → ¬ Committed before packet →
    rank (GeneralNominalFeedbackSites.install before packet (GeneralNominalFeedbackSites.emitted packet)) < rank before

theorem accessible_of_installation_descent (descent : InstallationDescent registry root)
    (state : State roles) (formed : SourceFormed registry root state) :
    Acc (fun next current => Step registry root current next) state := by
  have all : ∀ n current, descent.rank current ≤ n → SourceFormed registry root current →
      Acc (fun next current => Step registry root current next) current := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n lower =>
      intro current
      have admin := GeneralNominalFeedbackAdministrative.accessible registry current
      induction admin with
      | intro current below ih =>
        intro bound formed
        refine Acc.intro current ?_
        intro next step
        rcases formed_step_cases formed step with administrative | ⟨packet,enabled,novel,rfl⟩
        · exact ih next administrative (Nat.le_trans (descent.administrative current next formed administrative) bound)
            (.update formed step)
        · have strict := descent.installation current formed packet enabled novel
          exact lower _ (Nat.lt_of_lt_of_le strict bound) _ (Nat.le_refl _) (.update formed step)
  exact all (descent.rank state) state (Nat.le_refl _) formed

end Yulang.GeneralNominalFeedbackDescent
