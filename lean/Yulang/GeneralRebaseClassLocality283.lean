import Yulang.GeneralRebaseClassMutation283
import Yulang.GeneralRebaseMergeRequests264

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseClassLocality283
open GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedAdministrative232 (merge)
open GeneralNominalVersionedInstall232 (installCore)
open GeneralNominalVersionedMixedRegistry234 (LegacyEmpty)
open GeneralNominalSaturationState (Alias)
open GeneralNominalCenteredHeadOutputs (requests mem_requests_iff request_retained)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseClassMutation283 (frontier)
open Core.PresenceGeneration (CompTerm)

def hits (state : State roles) (first last focus : Occurrence roles) : Prop :=
  Alias state.core.erased.current focus.identity first.identity ∨
  Alias state.core.erased.current focus.identity last.identity

theorem quiet_merge (state : State roles) (first last : Site roles) (prior : Effect roles)
    (off : ¬ hits state first.occurrence last.occurrence prior.plan.packet.site.occurrence)
    (assignment : Assignment) :
    (frontier state.core (merge state first last).core prior CompTerm.var).Holds assignment := by
  apply (GeneralRebaseClassFrontier283.exact prior.plan CompTerm.var _ _ assignment).mpr
  apply GeneralRebaseClassFrontier283.no_growth
  intro out member
  exact (GeneralRebaseMergeRequests264.requests_unaffected state first last _
    (fun same => off (Or.inl same)) (fun same => off (Or.inr same)) out).mp member

theorem merge_local (state : State roles) (empty : LegacyEmpty state) (first last : Site roles) (a : Assignment) :
    Models (merge state first last) a ↔ Models state a ∧
      PresenceNormalForm.All CommonNominalFullCarrier.model a
        (GeneralNominalDemandMerging.outputAtoms first.observed last.observed) ∧
      ∀ prior ∈ state.effects,
        hits state first.occurrence last.occurrence prior.plan.packet.site.occurrence →
        (frontier state.core (merge state first last).core prior CompTerm.var).Holds a := by
  rw [GeneralRebaseClassMutation283.exact_merge state empty first last a]
  constructor
  · rintro ⟨models,atoms,all⟩
    exact ⟨models,atoms,fun p member _ => all p member⟩
  · rintro ⟨models,atoms,recheck⟩
    refine ⟨models,atoms,?_⟩
    intro p listed
    classical
    by_cases on : hits state first.occurrence last.occurrence p.plan.packet.site.occurrence
    · exact recheck p listed on
    · exact quiet_merge state first last p on a

theorem install_alias (core : GeneralNominalCenteredSteps.State roles) (p : Plan roles) (a b : Nat) :
    Alias (installCore core p).erased.current a b ↔ Alias core.erased.current a b := by
  constructor <;> intro path <;> induction path with
  | refl => exact .refl _
  | edge h => exact .edge h
  | symm _ h => exact .symm h
  | trans _ _ h k => exact .trans h k

theorem install_fresh_request (core : GeneralNominalCenteredSteps.State roles) (p : Plan roles)
    (focus : Occurrence roles) (out : GeneralSourceState.Output) :
    out ∈ requests (installCore core p) focus ∧ out ∉ requests core focus ↔
    (∃ site ∈ GeneralNominalVersionedChildren232.rawSites p,
      Alias core.erased.current focus.identity site.occurrence.identity ∧ out ∈ site.occurrence.demand.outputs) ∧
    out ∉ requests core focus := by
  constructor
  · rintro ⟨next,notBefore⟩
    obtain ⟨site,listed,same,used⟩ := mem_requests_iff.mp next
    have priorAlias := (install_alias core p _ _).mp same
    rcases List.mem_append.mp listed with prev|added
    · exact False.elim (notBefore (request_retained site prev priorAlias used))
    · exact ⟨⟨site,added,priorAlias,used⟩,notBefore⟩
  · rintro ⟨⟨site,new,same,used⟩,notBefore⟩
    exact ⟨request_retained site (List.mem_append_right _ new)
      ((install_alias core p _ _).mpr same) used,notBefore⟩

end Yulang.GeneralRebaseClassLocality283
