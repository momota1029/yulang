import Yulang.GeneralMixedCompoundUpperEqClosed307
import Yulang.GeneralMixedCompoundUpperObstruction307

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 19000
set_option maxHeartbeats 9000000
namespace Yulang.GeneralMixedCompoundUpperHalt307
open GeneralDictionaryJournalRefinement228Source (roles root snapshot foo)
open GeneralDictionaryCompoundSource238 (registry)
open GeneralDictionaryCompoundSites238 (childSite)
open GeneralDictionaryCompoundObstruction238 (oldPlan)
open GeneralDictionaryCompoundBase239 (lo hi)
open GeneralMixedCompoundChildEquality307 (historical_child_center mid)
open GeneralMixedCompoundChildHidden307 (child_center)
open GeneralMixedCompoundUpperSnapshot307 (snap desc)
open GeneralMixedCompoundUpperRefresh307 (upperState)
open GeneralMixedCompoundUpperSupport307 (witness child_history impossible_further_refresh)
open GeneralMixedCompoundUpperTypes307 (equiv_kind)
open GeneralMixedCompoundUpperEqClosed307 (equality_closed)
open GeneralMixedCompoundUpperObstruction307 (no_install_root no_install_child)
open GeneralNominalCenters (Site SameInputs rootSite)
open GeneralNominalSaturationState (Generated)
open GeneralNominalVersionedMixedKernel234 (Stable Step)
open GeneralNominalVersionedJournal232 (State)
open GeneralDictionaryDefaultExpression209 (equivalent_trans)
open CommonNominalFullCarrier

theorem raw_sites : upperState.core.erased.current.sites =
    [GeneralNominalDemandMerging.pointSite root,childSite.observed] :=
  GeneralDictionaryCompoundSites238.raw_sites

theorem centers : upperState.core.sites = [rootSite snapshot.seed root,childSite] :=
  GeneralDictionaryCompoundSites238.centers

theorem reached_cases {focus : GeneralSourceDictionaries.Occurrence roles}
    (reached : Generated upperState.core.erased.current root focus) :
    focus = root ∨ focus = childSite.occurrence := by
  obtain ⟨raw,present,eq⟩ := GeneralNominalVersionedMixedTrace235.generated_registered
    (GeneralNominalVersionedMixedTrace235.reachable GeneralMixedCompoundUpperChild307.reachable).1 reached
  rw [raw_sites] at present
  rcases List.mem_cons.mp present with first|last
  · subst raw; exact Or.inl eq.symm
  · cases List.mem_singleton.mp last
    exact Or.inr eq.symm

theorem point_closed : GeneralNominalReobservationSteps.PointClosed snap := by
  intro idx d found
  have same : d = desc := by
    change (if idx = 0 ∨ idx = 1 then some desc else none) = some d at found
    split at found
    · exact (Option.some.inj found).symm
    · cases found
  subst d
  intro parameter contained
  change parameter ∈ [.type ((2 : Fin 8),2),.type (2,2)] at contained
  rcases List.mem_cons.mp contained with p|rest
  · subst parameter; rfl
  · cases List.mem_singleton.mp rest; rfl

noncomputable abbrev w := GeneralDictionaryCompoundVersionedModel238.extended
abbrev rSite := rootSite snapshot.seed root

theorem root_denotes : GeneralNominalDemandMerging.Denotes w rSite.observed [(w 0).1] := by
  change GeneralNominalDemandMerging.All₂
    (fun ref value => ∃ origin : GeneralNominalRecursiveInspection.Origin,
      ref = some origin ∧ GeneralNominalRecursiveInspection.Observes w origin value)
    [some (.source 0)] [(w 0).1]
  exact .cons ⟨_,rfl,.source 0⟩ .nil

theorem child_denotes : GeneralNominalDemandMerging.Denotes w childSite.observed [(w mid).1] := by
  change GeneralNominalDemandMerging.All₂
    (fun ref value => ∃ origin : GeneralNominalRecursiveInspection.Origin,
      ref = some origin ∧ GeneralNominalRecursiveInspection.Observes w origin value)
    [some (.source mid)] [(w mid).1]
  exact .cons ⟨_,rfl,.source mid⟩ .nil

theorem different : ¬ Equivalent (w 0).1 (w mid).1 := by
  intro collapse
  have held := child_history w witness
  have a := GeneralDictionaryJournalRefinement228Source.root_fixed w held.1
  have b := GeneralDictionaryJournalRefinement228Source.width_two w held.1
  have c := historical_child_center w held
  have midValue := equivalent_trans c ⟨(common_variant_iff ..).mpr b.1,(common_variant_iff ..).mpr b.2⟩
  have impossible : Equivalent (GeneralMixedCompoundUpperTypes307.meaning .nominal)
      (GeneralMixedCompoundUpperTypes307.meaning .variantWidth) :=
    equivalent_trans ⟨a.2,a.1⟩ (equivalent_trans collapse midValue)
  cases equiv_kind impossible

theorem no_merge_forward : ¬ SameInputs (GeneralNominalVersionedJournal232.Models upperState) rSite childSite := by
  intro yes
  have all := GeneralNominalDemandMerging.same_inputs_denote _ _ _ yes w witness _ _ root_denotes child_denotes
  cases all with | cons h _ => exact different h

theorem no_merge_backward : ¬ SameInputs (GeneralNominalVersionedJournal232.Models upperState) childSite rSite := by
  intro yes
  have all := GeneralNominalDemandMerging.same_inputs_denote _ _ _ yes w witness _ _ child_denotes root_denotes
  cases all with | cons h _ => exact different ⟨h.2,h.1⟩

theorem halted (next : State roles) : ¬ Step registry root upperState next := by
  rintro ⟨focus,reachable,op⟩
  have casesFocus := reached_cases reachable
  cases op with
  | administrative act =>
    cases act with
    | enqueue linked absent =>
      rcases casesFocus with rfl|rfl
      · exact absent _ (raw_sites ▸ List.mem_cons_self ..) rfl
      · exact absent _ (raw_sites ▸ List.mem_cons_of_mem _ (List.mem_singleton_self _)) rfl
    | refresh ctx cert index present unknown known =>
      exact impossible_further_refresh ctx cert index present unknown known
    | equate first last a b equal novel => exact novel (equality_closed first last a b equal)
    | reobserve rev _ imp =>
      exact GeneralNominalReobservationSteps.pointClosed_no_revision
        (state := upperState.core.erased.current) point_closed rev imp
  | refresh target ctx cert index present unknown known =>
    exact impossible_further_refresh ctx cert index present unknown known
  | install effect enabled novel =>
    rcases casesFocus with same|same
    · exact no_install_root effect enabled same
    · exact no_install_child effect enabled same
  | merge first last firstMember lastMember equal novel =>
    rw [centers] at firstMember lastMember
    rcases List.mem_cons.mp firstMember with rfl|firstMember <;>
      rcases List.mem_cons.mp lastMember with rfl|lastMember
    · exact novel (.refl _)
    · cases List.mem_singleton.mp lastMember; exact no_merge_forward equal
    · cases List.mem_singleton.mp firstMember; exact no_merge_backward equal
    · cases List.mem_singleton.mp firstMember; cases List.mem_singleton.mp lastMember; exact novel (.refl _)

theorem stable : Stable registry upperState root :=
  (GeneralNominalVersionedMixedKernel234.closure halted).1

end Yulang.GeneralMixedCompoundUpperHalt307
