import Yulang.GeneralLatePeerCurrent311

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32000
set_option maxHeartbeats 21500000
namespace Yulang.GeneralLatePeerTransfer311
open GeneralLatePeerSource311 (compiled registry checked root receiver)
open GeneralLatePeerRoot311 (direct branch z)
open GeneralLatePeerRoutePlan311 (child)
open GeneralLatePeerRouteInstall311 (emitted)
open GeneralLatePeerDirectInstall311 (recorded)
open GeneralLatePeerMerge311 (final reached context_same identity_before child_new child_root child_branch)
open GeneralLatePeerCurrent311 (picked inhabited fresh frame classes current_z)
open GeneralLatePeerFinalPeerPlan311 (plan packet)
open GeneralNominalSaturationState (Alias Packet)
open GeneralVersionedPeerChoice311 (PeerCertificate reads)
open GeneralVersionedHistoryChoice310 (OrdinaryOwner)
open GeneralNominalVersionedInstallation231 (reserved atoms allocated)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarationExamples (roles)
open GeneralNominalCenters (Plan)
open GeneralDictionaryOrdinaryTransport (extend)

abbrev old := GeneralLatePeerDirectPlan311.packet
abbrev route := GeneralLatePeerRouteInstall311.packet

theorem recorded_old : old ∈ final.core.erased.current.packets :=
  List.mem_cons_of_mem _ List.mem_cons_self

theorem owner : OrdinaryOwner final old direct.occurrence := by
  refine ⟨rfl,reserved old ++ reserved route, atoms old ++ atoms route,allocated old ++ allocated route,?_,?_⟩
  · rw [context_same]
    change extend (extend old.context (reserved old) (atoms old) (allocated old))
      (reserved route) (atoms route) (allocated route) = _
    exact GeneralVersionedReplayComposition310.context _ _ _ _ _ _ _
  · exact fun _ h => List.mem_append_left _ h

theorem direct_observation : reads final.core.erased.current.context direct.occurrence =
    reads final.core.erased.current.context child.occurrence := by
  have first : reads final.core.erased.current.context direct.occurrence =
      some [(GeneralLatePeerFinalPeerPlan311.two,GeneralLatePeerFinalPeerPlan311.two)] := by
    decide +kernel
  exact first.trans GeneralLatePeerCurrent311.located.symm

theorem actual_peer : PeerCertificate registry final old child.occurrence := by
  refine ⟨owner,direct_observation,?_,?_⟩
  · intro _ _
    exact fresh _
  · intro bounds _ name present
    cases present

theorem alias_old_only {other : Packet roles} (seen : other ∈ final.core.erased.current.packets)
    (related : Alias final.core.erased.current child.occurrence.identity other.site.occurrence.identity) :
    other = old := by
  have exact := (GeneralRebaseMergeRequests264.alias_merge emitted direct child _ _).mp related
  have loc : other.site.occurrence.identity = child.occurrence.identity ∨
      other.site.occurrence.identity = direct.occurrence.identity := by
    rcases exact with oldRel|⟨one,two⟩|⟨one,two⟩
    · exact .inl (identity_before oldRel).symm
    · exact .inl (identity_before two).symm
    · exact .inr (identity_before two).symm
  change other ∈ [route,old,GeneralLatePeerRoot311.packet] at seen
  simp only [List.mem_cons,List.not_mem_nil,or_false] at seen
  rcases seen with rfl|rfl|rfl
  · rcases loc with one|two
    · exact False.elim (child_branch one.symm)
    · exact False.elim (GeneralLatePeerFresh311.distinct_child two)
  · rfl
  · rcases loc with one|two
    · exact False.elim (child_root one.symm)
    · exact False.elim (GeneralLatePeerFresh311.direct_different two.symm)

theorem compatible :
    GeneralNominalCycleSteps.ChoiceCompatible final.core.erased.current packet := by
  apply GeneralVersionedPeerChoice311.choice ⟨rfl,checked⟩ reached picked inhabited
  intro history stored related
  cases alias_old_only stored related
  exact actual_peer

theorem no_recorded_focus (p : Plan roles) (member : p ∈ final.plans) :
    p.packet.site.occurrence.identity ≠ child.occurrence.identity := by
  change p ∈ [GeneralLatePeerRouteInstall311.plan,GeneralLatePeerDirectPlan311.plan,GeneralLatePeerRoot311.plan] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl
  · exact Ne.symm child_branch
  · exact Ne.symm child_new
  · exact Ne.symm child_root

theorem genuinely_not_replay :
    ¬ GeneralVersionedRecursiveBridge310.ReplayFrame registry final child.occurrence 2 [] := by
  rintro ⟨p,stored,rs,ats,allocated,cur,ordered⟩
  have eq := congrArg GeneralSourceDictionaries.Occurrence.identity cur.occurrence_eq
  exact no_recorded_focus p stored eq

/-- Actual cross-occurrence compatibility without a replay at the peer, even
    though that peer inherits an existing live named request. -/
theorem nontrivial :
    old ∈ final.core.erased.current.packets ∧
    old.site.occurrence.identity ≠ packet.site.occurrence.identity ∧
    Alias final.core.erased.current packet.site.occurrence.identity old.site.occurrence.identity ∧
    ¬ GeneralVersionedRecursiveBridge310.ReplayFrame registry final packet.site.occurrence 2 [] ∧
    GeneralNominalCycleSteps.ChoiceCompatible final.core.erased.current packet :=
  ⟨recorded_old,Ne.symm child_new,GeneralLatePeerMerge311.alias,genuinely_not_replay,compatible⟩

end Yulang.GeneralLatePeerTransfer311
