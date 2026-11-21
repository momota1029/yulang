import Yulang.GeneralWherePhysicalCurrentCycle319

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 33000
set_option maxHeartbeats 36000000
namespace Yulang.GeneralWherePhysicalCurrentPick319
open CommonNominalFullCarrier
open GeneralWhereOriginSingleSource318
open GeneralWherePhysicalCurrentRead319 (packet plan locate zero exact_report)
open GeneralWherePhysicalCurrentFrame319 (frame prepared unique no_pending)
open GeneralWherePhysicalCurrentCycle319 (no_raw no_semantic current_tests)
open GeneralWherePhysicalCurrentModel319 (actual_n captures tests)
open GeneralWherePhysicalPatch319 (n compatible_update)
open GeneralWherePhysicalReobserve319 (updated requests)
open GeneralWherePhysicalPast319 (point)
open GeneralWhereOriginSingleCells318 (oldChild sig)
open GeneralDictionaryJournalRefinement228Source (roles root snapshot root_point)
open GeneralNominalVersionedCandidates231 (inputs)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedDiagnostic232 (AdministrativeReady HeadEquations boundary)
open GeneralNominalVersionedEffects231 (ClassEffects)
open GeneralNominalCenteredHeadOutputs (EqualOutputs)
open GeneralNominalCenters
open GeneralLiveCompoundRegistry316 (otherChild)
open GeneralLiveCompoundPostFrames316 (frame_unique)

abbrev sourceRoot := rootSite snapshot.seed root

theorem old_emitted : GeneralWhereVersionInstall317.emitted oldPlan = [oldChild] := by
  have kids : GeneralWhereVersionCompiler317.children oldPlan = [oldChild.occurrence] := by
    unfold GeneralWhereVersionCompiler317.children
    rw [GeneralWherePhysicalOldModel319.compiled_emission]
    rfl
  have len := congrArg List.length (GeneralWhereVersionInstall317.ordered oldPlan)
  rw [kids] at len
  simp only [List.length_map,List.length_singleton] at len
  obtain ⟨one,eq⟩ := List.length_eq_one_iff.mp len
  have member : one ∈ GeneralWhereVersionInstall317.emitted oldPlan := eq ▸ List.mem_singleton_self _
  obtain ⟨clause,_,same⟩ := List.mem_map.mp member
  have visible := (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr clause.property
  have named : clause.val = otherChild := List.mem_singleton.mp visible
  have sameSite : one = oldChild := by
    rw [← same]
    rcases clause with ⟨clause,valid⟩
    change clause = otherChild at named
    subst clause
    rfl
  exact eq.trans (congrArg List.singleton sameSite)

theorem raw_sites : updated.mixed.core.erased.current.sites =
    [GeneralNominalDemandMerging.pointSite root,oldChild.observed] := by
  change [GeneralNominalDemandMerging.pointSite root] ++
    (GeneralWhereVersionInstall317.emitted oldPlan).map Site.observed = _
  rw [old_emitted]; rfl

theorem centers : updated.mixed.core.sites = [sourceRoot,oldChild] := by
  change [sourceRoot] ++ GeneralWhereVersionInstall317.emitted oldPlan = _
  rw [old_emitted]; rfl

theorem different_occ : oldChild.occurrence ≠ root := by
  intro same
  have bad : (1:Nat) = 0 := congrArg (fun o : GeneralSourceDictionaries.Occurrence roles => o.demand.role) same
  cases bad

theorem root_frame {key} {p : Plan roles} (h : Frame registry updated.mixed.core root key p) : p = plan := by
  apply frame_unique (focus := root) (last := plan) h.registry_eq h.context_eq
  · rcases List.mem_cons.mp h.visible with first|tail
    · exact first
    · have eq := List.mem_singleton.mp tail
      have role := h.role_eq
      rw [eq] at role
      cases role
  · have seen := h.raw_recorded
    rw [raw_sites] at seen
    rcases List.mem_cons.mp seen with same|tail
    · exact same
    · have eq := congrArg GeneralNominalDemandMerging.Site.occurrence (List.mem_singleton.mp tail)
      exact False.elim (different_occ (eq.symm.trans h.occurrence_eq))
  · have seen := h.center_recorded
    rw [centers] at seen
    rcases List.mem_cons.mp seen with same|tail
    · exact same
    · have eq := congrArg Site.occurrence (List.mem_singleton.mp tail)
      exact False.elim (different_occ (eq.symm.trans (p.input_exact.trans h.occurrence_eq)))
  · exact h.located
  · exact locate

theorem administrative : AdministrativeReady updated.mixed root := by
  refine ⟨⟨sourceRoot,centers ▸ List.mem_cons_self,rfl⟩,?_⟩
  intro first one _ last two same
  rw [centers] at one two
  rcases List.mem_cons.mp one with rfl|one <;> rcases List.mem_cons.mp two with rfl|two
  · exact .refl _
  · cases List.mem_singleton.mp two
    have impossible : (0:Nat) = 1 := same.1
    cases impossible
  · cases List.mem_singleton.mp one
    have impossible : (1:Nat) = 0 := same.1
    cases impossible
  · cases List.mem_singleton.mp one
    cases List.mem_singleton.mp two
    exact .refl _

theorem request_exact (focus : GeneralSourceDictionaries.Occurrence roles) (out)
    (seen : out ∈ GeneralNominalCenteredHeadOutputs.requests updated.mixed.core focus) :
    out = ⟨0,4⟩ := by
  apply GeneralWherePhysicalOldPick319.all_requests focus
  exact (GeneralWhereOriginSuccessor318.requests_unchanged _ _ _ GeneralWherePhysicalOldInstall319.silent focus out).mp
    ((requests focus out).mp seen)

theorem equal_outputs (focus : GeneralSourceDictionaries.Occurrence roles) :
    EqualOutputs updated.mixed.core focus n := by
  intro a ha b hb _
  cases request_exact focus a ha
  cases request_exact focus b hb
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem classes : ClassEffects updated.mixed.core root plan n := by
  apply (GeneralNominalVersionedEffects231.class_effects_iff ..).mpr
  refine ⟨?_,equal_outputs root⟩
  intro out used body resolved
  cases request_exact root out used
  have bodyEq : body = .explicit ⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩ :=
    Option.some.inj resolved |>.symm
  subst body
  intro row member
  cases List.mem_singleton.mp member
  exact actual_n

theorem ready : GeneralNominalCenteredHeadMatEffects.Ready updated.mixed.core root plan := by
  intro out used
  cases request_exact root out used
  exact ⟨.explicit ⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩,rfl,rfl⟩

theorem equations : HeadEquations plan n :=
  ⟨point_root_holds _ _ root_point _,fun i h => captures i (.inl h),tests⟩

theorem safe : B4TargetV8.SafeKnown (boundary roles) registry updated.mixed root := by
  refine ⟨no_pending,?_,?_,?_⟩
  · rintro (raw | (⟨i,cycle⟩ | ⟨site,seen,atRoot,idx,cycle⟩))
    · obtain ⟨_,_,_,slot,named,cycle⟩ := raw
      have eq : slot = zero := point.base.source_injective named
      subst slot
      exact no_raw cycle
    · exact no_semantic cycle
    · rw [centers] at seen
      rcases List.mem_cons.mp seen with rfl|tail
      · exact no_semantic cycle
      · cases List.mem_singleton.mp tail
        exact different_occ atRoot
  · rintro (raw | ⟨p,framed,entry,seen,cycle⟩)
    · obtain ⟨_,d,visible,_,atRole,_,bounds,found,visited,hit,cycled⟩ := raw
      rcases List.mem_cons.mp visible with first|tail
      · subst d
        have equal : bounds = [(zero,zero)] := Option.some.inj (found.symm.trans locate)
        subst bounds
        change visited ∈ (GeneralNominalRecursiveCandidates.report GeneralWherePhysicalPast319.pointCtx declaration [(zero,zero)]).inspected at hit
        rw [exact_report] at hit
        cases List.mem_singleton.mp hit
        exact no_raw cycled
      · cases List.mem_singleton.mp tail; cases atRole
    · cases root_frame framed
      rw [current_tests] at seen
      cases List.mem_singleton.mp seen
      exact no_semantic cycle
  · rintro (⟨_,d,visible,role,_,unprepared⟩ | unready)
    · rcases List.mem_cons.mp visible with eq|rest
      · subst d; exact unprepared prepared
      · cases List.mem_singleton.mp rest
        cases role
    · exact unready administrative

theorem selected : GeneralNominalVersionedMixedSourceBoundary234.Local sourceRegistry updated.mixed root
    (.selected declaration.id (GeneralNominalVersionedFrame231.children packet)) := by
  apply GeneralNominalVersionedMixedSourceBoundary234.local_iff.mpr
  apply GeneralNominalVersionedMixedBoundary234.local_iff.mpr
  refine .ordinary ?_ (.ordinary ?_ (.selected safe unique ?_))
  · rintro ⟨key,kids,picked,_,blocked⟩
    have same := (unique.2 key kids picked.1).1
    subst key
    exact blocked.2.2 ⟨n,compatible_update.1,plan,frame,GeneralNominalVersionedHeadSharing232.schema_holds plan n tests⟩
  · exact GeneralNominalVersionedMergedConflict232.models_exclude_conflict compatible_update.1
      (fun focus _ => equal_outputs focus) (equal_outputs root)
  · intro clash
    exact clash.2 ⟨n,compatible_update.1,⟨⟨_,unique⟩,plan,frame,ready,equations,classes⟩⟩

end Yulang.GeneralWherePhysicalCurrentPick319
