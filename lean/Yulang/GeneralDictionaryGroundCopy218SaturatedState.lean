import Yulang.GeneralDictionaryGroundCopy218Reinstall

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDictionaryGroundCopy218SaturatedState
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters CommonNominalFullCarrier
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryGroundCopy218Install (model plan packet childSite effect sourceForm model_forms)
open GeneralDictionaryGroundCopy218Reobserve
open GeneralDictionaryGroundCopy218Reinstall (reinstalled newPlan newPacket newChild newEffect)
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalSaturationState (Generated Alias)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryGroundCopy218Stability (Owned Supported)
variable {atoms : List (PresenceNormalForm.Atom Nat)}

abbrev allocation := newPacket.privateContext.state.allocated
abbrev reservation := newPacket.privateContext.state.reserved
abbrev current (atoms : List (PresenceNormalForm.Atom Nat)) := pointExtended allocation reservation atoms

def stage (atoms : List (PresenceNormalForm.Atom Nat)) : State roles :=
  { reinstalled with core := { reinstalled.core with erased := { reinstalled.core.erased with current :=
    { reinstalled.core.erased.current with context :=
      ⟨{ reinstalled.core.erased.current.context.state with ordinary := atoms },context.interpretation⟩ } } } }

abbrev initialAtoms := reinstalled.core.erased.current.context.state.ordinary

theorem stage_initial : stage initialAtoms = reinstalled := rfl
theorem stage_context (atoms) : (stage atoms).core.erased.current.context = ⟨current atoms,interpretation⟩ := rfl

theorem sites_exact (atoms) : (stage atoms).core.sites = [plan.input,childSite,newChild] := rfl
theorem raw_sites_exact (atoms) : (stage atoms).core.erased.current.sites =
    [GeneralNominalDemandMerging.pointSite root,childSite.observed,newChild.observed] := rfl
theorem plans_exact (atoms) : (stage atoms).core.plans = [newPlan,plan] := rfl
theorem effects_exact (atoms) : (stage atoms).effects = [newEffect,effect] := rfl
theorem aliases_empty (atoms) : (stage atoms).core.erased.current.aliases = [] := rfl
theorem edges_exact (atoms) : (stage atoms).core.erased.current.edges =
    [(root,childSite.occurrence),(root,newChild.occurrence)] := GeneralDictionaryGroundCopy218Reinstall.reinstalled_edges

theorem requests_empty (atoms) (focus : Occurrence roles) :
    GeneralNominalCenteredHeadOutputs.requests (stage atoms).core focus = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro output member
  obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
  rw [raw_sites_exact] at present
  rcases List.mem_cons.mp present with rfl | present
  · cases within
  · rcases List.mem_cons.mp present with rfl | present
    · cases within
    · cases List.mem_singleton.mp present; cases within

theorem class_effects (atoms) (focus : Occurrence roles) (candidate : Plan roles) (given : Assignment) :
    GeneralNominalCenteredHeadMatEffects.ClassEffects (stage atoms).core focus candidate given := by
  constructor <;> intro output member <;> simp [requests_empty] at member

theorem model_if_atoms (atoms)
    (held : PresenceNormalForm.All CommonNominalFullCarrier.model model atoms) : Models (stage atoms) model := by
  have prior := GeneralDictionaryGroundCopy218Reinstall.reinstalled_models
  refine ⟨⟨prior.1.1,prior.1.2.1,held⟩,prior.2.1,prior.2.2.1,prior.2.2.2.1,prior.2.2.2.2.1,?_⟩
  intro effect member
  exact ⟨(prior.2.2.2.2.2 effect member).1,class_effects atoms _ _ model⟩

theorem atoms_initial : PresenceNormalForm.All CommonNominalFullCarrier.model model initialAtoms :=
  GeneralDictionaryGroundCopy218Reinstall.reinstalled_models.1.2.2

theorem stage_old_models {given : Assignment} (held : Models (stage atoms) given) : Models reinstalled given := by
  have packetHeld := held.2.2.2.2.1 newPlan List.mem_cons_self
  have ordinary := (GeneralNominalCenteredHeadMatStepPackets.private_models packetHeld).2.2
  refine ⟨⟨held.1.1,held.1.2.1,ordinary⟩,held.2.1,held.2.2.1,held.2.2.2.1,held.2.2.2.2.1,?_⟩
  intro effect member
  exact ⟨(held.2.2.2.2.2 effect member).1,class_effects initialAtoms _ _ given⟩

theorem generated_from_root_only {focus}
    (generated : Generated (stage atoms).core.erased.current root focus) :
    focus = root ∨ focus = childSite.occurrence ∨ focus = newChild.occurrence := by
  induction generated with
  | root => exact Or.inl rfl
  | child prior member ih =>
    rw [edges_exact] at member
    rcases List.mem_cons.mp member with same | member
    · exact Or.inr (Or.inl (congrArg Prod.snd same))
    · exact Or.inr (Or.inr (congrArg Prod.snd (List.mem_singleton.mp member)))
  | alias prior one two related ih =>
    rw [raw_sites_exact] at two
    rcases List.mem_cons.mp two with rfl | two
    · exact Or.inl rfl
    · rcases List.mem_cons.mp two with rfl | two
      · exact Or.inr (Or.inl rfl)
      · cases List.mem_singleton.mp two; exact Or.inr (Or.inr rfl)

theorem old_generated (atoms) : Generated (stage atoms).core.erased.current root childSite.occurrence :=
  .child .root (edges_exact atoms ▸ List.mem_cons_self)
theorem new_generated (atoms) : Generated (stage atoms).core.erased.current root newChild.occurrence :=
  .child .root (edges_exact atoms ▸ List.mem_cons_of_mem _ (List.mem_singleton_self _))

theorem impossible (given : Assignment) (held : Models (stage atoms) given) :
    GeneralDictionarySharingObstruction217.Impossible registry (stage atoms).core given childSite.occurrence 1 := by
  apply GeneralDictionaryTopLevelSharing217.impossible registry (stage atoms) given childSite.occurrence 1 0
  · intro declaration visible key
    cases GeneralDictionaryGroundCopy218Obstruction.key_leaf visible key
    exact GeneralDictionaryGroundCopy218Obstruction.leaf_queries _
  · intro site member equal
    rw [sites_exact] at member
    rcases List.mem_cons.mp member with rfl | member
    · have mismatch := congrArg (fun o : Occurrence roles => o.demand.role) equal
      cases mismatch
    · rcases List.mem_cons.mp member with rfl | member
      · exact GeneralDictionaryGroundCopy218Obstruction.centers_different given
          (held.2.2.2.2.1 plan (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
      · cases List.mem_singleton.mp member
        exact False.elim (GeneralDictionaryGroundCopy218Reinstall.different_child equal)

theorem no_evidence (given : Assignment) (held : Models (stage atoms) given) (dictionaries) :
    ¬ GeneralDictionaryTotalEvidence206.Evidence registry (stage atoms).core given childSite.occurrence (.node 1 dictionaries) :=
  GeneralDictionarySharingObstruction217.no_evidence (impossible given held) dictionaries

theorem no_output_conflict (atoms) :
    ¬ GeneralNominalCenteredHeadMatStepLocal.OutputConflict registry (stage atoms) childSite.occurrence 1 :=
  GeneralDictionarySharingObstruction217.no_output_conflict (fun given held => impossible given held)

theorem no_install_old (candidate : Effect roles)
    (focus : candidate.plan.packet.site.occurrence = childSite.occurrence) :
    ¬ GeneralDictionaryDefaultKernel208.Installable registry (stage atoms) candidate := by
  intro enabled
  obtain ⟨given,valid,held,_⟩ := enabled.common
  have frame : GeneralNominalCenteredHeadOutputs.Frame registry (stage atoms).core
      childSite.occurrence candidate.plan.packet.declaration.id candidate.plan := by
    rw [← focus,← enabled.registry_eq,← enabled.snapshot_eq]
    exact candidate.frame
  have declarationEq := GeneralDictionaryGroundCopy218Obstruction.role_leaf frame.visible frame.role_eq
  have key : candidate.plan.packet.declaration.id = 1 := congrArg GeneralDeclarations.Declaration.id declarationEq
  exact impossible given valid candidate.plan (key ▸ frame)
    (GeneralDictionarySharingObstruction217.packet_agreement candidate.plan given held)

theorem new_pending (atoms) : GeneralNominalState.RootPending (current atoms) newChild.occurrence.demand :=
  GeneralDictionaryGroundCopy218Reinstall.new_child_pending

theorem no_install_new (candidate : Effect roles)
    (focus : candidate.plan.packet.site.occurrence = newChild.occurrence) :
    ¬ GeneralDictionaryDefaultKernel208.Installable registry (stage atoms) candidate := by
  intro enabled
  exact enabled.safe.1 (focus ▸ new_pending atoms)

theorem no_reobserve (revision : GeneralNominalReobservationSteps.Revision (stage atoms).core.erased.current) :
    ¬ GeneralNominalReobservationSteps.Improves revision :=
  GeneralNominalReobservationSteps.pointClosed_no_revision (point_closed allocation reservation atoms) revision

theorem no_refresh (held : PresenceNormalForm.All CommonNominalFullCarrier.model model atoms)
    (certificate : GeneralNominalCenteredHeadMatStepRefresh.Refresh (stage atoms) nextContext)
    (unknown : ¬ GeneralNominalState.Known (current atoms) identity)
    (known : GeneralNominalState.Known nextContext.state identity) : False :=
  GeneralDictionaryGroundCopy218Refresh.no_new_head (stage atoms) model (model_if_atoms atoms held)
    nextContext.state certificate.cache identity
    (GeneralDictionaryGroundCopy218Stability.unknown_shape (atoms := atoms) unknown) known

theorem raw_edge_decreases (held : PresenceNormalForm.All CommonNominalFullCarrier.model model atoms)
    {a b : Fin 8} (edge : GeneralNominalMixedRecurrence.Edge (current atoms) a b) :
    (sourceForm b.val).rank < (sourceForm a.val).rank := by
  rcases edge with structural | nominal
  · obtain ⟨kind,children,recorded,index,child⟩ := structural
    change (if a = 2 then .structural 0 (fun _ => 0) else if a = 3 then .structural 0 (fun _ => 1) else
      .deferred .unresolved : GeneralNormalizedObservation.Head GeneralDictionaryGroundCopy218Source.view.shapes 8) = .structural kind children at recorded
    split at recorded
    · rename_i equal; subst a
      cases recorded
      have zero : b = 0 := child.symm
      subst b
      change 0 < 1; decide
    · split at recorded
      · rename_i equal; subst a
        cases recorded
        have one : b = 1 := child.symm
        subst b
        change 0 < 1; decide
      · cases recorded
  · obtain ⟨descriptor,recorded,index,actual,seen,same⟩ :=
      GeneralNominalMixedRecurrence.actual_edge_sound (current atoms) a b nominal model (model_if_atoms atoms held).1
    have observation := GeneralNominalRecursiveInspection.embed_observation model _ actual seen
    cases observation with
    | nominal parent equal found =>
      cases parent
      have firstValue : (model a.val).1 = (sourceForm a.val).value :=
        (GeneralDictionaryGroundCopy218Install.model_small a.val (by omega)).trans (GeneralDictionaryGroundCopy218Install.source_form a.val)
      have lastValue : (model b.val).1 = (sourceForm b.val).value :=
        (GeneralDictionaryGroundCopy218Install.model_small b.val (by omega)).trans (GeneralDictionaryGroundCopy218Install.source_form b.val)
      rw [firstValue] at equal
      obtain ⟨child,smaller,meaning⟩ := GeneralDictionaryGroundCopy218Cycles.nominal_child
        (sourceForm a.val) equal found
      rw [lastValue] at same
      have rankEq := GeneralDictionaryGroundCopy218Cycles.equivalent_rank child (sourceForm b.val)
        ⟨subtype_trans meaning.2 same.1,subtype_trans same.2 meaning.1⟩
      omega

theorem no_raw_recurs (held : PresenceNormalForm.All CommonNominalFullCarrier.model model atoms)
    (slot : Fin 8) : ¬ GeneralNominalCycleK2.RecursAt (current atoms) slot := by
  have paths : ∀ a b, GeneralNominalMixedRecurrence.Path (current atoms) a b →
      (sourceForm b.val).rank ≤ (sourceForm a.val).rank := by
    intro a b path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge path ih => exact Nat.le_trans ih (Nat.le_of_lt (raw_edge_decreases held edge))
  intro cycle
  obtain ⟨next,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle _ _ cycle
  have smaller := raw_edge_decreases held edge
  have larger := paths _ _ path
  omega

theorem sources_iff (identity : Nat) :
    identity ∈ GeneralNominalState.sources (current atoms) ↔
      identity ∈ GeneralNominalState.sources (GeneralDictionaryGroundCopy218Stability.current atoms) := by
  have reserves : reservation = installedReservation ++ installedReservation := by
    simp only [reservation,installedReservation,GeneralNominalSaturationState.Packet.privateContext,
      GeneralNominalRecursiveCandidates.privateState,GeneralNominalAllocation.propagate,
      GeneralNominalState.extend,List.nil_append,List.append_nil]
    rfl
  change identity ∈ List.ofFn base.source ++ List.ofFn base.rowSource ++ reservation ++
      atoms.flatMap GeneralNominalState.atomSources ↔
    identity ∈ List.ofFn base.source ++ List.ofFn base.rowSource ++ installedReservation ++
      atoms.flatMap GeneralNominalState.atomSources
  rw [reserves]
  simp only [List.mem_append,or_self]

theorem source_owned (supported : Supported atoms)
    (member : identity ∈ GeneralNominalState.sources (current atoms)) : Owned identity :=
  GeneralDictionaryGroundCopy218Stability.source_owned supported ((sources_iff identity).mp member)

theorem missing (supported : Supported atoms) :
    ∀ identity ∈ GeneralNominalState.sources (current atoms),
      identity ≠ GeneralDictionaryGroundCopy218Leaf.lo ∧ identity ≠ GeneralDictionaryGroundCopy218Leaf.hi :=
  fun identity member => GeneralDictionaryGroundCopy218Stability.missing supported identity ((sources_iff identity).mp member)

theorem fresh (supported : Supported atoms) :
    GeneralNominalAllocation.Fresh (current atoms) registry GeneralDictionaryGroundCopy218Leaf.childId := by
  intro key member collision
  exact False.elim (GeneralDictionaryGroundCopy218Stability.owned_not_child
    (source_owned supported collision) key (GeneralDictionaryGroundCopy218Stability.key_invocation member) rfl)

theorem supported_equate (supported : Supported atoms)
    (one : first ∈ GeneralNominalState.sources (current atoms))
    (two : last ∈ GeneralNominalState.sources (current atoms)) :
    Supported (atoms ++ GeneralNominalAllocation.equations first (.var last)) :=
  GeneralDictionaryGroundCopy218Stability.supported_equate supported
    ((sources_iff first).mp one) ((sources_iff last).mp two)

theorem supported_initial : Supported initialAtoms := by
  have ordinary : initialAtoms = GeneralDictionaryGroundCopy218Obstruction.initialAtoms ++
      [.tyLe (.var 4) (.var 4),.tyLe (.var 5) (.var 5),
       .tyLe (.var 6) (.var 6),.tyLe (.var 6) (.var 6),
       .tyLe (.var 4) (.var 4),.tyLe (.var 5) (.var 5)] := by
    change (GeneralNominalRecursiveCandidates.privateState registry
      GeneralDictionaryGroundCopy218Reinstall.currentContext root
      GeneralDictionaryGroundCopy218Install.declaration [(6,6)]).ordinary = _
    unfold GeneralNominalRecursiveCandidates.privateState
    rw [GeneralDictionaryGroundCopy218Reinstall.report_exact]
    simp only [GeneralNominalState.extend,GeneralNominalAllocation.propagate,List.append_assoc]
    rfl
  intro identity member
  rw [ordinary,List.flatMap_append] at member
  rcases List.mem_append.mp member with old | fresh
  · exact GeneralDictionaryGroundCopy218Stability.supported_initial identity old
  · change identity ∈ [4,4,5,5,6,6,6,6,4,4,5,5] at fresh
    simp only [List.mem_cons,List.not_mem_nil,or_false] at fresh
    exact Or.inl (by omega)

theorem merges_closed {first last}
    (one : first ∈ (stage atoms).core.sites) (two : last ∈ (stage atoms).core.sites)
    (same : SameInputs models first last) :
    Alias (stage atoms).core.erased.current first.occurrence.identity last.occurrence.identity := by
  rw [sites_exact] at one two
  simp only [List.mem_cons,List.not_mem_nil,or_false] at one two
  rcases one with rfl | rfl | rfl <;> rcases two with rfl | rfl | rfl
  all_goals first
    | exact .refl _
    | exact False.elim (by have impossible := same.1; cases impossible)

theorem registered {focus}
    (generated : Generated (stage atoms).core.erased.current root focus) :
    ∃ site ∈ (stage atoms).core.erased.current.sites, site.occurrence = focus := by
  rcases generated_from_root_only generated with rfl | rfl | rfl
  · exact ⟨GeneralNominalDemandMerging.pointSite root,
      by rw [raw_sites_exact]; exact List.mem_cons_self,rfl⟩
  · exact ⟨childSite.observed,
      by rw [raw_sites_exact]; exact List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩
  · exact ⟨newChild.observed,
      by rw [raw_sites_exact]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),rfl⟩

theorem administrative_ready (atoms) :
    GeneralNominalCenteredHeadMatStepLocal.AdministrativeReady (stage atoms) childSite.occurrence := by
  refine ⟨⟨childSite,by rw [sites_exact]; exact List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩,?_⟩
  intro first one _ last two same
  exact merges_closed one two same

theorem merged_clear (atoms) :
    ¬ GeneralNominalCenteredHeadAllocMergedConflict.MergedOutputConflict (stage atoms) childSite.occurrence := by
  rintro ⟨⟨a,b,member,_⟩,_⟩
  cases member

end Yulang.GeneralDictionaryGroundCopy218SaturatedState
