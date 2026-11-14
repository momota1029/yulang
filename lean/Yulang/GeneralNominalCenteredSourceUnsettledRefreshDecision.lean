import Yulang.GeneralNominalCenteredSourceUnsettledRefreshWitness
import Yulang.GeneralNominalCenteredSourceUnsettledRefreshControl
import Yulang.GeneralNominalCenteredBoundary
import Yulang.GeneralNominalCenteredSourceSnapshotLedger
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralNominalCenteredSourceUnsettledRefreshDecision
open GeneralNominalCenteredSourceUnsettledRefreshWitness
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalCenteredSteps GeneralNominalCenters GeneralNominalRecursiveInspection
open GeneralSourceState (equationAtoms)
open Core.PresenceGeneration (TyTerm)

abbrev controlView : GeneralNormalizedObservation.Snapshot refreshedBase where
  kinds := refreshedView.kinds
  shapes := refreshedView.shapes
  shapes_injective := refreshedView.shapes_injective
  canonical := refreshedView.canonical
  heads := fun slot => if slot = 1 then .structural 0 (fun _ => 2) else refreshedView.heads slot
  checked := by
    intro slot term recorded
    by_cases one : slot = 1
    · subst slot
      have equal : (.pair (.var 2) (.var 2) : TyTerm (Fin 5)) = term := by
        simpa [GeneralNormalizedObservation.Head.term,GeneralNormalizedObservation.Shape.term] using recorded
      subst term
      exact .ordinary (by decide +kernel) (by decide +kernel)
    · have old : (refreshedView.heads slot).term = some term := by simpa only [one,ite_false] using recorded
      exact refreshedView.checked slot term old

abbrev controlSource : GeneralNominalState.State :=
  {refreshedSource with view := controlView, bodies_opaque := by intro slot descriptor recorded; cases recorded}
abbrev controlContext : GeneralNominalCandidates.Context := ⟨controlSource,interpretation⟩
noncomputable abbrev control := refresh afterP controlContext

theorem identical_models (model : GeneralNominalCommonBridge.Assignment) :
    Models control model ↔ Models refreshed model := Iff.rfl

theorem control_known (identity : Nat) (known : GeneralNominalState.Known refreshedSource identity) :
    GeneralNominalState.Known controlSource identity := by
  obtain ⟨slot,equal,head|⟨descriptor,recorded⟩⟩ := known
  · refine ⟨slot,equal,Or.inl ?_⟩
    by_cases one : slot = 1
    · subst slot; intro impossible; cases impossible
    · simpa only [controlSource,controlView,GeneralNormalizedObservation.Snapshot.graph,one,ite_false] using head
  · cases recorded

noncomputable def controlCertificate : Refresh afterP controlContext where
  refines := {refreshRefines with known := fun identity known => control_known identity (refreshRefines.known identity known)}
  interpretation := rfl
  exact := refreshed_exact
  support := refreshed_support

theorem controlStep : Step registry root afterP control := by
  refine ⟨root,.root,.refresh root controlContext controlCertificate 3 ?_ progress_unknown ?_⟩
  · exact GeneralNominalAllocationSupport.slot_source afterP.erased.current.context.state (3 : Fin 4)
  · exact control_known 3 progress_known

theorem control_reachable : B4Target.Steps (Step registry root) initialState control :=
  .tail (.tail .refl stepP) controlStep

theorem control_arguments : GeneralNominalRecursiveCandidates.arguments controlContext emittedChild.occurrence = some [(1,1)] := by
  change GeneralNominalCandidates.arguments controlContext emittedChild.occurrence = some [(1,1)]
  have args : emittedChild.occurrence.demand.arguments = fun _ => (1,1) := funext (childP_arguments childSignature)
  rw [GeneralNominalCandidates.arguments,args]
  rfl

theorem control_queries : GeneralNominalInspection.queries controlSource interpretation r =
    [.node .pair [.scalar .int,.variables [1]]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,GeneralNominalInspection.translate,normalizeArgs,normalize,interpretation,
    constructors,GeneralDeclarationExamples.constructors]

theorem control_reads : GeneralNominalSupport.readsMany controlSource
    (GeneralNominalInspection.queries controlSource interpretation r) [(1,1)] = [1,1,2] := by
  rw [control_queries]
  have atOne : controlSource.view.heads 1 = .structural 0 (fun _ => 2) := rfl
  simp only [GeneralNominalSupport.readsMany,GeneralNominalSupport.reads,atOne]
  change [1,1] ++ GeneralNominalSupport.readsMany controlSource [.scalar .int,.variables [1]] [(2,2),(2,2)] ++ [] = _
  simp [GeneralNominalSupport.readsMany,GeneralNominalSupport.reads]

theorem no_head_two (test : Test) (observation : GeneralCanonicalObservations.Observation) :
    ¬ GeneralNominalSupport.Head controlSource 2 test observation := by
  intro seen
  generalize identityEq : (2 : Nat) = identity at seen
  cases seen with
  | scalar slot base recorded =>
    have equal := identityEq.symm
    have pos : slot = (2 : Fin 5) := by
      apply Fin.ext
      change slot.val = 2
      have fresh := outputP_large
      change (if slot.val = 4 then outputP else slot.val) = 2 at equal
      split at equal <;> omega
    subst slot
    cases recorded
  | structural slot kind children recorded =>
    have equal := identityEq.symm
    have pos : slot = (2 : Fin 5) := by
      apply Fin.ext
      change slot.val = 2
      have fresh := outputP_large
      change (if slot.val = 4 then outputP else slot.val) = 2 at equal
      split at equal <;> omega
    subst slot
    cases recorded
  | nominal slot descriptor recorded => cases recorded

theorem control_not_decision : ¬ DecisionGuard registry control emittedChild.occurrence := by
  intro guard
  have visited : (2 : Fin 5) ∈ GeneralNominalSupport.readsMany controlSource
      (GeneralNominalInspection.queries controlSource interpretation r) [(1,1)] := by
    rw [control_reads]
    simp
  have ready := guard.2 r (by simp [registry]) rfl ([(1,1)] : List (Fin 5 × Fin 5)) control_arguments (2 : Fin 5) visited
  obtain ⟨test,observation,seen,_⟩ := ready
  exact no_head_two test observation seen

theorem control_smaller (first last : Fin controlSource.base.slots)
    (edge : GeneralSourceK2.Child controlSource.view first last) :
    height (controlSource.base.source last) < height (controlSource.base.source first) := by
  obtain ⟨kind,children,recorded,index,rfl⟩ := edge
  by_cases one : first = 1
  · subst first
    change GeneralNormalizedObservation.Head.structural 0 (fun _ => 2) = _ at recorded
    cases recorded
    change height 2 < height 1
    decide +kernel
  · by_cases zero : first = 0
    · subst first
      change GeneralNormalizedObservation.Head.structural 0 (fun i => if i.val = 0 then 1 else 2) = _ at recorded
      cases recorded
      by_cases atZero : index.val = 0
      · simp [height,witnessTree,atZero,GeneralNominalBranchingReadback.Tree.mass,refreshedIdentifiers]
      · simp [height,witnessTree,atZero,GeneralNominalBranchingReadback.Tree.mass,refreshedIdentifiers]
    · by_cases three : first = 3
      · subst first
        change GeneralNormalizedObservation.Head.scalar .int = _ at recorded
        cases recorded
      · have absent : controlSource.view.heads first = .deferred .unresolved := by
          simp [controlSource,controlView,refreshedView,one,zero,three]
        rw [absent] at recorded
        cases recorded

theorem control_witness : Models control witness := (identical_models witness).mpr witness_refreshed

theorem control_no_raw (slot : Fin controlSource.base.slots) :
    ¬ GeneralNominalCycleK2.Cycle controlSource slot :=
  raw_acyclic controlSource (fun _ => rfl) control_smaller slot

theorem control_no_feedback (identity : Nat) :
    ¬ GeneralNominalFeedbackK2.Cycle control.erased.current identity :=
  feedback_acyclic control.erased.current control_witness.1 control_smaller identity

theorem control_no_cyclic (origin : Origin) : ¬ Cyclic control origin := by
  rintro (⟨identity,_,cycle,_⟩|cycle)
  · exact control_no_feedback identity cycle
  · exact graph_acyclic_refreshed origin cycle

theorem control_no_root : ¬ GeneralNominalFeedbackK2.RootK2 control.erased.current emittedChild.occurrence := by
  rintro (⟨_,_,_,slot,_,cycle⟩|⟨_,_,_,cycle,_⟩)
  · exact control_no_raw slot (GeneralNominalCycleK2.recurs_cycle _ _ cycle)
  · exact control_no_feedback _ cycle

theorem control_no_candidate : ¬ GeneralNominalFeedbackK2.CandidateK2 registry control.erased.current emittedChild.occurrence := by
  rintro (⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩|⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩)
  · exact control_no_raw visited.1 (GeneralNominalCycleK2.recurs_cycle _ _ cycle)
  · exact control_no_feedback _ cycle

theorem control_local_pending : GeneralNominalCenteredBoundary.Local registry control emittedChild.occurrence .pending := by
  apply GeneralNominalLocalBoundary.Local.inspectionPending
  · rintro ⟨index,unknown⟩
    apply unknown
    rw [childP_arguments childSignature index]
    exact ⟨(1 : Fin 5),rfl,Or.inl (by intro impossible; cases impossible)⟩
  · exact Or.inr control_not_decision
  · rintro (legacy|⟨site,member,same,index,cycle⟩)
    · exact control_no_root legacy
    · exact control_no_cyclic _ cycle
  · rintro (legacy|⟨plan,member,same,reg,ctx,visible,role,ready,located,entry,present,cycle⟩)
    · exact control_no_candidate legacy
    · exact control_no_cyclic _ cycle

theorem refreshed_local_selected : GeneralNominalCenteredBoundary.Local registry refreshed emittedChild.occurrence
    (.selected r.id packetR.children) :=
  GeneralNominalCenteredBoundary.installable_selected ⟨enabledR,[],guardR⟩

theorem decisive_local_change :
    GeneralNominalCenteredBoundary.Local registry control emittedChild.occurrence .pending ∧
      GeneralNominalCenteredBoundary.Local registry refreshed emittedChild.occurrence (.selected r.id packetR.children) ∧
      Step registry root refreshed afterR :=
  ⟨control_local_pending,refreshed_local_selected,stepR⟩

theorem control_observations_source_supported
    (seen : GeneralNominalSupport.Head controlSource identity test observation)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models source model) :
    observation.Holds model := by
  cases seen with
  | scalar slot scalar recorded =>
    by_cases one : slot = 1
    · subst slot; cases recorded
    · by_cases zero : slot = 0
      · subst slot; cases recorded
      · by_cases three : slot = 3
        · subst slot
          change GeneralNormalizedObservation.Head.scalar .int = _ at recorded
          cases recorded
          exact GeneralNominalCenteredSourceUnsettledRefreshControl.int_sound model valid
        · simp [controlSource,controlView,refreshedView,one,zero,three] at recorded
  | structural slot kind children recorded =>
    by_cases one : slot = 1
    · subst slot
      change GeneralNormalizedObservation.Head.structural 0 (fun _ => 2) = _ at recorded
      cases recorded
      exact GeneralNominalState.normalized_models source model valid (1 : Fin 4)
        (.pair (.var 2) (.var 2)) rfl
    · by_cases zero : slot = 0
      · subst slot
        change GeneralNormalizedObservation.Head.structural 0 (fun i => if i.val = 0 then 1 else 2) = _ at recorded
        cases recorded
        exact GeneralNominalState.normalized_models source model valid (0 : Fin 4)
          (.pair (.var 1) (.var 2)) rfl
      · by_cases three : slot = 3
        · subst slot; cases recorded
        · simp [controlSource,controlView,refreshedView,one,zero,three] at recorded
  | nominal slot descriptor recorded => cases recorded

theorem control_snapshot_supported :
    GeneralNominalCenteredSourceSnapshotLedger.SnapshotReadbacks control [] := by
  intro identity test observation seen model valid
  exact control_observations_source_supported seen model valid.1

theorem only_parent_view_changes (slot : Fin 5) (other : slot ≠ 1) :
    controlSource.view.heads slot = refreshedSource.view.heads slot := by
  simp only [controlSource,controlView,other,ite_false]

theorem same_base_and_ordinary :
    controlSource.base = refreshedSource.base ∧ controlSource.ordinary = refreshedSource.ordinary ∧
      control.erased.facts = refreshed.erased.facts ∧ control.sites = refreshed.sites ∧ control.plans = refreshed.plans :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem no_control_install {plan : Plan roles} {support}
    (focus : plan.packet.site.occurrence = emittedChild.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry control.erased.current plan.packet)
    (guard : PacketGuard control plan support) : False := by
  have selected := GeneralNominalCenteredBoundary.installable_selected ⟨enabled,support,guard⟩
  rw [focus] at selected
  have same := GeneralNominalCenteredBoundary.local_functional control_local_pending selected
  cases same

theorem unknown_input : ¬ GeneralNominalState.Known source 2 := by
  rintro ⟨slot,equal,known⟩
  have same : slot = (2 : Fin 4) := Fin.ext equal
  subst slot
  rcases known with impossible | ⟨descriptor,recorded⟩
  · exact impossible rfl
  · cases recorded

theorem decisive_unsettled_refresh :
    Checked registry ∧ GeneralNominalSourceFormation.InitialSource registry context root ∧
      GeneralNominalActualBudget.PointSource context root ∧ ¬ GeneralNominalState.Known source 2 ∧
      Step registry root afterP control ∧ Step registry root afterP refreshed ∧
      B4Target.Steps (Step registry root) initialState control ∧
      B4Target.Steps (Step registry root) initialState refreshed ∧
      (∀ model, Models control model ↔ Models refreshed model) ∧
      GeneralNominalCenteredSourceSnapshotLedger.SnapshotReadbacks control [] ∧
      ¬ GeneralNominalSettledSupport.PacketSettled afterP.erased.current packetP ∧
      ¬ GeneralNominalSettledSupport.PacketSettled refreshed.erased.current packetP ∧
      (¬ ∃ facts, GeneralNominalCenteredSupport.Trusted refreshed.erased refreshed.sourceSites refreshed.plans facts ∧
        ∀ model, GeneralNominalCenteredSupport.Models refreshed.erased refreshed.sourceSites facts model →
          (GeneralCanonicalObservations.Observation.normalized refreshedBase 1 (.pair (.var 3) (.var 3))).Holds model) ∧
      GeneralNominalCenteredBoundary.Local registry control emittedChild.occurrence .pending ∧
      GeneralNominalCenteredBoundary.Local registry refreshed emittedChild.occurrence (.selected r.id packetR.children) ∧
      Step registry root refreshed afterR :=
  ⟨checked,initial_source,point,unknown_input,controlStep,refreshStep,control_reachable,refreshed_reachable,
    identical_models,control_snapshot_supported,no_settled_afterP packetP,no_settled_packet packetP,no_trusted_redirected_head,control_local_pending,refreshed_local_selected,stepR⟩

end Yulang.GeneralNominalCenteredSourceUnsettledRefreshDecision
