import Yulang.GeneralWhereVersionRootRegistry317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 34000
set_option maxHeartbeats 49000000
namespace Yulang.GeneralWhereVersionRootSelect317
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralLiveCompoundRegistry316 (registry declaration)
open GeneralWhereVersionSnapshot317 (snap context zero nextDesc)
open GeneralWhereVersionCase317 (occ)
open GeneralWhereVersionCommit317 (core framedState compiled_models)
open GeneralWhereVersionWitness317 (ParentHolds inhabited)
open GeneralWhereVersionRootReport317 (packet plan query exact_report location same)
open GeneralWhereVersionRootRegistry317 (administrative unique_frame found_center ready classes)
open GeneralWhereVersionRootHead317 (known prepared frame schema_hold unique)
open GeneralWhereVersionRootSafety317 (no_semantic no_raw)
open GeneralLiveCompoundChildSite316 (child)
open GeneralNominalVersionedDiagnostic232 (boundary HeadEquations)
open GeneralNominalVersionedCandidates231 (inputs)
open GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)

theorem current_tests :
    (GeneralNominalCenteredSteps.inspection plan).tests = [(.source 0,.nominal 0 2)] := by
  unfold GeneralNominalCenteredSteps.inspection
  rw [query]
  have atZero : snap.nominals zero = some nextDesc := rfl
  have args : typeArguments nextDesc.arguments =
    some [(GeneralWhereVersionBase317.two,GeneralWhereVersionBase317.two),
      (GeneralWhereVersionBase317.two,GeneralWhereVersionBase317.two)] := rfl
  have tag : nextDesc.declaration.name = 0 := rfl
  have obs : (GeneralNominalCenters.rootSite 4 root).observed.inputs[0]?.join = some (.source 0) := rfl
  have sub (origins : Nat → Option Origin) :
      (inspectMany snap [.variables [0],.variables [0]]
        [(GeneralWhereVersionBase317.two,GeneralWhereVersionBase317.two),
          (GeneralWhereVersionBase317.two,GeneralWhereVersionBase317.two)] origins 0).tests = [] := by
    simp [inspectMany,inspect,Report.append]
  simp [inspectMany,inspect,Report.append,Report.visit,atZero,args,tag,obs,sub]

theorem safe (m : Assignment) (valid : ParentHolds m) :
    B4TargetV8.SafeKnown (boundary roles) registry framedState root := by
  refine ⟨known,?_,?_,?_⟩
  · rintro (bad | (⟨i,cycle⟩ | ⟨site,present,atRoot,i,cycle⟩))
    · obtain ⟨_,_,i,slot,atSource,cycle⟩ := bad
      change GeneralWhereVersionBase317.source slot = 0 at atSource
      have zeroSource : GeneralWhereVersionBase317.source zero = 0 := by
        rw [GeneralWhereVersionBase317.source_old]; rfl
      have sameSlot := GeneralWhereVersionBase317.injective (atSource.trans zeroSource.symm)
      subst slot
      exact no_raw m valid cycle
    · exact no_semantic m valid cycle
    · cases found_center present atRoot
      exact no_semantic m valid cycle
  · rintro (bad | ⟨p,framed,entry,member,cycle⟩)
    · obtain ⟨_,d,visible,_,atRole,_,bounds,found,visited,hit,cycle⟩ := bad
      rcases List.mem_cons.mp visible with first|rest
      · subst d
        have equal : bounds = [(zero,zero)] := Option.some.inj (found.symm.trans location)
        subst bounds
        change visited ∈ (GeneralNominalRecursiveCandidates.report context declaration [(zero,zero)]).inspected at hit
        rw [exact_report] at hit
        cases List.mem_singleton.mp hit
        exact no_raw m valid cycle
      · cases List.mem_singleton.mp rest; cases atRole
    · have equal := unique_frame framed
      subst p
      rw [current_tests] at member
      cases List.mem_singleton.mp member
      exact no_semantic m valid cycle
  · rintro (⟨_,d,visible,atRole,_,bad⟩ | pending)
    · rcases List.mem_cons.mp visible with first|rest
      · subst d; exact bad (prepared m valid)
      · cases List.mem_singleton.mp rest; cases atRole
    · exact pending administrative

theorem head_equations (m : Assignment) (valid : ParentHolds m) : HeadEquations plan m := by
  have prior := GeneralWhereVersionSemantics317.full m valid
  refine ⟨prior.input,?_,schema_hold m valid⟩
  intro name member
  rw [← GeneralDeferredLadderTransport302.capture_eq same, ← GeneralDeferredLadderTransport302.binder_eq same]
  exact prior.captures name (.inl member)

theorem reselected :
    GeneralNominalVersionedDiagnostic232.Local registry framedState root (.selected declaration.id [child]) := by
  obtain ⟨m,valid⟩ := inhabited
  have live := compiled_models m valid
  have u := unique m valid
  refine .ordinary ?_ (.ordinary ?_ (.selected (safe m valid) u ?_))
  · rintro ⟨key,kids,picked,_,blocked⟩
    have eq := (u.2 key kids picked.1).1
    subst key
    exact blocked.2.2 ⟨m,live,plan,frame m valid,GeneralNominalVersionedHeadSharing232.schema_holds plan m (schema_hold m valid)⟩
  · exact GeneralNominalVersionedMergedConflict232.models_exclude_conflict live
      (fun focus _ => GeneralWhereVersionLeafRegistry317.equal_outputs m focus)
      (GeneralWhereVersionLeafRegistry317.equal_outputs m root)
  · intro conflict
    exact conflict.2 ⟨m,live,⟨⟨_,u⟩,plan,frame m valid,ready,head_equations m valid,classes m valid⟩⟩

theorem root_and_leaf_on_reobservation :
    GeneralNominalVersionedDiagnostic232.Local registry framedState root (.selected declaration.id [child]) ∧
    GeneralWhereVersionCompiler317.children plan = [occ] ∧
    GeneralNominalVersionedDiagnostic232.Local registry framedState occ
      (.selected GeneralLiveCompoundRegistry316.leaf.id []) :=
  ⟨reselected,GeneralWhereVersionRecompile317.actual_after_observation.1,GeneralWhereVersionLeafSelect317.selected⟩

end Yulang.GeneralWhereVersionRootSelect317
