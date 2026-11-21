import Yulang.GeneralWhereVersionLeafRegistry317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32000
set_option maxHeartbeats 44000000
namespace Yulang.GeneralWhereVersionLeafSelect317
open GeneralDictionaryJournalRefinement228Source (roles)
open GeneralLiveCompoundRegistry316 (registry leaf declaration)
open GeneralWhereVersionCase317 (site occ lower descriptor centers_preserved)
open GeneralWhereVersionBase317 (loSlot hiSlot two injective source_lo)
open GeneralWhereVersionSnapshot317 (snap context)
open GeneralWhereVersionCommit317 (core framedState compiled_models)
open GeneralWhereVersionWitness317 (ParentHolds inhabited)
open GeneralWhereVersionLeafHead317 (packet plan located query report_exact)
open GeneralWhereVersionLeafFresh317 (known prepared)
open GeneralWhereVersionLeafProof317 (ref mid holds schema)
open GeneralWhereVersionLeaf317 (frame unique)
open GeneralWhereVersionLeafSafety317 (no_lower no_center no_raw)
open GeneralWhereVersionLeafRegistry317 (administrative unique_frame found_center classes ready equal_outputs)
open GeneralNominalVersionedDiagnostic232 (boundary)
open GeneralNominalVersionedCandidates231 (inputs)
open GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)

theorem inherited :
    (GeneralNominalCenteredSteps.inspection plan).inspected = [(loSlot,hiSlot)] ∧
    (GeneralNominalCenteredSteps.inspection plan).tests = [(ref,.structural (.variant 0))] := by
  unfold GeneralNominalCenteredSteps.inspection
  rw [query]
  have sub (o : Nat → Option Origin) :
      (inspectMany snap [.variables [0]] [(two,two)] o 0).tests = [] ∧
      (inspectMany snap [.variables [0]] [(two,two)] o 0).inspected = [] := by
    rw [inspectMany.eq_2,inspectMany.eq_1]
    simp only [inspect.eq_1,Report.append]
    exact ⟨rfl,rfl⟩
  have obs : site.observed.inputs = [some ref] := by
    simp [GeneralNominalCenters.Site.observed,centers_preserved,ref]
  have one : snap.view.heads loSlot = .structural (1 : Fin 2) (fun _ => two) := rfl
  have two' : snap.view.heads hiSlot = .structural (1 : Fin 2) (fun _ => two) := rfl
  have sh : snap.view.shapes (1 : Fin 2) = .variant 0 := rfl
  simp [inspectMany,inspect,Report.append,Report.visit,obs,one,two',sh]

theorem safe_positions (m : Assignment) (valid : ParentHolds m) :
    GeneralNominalVersionedCycles232.Safe framedState plan := by
  rw [GeneralNominalVersionedCycles232.Safe,inherited.1,inherited.2]
  refine ⟨rfl,?_⟩
  intro entry member
  cases List.mem_singleton.mp member
  exact no_center m valid

theorem first_arg (i : Fin (roles occ.demand.role).arity) :
    (occ.demand.arguments i).1 = lower := by
  have z : i = 0 := Fin.ext (by
    have bound : i.val < 1 := i.isLt
    exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ bound))
  subst i
  exact congrArg Prod.fst descriptor

theorem safe (m : Assignment) (valid : ParentHolds m) :
    B4TargetV8.SafeKnown (boundary roles) registry framedState occ := by
  refine ⟨known,?_,?_,?_⟩
  · rintro (raw | (⟨i,cycle⟩ | ⟨seen,present,atChild,i,cycle⟩))
    · obtain ⟨_,_,i,slot,atSource,cycle⟩ := raw
      change GeneralWhereVersionBase317.source slot = (occ.demand.arguments i).1 at atSource
      have eq : slot = loSlot := injective ((atSource.trans (first_arg i)).trans source_lo.symm)
      subst slot
      exact no_raw m valid cycle
    · change GeneralNominalVersionedCycles232.Cyclic framedState (.source (occ.demand.arguments i).1) at cycle
      rw [first_arg] at cycle
      exact no_lower m valid cycle
    · cases found_center present atChild
      have iz : i = 0 := Fin.ext (by
        have bound : i.val < 1 := i.isLt
        exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ bound))
      subst i
      rw [centers_preserved] at cycle
      exact no_center m valid cycle
  · rintro (raw | ⟨p,framed,entry,member,cycle⟩)
    · obtain ⟨_,d,vis,_,role,_,bounds,whereAt,visited,seen,cycle⟩ := raw
      rcases List.mem_cons.mp vis with h|last
      · subst d
        have contra : (0:Nat) = 1 := role
        cases contra
      · cases List.mem_singleton.mp last
        change GeneralNominalRecursiveCandidates.arguments context (inputs occ) = some bounds at whereAt
        have exacts := Option.some.inj (located.symm.trans whereAt)
        subst bounds
        change visited ∈ (GeneralNominalRecursiveCandidates.report context leaf [(loSlot,hiSlot)]).inspected at seen
        rw [report_exact] at seen
        cases List.mem_singleton.mp seen
        exact no_raw m valid cycle
    · have same := unique_frame framed
      subst p
      exact (safe_positions m valid).2 entry member cycle
  · rintro (⟨_,d,vis,role,_,no⟩ | blocked)
    · rcases List.mem_cons.mp vis with h|last
      · subst d
        have contra : (0:Nat) = 1 := role
        cases contra
      · cases List.mem_singleton.mp last
        exact no (prepared m valid)
    · exact blocked administrative

theorem selected :
    GeneralNominalVersionedDiagnostic232.Local registry framedState occ (.selected leaf.id []) := by
  obtain ⟨m,valid⟩ := inhabited
  have live := compiled_models m valid
  have unique := unique m valid
  refine .ordinary ?_ (.ordinary ?_ (.selected (safe m valid) unique ?_))
  · rintro ⟨key,kids,picked,_,blocked⟩
    have same := (unique.2 key kids picked.1).1
    subst key
    exact blocked.2.2 ⟨m,live,plan,frame m valid,
      GeneralNominalVersionedHeadSharing232.schema_holds plan m (schema m valid)⟩
  · exact GeneralNominalVersionedMergedConflict232.models_exclude_conflict live
      (fun focus _ => equal_outputs m focus) (equal_outputs m occ)
  · intro conflict
    exact conflict.2 ⟨m,live,⟨⟨_,unique⟩,plan,frame m valid,ready,
      GeneralNominalVersionedDiagnostic232.head_equations (holds m valid),classes m⟩⟩

end Yulang.GeneralWhereVersionLeafSelect317
