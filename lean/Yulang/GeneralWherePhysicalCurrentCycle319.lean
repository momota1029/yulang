import Yulang.GeneralWherePhysicalCurrentFrame319

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 33000
set_option maxHeartbeats 32000000
namespace Yulang.GeneralWherePhysicalCurrentCycle319
open CommonNominalFullCarrier
open GeneralWherePhysicalCurrentRead319 (zero desc plan)
open GeneralWherePhysicalCurrentModel319 (root_value)
open GeneralWherePhysicalPatch319 (n prior_raw physical_raw compatible_update)
open GeneralWherePhysicalReobserve319 (updated)
open GeneralWherePhysicalPast319 (point layout)
open GeneralWherePhysicalIndex319 (old new)
open GeneralWherePhysicalView319 (head)
open GeneralWherePhysicalDeferred319 (deferred)
open GeneralWherePhysicalNominal319 (nominal_old nominal_new)
open GeneralDictionaryJournalRefinement228Reobserve (pointSnapshot exactCopy)
open GeneralDictionaryJournalRefinement228Source (foo root)
open GeneralNominalMixedRecurrence (Edge Path)
open GeneralNormalizedObservation (Head)

theorem no_struct (i j : Fin 7) : ¬ GeneralSourceK2.Child point.view i j := by
  rintro ⟨kind,children,found,index,_⟩
  revert found
  refine Fin.addCases (m := 5) (n := 2) (fun i found => ?_) (fun i found => ?_) i
  · change Fin.addCases (motive := fun _ => Head pointSnapshot.view.shapes 7)
      (fun k => head (old 2) (pointSnapshot.view.heads k)) (deferred pointSnapshot 2) (old 2 i) = _ at found
    rw [Fin.addCases_left] at found
    change head (old 2) (if i = 2 then Head.structural (shapes := pointSnapshot.view.shapes) (0 : Fin 1) Fin.elim0 else .deferred .unresolved) = _ at found
    split at found
    · cases found
      exact Fin.elim0 index
    · cases found
  · change Fin.addCases (motive := fun _ => Head pointSnapshot.view.shapes 7)
      (fun k => head (old 2) (pointSnapshot.view.heads k)) (deferred pointSnapshot 2) (new 5 i) = _ at found
    rw [Fin.addCases_right] at found
    cases found

theorem nominal_sources {i : Fin 7} {d} (found : point.nominals i = some d) :
    point.base.source i = 0 ∨ point.base.source i = 1 := by
  revert found
  refine Fin.addCases (m := 5) (n := 2) (fun j found => ?_) (fun j found => ?_) i
  · change GeneralWherePhysicalNominal319.nominals pointSnapshot 2 (old 2 j) = _ at found
    rw [nominal_old] at found
    change (if j = 0 ∨ j = 1 then some exactCopy else none).map _ = some d at found
    split at found
    · rename_i e
      rcases e with rfl|rfl
      · exact .inl rfl
      · exact .inr rfl
    · cases found
  · change GeneralWherePhysicalNominal319.nominals pointSnapshot 2 (new 5 j) = _ at found
    rw [nominal_new] at found
    cases found

theorem no_incoming (slot : Fin 7) : ¬ Edge point slot zero := by
  rintro (structural | nominal)
  · exact no_struct _ _ structural
  · obtain ⟨d,saved,i,actual,seen,equal⟩ :=
      GeneralNominalMixedRecurrence.actual_edge_sound point _ _ nominal n physical_raw
    have fooAt : Equivalent (n (point.base.source slot)).1 foo := by
      rcases nominal_sources saved with id|id
      · rw [id]; exact root_value
      · rw [id]
        have a := GeneralDictionaryJournalRefinement228Source.alias_zero n prior_raw
        exact GeneralDictionaryDefaultExpression209.equivalent_trans ⟨a.2,a.1⟩ root_value
    have v := GeneralNominalRecursiveInspection.embed_observation n _ actual seen
    cases v with
    | nominal h eq valid =>
      cases h
      have nom := GeneralDictionaryDefaultExpression209.equivalent_trans ⟨fooAt.2,fooAt.1⟩ eq
      obtain ⟨form,smaller,asWidth⟩ := GeneralDictionaryJournalRefinement228Cycles.nominal_child .foo nom valid
      have equal' : Equivalent actual (n 0).1 := equal
      have contradiction := GeneralDictionaryDefaultExpression209.equivalent_trans
        ⟨asWidth.2,asWidth.1⟩
        (GeneralDictionaryDefaultExpression209.equivalent_trans equal' root_value)
      have same := GeneralDictionaryJournalRefinement228Cycles.equivalent_rank form .foo contradiction
      omega

private theorem path_to_zero {s : GeneralNominalState.State} (z : Fin s.base.slots)
    (no : ∀ i, ¬ Edge s i z) {a b : Fin s.base.slots} (path : Path s a b) : b = z → a = z := by
  induction path with
  | nil => exact id
  | cons edge _ ih =>
    intro isLast
    have bad := ih isLast
    cases bad
    exact False.elim (no _ edge)

theorem no_raw : ¬ GeneralNominalCycleK2.RecursAt point zero := by
  intro found
  obtain ⟨next,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle _ _ found
  exact no_incoming _ (path_to_zero zero no_incoming path rfl ▸ edge)

theorem no_semantic :
    ¬ GeneralNominalVersionedCycles232.Cyclic updated.mixed (.source 0) := by
  apply GeneralRebaseTreeAcyclic272.acyclic _ n compatible_update.1 _ _
    GeneralVersionedEndpointObstructionSelect315.canonical
  exact GeneralRebaseInstalledReadback271.source_at _ _ _ root_value

theorem current_tests :
    (GeneralNominalCenteredSteps.inspection plan).tests = [(.source 0,.nominal 0 2)] := by
  have obs : (GeneralNominalCenters.rootSite 4 root).observed.inputs[0]?.join =
      some (.source 0) := rfl
  let a := GeneralWherePhysicalPast319.two
  have args : GeneralNominalRecursiveInspection.typeArguments desc.arguments =
      some [(a,a),(a,a)] := rfl
  have tag : desc.declaration.name = 0 := rfl
  have sub (origins : Nat → Option GeneralNominalRecursiveInspection.Origin) :
      (GeneralNominalRecursiveInspection.inspectMany point [.variables [0],.variables [1]] [(a,a),(a,a)] origins 0).tests = [] := by
    simp [GeneralNominalRecursiveInspection.inspectMany,GeneralNominalRecursiveInspection.inspect,GeneralNominalRecursiveInspection.Report.append]
  unfold GeneralNominalCenteredSteps.inspection
  change (GeneralNominalRecursiveInspection.inspectMany point
    (GeneralNominalInspection.queries point GeneralDictionaryJournalRefinement228Source.interpretation GeneralWhereOriginSingleSource318.declaration)
    [(zero,zero)] (fun i => (GeneralNominalCenters.rootSite _ root).observed.inputs[i]?.join) 0).tests = _
  rw [GeneralWherePhysicalCurrentRead319.query]
  simp [GeneralNominalRecursiveInspection.inspectMany,GeneralNominalRecursiveInspection.inspect,
    GeneralNominalRecursiveInspection.Report.append,GeneralNominalRecursiveInspection.Report.visit,
    GeneralWherePhysicalCurrentRead319.nominal0,tag]
  rw [obs,args,sub]
  rfl

end Yulang.GeneralWherePhysicalCurrentCycle319
