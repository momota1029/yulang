import Yulang.GeneralVersionedEndpointObstructionHead315
import Yulang.GeneralMixedCompoundPointSafe308

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 23000
set_option maxHeartbeats 15000000
/-! Check the real selected, reachable root of the existing compound
obstruction, including current K2 guards and output diagnostics. -/
namespace Yulang.GeneralVersionedEndpointObstructionSelect315
open GeneralDictionaryJournalRefinement228Source (roles root root_fixed snapshot)
open GeneralDictionaryCompoundSource238 (registry sourceRegistry declaration checked)
open GeneralDictionaryCompoundSites238 (childSite)
open GeneralMixedCompoundUpperRefresh307 (upperState)
open GeneralMixedCompoundUpperSnapshot307 (snap context)
open GeneralMixedCompoundUpperHalt307 (centers raw_sites stable)
open GeneralMixedCompoundUpperChild307 (reachable)
open GeneralMixedCompoundUpperRoot307 (plan packet located report_exact frame_plan)
open GeneralVersionedEndpointObstructionHead315 (valid frame prepared known unique schema head_eq)
open GeneralDictionaryCompoundPointModel238 (extended)
open GeneralNominalVersionedCandidates231 (inputs Survivor Unique)
open GeneralNominalRecursiveInspection (Origin)
open GeneralNominalVersionedDiagnostic232 (boundary)
open GeneralNominalVersionedCycles232 (Cyclic)
open GeneralRebaseFiniteTree272 (Tree Canonical value)
open CommonNominalFullCarrier

abbrev leaf : Tree := .node (.structural (.record [])) Fin.elim0
abbrev nominalTree : Tree := .node (.nominal 0 2) (fun _ => leaf)

theorem canonical : Canonical nominalTree :=
  ⟨trivial,fun _ => ⟨by exact List.Pairwise.nil,fun i => Fin.elim0 i⟩⟩

theorem model_origin :
    GeneralNominalFiniteMeaning.At extended .actual (.source 0) (value nominalTree) :=
  GeneralRebaseInstalledReadback271.source_at _ _ _
    (root_fixed _ valid.1.2.1)

theorem no_semantic : ¬ Cyclic upperState (.source 0) :=
  GeneralRebaseTreeAcyclic272.acyclic _ _ valid _ _ canonical model_origin

private theorem no_raw_incoming (slot : Fin 8) :
    ¬ GeneralNominalMixedRecurrence.Edge snap slot (0 : Fin 8) := by
  rintro (structural | nominal)
  · obtain ⟨kind,children,recorded,index,atChild⟩ := structural
    change GeneralMixedCompoundUpperBase307.viewHeads slot = _ at recorded
    unfold GeneralMixedCompoundUpperBase307.viewHeads at recorded
    split at recorded
    · cases recorded; exact Fin.elim0 index
    · split at recorded
      · cases recorded; cases atChild
      · split at recorded
        · cases recorded; cases atChild
        · cases recorded
  · obtain ⟨d,saved,i,actual,seen,equal⟩ :=
      GeneralNominalMixedRecurrence.actual_edge_sound snap _ _ nominal extended valid.1.1
    have first : slot = 0 ∨ slot = 1 := by
      change (if slot = 0 ∨ slot = 1 then some GeneralMixedCompoundUpperSnapshot307.desc else none) = some d at saved
      split at saved
      · assumption
      · cases saved
    have canonicalValue := root_fixed extended valid.1.2.1
    have parent : Equivalent (extended (snap.base.source slot)).1 GeneralDictionaryJournalRefinement228Source.foo := by
      rcases first with rfl|rfl
      · exact canonicalValue
      · have aliased := GeneralDictionaryJournalRefinement228Source.alias_zero extended valid.1.2.1
        exact GeneralDictionaryDefaultExpression209.equivalent_trans ⟨aliased.2,aliased.1⟩ canonicalValue
    have v := GeneralNominalRecursiveInspection.embed_observation extended _ actual seen
    cases v with
    | nominal upperState eq valid =>
      cases upperState
      have nom := GeneralDictionaryDefaultExpression209.equivalent_trans ⟨parent.2,parent.1⟩ eq
      obtain ⟨form,smaller,asWidth⟩ := GeneralDictionaryJournalRefinement228Cycles.nominal_child .foo nom valid
      have lower := GeneralDictionaryDefaultExpression209.equivalent_trans
        ⟨asWidth.2,asWidth.1⟩
        (GeneralDictionaryDefaultExpression209.equivalent_trans equal canonicalValue)
      have same := GeneralDictionaryJournalRefinement228Cycles.equivalent_rank form .foo lower
      omega

private theorem path_to_no_incoming {s : GeneralNominalState.State} (zero : Fin s.base.slots)
    (no : ∀ a, ¬ GeneralNominalMixedRecurrence.Edge s a zero)
    {a b : Fin s.base.slots} (path : GeneralNominalMixedRecurrence.Path s a b) : b = zero → a = zero := by
  induction path with
  | nil => exact id
  | cons edge rest ih =>
    intro isLast
    have same := ih isLast
    cases same
    exact False.elim (no _ edge)

theorem no_raw_zero : ¬ GeneralNominalCycleK2.RecursAt snap (0 : Fin 8) := by
  intro found
  obtain ⟨next,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle _ _ found
  have zero := path_to_no_incoming (0 : Fin 8) no_raw_incoming path rfl
  subst next
  exact no_raw_incoming _ edge

theorem current_tests :
    (GeneralNominalCenteredSteps.inspection plan).tests = [(.source 0,.nominal 0 2)] := by
  have args : GeneralNominalRecursiveInspection.typeArguments GeneralMixedCompoundUpperSnapshot307.desc.arguments =
      some [((2 : Fin 8),2),(2,2)] := rfl
  have tag : GeneralMixedCompoundUpperSnapshot307.desc.declaration.name = 0 := rfl
  have obs : (GeneralNominalCenters.rootSite 4 root).observed.inputs[0]?.join =
      some (.source 0) := rfl
  have sub (origins : Nat → Option Origin) :
      (GeneralNominalRecursiveInspection.inspectMany snap
        [.variables [0],.variables [0]] [(2,2),(2,2)] origins 0).tests = [] := by
    simp [GeneralNominalRecursiveInspection.inspectMany,GeneralNominalRecursiveInspection.inspect,
      GeneralNominalRecursiveInspection.Report.append]
  unfold GeneralNominalCenteredSteps.inspection
  rw [GeneralMixedCompoundUpperRoot307.query]
  simp [GeneralNominalRecursiveInspection.inspectMany,GeneralNominalRecursiveInspection.inspect,
    GeneralNominalRecursiveInspection.Report.append,GeneralNominalRecursiveInspection.Report.visit,args,tag,obs,sub]

theorem source_at_zero (slot : Fin 8) (h : snap.base.source slot = 0) : slot = 0 :=
  GeneralMixedCompoundUpperBase307.injective (h.trans (show snap.base.source 0 = 0 from rfl).symm)

theorem safe : B4TargetV8.SafeKnown (boundary roles) registry upperState root := by
  refine ⟨known,?_,?_,?_⟩
  · rintro (raw | (⟨i,cycle⟩ | ⟨site,present,atRoot,i,cycle⟩))
    · obtain ⟨_,_,i,slot,atSource,cycle⟩ := raw
      change snap.base.source slot = 0 at atSource
      cases source_at_zero slot atSource
      exact no_raw_zero cycle
    · exact no_semantic cycle
    · rw [centers] at present
      rcases List.mem_cons.mp present with rfl|rest
      · exact no_semantic cycle
      · cases List.mem_singleton.mp rest
        exact GeneralDictionaryCompoundSites238.child_not_root atRoot
  · rintro (raw | ⟨p,framed,entry,member,cycle⟩)
    · obtain ⟨_,d,visible,_,_,_,bounds,found,visited,hit,cycle⟩ := raw
      cases List.mem_singleton.mp visible
      change GeneralNominalRecursiveCandidates.arguments context (inputs root) = some bounds at found
      have same : bounds = [((0 : Fin 8),(0 : Fin 8))] := Option.some.inj (found.symm.trans located)
      subst bounds
      change visited ∈ (GeneralNominalRecursiveCandidates.report context declaration [(0,0)]).inspected at hit
      rw [report_exact] at hit
      cases List.mem_singleton.mp hit
      exact no_raw_zero cycle
    · have same := frame_plan framed
      subst p
      rw [current_tests] at member
      cases List.mem_singleton.mp member
      exact no_semantic cycle
  · rintro (⟨_,d,visible,_,_,unprepared⟩ | pending)
    · cases List.mem_singleton.mp visible
      exact unprepared prepared
    · exact pending (GeneralNominalVersionedMixedTrace235.administrative_ready reachable stable .root)


theorem request_exact (focus : GeneralSourceDictionaries.Occurrence roles)
    (output : GeneralSourceState.Output)
    (member : output ∈ GeneralNominalCenteredHeadOutputs.requests upperState.core focus) : output = ⟨0,4⟩ := by
  obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
  rw [raw_sites] at present
  rcases List.mem_cons.mp present with same | present
  · subst site; exact List.mem_singleton.mp within
  · cases List.mem_singleton.mp present
    cases within

theorem equal_outputs (focus : GeneralSourceDictionaries.Occurrence roles) :
    GeneralNominalCenteredHeadOutputs.EqualOutputs upperState.core focus extended := by
  intro first one last two _
  cases request_exact focus first one
  cases request_exact focus last two
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem class_effects : GeneralNominalVersionedEffects231.ClassEffects upperState.core root plan extended := by
  apply (GeneralNominalVersionedEffects231.class_effects_iff ..).mpr
  refine ⟨?_,equal_outputs root⟩
  intro output member body found
  cases request_exact root output member
  have same : body = .explicit ⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩ := Option.some.inj found |>.symm
  subst body
  intro equation present
  cases List.mem_singleton.mp present
  change Equivalent (extended 4).1 GeneralDictionaryOptionalOutput229.value
  rw [GeneralDictionaryCompoundPrepared238.values.output]
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem output_clear : ¬ GeneralNominalVersionedDiagnostic232.OutputConflict registry upperState root declaration.id := by
  intro h
  have ready := GeneralNominalVersionedMixedReady235.ready ⟨rfl,checked⟩ reachable frame
  exact h.2 ⟨extended,valid,⟨⟨_,unique⟩,plan,frame,ready,head_eq,class_effects⟩⟩

theorem sharing_clear : ¬ GeneralNominalVersionedDiagnostic232.SharingConflict registry upperState root := by
  rintro ⟨key,kids,picked,_,blocked⟩
  have same := (unique.2 key kids picked.1).1
  subst key
  exact blocked.2.2 ⟨extended,valid,plan,frame,
    GeneralNominalVersionedHeadSharing232.schema_holds plan extended schema⟩

theorem merged_clear : ¬ GeneralNominalVersionedMergedConflict232.MergedOutputConflict upperState root :=
  GeneralNominalVersionedMergedConflict232.models_exclude_conflict valid
    (fun focus _ => equal_outputs focus) (equal_outputs root)

theorem selected :
    GeneralNominalVersionedMixedSourceBoundary234.Local sourceRegistry upperState root
      (.selected declaration.id [childSite.occurrence]) := by
  apply GeneralNominalVersionedMixedSourceBoundary234.local_iff.mpr
  apply GeneralNominalVersionedMixedBoundary234.local_iff.mpr
  have localRule : GeneralNominalVersionedDiagnostic232.Local registry upperState root
      (.selected declaration.id (GeneralNominalVersionedFrame231.children packet)) :=
    .ordinary sharing_clear (.ordinary merged_clear (.selected safe unique output_clear))
  rw [GeneralMixedCompoundUpperOutcome307.child_history_shape] at localRule
  exact localRule

end Yulang.GeneralVersionedEndpointObstructionSelect315
