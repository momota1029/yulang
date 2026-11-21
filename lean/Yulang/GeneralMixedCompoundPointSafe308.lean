import Yulang.GeneralMixedCompoundPointAdmin308
import Yulang.GeneralRebaseTreeAcyclic272

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 23000
set_option maxHeartbeats 15000000
namespace Yulang.GeneralMixedCompoundPointSafe308
open GeneralDictionaryJournalRefinement228Source (roles root root_fixed snapshot)
open GeneralDictionaryCompoundSource238 (registry declaration checked)
open GeneralMixedCompoundPointFirstPlan308 (candidateModel)
open GeneralMixedCompoundPointView308 (snap context)
open GeneralMixedCompoundPointViewTrust308 (observed)
open GeneralMixedCompoundPointSites308 (centers)
open GeneralMixedCompoundPointRoot308 (plan packet located frame_plan models_observed prepared report_exact)
open GeneralMixedCompoundPointAdmin308 (root_ready)
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
    GeneralNominalFiniteMeaning.At candidateModel .actual (.source 0) (value nominalTree) :=
  GeneralRebaseInstalledReadback271.source_at _ _ _
    (root_fixed _ models_observed.1.2.1)

theorem no_semantic : ¬ Cyclic observed (.source 0) :=
  GeneralRebaseTreeAcyclic272.acyclic _ _ models_observed _ _ canonical model_origin

private theorem no_raw_incoming (slot : Fin 8) :
    ¬ GeneralNominalMixedRecurrence.Edge snap slot (0 : Fin 8) := by
  rintro (structural | nominal)
  · obtain ⟨kind,children,recorded,index,atChild⟩ := structural
    change GeneralMixedCompoundPointViewBase308.viewHeads slot = _ at recorded
    unfold GeneralMixedCompoundPointViewBase308.viewHeads at recorded
    split at recorded
    · cases recorded; exact Fin.elim0 index
    · split at recorded
      · cases recorded; cases atChild
      · split at recorded
        · cases recorded; cases atChild
        · cases recorded
  · obtain ⟨d,saved,i,actual,seen,equal⟩ :=
      GeneralNominalMixedRecurrence.actual_edge_sound snap _ _ nominal candidateModel models_observed.1.1
    have first : slot = 0 ∨ slot = 1 := by
      change (if slot = 0 ∨ slot = 1 then some GeneralMixedCompoundUpperSnapshot307.desc else none) = some d at saved
      split at saved
      · assumption
      · cases saved
    have canonicalValue := root_fixed candidateModel models_observed.1.2.1
    have parent : Equivalent (candidateModel (snap.base.source slot)).1 GeneralDictionaryJournalRefinement228Source.foo := by
      rcases first with rfl|rfl
      · exact canonicalValue
      · have aliased := GeneralDictionaryJournalRefinement228Source.alias_zero candidateModel models_observed.1.2.1
        exact GeneralDictionaryDefaultExpression209.equivalent_trans ⟨aliased.2,aliased.1⟩ canonicalValue
    have v := GeneralNominalRecursiveInspection.embed_observation candidateModel _ actual seen
    cases v with
    | nominal observed eq valid =>
      cases observed
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
  rw [GeneralMixedCompoundPointRoot308.query]
  simp [GeneralNominalRecursiveInspection.inspectMany,GeneralNominalRecursiveInspection.inspect,
    GeneralNominalRecursiveInspection.Report.append,GeneralNominalRecursiveInspection.Report.visit,args,tag,obs,sub]

theorem known : ¬ GeneralNominalState.RootPending snap (inputs root).demand := by
  rintro ⟨i,h⟩
  have zero : i = 0 := Fin.ext (by exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (show i.val < 1 from i.isLt)))
  subst i
  exact h ⟨0,rfl,Or.inr ⟨_,rfl⟩⟩

theorem source_at_zero (slot : Fin 8) (h : snap.base.source slot = 0) : slot = 0 :=
  GeneralMixedCompoundPointViewBase308.injective (h.trans (show snap.base.source 0 = 0 from rfl).symm)

theorem safe : B4TargetV8.SafeKnown (boundary roles) registry observed root := by
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
    · exact pending root_ready

theorem survivor : Survivor registry context root declaration.id (GeneralNominalVersionedFrame231.children packet) :=
  ⟨known,declaration,List.mem_singleton_self _,GeneralDictionaryCompoundSource238.declaration_checked,
    rfl,rfl,[(0,0)],located,prepared,rfl⟩

theorem unique : Unique registry context root declaration.id (GeneralNominalVersionedFrame231.children packet) := by
  refine ⟨survivor,?_⟩
  intro key kids other
  have copy := other
  obtain ⟨_,d,visible,_,eq,_⟩ := copy
  cases List.mem_singleton.mp visible
  subst key
  exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional checked other survivor⟩

end Yulang.GeneralMixedCompoundPointSafe308
