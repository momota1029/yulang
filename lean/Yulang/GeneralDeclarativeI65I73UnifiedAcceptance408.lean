import Yulang.GeneralDeclarativeI65I73UnifiedReport408

namespace Yulang.GeneralDeclarativeI65.I72.Check408
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open CommonRoleOutermostResolver (Tree Summarizes)
open GeneralDeclarativeWitnessTree349 (eq_tree eq_result)

theorem matchesNoWrites_exact408 {r : Result} {t : Tree} {v : CommonRoleOutermostResolver.Result} :
    matchesNoWrites r t v = true ↔ r.tree = t ∧ r.verdict = v ∧ r.writes = [] := by
  simp [matchesNoWrites,Bool.and_eq_true,eq_tree,eq_result,and_assoc]

theorem retained_nullary_trace408 (p : Problem) (d : Declaration)
    (whole : visible p.state.core p.root = [d]) (okay : checksNullary p d = true) :
    ∃ e : Event p.state p.root,
      ∃ trace : SourceTrace R0 p.state p.root (.selected d.id []) (some e), traceWrites trace = [] := by
  simp only [checksNullary,Bool.and_eq_true,List.isEmpty_iff] at okay
  obtain ⟨⟨⟨⟨⟨⟨⟨validRoles,covers⟩,checkRegistry⟩,declCoverage⟩,nullaryHead⟩,noWhere⟩,noArgs⟩,noOutputs⟩ := okay
  have checked := GeneralDeclarativeWitnessHeader349.registry_checked
    ((GeneralDeclarativeWitnessProblem349.covered_iff
      ((GeneralSourceMetadataRoles291.check_exact _).mp validRoles)).mp covers) checkRegistry
  have covered := (GeneralDeclarativeWitnessModeCoverage357.declaration_exact _ _).mp declCoverage
  have safe : ¬ RootCycle p.state p.root := by simp [RootCycle,noArgs]
  let scope : VariableScope403 p.state p.root :=
    ⟨by intro a atArg; simp [noArgs] at atArg,checked,fun row atRow => by
        rw [whole] at atRow
        cases List.mem_singleton.mp atRow
        exact covered,
      fun row atRow => by
        rw [whole] at atRow
        cases List.mem_singleton.mp atRow
        exact ⟨[],nullaryHead,List.nodup_nil,by simp [noArgs],noWhere⟩⟩
  have noIndex : ∀ i : Fin p.root.demand.outputs.length, False := by
    intro i
    have tooFew := i.isLt
    simp [noOutputs] at tooFew
  obtain ⟨event,⟨read⟩,row,kids,_⟩ := elected_source_reads_original_B6403 scope safe whole
    (fun i => (noIndex i).elim) (fun _ i => (noIndex i).elim)
  have empty : WhereForest R0 p.state event.kids [] := kids ▸ .nil
  have chosen : R0.elected p.state p.root event [] :=
    ⟨variableSource403,.variableOnly,⟨rfl,⟨read⟩,fun i => (noIndex i).elim⟩⟩
  let natural : SourceTrace R0 p.state p.root (.selected event.frame.decl.id []) (some event) :=
    .selected event safe chosen .nil empty
  have matchTree : Tree.selected event.frame.decl.id [] = .selected d.id [] := by rw [row]
  let trace : SourceTrace R0 p.state p.root (.selected d.id []) (some event) := matchTree ▸ natural
  have nil : traceWrites natural = [] := by
    have emptyWrites : encodedEventWrites event = [] := List.length_eq_zero_iff.mp (by simp [encodedEventWrites,noOutputs])
    change encodedEventWrites event ++ forestWrites empty = []
    rw [empty_diag_forest_has_no_writes408 empty,emptyWrites]
    rfl
  have sameWrites : traceWrites trace = traceWrites natural := trace_writes_keep_tree_transport408 matchTree natural
  exact ⟨event,trace,sameWrites.trans nil⟩

theorem check_reflects_same_original_report408 (p : Problem) (r : Result) (w : Witness)
    (accepted : check p r w = true) :
    ClassifiedAs p.state p.root r := by
  cases r with
  | mk printed verdict writes =>
    cases w with
    | unsupported => simp [check] at accepted
    | rawRoot witness =>
      obtain ⟨valid,matchOut⟩ := GeneralDeclarativeWitnessProblem349.splitAnd accepted
      obtain ⟨rfl,rfl,rfl⟩ := matchesNoWrites_exact408.mp matchOut
      have raw : RootCycle p.state p.root := GeneralDeclarativeWitnessCycle350.rooted valid
      exact ⟨none,.rootK2 raw,.rejected,rfl⟩
    | nullary =>
      simp only [check] at accepted
      split at accepted
      · rename_i declared chosen
        obtain ⟨valid,matchOut⟩ := GeneralDeclarativeWitnessProblem349.splitAnd accepted
        obtain ⟨rfl,rfl,rfl⟩ := matchesNoWrites_exact408.mp matchOut
        obtain ⟨e,trace,noWrites⟩ := retained_nullary_trace408 p declared chosen valid
        exact ⟨some e,trace,.selected .nil (.selected rfl),noWrites.symm⟩
      · simp at accepted

end Yulang.GeneralDeclarativeI65.I72.Check408
