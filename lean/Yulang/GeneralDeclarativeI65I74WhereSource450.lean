import Yulang.GeneralDeclarativeI65I74WhereParent450
import Yulang.GeneralDeclarativeI65GuardedWhereCenter400
import Yulang.GeneralDeclarativeI65I74ListFrameEntry449

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereSites450
open Yulang.GeneralDeclarativeI65
open GeneralDeclarations (Declaration Clause)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWitnessDeclaredState357 (point)
open Checker408 (Problem)
open ListSites449.Frame (FramedSelection selectedFrameEvent listFrameRule)
open CommonRoleOutermostResolver (Tree)

structure ParentSelection (p : Problem) where
  decl : Declaration
  chosen : ParentChoice p decl

def ParentSelection.event {p : Problem} (a : ParentSelection p)
    (source : SelectedHeadOrigin395 (row := a.decl) a.chosen.tape) : Event p.state p.root :=
  ⟨preoutputFrameOfOrigin399 source unusedPlacement403 (fun _ => emptyCapture403),
    source.pick.head, fun i => (by
      have absent := i.isLt
      simp [a.chosen.noOutputs] at absent : False).elim⟩

def literalDemand (capture : Nat → Capture) (c : Clause) : Demand :=
  match c.arguments with
  | [.var binder] => ⟨c.role,[capture binder],[]⟩
  | _ => ⟨c.role,[],[]⟩

def ParentSelection.children {p : Problem} (a : ParentSelection p) : List I72.Request :=
  GeneralDeclarativeI65.children p.root
    (a.decl.requirements.map (literalDemand a.chosen.roster.capture))

/-- The occurrence and role come from the literal clause, not the wire. -/
theorem actual_child_at_original_clause450 {p : Problem} (a : ParentSelection p)
    {i : Nat} {c : Clause} (atClause : a.decl.requirements[i]? = some c) :
    a.children[i]? =
      some ⟨p.root.occurrence ++ [i],literalDemand a.chosen.roster.capture c⟩ := by
  unfold ParentSelection.children GeneralDeclarativeI65.children
  rw [List.getElem?_map,List.getElem?_zipIdx,List.getElem?_map,atClause]
  simp

theorem picked_parent_is_original450 {p : Problem} (a : ParentSelection p)
    (source : SelectedHeadOrigin395 (row := a.decl) a.chosen.tape) :
    source.pick = a.chosen.candidate := by
  have shape : ∀ rows (xs : rows = [a.decl]),
      let t : CandidateTape p.state.core p.root rows := xs.symm ▸ .next (.matched a.chosen.candidate) .nil
      storedCandidateEntries401 t = [(0,⟨a.decl,a.chosen.candidate⟩)] := by
    intro rows xs
    cases xs
    rfl
  have atSource := original_stored_entry_is_listed401 source.stored
  change (source.visibleOrdinal,⟨a.decl,source.pick⟩) ∈ storedCandidateEntries401 a.chosen.tape at atSource
  unfold ParentChoice.tape at atSource
  rw [shape _ a.chosen.only] at atSource
  exact eq_of_heq (Sigma.mk.inj (congrArg Prod.snd (List.mem_singleton.mp atSource))).2

theorem literal_parent_reconstructs_all_original_children450 {p} (a : ParentSelection p)
    (source : SelectedHeadOrigin395 (row := a.decl) a.chosen.tape) :
    (a.event source).kids = a.children := by
  let e := a.event source
  have inputEq : e.frame.input = a.chosen.roster.capture := by
    change preoutputInputOfHead399 source.pick.head (fun _ => emptyCapture403) = _
    rw [picked_parent_is_original450 a source]
    rfl
  have clauses : ∀ c ∈ a.decl.requirements,
      (e.frame.whereFor c).demand = literalDemand a.chosen.roster.capture c := by
    intro c atDecl
    obtain ⟨b,args,noOut⟩ := a.chosen.literal c atDecl
    have out := literal_variable_where_uses_actual_names403 e.frame
      (binders := [b]) (by simpa using args) noOut
    have used : b ∈ a.decl.inputNames :=
      a.chosen.checked.scope.1 c atDecl _ (by simp [args,
        GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
        GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.Pattern.variables])
    have writes : e.frame.names.input b = e.frame.input b :=
      GeneralDeclarativeProducedNames325.exact_input a.chosen.checked used
    simpa [literalDemand,args,writes,inputEq] using out
  change frameWhereKids400 e.frame = a.children
  unfold frameWhereKids400 AuthoredBodyFrame393.clauses ParentSelection.children
  rw [List.map_map]
  congr 1
  exact List.map_congr_left clauses

def parentWhereRule450 : SourcePrimitives where
  elected := fun s q e needs => needs = [] ∧
    ((∃ a : ParentSelection ⟨s,q⟩,
      ∃ source : SelectedHeadOrigin395 (row := a.decl) a.chosen.tape, e = a.event source) ∨
      listFrameRule.elected s q e needs)
  other := fun _ _ _ _ => False

theorem parent_where_local_evidence450 : LocalEvidence407 parentWhereRule450 := by
  intro s q e needs valid
  refine valid.2.elim ?_ ?_
  · rintro ⟨a,source,rfl⟩
    refine ⟨node_from_exact_preoutput_head405 _ a.chosen.checked (fun _ => emptyCapture403) rfl,.inl ?_⟩
    intro i
    have absent := i.isLt
    have no : q.demand.outputs = [] := a.chosen.noOutputs
    simp [no] at absent
  · rintro ⟨_,a,source,rfl⟩
    refine ⟨node_from_exact_preoutput_head405 _ a.chosen.checked (fun _ => emptyCapture403) rfl,.inl ?_⟩
    intro i
    have absent := i.isLt
    have no : q.demand.outputs = [] := a.chosen.noOutputs
    simp [no] at absent

theorem dictionary_sound_parent_where450 : DictionarySound parentWhereRule450 := by
  intro s q d chosen m fit
  obtain ⟨t,e,⟨trace⟩,summary⟩ := chosen
  let nodeOf : S10 parentWhereRule450 := fun s q event needs _ localRule _ =>
    (parent_where_local_evidence450 s q event needs localRule).1
  let keep : KeepsFixedOutputs404 parentWhereRule450 := fun s q event needs localRule =>
    (parent_where_local_evidence450 s q event needs localRule).2
  obtain ⟨⟨tree⟩,shape⟩ := (lower_selected_at_exact_trace _ s (nodeOf s)).tree trace summary
  have aligned : CanonicalReplay tree tree.ledger := ⟨rfl,shape,rfl⟩
  have mTree := general_tree_meaning_from_local _ semantic_node_in_signature s q t e d trace tree m fit
  have meaning := typed_replay_keeps_same_event_meaning _ s q t e d trace tree tree.ledger m aligned mTree
  exact exact_ledger_evidence405 tree.ledger m meaning
    (fixed_targets_from_own_elected_events405 keep tree m fit)
end Yulang.GeneralDeclarativeI65.I72.WhereSites450
