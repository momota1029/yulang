import Yulang.GeneralDeclarativeI65Tape367
import Yulang.GeneralDeclarativeI65I74StructuralWhereBodyReplay428
import «Cycle427I74StructuralWhereSameRole»

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.StructuralWhere428
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern)

private theorem written_record_at_no_app428 {d : Declaration} {label index key : Nat}
    {payload tail : Pattern} {args : List Pattern}
    (recordHead : d.head = [.record label payload tail]) :
    d.head[index]? ≠ some (.app key args) := by
  rw [recordHead]
  cases index <;> simp

theorem ordinary_singleton_record_is_not_a_RigidCandidateMiss367_428
    {s q d label payload tail}
    (recordHead : d.head = [.record label payload tail]) :
    ¬ Nonempty (RigidCandidateMiss s q d) := by
  rintro ⟨miss⟩
  exact written_record_at_no_app428 recordHead miss.exactHead

theorem ordinary_singleton_record_is_not_a_PendingCandidate367_428
    {s q d label payload tail}
    (recordHead : d.head = [.record label payload tail]) :
    ¬ Nonempty (PendingCandidate s q d) := by
  rintro ⟨waiting⟩
  obtain ⟨key,args,written⟩ := waiting.written
  exact written_record_at_no_app428 recordHead (waiting.source.trans (congrArg some written))

theorem generic_tape_does_not_represent_actual_C427_ordinary_rival428 :
    ¬ Nonempty (CandidateTape I72.StructuralWhereSameRole427.fixture.state.core
      I72.StructuralWhereSameRole427.fixture.root
      (visible I72.StructuralWhereSameRole427.fixture.state.core I72.StructuralWhereSameRole427.fixture.root)) := by
  open I72.StructuralWhereSameRole427 in
  let s := fixture.state.core
  open I72.StructuralWhereSameRole427 in
  let q := fixture.root
  change ¬ Nonempty (CandidateTape s q (visible s q))
  rintro ⟨tape⟩
  open I72.StructuralWhereSameRole427 in
  have whole : visible s q = [compoundParent,scalarBase] := by decide +kernel
  have quiet : tape.waits = false := by
    cases h : tape.waits with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨r,member,waiting⟩ := tape_waiting_origin tape h
      rw [whole] at member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl
      · exact ordinary_singleton_record_is_not_a_PendingCandidate367_428 rfl waiting
      · exact ordinary_singleton_record_is_not_a_PendingCandidate367_428 rfl waiting
  open I72.StructuralWhereSameRole427 in
  have located : scalarBase ∈ visible s q := by
    rw [whole]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  open I72.StructuralWhereSameRole427 in
  have live : scalarBase ∈ tape.live := by
    by_cases already : scalarBase ∈ tape.live
    · exact already
    · exact False.elim (ordinary_singleton_record_is_not_a_RigidCandidateMiss367_428 rfl
        (every_nonlive_unblocked_row_is_a_real_miss quiet located already))
  obtain ⟨head,_⟩ := live_readback tape _ live
  open I72.StructuralWhereSameRole427 in
  exact (StructuralWhere427.model_excludes_source_head_with_actual_opposite_payload427
    parentRival.found model same_role_original_snapshot_fits427) ⟨head.head⟩


open GeneralDeclarativeInspect321 (Visit fieldPatterns variable_has_no_visit PatternK2)
open GeneralDeclarativeGraphRows321 (observed structural)
open GeneralDeclarativeK2Alias321 (AliasCycle)

theorem literal_closed_record_variable_child_does_not_inspect_payload428
    {s : GeneralDeclarativeHead320.State} {root label binder site}
    (actual : Visit (structural s) root (.record label (.variable binder) (.primitive .emptyRecord [])) site) :
    site = root := by
  cases actual with
  | here => rfl
  | field _ _ key deep =>
    have exact := Prod.mk.inj (List.mem_singleton.mp (by simpa [fieldPatterns] using key))
    rw [exact.2] at deep
    exact False.elim (variable_has_no_visit deep)

theorem closed_structural_child_cannot_skip_any_actual_raw_visit428
    {s : GeneralDeclarativeHead320.State} {site label binder}
    (rootSafe : ¬ AliasCycle s (observed s) site) :
    ¬ PatternK2 s site (.record label (.variable binder) (.primitive .emptyRecord [])) := by
  rintro ⟨other,seen,cyclic⟩
  rw [literal_closed_record_variable_child_does_not_inspect_payload428 seen] at cyclic
  exact rootSafe cyclic

#print axioms literal_closed_record_variable_child_does_not_inspect_payload428
#print axioms closed_structural_child_cannot_skip_any_actual_raw_visit428
#print axioms ordinary_singleton_record_is_not_a_RigidCandidateMiss367_428
#print axioms ordinary_singleton_record_is_not_a_PendingCandidate367_428
#print axioms generic_tape_does_not_represent_actual_C427_ordinary_rival428
end Yulang.GeneralDeclarativeI65.StructuralWhere428
