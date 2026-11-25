import Yulang.GeneralDeclarativeI65I74ClosedResidualFidelity415

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ClosedResidual415
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern normalize)
open Checker408 (Problem Result)
open RecordK2412 (closedHead412)

structure ShallowRecord (s : I72.State) (q : I72.Request) where
  decl : Declaration
  only : visible s.core q = [decl]
  head : ∃ l p t, decl.head = [.record l p t]
  notNested : ∀ box tick empty binder, decl.head ≠ [closedHead412 box tick empty binder]

private theorem record_head415 {s q} (a : ShallowRecord s q)
    (d : Declaration) (h : d ∈ visible s.core q) :
    ∃ l p t, d.head = [.record l p t] := by
  rw [a.only] at h
  cases List.mem_singleton.mp h
  exact a.head

def ClosedParent.shallow {s q} {a : ClosedRows s q} (p : ClosedParent a) : ShallowRecord s q :=
  ⟨p.candidate.decl,p.candidate.visibleOne,⟨_,_,_,p.literal⟩,fun _ _ _ _ h => by
     have contra := List.cons.inj (p.literal.symm.trans h)
     simp [OpenTail414.openHead,closedHead412] at contra⟩

def ClosedChild.shallow {s q} {a : ClosedRows s q} {p : ClosedParent a}
    (c : ClosedChild p) : ShallowRecord s (query415 q p.childRole a.residual) :=
  ⟨c.candidate.decl,c.candidate.visibleOne,⟨_,_,_,c.literal⟩,fun _ _ _ _ h => by
     have contra := List.cons.inj (c.literal.symm.trans h)
     simp [childHead415,closedHead412] at contra⟩

private theorem any_record_rules_out_all_var415 {s q} (shape : ShallowRecord s q)
    (assumed : (d : Declaration) → d ∈ visible s.core q → RepeatedRow403 q d) : False := by
  let d := shape.decl
  have member : d ∈ visible s.core q := by simp [shape.only,d]
  obtain ⟨label,p,tail,h⟩ := record_head415 shape d member
  have visiblePattern : Pattern.record label p tail ∈ d.head := by simp [h]
  rw [(assumed d member).literal] at visiblePattern
  obtain ⟨_,_,bad⟩ := List.mem_map.mp visiblePattern
  cases bad

private theorem no_app_from_record415 {s q} (scan : ShallowRecord s q)
    {d : Declaration} (seen : d ∈ visible s.core q)
    {p : Pattern} (written : d.head = [p]) {k args}
    (normal : normalize p = .app k args) : False := by
  obtain ⟨label,payload,tail,head⟩ := record_head415 scan d seen
  have same := (List.cons.inj (written.symm.trans head)).1
  rw [same] at normal
  change Pattern.record label _ _ = Pattern.app k args at normal
  cases normal

private theorem no_repeated_other415 {s q v} (shape : ShallowRecord s q)
    (old : RepeatedOther403 s q v) : False := by
  cases old with
  | ambiguous scope _ =>
    obtain ⟨s⟩ := scope
    exact any_record_rules_out_all_var415 shape s.allVisible

private theorem no_native_other415 {s q v needs} (shape : ShallowRecord s q)
    (old : variableWithNativeK2403.other s q v needs) : False := by
  rcases old.2 with repeatCase|⟨_,_,opened,_⟩
  · exact no_repeated_other415 shape repeatCase
  · exact no_app_from_record415 shape opened.visibleRow opened.exactHead opened.dispatch

private theorem no_completed_native_other415 {s q v needs} (shape : ShallowRecord s q)
    (old : completedNativePrioritySource404.other s q v needs) : False := by
  rcases old with earlier|⟨_,⟨opened⟩⟩
  · exact no_native_other415 shape earlier
  · exact no_app_from_record415 shape opened.entry.visibleRow opened.entry.exactHead opened.entry.dispatch

private theorem no_completed_choice_other415 {s q v needs} (shape : ShallowRecord s q)
    (old : completedChoiceSource404.other s q v needs) : False := by
  rcases old with earlier|⟨_,⟨scope⟩⟩
  · exact no_completed_native_other415 shape earlier
  · exact any_record_rules_out_all_var415 shape scope.allVisible

theorem no_R4_diagnostic_on_shallow_record415 {s q v needs} (shape : ShallowRecord s q) :
    ¬RecordK2412.R4.other s q v needs := by
  rintro (⟨_,family,old⟩|⟨_,_,⟨one⟩⟩)
  · cases family with
    | variableOnly =>
      cases old.2 with
      | ambiguous scope _ =>
        obtain ⟨someScope⟩ := scope
        let d := shape.decl
        have member : d ∈ visible s.core q := by simp [shape.only,d]
        obtain ⟨l,p,t,head⟩ := record_head415 shape d member
        have literal : Pattern.record l p t ∈ d.head := by simp [head]
        let mine := someScope.allVisible d member
        rw [mine.literal] at literal
        obtain ⟨_,_,absurd⟩ := List.mem_map.mp literal
        cases absurd
    | repeated | whereTree => exact no_repeated_other415 shape old.2
    | nativeK2 | supported => exact no_native_other415 shape old
    | supportedK2 => exact no_completed_native_other415 shape old
    | supportedAmbiguity | authoredNative => exact no_completed_choice_other415 shape old
  · have oneDecl : one.decl ∈ visible s.core q := by simp [one.field.only]
    have eq : one.decl = shape.decl := by
      simpa [shape.only] using oneDecl
    exact shape.notNested _ _ _ _ ((congrArg Declaration.head eq).symm.trans one.field.head)

theorem no_R4_election_on_shallow_record415 {s q needs} (shape : ShallowRecord s q)
    (e : Event s q) : ¬RecordK2412.R4.elected s q e needs := by
  obtain ⟨label,payload,tail,head⟩ := record_head415 shape e.frame.decl e.frame.inScope
  have written : Pattern.record label payload tail ∈ e.frame.decl.head := by simp [head]
  rintro (((legacy|named)|leaf)|whereList)
  · rcases R0_selection_uses_independent_original_rule407 e legacy with plain|native
    · obtain ⟨_,bad,_⟩ := plain.2 e.frame.decl e.frame.inScope _ written
      cases bad
    · obtain ⟨source⟩ := native
      have bad := (List.cons.inj (source.test.writtenHead.symm.trans head)).1
      cases bad
  · obtain ⟨_,⟨name⟩⟩ := named
    exact no_app_from_record415 shape e.frame.inScope name.test.named rfl
  · obtain ⟨_,⟨list⟩⟩ := leaf
    exact no_app_from_record415 shape e.frame.inScope list.test.named rfl
  · obtain ⟨_,⟨list⟩⟩ := whereList
    exact no_app_from_record415 shape e.frame.inScope list.test.named rfl

theorem no_R5_diagnostic_on_shallow_record415 {s q v needs} (a : ShallowRecord s q) :
    ¬ MixedRecord413.R5.other s q v needs := by
  rintro (old|fresh)
  · exact no_R4_diagnostic_on_shallow_record415 a old
  · obtain ⟨_,_,⟨data⟩⟩ := fresh
    have h := data.rivalsExist
    simp [a.only] at h


theorem no_prior_parent_diagnostic415 {s q v needs} {a : ClosedRows s q} (p : ClosedParent a) :
    ¬ OpenTail414.R6.other s q v needs := by
  rintro (old|openRule)
  · exact no_R5_diagnostic_on_shallow_record415 p.shallow old
  · obtain ⟨_,_,⟨prior⟩⟩ := openRule
    have whole := a.whole
    rw [prior.input.exactRows] at whole
    simp [wholeExpr,residualExpr,OpenTail414.openRow,OpenTail414.intRow] at whole

theorem no_prior_child_diagnostic415 {s q v} {a : ClosedRows s q} {p : ClosedParent a}
    (c : ClosedChild p) {needs} :
    ¬ OpenTail414.R6.other s (query415 q p.childRole a.residual) v needs := by
  rintro (old|openRule)
  · exact no_R5_diagnostic_on_shallow_record415 c.shallow old
  · obtain ⟨_,_,⟨prior⟩⟩ := openRule
    have same := (List.cons.inj (c.candidate.visibleOne.symm.trans prior.candidate.exactVisible)).1
    have h := c.literal.symm.trans ((congrArg Declaration.head same).trans prior.candidate.head)
    simp [childHead415,OpenTail414.openHead] at h

theorem closed_parent_branch_preserves_previous_disjointness415 (p : Problem)
    (report prior : Result) (w : ClosedWire) (v : OpenTail414.Witness)
    (yes : check p report (.closedRows w) = true) :
    check p prior (.previous v) = false := by
  obtain ⟨now,_,_⟩ := checked_closed_rows_reflect_original415 p report w yes
  cases old : OpenTail414.check p prior v with
  | false => exact old
  | true =>
    exfalso
    obtain ⟨e,t,_,_⟩ := (OpenTail414.check_sound p prior v old).1
    generalize prior.tree = tree at t
    cases t with
    | rootK2 cyclic => exact now.rootSafe cyclic
    | other _ _ decision _ => exact no_prior_parent_diagnostic415 now.parent decision
    | selected ev _ decision _ _ => exact no_R4_election_on_shallow_record415 now.parent.shallow ev decision

end Yulang.GeneralDeclarativeI65.I72.ClosedResidual415
