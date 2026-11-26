import Yulang.GeneralDeclarativeI65I74CompletedLowerReplay438
import Yulang.GeneralDeclarativeI65I74PendingAssociatedEntry434

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.CompletedEntry438
open GeneralDeclarativeI65
open Checker408 (Problem Result)
open CommonRoleOutermostResolver (Tree)
open GeneralDeclarativeWitnessProblem349 (splitAnd)

/-- R18 adds the new source rule above the old acyclic fixed-goal
modules; it does not edit or reinterpret R0--R17. -/
def R18 := Classifies18 PendingAssociated434.R17

theorem dictionary_sound_R18 :
    ∀ s q d, R18 s q (.selected d) → ∀ m, I72.Fits s m → DictionaryEvidence18 s m q d :=
  dictionary_sound_of_prior438 PendingAssociated434.dictionary_sound_R17

def Selected18.report {s q} (a : Selected18 s q) : Result :=
  ⟨.selected a.invocation.row.id [],.selected a.dictionary,[]⟩

def ClassifiedAs (s : I72.State) (q : Request) (r : Result) : Prop :=
  PendingAssociated434.ClassifiedAs s q r ∨ ∃ a : Selected18 s q, r = a.report

def ReportEvidence (s : I72.State) (m : I72.Model) (q : Request) (r : Result) : Prop :=
  PendingAssociated434.ReportEvidence s m q r ∨
  ∃ a : Selected18 s q, r = a.report ∧ DictionaryEvidence18 s m q a.dictionary

inductive Witness where
  | previous (w : PendingAssociated434.Witness)
  | completedLower (data : Wire438)
  | unsupported

def check (p : Problem) (r : Result) : Witness → Bool
  | .previous old => PendingAssociated434.check p r old
  | .completedLower data =>
    match replay438 p.state p.root data with
    | none => false
    | some found => Check408.matchesNoWrites r found.selected.report.tree found.selected.report.verdict
  | .unsupported => false

theorem previous_R17_entry_is_unchanged438 (p : Problem) (r : Result)
    (old : PendingAssociated434.Witness) :
    check p r (.previous old) = PendingAssociated434.check p r old := rfl

theorem checked_completed_reads_exact_report438 {p : Problem} {r : Result} {w : Wire438}
    (yes : check p r (.completedLower w) = true) :
    ∃ a : Replay438 p.state p.root w, replay438 p.state p.root w = some a ∧ r = a.selected.report := by
  change (match replay438 p.state p.root w with
    | none => false
    | some a => Check408.matchesNoWrites r a.selected.report.tree a.selected.report.verdict) = true at yes
  cases actual : replay438 p.state p.root w with
  | none => simp [actual] at yes
  | some a =>
    rw [actual] at yes
    obtain ⟨tree,verdict,writes⟩ := Check408.matchesNoWrites_exact408.mp yes
    refine ⟨a,rfl,?_⟩
    cases r
    simp only [Selected18.report] at tree verdict writes
    subst_vars
    rfl

theorem check_sound (p : Problem) (r : Result) (w : Witness)
    (yes : check p r w = true) :
    ClassifiedAs p.state p.root r ∧
    ∀ m : I72.Model, I72.Fits p.state m → ReportEvidence p.state m p.root r := by
  cases w with
  | previous old =>
    obtain ⟨prior,same⟩ := PendingAssociated434.check_sound p r old yes
    exact ⟨.inl prior,fun m fit => .inl (same m fit)⟩
  | completedLower data =>
    obtain ⟨a,_,same⟩ := checked_completed_reads_exact_report438 yes
    have declared : R18 p.state p.root (.selected a.selected.dictionary) := .inr ⟨a.selected,rfl⟩
    exact ⟨.inr ⟨a.selected,same⟩,fun m fit =>
      .inr ⟨a.selected,same,dictionary_sound_R18 _ _ _ declared m fit⟩⟩
  | unsupported => simp [check] at yes

theorem verified_R18_result_classifies_in_same_State438 (p : Problem) (r : Result)
    (w : Witness) (good : check p r w = true) :
    R18 p.state p.root r.verdict ∧
      ∀ m : I72.Model, I72.Fits p.state m → ReportEvidence p.state m p.root r := by
  refine ⟨?_,(check_sound p r w good).2⟩
  cases w with
  | previous old =>
    exact .inl (PendingAssociated434.verified_R17_result_classifies_in_same_State434 p r old good).1
  | completedLower data =>
    obtain ⟨a,_,same⟩ := checked_completed_reads_exact_report438 good
    exact .inr ⟨a.selected,congrArg (fun x : Result => x.verdict) same⟩
  | unsupported => simp [check] at good

theorem real_raw_K2_refuses_completed_witness438 {p : Problem} {r : Result} {w : Wire438}
    (cyclic : RootCycle p.state p.root) :
    check p r (.completedLower w) = false ∧ R18 p.state p.root .rejected := by
  refine ⟨?_,(raw_root_K2_has_priority438 cyclic).1⟩
  cases report : check p r (.completedLower w) with
  | false => rfl
  | true =>
    obtain ⟨a,_,_⟩ := checked_completed_reads_exact_report438 report
    exact (replay_completed_preserves_raw_safety438 a cyclic).elim

end Yulang.GeneralDeclarativeI65.I72.CompletedEntry438
