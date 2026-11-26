import Yulang.GeneralDeclarativeI65I74MergedOutputRead439

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.MergedOutput439
open GeneralDeclarativeI65
open Checker408 (Problem Result)
open CommonRoleOutermostResolver (Dictionary Summarizes)
open GeneralDeclarations (Declaration)

/-- The added source rule reports only rejection of the actual
merged child, retaining the original parent head and the two
ordered source requests. It does not add a successful dictionary,
and leaves every old classification and proof type untouched. -/
def R19 (s : I72.State) (q : Request) (r : CommonRoleOutermostResolver.Result) : Prop :=
  CompletedEntry438.R18 s q r ∨ (r = .rejected ∧ Nonempty (Original439 s q))

theorem dictionary_sound_R19 : ∀ s q d, R19 s q (.selected d) →
    ∀ m, I72.Fits s m → CompletedEntry438.DictionaryEvidence18 s m q d := by
  intro s q d selected m fits
  rcases selected with old | ⟨bad,_⟩
  · exact CompletedEntry438.dictionary_sound_R18 _ _ _ old m fits
  · cases bad

def ClassifiedAs (s : I72.State) (q : Request) (r : Result) : Prop :=
  CompletedEntry438.ClassifiedAs s q r ∨ ∃ merged : Original439 s q, r = merged.report

def ReportEvidence (s : I72.State) (m : I72.Model) (q : Request) (r : Result) : Prop :=
  CompletedEntry438.ReportEvidence s m q r ∨
  ∃ merged : Original439 s q, r = merged.report ∧ ConflictMeaning439 merged m

inductive Witness where
  | previous (old : CompletedEntry438.Witness)
  | mergedOutput (source : Wire439)
  | unsupported

def check (p : Problem) (r : Result) : Witness → Bool
  | .previous w => CompletedEntry438.check p r w
  | .mergedOutput w =>
    match replay439 p.state p.root w with
    | none => false
    | some a => Check408.matchesNoWrites r a.report.tree a.report.verdict
  | .unsupported => false

theorem every_previous_R18_Bool_is_unchanged439 (p : Problem) (r : Result)
    (w : CompletedEntry438.Witness) :
    check p r (.previous w) = CompletedEntry438.check p r w := rfl

theorem checked_merged_replay_matches_exact_tree439 {p : Problem} {r : Result} {w : Wire439}
    (ok : check p r (.mergedOutput w) = true) :
    ∃ a : Original439 p.state p.root, replay439 p.state p.root w = some a ∧ r = a.report := by
  change (match replay439 p.state p.root w with
    | none => false
    | some a => Check408.matchesNoWrites r a.report.tree a.report.verdict) = true at ok
  cases read : replay439 p.state p.root w with
  | none => simp [read] at ok
  | some a =>
    rw [read] at ok
    obtain ⟨tree,verdict,writes⟩ := Check408.matchesNoWrites_exact408.mp ok
    refine ⟨a,rfl,?_⟩
    cases r
    simp only [Original439.report] at tree verdict writes
    subst_vars
    rfl

theorem check_sound (p : Problem) (r : Result) (w : Witness)
    (yes : check p r w = true) :
    ClassifiedAs p.state p.root r ∧
      ∀ m : I72.Model, I72.Fits p.state m → ReportEvidence p.state m p.root r := by
  cases w with
  | previous w =>
    obtain ⟨old,meaning⟩ := CompletedEntry438.check_sound p r w yes
    exact ⟨.inl old,fun m fit => .inl (meaning m fit)⟩
  | mergedOutput w =>
    obtain ⟨a,_,eq⟩ := checked_merged_replay_matches_exact_tree439 yes
    exact ⟨.inr ⟨a,eq⟩,fun m fit =>
      .inr ⟨a,eq,producer_rows_give_separate_meanings_and_merge_conflicts439 a m fit⟩⟩
  | unsupported => simp [check] at yes

theorem verified_R19_result_classifies_in_same_State439 (p : Problem) (r : Result)
    (w : Witness) (yes : check p r w = true) :
    R19 p.state p.root r.verdict ∧
      ∀ m : I72.Model, I72.Fits p.state m → ReportEvidence p.state m p.root r := by
  refine ⟨?_,(check_sound p r w yes).2⟩
  cases w with
  | previous old =>
    exact .inl (CompletedEntry438.verified_R18_result_classifies_in_same_State438 p r old yes).1
  | mergedOutput data =>
    obtain ⟨a,_,same⟩ := checked_merged_replay_matches_exact_tree439 yes
    exact .inr ⟨congrArg (fun x : Result => x.verdict) same,⟨a⟩⟩
  | unsupported => simp [check] at yes

theorem original_raw_root_K2_distinct_from_merged_rejection439 {p : Problem} {r : Result} {w : Wire439}
    (root : RootCycle p.state p.root) :
    check p r (.mergedOutput w) = false ∧ R19 p.state p.root .rejected := by
  refine ⟨?_,.inl (CompletedEntry438.raw_root_K2_has_priority438 root).1⟩
  cases b : check p r (.mergedOutput w) with
  | false => rfl
  | true =>
    obtain ⟨a,_,_⟩ := checked_merged_replay_matches_exact_tree439 b
    exact (a.safe root).elim

theorem actual_visible_rival_prevents_new_conflict_report439 {p : Problem} {r : Result} {w : Wire439}
    (two : ∀ parent ∈ visible p.state.core p.root, ∀ original : GeneralDeclarations.Clause,
      parent.requirements.head? = some original →
      1 < ((GeneralDeclarativeWitnessDeclaredState357.authoredRegistry p.state.core.current).declarations.filter
        (fun row => row.role == original.role)).length) :
    check p r (.mergedOutput w) = false := by
  cases b : check p r (.mergedOutput w) with
  | false => rfl
  | true =>
    obtain ⟨a,_,_⟩ := checked_merged_replay_matches_exact_tree439 b
    have rival := two a.frame.decl (by rw [a.oneParent]; exact List.mem_cons_self)
      a.firstClause (by rw [a.originalClauses]; rfl)
    have witness := congrArg List.length a.oneLeaf
    change ((GeneralDeclarativeWitnessDeclaredState357.authoredRegistry p.state.core.current).declarations.filter
      (fun row => row.role == a.childRole)).length = 1 at witness
    rw [a.firstRole,witness] at rival
    exact (Nat.lt_irrefl _ rival).elim

end Yulang.GeneralDeclarativeI65.I72.MergedOutput439
