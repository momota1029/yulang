import Yulang.GeneralDeclarativeI65I74ListFrameEntry449

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ListSites449.Frame
open Yulang.GeneralDeclarativeI65
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarationPatterns (Pattern)
open Checker408 (Problem Result)
open GeneralDeclarations (Declaration)
open RetainedFull445
open List410 (ExactEscapeWire)
open SplitEscape446

/-- The authenticated original positions of a read frame, in the
original written order. This is not just a length comparison. -/
inductive OriginOrder (s : GeneralDeclarativeI65.State) :
    {args : List Capture} → {heads : List Pattern} → AuthoredFrame s args heads →
      List Nat → Prop where
  | nil : OriginOrder s AuthoredFrame.nil []
  | next {args heads arg head idx later} {a : WrittenListSite s arg head}
      {tail : AuthoredFrame s args heads}
      (atOriginal : s.origins[idx]? = some a.origin)
      (rest : OriginOrder s tail later) :
      OriginOrder s (.cons a tail) (idx :: later)

theorem actual_readsite_index_is_original449 {s arg head i} {a : WrittenListSite s arg head}
    (accepted : readSite s arg head i = some a) :
    s.origins[i]? = some a.origin := by
  unfold readSite at accepted
  repeat first
    | cases accepted
    | simp only [Bind.bind,Option.bind] at accepted
    | split at accepted
  all_goals first | contradiction | assumption

theorem actual_read_frame_has_exact_origin_order449 {s args heads ids} {a : AuthoredFrame s args heads}
    (found : readAuthoredFrame s args heads ids = some a) :
    OriginOrder s a ids := by
  induction args generalizing heads ids with
  | nil =>
    cases heads <;> cases ids <;> simp only [readAuthoredFrame] at found <;> cases found
    exact .nil
  | cons first rest ih =>
    cases heads with
    | nil => simp [readAuthoredFrame] at found
    | cons hp tp =>
      cases ids with
      | nil => simp [readAuthoredFrame] at found
      | cons i is =>
        simp only [readAuthoredFrame,Bind.bind,Option.bind] at found
        cases here : readSite s first hp i with
        | none => simp [here] at found
        | some source =>
          simp only [here] at found
          cases later : readAuthoredFrame s rest tp is with
          | none => simp [later] at found
          | some tail =>
            simp only [later,Option.pure_def] at found
            cases Option.some.inj found
            exact .next (actual_readsite_index_is_original449 here) (ih later)

theorem nth_table_proof_is_for_this_original_site449 {s sites certs}
    (passed : checkSiteTable s sites certs = true)
    {i n : Nat} {w : ExactEscapeWire} (site : sites[i]? = some n)
    (certificate : certs[i]? = some w) : splitCheck446 s n w = true := by
  induction sites generalizing certs i with
  | nil => simp at site
  | cons first rest ih =>
    cases certs with
    | nil => simp at certificate
    | cons c later =>
      have good := Bool.and_eq_true_iff.mp passed
      cases i with
      | zero =>
        simp at site certificate
        subst n
        subst w
        exact good.1
      | succ i => exact ih good.2 (by simpa using site) (by simpa using certificate)

theorem actual_choice_checks_real_origins_and_exact_sites449 {p : Problem}
    {d : Declaration} {scope w} {a : ListFrameChoice p d}
    (passed : readListFrameChoice p d scope w = some a) :
    OriginOrder p.state.core a.roster w.origins ∧
      checkSiteTable p.state.core.current.ordinary
        (p.root.demand.arguments.map Capture.lower) w.certificates = true := by
  unfold readListFrameChoice at passed
  repeat first
    | cases passed
    | simp only [Bind.bind,Option.bind] at passed
    | split at passed
  all_goals first | contradiction |
    (constructor
     · apply actual_read_frame_has_exact_origin_order449
       assumption
     · assumption)

theorem accepted_frame_wire_indexes_actual_source_and_visited_cut449 {p : FullProblem} {r : Result}
    {w : FrameWire} (ok : check_full449 p r (.inspectedFrame w) = true) :
    ∃ a : FramedSelection p.old, r = a.report ∧
      OriginOrder p.state.base.core a.chosen.roster w.origins ∧
      ∀ (i n : Nat) (c : ExactEscapeWire), (p.root.demand.arguments.map Capture.lower)[i]? = some n →
        w.certificates[i]? = some c → splitCheck446 p.state.base.core.current.ordinary n c = true := by
  obtain ⟨a,same,replayed⟩ := actual_checked_frame_reads_exact_source449 ok
  have real := actual_choice_checks_real_origins_and_exact_sites449 replayed
  exact ⟨a,same,real.1,fun _ _ _ atSite atCert =>
    nth_table_proof_is_for_this_original_site449 real.2 atSite atCert⟩

end Yulang.GeneralDeclarativeI65.I72.ListSites449.Frame
