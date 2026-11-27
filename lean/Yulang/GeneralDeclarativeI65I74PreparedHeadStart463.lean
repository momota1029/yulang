import Yulang.GeneralDeclarativeI65I74PreparedDeclarations463
import Yulang.GeneralDeclarativeI65I74OriginalReportAnchor460

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.PreparedDeclarations463
open Yulang.GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessClassifyVariance357 (DeclarationReady)
open AuthoredInspectQuery456 (AuthoredQuery compileQuery compile_query_exact)
open Checker408 (Problem)
open WrittenPattern460

/-- Locate a head inspection independently of where-clause count. These are
source positions, not candidate priority or which diagnostic to display. -/
structure HeadAddress where
  visibleOrdinal : Nat
  headArgument : Nat
  deriving DecidableEq

structure OriginalHead (p : Problem) where
  location : HeadAddress
  declaration : Declaration
  original : Pattern
  capture : Capture
  code : Expr
  actualVisible : (visible p.state.core p.root)[location.visibleOrdinal]? = some declaration
  actualHead : declaration.head[location.headArgument]? = some original
  actualArgument : p.root.demand.arguments[location.headArgument]? = some capture
  compiled : AuthoredQuery p.state.core (normalize original) code

def headOfAnchor {p : Problem} (a : OriginalAnchor p) : OriginalHead p :=
  ⟨⟨a.location.visibleOrdinal,a.location.headArgument⟩,a.declaration,a.original,a.capture,a.code,
    a.actualVisible,a.actualHead,a.actualArgument,a.compiled⟩

def readOriginalHead (p : Problem) (a : HeadAddress) : Option (OriginalHead p) :=
  match v : (visible p.state.core p.root)[a.visibleOrdinal]? with
  | none => none
  | some d =>
    match h : d.head[a.headArgument]?, arg : p.root.demand.arguments[a.headArgument]? with
    | some original, some capture =>
      match compiled : compileQuery p.state.core (normalize original) with
      | none => none
      | some e =>
        some ⟨a,d,original,capture,e,v,h,arg,(compile_query_exact ..).mp compiled⟩
    | _,_ => none

theorem each_original_head_position_replays {p : Problem} (a : OriginalHead p) :
    readOriginalHead p a.location = some a := by
  rcases a with ⟨loc,d,pat,arg,code,vis,head,argv,auth⟩
  have run := (compile_query_exact ..).mpr auth
  unfold readOriginalHead
  split
  · rename_i wrong
    rw [vis] at wrong
    cases wrong
  · rename_i got h
    have same : got = d := Option.some.inj (h.symm.trans vis)
    subst got
    split
    · rename_i original capture hA hB
      have sameHead : original = pat := Option.some.inj (hA.symm.trans head)
      have sameArg : capture = arg := Option.some.inj (hB.symm.trans argv)
      subst original capture
      split
      · rename_i fail
        rw [run] at fail
        cases fail
      · rename_i out found
        have result : out = code := Option.some.inj (found.symm.trans run)
        subst out
        rfl
    · simp_all

theorem forgetting_original_where_does_not_replace_head_or_visible_position
    {p : Problem} (old : OriginalAnchor p) :
    readOriginalHead p ⟨old.location.visibleOrdinal,old.location.headArgument⟩ =
      some (headOfAnchor old) :=
  each_original_head_position_replays (headOfAnchor old)

theorem source_head_member_compiles_exactly_once_for_its_original_pattern
    {p : Problem} (h : OriginalHead p) :
    AuthoredQuery p.state.core
      (writeTerm (normalized (readTerm h.original))) h.code := by
  simpa only [normalized_reencodes_exactly,write_read_term] using h.compiled

structure PrecheckedHead {p : Problem} (tab : CheckedTable p.state.core.current) where
  orig : OriginalHead p
  stored : orig.declaration ∈ tab.rows
  point : orig.capture.lower = orig.capture.center ∧ orig.capture.center = orig.capture.upper

def readPrecheckedHead {p : Problem} (tab : CheckedTable p.state.core.current)
    (source : HeadAddress) : Option (PrecheckedHead tab) := do
  let head ← readOriginalHead p source
  if found : tableContains tab head.declaration = true then
    if point : head.capture.lower = head.capture.center ∧ head.capture.center = head.capture.upper then
      some ⟨head,of_decide_eq_true found,point⟩
    else none
  else none

theorem each_prechecked_head_position_replays {p : Problem}
    (tab : CheckedTable p.state.core.current) (a : PrecheckedHead tab) :
    readPrecheckedHead tab a.orig.location = some a := by
  have member : tableContains tab a.orig.declaration = true := decide_eq_true a.stored
  cases a with
  | mk orig stored point =>
    simp [readPrecheckedHead,each_original_head_position_replays orig,member,point,Option.bind]

theorem prechecked_head_is_genuinely_ready {p : Problem} {tab : CheckedTable p.state.core.current}
    (a : PrecheckedHead tab) : DeclarationReady (authoredRegistry p.state.core.current) a.orig.declaration :=
  tab.prepared _ a.stored

/-- Exact list-order indices among *all* visible resolved declarations. A
read of one such index does not prove that it actually matches or wins. -/
theorem prechecked_reader_never_renumbers_the_visible_roster {p : Problem}
    {tab : CheckedTable p.state.core.current} {addr : HeadAddress} {a : PrecheckedHead tab}
    (read : readPrecheckedHead tab addr = some a) : a.orig.location = addr := by
  have h {out : OriginalHead p} (real : readOriginalHead p addr = some out) : out.location = addr := by
    unfold readOriginalHead at real
    repeat' first | (cases real; rfl) | split at real | contradiction
  cases found : readOriginalHead p addr with
  | none => simp [readPrecheckedHead,found,Option.bind] at read
  | some out =>
    by_cases yes : tableContains tab out.declaration = true
    · by_cases point : out.capture.lower = out.capture.center ∧ out.capture.center = out.capture.upper
      · have same : a.orig = out := congrArg PrecheckedHead.orig
          (Option.some.inj (by simpa [readPrecheckedHead,found,yes,point,Option.bind] using read)).symm
        rw [same]
        exact h found
      · simp [readPrecheckedHead,found,yes,point,Option.bind] at read
    · simp [readPrecheckedHead,found,yes,Option.bind] at read

end Yulang.GeneralDeclarativeI65.I72.PreparedDeclarations463
