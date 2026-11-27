import Yulang.GeneralDeclarativeI65I74AuthoredPatternKeys460
import Yulang.GeneralDeclarativeI65I74RoutedInlineStructuralEntry458

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
open GeneralNominalCenteredHeadMatExpressions (Expr)
open RecordTraversal455 (RawSnapshot termInspects term_inspects_exact455)
open RecordTraversal455.MixedQA (MixedPath)
open GeneralDeclarativeInspect321 (Inspects Visit)
open GeneralDeclarativeGraphRows321 (observed structural)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open RecordK2412 (FieldCycleWire checkCycleAt412 cycle_at_sound412)
open List410 (ExactEscapeWire)
open SplitEscape446 (splitCheck446 checked_split_escape_excludes_exact_raw_K2446)
open SplitEscape446.SplitCompact447 (raw_safe_iff_small_witness447)

abbrev RawAddress := RecordTraversal455.MixedQA.Address

def writtenAddress : RawAddress → Address
  | .primitive _ i | .nominal _ i => .arg i
  | .field l => .field l
  | .variant t => .tag t

/-- The grammar/code alignment at *this* coordinate. Its finite
reflection is an explicit obligation, not inferred from matching labels.
Both the next written term and next compiled query are checked at the next
node. Implementations must retain original positions across normalization. -/
structure Alignment where
  Token : Type
  exactAt : Nat → Term → Expr → Prop
  checks : Nat → Term → Expr → Token → Bool
  reflects : ∀ n t e, (∃ w, checks n t e w = true) ↔ exactAt n t e

inductive JointTrail (s : RawSnapshot) (policy : AuthenticatedHop458.Policy)
    (keys : Nat → KeyRead) (aligned : Alignment) :
    Nat → Term → Expr → MixedPath → Nat → Term → Bool → Prop
  | stop : aligned.exactAt root t e → Inspects e →
      JointTrail s policy keys aligned root t e [] root t false
  | down : aligned.exactAt root t e → ¬ AliasCycle s (observed s) root →
      AuthenticatedHop458.AtStep s policy root e a child q one →
      Step (keys root) t (writtenAddress a) u →
      JointTrail s policy keys aligned child u q rest terminal last other →
      JointTrail s policy keys aligned root t e ((a,child) :: rest) terminal last (one || other)

inductive JointWire (policy : AuthenticatedHop458.Policy) (aligned : Alignment) where
  | stop (placement : aligned.Token)
  | down (placement : aligned.Token) (raw : AuthenticatedHop458.HopWire policy)
      (safe : ExactEscapeWire) (rest : JointWire policy aligned)

def readJoint (s : RawSnapshot) (policy : AuthenticatedHop458.Policy)
    (keys : Nat → KeyRead) (aligned : Alignment)
    (root : Nat) (t : Term) (e : Expr) : JointWire policy aligned →
      Option (MixedPath × Nat × Term × Bool)
  | .stop placement =>
    if aligned.checks root t e placement && termInspects e then some ([],root,t,false)
    else none
  | .down placement hop safe rest => do
    if aligned.checks root t e placement && splitCheck446 s root safe then
      let (a,c,q,used) ← AuthenticatedHop458.readStep s policy root e hop
      let u ← readStep (keys root) t (writtenAddress a)
      let (as,last,lastTerm,others) ← readJoint s policy keys aligned c u q rest
      some ((a,c)::as,last,lastTerm,used || others)
    else none

theorem joint_has_actual_raw_trace {s policy keys aligned root t e path terminal last used}
    (j : JointTrail s policy keys aligned root t e path terminal last used) :
    AuthenticatedHop458.Trail s policy root e path terminal used := by
  induction j with
  | stop _ rigid => exact .stop rigid
  | down _ safe actual _ _ ih => exact .down safe actual ih

/-- Original logical coordinates select their own catalogue; the raw path
and grammar path cannot silently diverge in their chosen positions. -/
inductive CoordinateWalk (keys : Nat → KeyRead) : Nat → Term → MixedPath → Nat → Term → Prop
  | stop : CoordinateWalk keys n t [] n t
  | down : Step (keys n) t (writtenAddress a) u →
      CoordinateWalk keys c u as terminal last →
      CoordinateWalk keys n t ((a,c)::as) terminal last

theorem joint_has_exact_written_path {s policy keys aligned root t e path terminal last used}
    (j : JointTrail s policy keys aligned root t e path terminal last used) :
    CoordinateWalk keys root t path terminal last := by
  induction j with
  | stop => exact .stop
  | down _ _ _ step _ ih => exact .down step ih

theorem joint_aligns_exactly_at_start {s policy keys aligned root t e path terminal last used}
    (j : JointTrail s policy keys aligned root t e path terminal last used) :
    aligned.exactAt root t e := by
  cases j with
  | stop yes => exact yes
  | down yes => exact yes

theorem read_joint_sound {s policy keys aligned root t e path terminal last used}
    {w : JointWire policy aligned}
    (ok : readJoint s policy keys aligned root t e w = some (path,terminal,last,used)) :
    JointTrail s policy keys aligned root t e path terminal last used := by
  induction w generalizing root t e path terminal last used with
  | stop placement =>
    by_cases yes : aligned.checks root t e placement = true ∧ termInspects e = true
    · simp [readJoint,yes.1,yes.2] at ok
      obtain ⟨rfl,rfl,rfl,rfl⟩ := ok
      exact .stop ((aligned.reflects ..).mp ⟨placement,yes.1⟩)
        ((term_inspects_exact455 _).mp yes.2)
    · simp [readJoint,Bool.and_eq_true,yes] at ok
  | down placement hop safe rest ih =>
    by_cases yes : aligned.checks root t e placement = true ∧ splitCheck446 s root safe = true
    · cases found : AuthenticatedHop458.readStep s policy root e hop with
      | none => simp [readJoint,yes.1,yes.2,found,Option.bind] at ok
      | some raw =>
        obtain ⟨a,c,q,one⟩ := raw
        cases located : readStep (keys root) t (writtenAddress a) with
        | none => simp [readJoint,yes.1,yes.2,found,located,Option.bind] at ok
        | some u =>
          cases further : readJoint s policy keys aligned c u q rest with
          | none => simp [readJoint,yes.1,yes.2,found,located,further,Option.bind] at ok
          | some out =>
            obtain ⟨xs,endAt,term,other⟩ := out
            simp [readJoint,yes.1,yes.2,found,located,further,Option.bind] at ok
            obtain ⟨rfl,rfl,rfl,rfl⟩ := ok
            exact .down ((aligned.reflects ..).mp ⟨placement,yes.1⟩)
              (checked_split_escape_excludes_exact_raw_K2446 yes.2)
              (AuthenticatedHop458.read_step_sound458 found)
              (read_step_sound located) (ih further)
    · simp [readJoint,Bool.and_eq_true,yes] at ok

theorem joint_wire_complete {s policy keys aligned root t e path terminal last used}
    (j : JointTrail s policy keys aligned root t e path terminal last used) :
    ∃ w, readJoint s policy keys aligned root t e w = some (path,terminal,last,used) := by
  induction j with
  | stop align rigid =>
    obtain ⟨w,h⟩ := (aligned.reflects ..).mpr align
    exact ⟨.stop w,by simp [readJoint,h,(term_inspects_exact455 _).mpr rigid]⟩
  | down align clear actual locate _ ih =>
    obtain ⟨w,anchor⟩ := (aligned.reflects ..).mpr align
    obtain ⟨esc,checked,_,_⟩ := (raw_safe_iff_small_witness447 s _).mp clear
    obtain ⟨hop,found⟩ := AuthenticatedHop458.read_step_complete458 actual
    obtain ⟨rest,deep⟩ := ih
    exact ⟨.down w hop esc rest,by simp [readJoint,anchor,checked,found,read_step_complete locate,deep,Option.bind]⟩

theorem joint_finite_iff {s policy keys aligned root t e path terminal last used} :
    (∃ w, readJoint s policy keys aligned root t e w = some (path,terminal,last,used)) ↔
    JointTrail s policy keys aligned root t e path terminal last used :=
  ⟨fun ⟨_,ok⟩ => read_joint_sound ok,joint_wire_complete⟩

end Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
