import Yulang.GeneralRebaseRowClosedTerm287

/-! An executable refinement of the two-fact output driver for exactly
these two fixtures. One actual bounded child-inspection bit determines the
diagnosis once the separately proved safety and unique candidate facts hold. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 15000000
namespace Yulang.GeneralRebaseRowFixtureDriver287
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child)
open GeneralRebaseRowParentFrame287 (after)
open GeneralRebaseRowGeneratedChild287 (current)
open GeneralRebaseRowLocal287 (selected_parent selected_child)
open GeneralRebaseRowAfterSafety287 (blocked_local)
open GeneralRebaseRowProjection287 (observe support after_observe)
open GeneralRebaseSourceStepDriver270 (next)
open GeneralRebaseStep258 (done initial)
open GeneralNominalRecursiveCandidates (report)
open GeneralNominalVersionedMixedBoundary234 (Local)
open CommonRoleOutermostResolver (Tree Resolves)

def headFlag (s : GeneralNominalState.State) (data : GeneralNominalRecursiveInspection.Report s) : Bool :=
  data.blocked.isEmpty && data.conflicts.isEmpty && data.arity.isEmpty

def fromSource (choice : Bool) : Bool := headFlag raw (report ctx (childDecl choice) [(0,0)])

theorem source_bit (choice : Bool) : fromSource choice = choice := by
  cases choice <;> decide +kernel

theorem actually_read (choice : Bool) :
    fromSource choice = headFlag (current choice).state
      (report (current choice) (childDecl choice) [((0 : Fin 3),(0 : Fin 3))]) := by
  cases choice <;> decide +kernel

def childTree (ready : Bool) : Tree := if ready then .selected 1 [] else .pending
def rootTree (ready : Bool) : Tree := .selected 0 [childTree ready]

def run (choice : Bool) : Option (GeneralRebaseStep258.State support × Tree) :=
  (next support (initial support)).map fun stable => (stable,rootTree (fromSource choice))

theorem literal_result (choice : Bool) :
    run choice = some (done support,rootTree choice) := by
  unfold run
  rw [source_bit]
  rfl

theorem child_resolves (choice : Bool) :
    Resolves (Local (registry choice) (after choice)) (child choice) (childTree choice) := by
  cases choice
  · exact .pending blocked_local
  · exact .selected selected_child .nil

theorem only_child_tree (choice : Bool) (t : Tree)
    (trace : Resolves (Local (registry choice) (after choice)) (child choice) t) :
    t = childTree choice := by
  cases choice with
  | false =>
    cases trace with
    | pending => rfl
    | ambiguous h => cases B4TargetV8.local_functional h blocked_local
    | rejected h => cases B4TargetV8.local_functional h blocked_local
    | selected h _ => cases B4TargetV8.local_functional h blocked_local
  | true =>
    cases trace with
    | pending h => cases B4TargetV8.local_functional h selected_child
    | ambiguous h => cases B4TargetV8.local_functional h selected_child
    | rejected h => cases B4TargetV8.local_functional h selected_child
    | selected h kids =>
      cases B4TargetV8.local_functional h selected_child
      cases kids
      rfl

theorem only_root_tree (choice : Bool) (t : Tree)
    (trace : Resolves (Local (registry choice) (after choice)) root t) :
    t = rootTree choice := by
  cases trace with
  | pending h => cases B4TargetV8.local_functional h (selected_parent choice)
  | ambiguous h => cases B4TargetV8.local_functional h (selected_parent choice)
  | rejected h => cases B4TargetV8.local_functional h (selected_parent choice)
  | selected h kids =>
    cases B4TargetV8.local_functional h (selected_parent choice)
    cases kids with
    | cons childResult remaining =>
      cases remaining
      rw [only_child_tree choice _ childResult]
      rfl

theorem exact_run (choice : Bool) (t : Tree) :
    run choice = some (observe (after choice),t) ↔
      Resolves (Local (registry choice) (after choice)) root t := by
  rw [literal_result,after_observe]
  constructor
  · intro h
    have eq : rootTree choice = t := congrArg Prod.snd (Option.some.inj h)
    rw [← eq]
    exact .selected (selected_parent choice) (.cons (child_resolves choice) .nil)
  · intro trace
    rw [only_root_tree choice t trace]

end Yulang.GeneralRebaseRowFixtureDriver287
