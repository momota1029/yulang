import Yulang.GeneralDeclarativeObserverSource330
import Yulang.GeneralDeclarativeHiddenDecl324

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 4500000
namespace Yulang.GeneralDeclarativeRecordInline330
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeLowerKnown321 (Alias alias_refl Knows knows_row)
open GeneralDeclarativeRecordSpine330 (Spine)
open GeneralDeclarativeRecordPoints330 (Layout observed endpoint_spelling seed)
open GeneralDeclarativeRecordPoints330 (usesFrom ready expressions)
open GeneralDeclarativeRecordMaterial330 (tailExpr)
open GeneralDeclarativeOpaqueNominal328 (point point_bounded)
open GeneralDeclarativeObserverSource330 (Input)
open GeneralDeclarativeStableReads329 (One)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeHiddenDecl324 (catalogue interpretation)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarativeTrace321 (Trace)
open GeneralDeclarativeOpaqueConserve328 (Retains)
open GeneralDeclarativeNewNames321 (supply)

abbrev payload : Expr := .primitive .pair [.variable 3,.variable 4]
abbrev fields : List (Nat × Expr) :=
  [(7,payload),(7,.variable 3),(8,.variable 4),(9,.variable 7)]
abbrev taken : List (Nat × Expr) := [(7,payload),(8,.variable 4)]
abbrev written : List (Nat × Expr) := [(7,.variable 0),(8,.variable 1)]
abbrev pat : Pattern := .record 7 (.var 0) (.record 8 (.var 1) (.var 2))
abbrev terminal : Expr := .primitive .emptyRecord []
abbrev rawRow : Equation := ⟨0,withTail fields terminal⟩
abbrev initial : State := ⟨⟨[],[]⟩,[rawRow]⟩
abbrev keep := [5,6]
abbrev remain := tailExpr fields [7,8] terminal
abbrev named := ready initial 0 keep taken remain

def support (done : Nat → Prop) : Supported initial done :=
  ⟨fun e origin => e = rawRow ∧ origin = .source,fun h => List.mem_singleton.mpr h.1⟩

theorem original (done : Nat → Prop) : rawRow ∈ (restriction (support done)).equations :=
  from_source _ ⟨rfl,rfl⟩
theorem actually_closed (done : Nat → Prop) : Spine (restriction (support done)) 0 fields terminal :=
  .inline (alias_refl _) .width (original done)

theorem actual_seed : seed initial 0 keep taken remain = 8 := rfl
theorem consumed_children :
    usesFrom taken [0,1] 2 (seed initial 0 keep taken remain) =
      [(0,point 8),(1,point 4),(2,point 9)] := rfl
theorem exact_allocations : supply initial (0::keep) (expressions taken remain) =
    [⟨8,payload⟩,⟨9,.record 9 (.variable 7) terminal⟩] := rfl
theorem inline_ready : Retains initial named keep ∧
    One named catalogue interpretation (point 0) pat [(0,point 8),(1,point 4),(2,point 9)] := by
  apply observed (p := support (fun _ => False)) (arg := point 0) (fields := [7,8])
    (raw := fields) (terminal := terminal) (picked := taken)
    (pattern := written) (binders := [0,1]) (tailBinder := 2)
    (actually_closed _) (point_bounded _ _) (by decide)
  · rfl
  · exact .cons (.cons .nil)
  · rfl

theorem in_observer (done : Nat → Prop) : Input (support done) catalogue interpretation (point 0) pat :=
  .pointFields (keys := [7,8]) (chosen := taken) (written := written) (binders := [0,1])
    (binder := 2) (point_bounded _ _) (actually_closed _) (by decide) rfl (.cons (.cons .nil)) rfl

theorem lower_ready (done : Nat → Prop) : Knows (restriction (support done)) 0 (.record 7) :=
  knows_row (original done) rfl

/-- Ready is real, and the exact head walk exists without adding source
origins, but the old name-only endpoint relation has no candidate trace
for this raw inline spelling. This is a missing observer case, not a
counterexample to soundness of an approved selected program. -/
theorem endpoint_gap (done : Nat → Prop) (mode) :
    ¬∃ uses, Trace (restriction (support done)) mode 0
      (withTail written (.variable 2)) uses := by
  intro holds
  obtain ⟨_, trace⟩ := holds
  obtain ⟨owner,p,r,stored⟩ := endpoint_spelling trace
  obtain ⟨origin,proven,_⟩ := (GeneralDeclarativeOrigins321.backed_iff (support done) _).mp stored
  have e := proven.1
  change (⟨owner,.record 7 (.variable p) (.variable r)⟩ : Equation) = rawRow at e
  cases congrArg Equation.right e

end Yulang.GeneralDeclarativeRecordInline330
