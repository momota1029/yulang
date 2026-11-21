import Yulang.GeneralDeclarativeInlineRepeatDecl331
import Yulang.GeneralDeclarativeInlineCompiler331
import Yulang.GeneralDeclarativeStableWriteVerdict329
import Yulang.GeneralDeclarativeRank321
import Yulang.GeneralDeclarativeNestedModels328

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 9000000
namespace Yulang.GeneralDeclarativeInlineRepeat331
open GeneralDeclarativeInlineRepeatDecl331
open GeneralDeclarativeHiddenDecl324 (catalogue interpretation)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeLowerKnown321 (Ready alias_refl knows_row Alias)
open GeneralDeclarativeRecordSpine330 (Spine exact_subtraction)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarativeInlineGrowth331 (extend)
open GeneralDeclarativeRecordPoints330 (observed precise)
open GeneralDeclarativeRecordMaterial330 (tailExpr)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralDeclarativeObserverGrowth330 (preserve sources_grow)
open GeneralDeclarativeInlineEndpoint331 (Heads)
open GeneralDeclarativeStableAttempt329 (Elected Attempt RejectedByWrite reject_exact)
open GeneralDeclarativeStableWriteVerdict329 (Rejection error_tree not_pending)
open GeneralDeclarativeStableAssemble329 (firsts)
open GeneralDeclarativeStableCanonical329 (uses_existing EqualUses)
open GeneralDeclarativeStableTies329 (rows pairOf)
open GeneralDeclarativeStableReads329 (One)
open GeneralDeclarativeRank321 (graph_no_cycle)
open GeneralDeclarativeGraphRows321 (observed shapeOf fields)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativePriority321 (Candidates Recurs)
open GeneralDeclarativeOpaqueNominal328 (point point_bounded)
open GeneralDeclarativeEntailment320 (model_append)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty record exactEmpty Equivalent common_union_is_join subtype_refl)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_trans eqv_symm)
open GeneralDeclarativeExampleSource320 (int)
open GeneralDeclarativeNestedModels328 (payload_gt_int)
open CommonRoleOutermostResolver (Classify)

abbrev scalarInt : Expr := .primitive (.scalar .int) []
abbrev scalarBool : Expr := .primitive (.scalar .bool) []
abbrev terminal : Expr := .primitive .exactEmpty []
abbrev raw : List (Nat × Expr) := [(7,scalarInt),(8,scalarBool)]
abbrev recorded : List (Nat × Expr) := [(7,.variable 0),(8,.variable 0)]
abbrev row : Equation := ⟨0,withTail raw terminal⟩
abbrev initial : State := ⟨⟨[],[]⟩,[row]⟩
abbrev keep := [5,6]
abbrev stage := GeneralDeclarativeRecordPoints330.ready initial 0 keep raw terminal
abbrev spans : List (Nat × Capture) := [(0,point 7),(0,point 8),(1,point 9)]

def support0 (done : Nat → Prop) : Supported initial done :=
  ⟨fun e o => e = row ∧ o = .source,fun h => List.mem_singleton.mpr h.1⟩

theorem closed (done : Nat → Prop) : Spine (restriction (support0 done)) 0 raw terminal :=
  .inline (alias_refl _) .exactEnd (from_source _ ⟨rfl,rfl⟩)

def occurrences (mode : GeneralNominalMaterialization.Mode) : List Occurrence :=
  [⟨0,mode,scalarInt⟩,⟨0,mode,scalarBool⟩,⟨1,mode,terminal⟩]

theorem input (done : Nat → Prop) (mode) :
    Read (restriction (support0 done)) mode (.variable 0) normalizedExpr (occurrences mode) :=
  .record (.name (closed done)) (keys := [7,8]) (selected := raw) (by decide) (by decide) rfl
    (.cons .capture (.cons .capture .nil)) .binder .capture

theorem named_actual :
    GeneralDeclarativeOpaqueConserve328.Retains initial stage keep ∧
      One stage catalogue interpretation (point 0) pat spans := by
  exact GeneralDeclarativeRecordPoints330.observed (p := support0 (fun _ => False)) (arg := point 0)
    (fields := [7,8]) (raw := raw) (terminal := terminal) (picked := raw) (pattern := recorded)
    (binders := [0,0]) (tailBinder := 1) (closed _) (point_bounded _ _) (by decide) rfl
    (.cons (.cons .nil)) normal keep

def view (done : Nat → Prop) := preserve (support0 done) named_actual.1.grows

theorem lower_known (done : Nat → Prop) : Ready (view done) root := by
  intro arg incoming
  cases List.mem_singleton.mp incoming
  exact ⟨_,knows_row (from_source (view done) (row := row) ⟨rfl,rfl⟩) rfl⟩

def tests (done : Nat → Prop) : Candidates :=
  ⟨Heads (restriction (view done)) catalogue interpretation,
    fun d impl => ¬Heads (restriction (view done)) catalogue interpretation d impl⟩

theorem probes (done : Nat → Prop) : (tests done).viable root decl := by
  let ext := sources_grow (support0 done) named_actual.1.grows
  exact .cons ⟨point_bounded _ 0,normalizedExpr,_,_,normal,extend ext (input done .lower),
    extend ext (input done .upper)⟩ .nil

theorem no_cycles : ∀ n, ¬AliasCycle stage (GeneralDeclarativeGraphRows321.observed stage) n := by
  apply graph_no_cycle (fun _ => 0) (fun _ _ _ => rfl)
  rintro n shape child ⟨rhs,stored,found⟩ part
  change (⟨n,rhs⟩ : Equation) ∈ [row,⟨7,scalarInt⟩,⟨8,scalarBool⟩,⟨9,terminal⟩,
    ⟨0,.record 7 (.variable 7) (.record 8 (.variable 8) (.variable 9))⟩] at stored
  simp only [List.mem_cons,List.not_mem_nil,or_false] at stored
  rcases stored with h|h|h|h|h <;> cases h <;> cases found
  all_goals cases part

theorem no_recurs (done : Nat → Prop) : ¬Recurs stage registry interpretation (tests done) root := by
  rintro (⟨o,_,loop⟩|⟨_,_,_,_,_,_,_,_,_,site,_,loop⟩)
  · exact no_cycles o.lower loop
  · exact no_cycles site loop

theorem one_candidate (d) (present : d ∈ registry.declarations) (role : d.role = root.role) : d = decl := by
  rcases List.mem_cons.mp present with rfl|other
  · rfl
  · cases List.mem_singleton.mp other
    cases role

theorem proposal (done : Nat → Prop) : Elected stage registry interpretation (view done) (tests done) root decl := by
  refine ⟨lower_known done,no_recurs done,?_,⟨⟨List.mem_cons_self,rfl⟩,probes done⟩,?_⟩
  · rintro ⟨candidate,⟨listed,role⟩,pending⟩
    cases one_candidate candidate listed role
    exact pending (probes done)
  · intro other found
    rw [one_candidate other found.1.1 found.1.2]

abbrev fallback (_ : Nat) := point 7
def attempt (done : Nat → Prop) : Attempt stage registry interpretation (view done) (tests done) root decl :=
  ⟨proposal done,spans,firsts spans fallback,.cons (rest := []) named_actual.2 .nil,uses_existing spans fallback⟩

theorem exact_tie (done : Nat → Prop) :
    rows (attempt done).center (spans.map pairOf) = [⟨7,.variable 8⟩] := rfl

abbrev bool : Ty := .base .bool
abbrev headType := record 7 int (record 8 bool exactEmpty)
def witness : Assignment := fun n =>
  (if n = 0 then headType else if n = 8 then bool else if n = 9 then exactEmpty else int,Common.rowEmpty)

theorem at_start : Models initial witness := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,fun _ h => False.elim (List.not_mem_nil h)⟩,?_⟩
  intro e present
  cases List.mem_singleton.mp present
  exact eqv_refl _

theorem inhabited : Models stage witness := by
  let middle := GeneralDeclarativeRecordPoints330.named initial 0 keep raw terminal
  have withNames : Models middle witness := (model_append _).mpr ⟨at_start,fun e used => by
    change e ∈ [⟨7,scalarInt⟩,⟨8,scalarBool⟩,⟨9,terminal⟩] at used
    simp only [List.mem_cons,List.not_mem_nil,or_false] at used
    rcases used with h|h|h <;> cases h <;> exact eqv_refl _⟩
  apply (model_append _).mpr
  refine ⟨withNames,fun e used => ?_⟩
  cases List.mem_singleton.mp used
  have inSame := precise raw terminal 7 witness ((model_append _).mp withNames).2
  exact eqv_symm inSame

theorem values_incompatible (done : Nat → Prop) :
    RejectedByWrite (attempt done) := by
  apply (reject_exact _).mpr
  refine ⟨⟨witness,inhabited⟩,?_⟩
  intro m valid agrees
  have same := agrees 0 (point 7) (point 8) List.mem_cons_self
    (List.mem_cons_of_mem _ List.mem_cons_self)
  have i := valid.2 ⟨7,scalarInt⟩ (List.mem_cons_of_mem _ List.mem_cons_self)
  have b := valid.2 ⟨8,scalarBool⟩ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have yes := (eqv_trans (eqv_symm b) (eqv_trans (eqv_symm same) i)).1
  exact payload_gt_int ((common_union_is_join ..).mpr ⟨subtype_refl _,yes⟩)

theorem actual_rejected (done : Nat → Prop) :
    Classify (Rejection (attempt done)) root .rejected ∧ ¬Rejection (attempt done) root .pending :=
  ⟨error_tree (attempt done) (values_incompatible done),not_pending (attempt done)⟩

end Yulang.GeneralDeclarativeInlineRepeat331
