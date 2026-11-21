import Yulang.GeneralDeclarativeInlineFixture331
import Yulang.GeneralDeclarativeRank321

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 11000
set_option maxHeartbeats 9000000
namespace Yulang.GeneralDeclarativeInlineGuards331
open GeneralDeclarativeInlineDecl331
open GeneralDeclarativeInlineFixture331
open GeneralDeclarativeHiddenDecl324 (catalogue interpretation)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOrigins321 (Supported restriction from_source backed_iff)
open GeneralDeclarativeObserverGrowth330 (preserve backed_same)
open GeneralDeclarativeOutputOrigins323 (emit backed_unchanged)
open GeneralDeclarativeGrowth327 (Extends)
open GeneralDeclarativeLowerKnown321 (Ready Alias knows_row)
open GeneralDeclarativeInlineEndpoint331 (Heads Matches)
open GeneralDeclarativeInlineGrowth331 (extend)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarativePriority321 (Candidates Recurs)
open GeneralDeclarativeGraphRows321 (observed shapeOf fields)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeRank321 (graph_no_cycle)
open GeneralDeclarativeOpaqueNominal328 (point_bounded)
open GeneralDeclarativeExampleSource320 (leaf)

abbrev current (done : Nat → Prop) :=
  emit (emit (preserve (before done) actual_heads.1.grows) 1 [rootWrite]) 2 [leafWrite]

theorem source_kept (done : Nat → Prop) (eq : Equation) (backed : eq ∈ sourceRows) :
    eq ∈ (restriction (current done)).equations :=
  from_source _ (.inl (.inl ⟨backed,rfl⟩))

theorem no_new_input_origin (e : Equation) :
    e ∈ (restriction (current (fun _ => False))).equations ↔
      e ∈ (restriction (before (fun _ => False))).equations :=
  (backed_unchanged (emit (preserve (before _) actual_heads.1.grows) 1 [rootWrite])
    [leafWrite] (owner := 2) (fun h => h) e).trans
    ((backed_unchanged (preserve (before _) actual_heads.1.grows) [rootWrite]
      (owner := 1) (fun h => h) e).trans (backed_same (before _) actual_heads.1.grows e))

theorem raw_current (done : Nat → Prop) :
    Extends (restriction (before done)) (restriction (current done)) := by
  refine ⟨fun _ h => h,fun _ h => h,?_⟩
  intro eq old
  obtain ⟨o,origin,usable⟩ := (backed_iff (before done) eq).mp old
  exact (backed_iff (current done) eq).mpr ⟨o,.inl (.inl origin),usable⟩

theorem root_ready (done : Nat → Prop) : Ready (current done) root := by
  intro a member
  cases List.mem_singleton.mp member
  exact ⟨_,knows_row (source_kept done rawRow List.mem_cons_self) rfl⟩

theorem child_ready (done : Nat → Prop) : Ready (current done) child := by
  intro a member
  cases List.mem_singleton.mp member
  exact ⟨_,knows_row (source_kept done scalar (List.mem_cons_of_mem _ List.mem_cons_self)) rfl⟩

theorem root_matches (done : Nat → Prop) :
    Heads (restriction (current done)) catalogue interpretation root decl := by
  exact .cons ⟨point_bounded _ 0,normalizedExpr,_,_,normal,
    extend (raw_current done) (original done .lower),extend (raw_current done) (original done .upper)⟩ .nil

theorem child_matches (done : Nat → Prop) :
    Heads (restriction (current done)) catalogue interpretation child leaf :=
  .cons ⟨point_bounded _ 3,.variable 0,[⟨0,.lower,.variable 3⟩],[⟨0,.upper,.variable 3⟩],
    rfl,.capture,.capture⟩ .nil

def rank (n : Nat) : Nat := if n = 18 then 1 else 0

theorem same_rank {a b} (h : Alias final a b) : rank a = rank b := by
  have row {a b} (seen : (⟨a,.variable b⟩ : Equation) ∈ final.equations) : rank a = rank b := by
    rw [literal_frame] at seen
    simp only [sourceRows,storedReads,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at seen
    rcases seen with h|h|h|h|h|h|h <;> cases h <;> rfl
  have bounds {a b} (incl : GeneralDeclarativeBounds319.Bound final.normal a b) : rank a = rank b := by
    induction incl with
    | refl => rfl
    | interval e => cases e
    | constraint e => cases e
    | trans _ _ x y => exact x.trans y
  induction h with
  | bounds first _ => exact bounds first
  | forward h => exact row h
  | backward h => exact (row h).symm
  | trans _ _ x y => exact x.trans y

theorem no_cycles : ∀ n, ¬AliasCycle final (observed final) n := by
  apply graph_no_cycle rank (fun _ _ h => same_rank h)
  rintro name tag child ⟨rhs,row,found⟩ member
  rw [literal_frame] at row
  simp only [sourceRows,storedReads,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at row
  rcases row with h|h|h|h|h|h|h <;> cases h
  all_goals cases found
  all_goals simp [GeneralDeclarativeK2Graph321.Shape.children] at member
  rcases member with rfl|rfl <;> decide +kernel

def tests (done : Nat → Prop) : Candidates :=
  ⟨Heads (restriction (current done)) catalogue interpretation,
    fun d candidate => ¬Heads (restriction (current done)) catalogue interpretation d candidate⟩

theorem safe (done : Nat → Prop) (d : Demand) : ¬Recurs final registry interpretation (tests done) d := by
  rintro (⟨arg,_,cycle⟩|⟨_,_,_,_,_,_,_,_,_,site,_,cycle⟩)
  · exact no_cycles arg.lower cycle
  · exact no_cycles site cycle

end Yulang.GeneralDeclarativeInlineGuards331
