import Yulang.GeneralDeclarativeRecordState326
import Yulang.GeneralDeclarativeRank321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRecordProbe326
open GeneralDeclarativeRecordDecl326
open GeneralDeclarativeRecordState326
open GeneralDeclarativeHiddenDecl324 (catalogue interpretation)
open GeneralDeclarativeExampleSource320 (leaf)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeLowerKnown321 (Ready Alias knows_row alias_refl)
open GeneralDeclarativeTrace321 (Trace)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralDeclarativePriority321 (Candidates Recurs)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeRank321 (graph_no_cycle)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralNominalMaterialization (Mode)

theorem trace (done : Nat → Prop) (mode : Mode) :
    Trace (restriction (support2 done)) mode 0 normalizedExpr [⟨0,mode,3⟩,⟨1,mode,7⟩] :=
  .record (alias_refl _) (authorized done (show readRow ∈ sourceFacts by simp [sourceFacts])) .capture .capture

theorem ready_root (done : Nat → Prop) : Ready (support2 done) root := by
  intro a had
  cases List.mem_singleton.mp had
  exact ⟨_,knows_row (authorized done (show sourceRow ∈ sourceFacts from List.mem_cons_self)) rfl⟩

theorem ready_child (done : Nat → Prop) : Ready (support2 done) child := by
  intro a had
  cases List.mem_singleton.mp had
  exact ⟨_,knows_row (authorized done (show lower3 ∈ sourceFacts by simp [sourceFacts])) rfl⟩

theorem head_root (done : Nat → Prop) :
    HeadMatches (restriction (support2 done)) catalogue interpretation root decl :=
  .cons ⟨point_bound 0,normalizedExpr,_,_,normal,trace done .lower,trace done .upper⟩ .nil

theorem head_child (done : Nat → Prop) :
    HeadMatches (restriction (support2 done)) catalogue interpretation child leaf :=
  .cons ⟨point_bound 3,.variable 0,[⟨0,.lower,3⟩],[⟨0,.upper,3⟩],rfl,.capture,.capture⟩ .nil

def rank (n : Nat) : Nat := if n = 0 ∨ n = 6 ∨ n = 7 then 1 else 0

theorem alias_rank {a b} (eq : Alias final a b) : rank a = rank b := by
  have rowRank {a b} (seen : (⟨a,.variable b⟩ : Equation) ∈ final.equations) : rank a = rank b := by
    change _ ∈ sourceFacts ++ [parentRow] ++ [childRow] at seen
    simp only [sourceFacts,tail_exact,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at seen
    rcases seen with h|h|h|h|h|h|h <;> cases h <;> rfl
  have bound {a b} (read : GeneralDeclarativeBounds319.Bound final.normal a b) : rank a = rank b := by
    induction read with
    | refl => rfl
    | interval no => cases no
    | constraint no => cases no
    | trans _ _ x y => exact x.trans y
  induction eq with
  | bounds same _ => exact bound same
  | forward row => exact rowRank row
  | backward row => exact (rowRank row).symm
  | trans _ _ x y => exact x.trans y

theorem exact_labels :
    GeneralDeclarativeGraphRows321.fields (GeneralDeclarativeRecordK2326.row rawNames) =
      some [(7,3),(8,4)] := rfl

theorem no_cycles : ∀ root, ¬ AliasCycle final (observed final) root := by
  apply graph_no_cycle rank (fun _ _ same => alias_rank same)
  rintro n target child ⟨body,known,shape⟩ used
  change _ ∈ sourceFacts ++ [parentRow] ++ [childRow] at known
  simp only [sourceFacts,tail_exact,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at known
  rcases known with h|h|h|h|h|h|h <;> cases h
  all_goals cases shape
  all_goals simp [GeneralDeclarativeK2Graph321.Shape.children] at used
  all_goals first
    | (rcases used with rfl|rfl; all_goals decide +kernel)
    | (subst child; decide +kernel)

def tests (done : Nat → Prop) : Candidates :=
  ⟨HeadMatches (restriction (support2 done)) catalogue interpretation,
   fun d impl => ¬ HeadMatches (restriction (support2 done)) catalogue interpretation d impl⟩

theorem safe (done : Nat → Prop) (d : Demand) : ¬ Recurs final registry interpretation (tests done) d := by
  rintro (⟨arg,_,cycle⟩|⟨_,_,_,_,_,_,_,_,_,site,_,cycle⟩)
  · exact no_cycles arg.lower cycle
  · exact no_cycles site cycle

end Yulang.GeneralDeclarativeRecordProbe326
