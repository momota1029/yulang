import Yulang.GeneralDeclarativeStableClash329
import Yulang.GeneralDeclarativeStableAttempt329
import Yulang.GeneralDeclarativeStableOrigin329

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 10000000
namespace Yulang.GeneralDeclarativeStableRejected329
open GeneralDeclarativeStableClash329
open GeneralDeclarativeStableFixture329 (spans base pairRow)
open GeneralDeclarativeOpaqueFixture328 (endpoints oldRows prepared)
open GeneralDeclarativeOpaqueIntervals328 (low high)
open GeneralDeclarativeStableAttempt329 (Attempt Elected RejectedByWrite)
open GeneralDeclarativeStableCanonical329 (Representative)
open GeneralDeclarativeRepeatDecl327 (reg interp arg root impl headCode)
open GeneralDeclarativeHead320 (Equation State)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeLowerKnown321 (Ready Alias knows_row alias_refl)
open GeneralDeclarativeTrace321 (Trace)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralDeclarativePriority321 (Candidates Recurs)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeRank321 (graph_no_cycle)

theorem table : beforeChoice.equations = oldRows ++ [pairRow,pinInt,pinBool,pinWide] := rfl

def support (done : Nat → Prop) : Supported beforeChoice done :=
  ⟨fun e origin => e ∈ oldRows ∧ origin = .source,by
    intro e _ h
    rw [table]
    exact List.mem_append_left _ h.1⟩

theorem visible (done : Nat → Prop) {e : Equation} (h : e ∈ oldRows) :
    e ∈ (restriction (support done)).equations :=
  from_source _ ⟨h,rfl⟩

theorem ready (done : Nat → Prop) : Ready (support done) root := by
  intro a use
  cases List.mem_singleton.mp use
  exact ⟨_,knows_row (visible done (show (⟨0,low endpoints⟩ : Equation) ∈ oldRows from List.mem_cons_self)) rfl⟩

theorem match_root (done : Nat → Prop) :
    HeadMatches (restriction (support done)) reg.constructors interp root impl := by
  refine .cons ⟨?_,headCode,[⟨0,.lower,3⟩,⟨0,.lower,3⟩],[⟨0,.upper,4⟩,⟨0,.upper,4⟩],rfl,?_,?_⟩ .nil
  · exact ⟨.interval List.mem_cons_self,.interval (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  · exact .primitive (args := [3,3]) (alias_refl _)
      (visible done (show (⟨0,low endpoints⟩ : Equation) ∈ oldRows from List.mem_cons_self))
      (.cons .capture (.cons .capture .nil))
  · exact .primitive (args := [4,4]) (alias_refl _)
      (visible done (show (⟨2,high endpoints⟩ : Equation) ∈ oldRows from
        List.mem_cons_of_mem _ List.mem_cons_self)) (.cons .capture (.cons .capture .nil))

def rank (n : Nat) : Nat := if n ≤ 2 then 1 else 0

theorem acyclic : ∀ n, ¬AliasCycle beforeChoice (observed beforeChoice) n := by
  have alias_rank : ∀ a b, Alias beforeChoice a b → rank a = rank b := by
    intro a b link
    have noVar {a b : Nat} (h : (⟨a,.variable b⟩ : Equation) ∈ beforeChoice.equations) : False := by
      rw [table] at h
      simp only [oldRows,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with x|x|x|x|x|x|x <;> cases x
    have bounds {a b} (h : GeneralDeclarativeBounds319.Bound beforeChoice.normal a b) : rank a = rank b := by
      induction h with
      | refl => rfl
      | interval seen =>
        change _ ∈ [(0,1),(1,2)] at seen
        simp only [List.mem_cons,List.not_mem_nil,or_false] at seen
        rcases seen with h|h <;> cases h <;> rfl
      | constraint seen =>
        change _ ∈ [PresenceNormalForm.Atom.tyLe (.var 3) (.var 7),.tyLe (.var 7) (.var 4),
          .tyLe (.var 3) (.var 8),.tyLe (.var 8) (.var 4)] at seen
        simp only [List.mem_cons,List.not_mem_nil,or_false] at seen
        rcases seen with h|h|h|h <;> cases h <;> rfl
      | trans _ _ x y => exact x.trans y
    induction link with
    | bounds x _ => exact bounds x
    | forward x => exact False.elim (noVar x)
    | backward x => exact False.elim (noVar x)
    | trans _ _ x y => exact x.trans y
  apply graph_no_cycle rank alias_rank
  rintro n shape next ⟨term,there,print⟩ member
  rw [table] at there
  simp only [oldRows,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at there
  rcases there with h|h|h|h|h|h|h <;> cases h
  all_goals cases print
  all_goals simp [GeneralDeclarativeK2Graph321.Shape.children] at member
  all_goals (rcases member with rfl|rfl; all_goals decide +kernel)

def tests (done : Nat → Prop) : Candidates :=
  ⟨HeadMatches (restriction (support done)) reg.constructors interp,
    fun d impl => ¬HeadMatches (restriction (support done)) reg.constructors interp d impl⟩

theorem election (done : Nat → Prop) : Elected beforeChoice reg interp (support done) (tests done) root impl := by
  refine ⟨ready done,?_,?_,⟨⟨List.mem_cons_self,rfl⟩,match_root done⟩,?_⟩
  · rintro (⟨a,_,cycle⟩|⟨_,_,_,_,_,_,_,_,_,a,_,cycle⟩)
    · exact acyclic a.lower cycle
    · exact acyclic a cycle
  · rintro ⟨other,⟨registered,role⟩,blocked⟩
    cases GeneralDeclarativeStableResult329.root_only other registered role
    exact blocked (match_root done)
  · rintro other ⟨⟨registered,role⟩,_⟩
    rw [GeneralDeclarativeStableResult329.root_only other registered role]

def attempt (done : Nat → Prop) : Attempt beforeChoice reg interp (support done) (tests done) root impl := by
  refine ⟨election done,spans,base,from_shape,?_⟩
  intro key seen
  change key ∈ [0,0] at seen
  have zero : key = 0 := by simpa using seen
  subst key
  exact ⟨_,List.mem_cons_self,rfl⟩

theorem actual_rejection (done : Nat → Prop) : RejectedByWrite (attempt done) :=
  ⟨⟨_,inhabits⟩,impossible⟩

end Yulang.GeneralDeclarativeStableRejected329
