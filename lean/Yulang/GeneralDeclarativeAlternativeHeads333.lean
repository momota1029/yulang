import Yulang.GeneralDeclarativeAlternativeReadComplete333
import Yulang.GeneralDeclarativeNestedMaterial332
import Yulang.GeneralDeclarativeInlineEndpoint331

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAlternativeHeads333
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarationPatterns (Constructors Pattern normalize)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarativeInlineEndpoint331 (Matches)
open GeneralDeclarativeAlternativeView333 (Index)
open GeneralDeclarativeAlternativeRead333 (normalized normalized_sound)
open GeneralDeclarativeAlternativeReadComplete333 (normalized_plan)
open GeneralDeclarativeAlternativeNeeds333 (Planned Eventually eventually_pair)
open CommonRoleOutermostResolver (All₂)

def endpoint (src : Index s) (depth : Nat) (c : Constructors) (i : Interpretation)
    : List Capture → List Pattern → Bool
  | [],[] => true
  | a::as,p::ps => !(normalized src depth c i .lower (.variable a.lower) p).isEmpty &&
      !(normalized src depth c i .upper (.variable a.upper) p).isEmpty &&
      endpoint src depth c i as ps
  | _,_ => false

theorem inhabited_list {x : α} (inList : x ∈ xs) : (!List.isEmpty xs) = true := by
  cases xs with
  | nil => cases inList
  | cons => rfl

theorem endpoint_plan {s : State} (fresh : All₂ (Matches s c i) args pats) :
    Planned (fun src : Index s =>
      Eventually (fun f => endpoint src f c i args pats = true)) := by
  induction fresh with
  | nil => exact Planned.pure fun _ => ⟨0,fun _ _ => rfl⟩
  | cons head tail ih =>
    obtain ⟨_,printedCode,lowSites,highSites,printed,low,high⟩ := head
    apply (((normalized_plan printed low).both (normalized_plan printed high)).both ih).map
    intro src arrived
    obtain ⟨min,ready⟩ := eventually_pair (eventually_pair arrived.1.1 arrived.1.2) arrived.2
    refine ⟨min,fun depth enough => ?_⟩
    have good := ready depth enough
    change (!_ && !_ && _) = true
    rw [inhabited_list good.1.1,inhabited_list good.1.2,good.2]
    rfl

theorem from_nonempty {xs : List α} (good : (!xs.isEmpty) = true) :
    ∃ v ∈ xs, True := by
  cases xs with
  | nil => cases good
  | cons x xs => exact ⟨x,List.mem_cons_self,trivial⟩

theorem endpoint_sound {s : State} (src : Index s)
    (bounds : ∀ a ∈ args, Bounds s a) (good : endpoint src f c i args pats = true) :
    All₂ (Matches s c i) args pats := by
  induction args generalizing pats with
  | nil =>
    cases pats with
    | nil => exact .nil
    | cons p ps => cases good
  | cons a as ih =>
    cases pats with
    | nil => cases good
    | cons p ps =>
      simp only [endpoint,Bool.and_eq_true] at good
      obtain ⟨l,seenL,_⟩ := from_nonempty good.1.1
      obtain ⟨u,seenU,_⟩ := from_nonempty good.1.2
      obtain ⟨printed,left,readL⟩ := normalized_sound seenL
      obtain ⟨other,right,readU⟩ := normalized_sound seenU
      cases Option.some.inj (right.symm.trans left)
      exact .cons ⟨bounds a List.mem_cons_self,printed,l,u,left,readL,readU⟩
        (ih (fun b found => bounds b (List.mem_cons_of_mem _ found)) good.2)

/-- Recognizes exactly the independently witnessed positive endpoint
relation when an appropriate finite packet and a sufficient depth
exist. None of this quantifies over success of unapproved diagnostics. -/
theorem endpoint_exact {s : State} (bounds : ∀ a ∈ args, Bounds s a) :
    All₂ (Matches s c i) args pats ↔
    ∃ memo : List (GeneralDeclarativeAlternativeNeeds333.Need s),
      Eventually (fun fuel => endpoint (GeneralDeclarativeAlternativeNeeds333.finiteIndex memo)
          fuel c i args pats = true) := by
  constructor
  · intro ready
    exact (endpoint_plan ready).finite
  · rintro ⟨index,fuel,works⟩
    exact endpoint_sound _ bounds (works fuel (Nat.le_refl _))

/-- Actual centers are a separate ordinary source judgment. They are
not implied by the two endpoint projections or by a candidate verdict. -/
def Center (p : Supported s done) (c : Constructors) (i : Interpretation)
    (arg : Capture) (pat : Pattern) : Prop :=
  Bounds s arg ∧ ∃ code sites, translate c i (normalize pat) = some code ∧
    Read (restriction p) .actual (.variable arg.center) code sites

def Centers (p : Supported s done) (c : Constructors) (i : Interpretation)
    (args : List Capture) (pats : List Pattern) : Prop :=
  All₂ (Center p c i) args pats

theorem center_bounds {s : State} {p : Supported s done} (reading : Centers p c i args pats) : ∀ a ∈ args, Bounds s a := by
  induction reading with
  | nil => intro a absent; cases absent
  | cons head tail ih =>
    intro a comes
    rcases List.mem_cons.mp comes with rfl|later
    · exact head.1
    · exact ih _ later

end Yulang.GeneralDeclarativeAlternativeHeads333
