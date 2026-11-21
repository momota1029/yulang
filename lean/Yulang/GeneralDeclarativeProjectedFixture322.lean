import Yulang.GeneralDeclarativeProjectedLower322
import Yulang.GeneralDeclarativeRepeat320

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeProjectedFixture322
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeOrigins321 (Origin Available Supported)
open GeneralDeclarativeNormalSupport321 (NormalSupport observed)
open GeneralDeclarativeProjectedLower322 (Exposed pair_first_head)
open GeneralDeclarativeEqualities322 (Derives entails)
open GeneralDeclarativeLowerKnown321 (Tag)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeRepeat320 (int top_not_int)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open CommonNominalFullCarrier (pair)

abbrev left : Equation := ⟨0,.primitive .pair [.variable 1,.variable 3]⟩
abbrev right : Equation := ⟨0,.primitive .pair [.variable 2,.variable 3]⟩
abbrev scalar : Equation := ⟨2,.primitive (.scalar .int) []⟩
abbrev s : State := ⟨⟨[],[]⟩,[left,right,scalar]⟩
abbrev intTag : Tag := .primitive (.scalar .int) 0

def bases (row : Equation) (o : Origin) : Prop :=
  ((row = left ∨ row = scalar) ∧ o = .source) ∨ (row = right ∧ o = .output 8)

def support (completed : Nat → Prop) : NormalSupport s completed where
  eq := ⟨bases,by
    intro row origin h
    rcases h with ⟨rfl|rfl,_⟩|⟨rfl,_⟩ <;> simp⟩
  atomFrom := fun _ _ => False
  spanFrom := fun _ _ => False
  ordinary_atom := fun h => False.elim h
  ordinary_span := fun h => False.elim h

theorem eq_support (completed) :
    (observed (support completed)).equations =
      (GeneralDeclarativeOrigins321.restriction (support completed).eq).equations := rfl

theorem ready (completed : Nat → Prop) (finished : completed 8) :
    Exposed (observed (support completed)) 1 intTag := by
  have low : left ∈ (observed (support completed)).equations :=
    GeneralDeclarativeOrigins321.from_source (support completed).eq (.inl ⟨.inl rfl,rfl⟩)
  have high : right ∈ (observed (support completed)).equations :=
    GeneralDeclarativeOrigins321.from_completed (support completed).eq (.inr ⟨rfl,rfl⟩) finished
  have integer : scalar ∈ (observed (support completed)).equations :=
    GeneralDeclarativeOrigins321.from_source (support completed).eq (.inl ⟨.inr rfl,rfl⟩)
  exact pair_first_head (.row low) (.row high) (.refl _) (.row integer) rfl

def model (narrow : Bool) : Assignment := fun n =>
  (if n = 0 then pair (if narrow then int else .top) int
    else if n = 1 then if narrow then int else .top else int, Common.rowEmpty)

theorem ordinary_nonempty : Models s (model true) := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,by intro _ none; cases none⟩,?_⟩
  intro eq used
  change eq ∈ [left,right,scalar] at used
  simp only [List.mem_cons,List.not_mem_nil,or_false] at used
  rcases used with rfl|rfl|rfl <;> exact eqv_refl _

theorem unfinished_allows_broad (completed : Nat → Prop) (pending : ¬completed 8) :
    Models (observed (support completed)) (model false) := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro atom h
    obtain ⟨_,bad,_⟩ := (GeneralDeclarativeNormalSupport321.atom_iff _ _).mp h
    cases bad
  · intro span h
    obtain ⟨_,bad,_⟩ := (GeneralDeclarativeNormalSupport321.span_iff _ _).mp h
    cases bad
  · intro eq listed
    rw [eq_support] at listed
    obtain ⟨origin,path,available⟩ := (GeneralDeclarativeOrigins321.backed_iff _ _).mp listed
    rcases path with ⟨rfl|rfl,_⟩|⟨rfl,rfl⟩
    · exact eqv_refl _
    · exact eqv_refl _
    · cases available with
      | completed found => exact False.elim (pending found)

/-- Its exact scalar lower-head proof cannot use the pending output, even
though the ordinary equation was retained and is true in the full state. -/
theorem pending_cannot_project_scalar (completed : Nat → Prop) (pending : ¬completed 8) :
    ¬Derives (observed (support completed)) (.variable 1) (.primitive (.scalar .int) []) := by
  intro proof
  have forced := entails proof (model false) (unfinished_allows_broad completed pending)
  exact top_not_int forced.1

end Yulang.GeneralDeclarativeProjectedFixture322
