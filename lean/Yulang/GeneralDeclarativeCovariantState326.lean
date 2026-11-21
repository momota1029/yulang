import Yulang.GeneralDeclarativePairDecl326
import Yulang.GeneralDeclarativeOutputOrigins323

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCovariantState326
open GeneralDeclarativePairDecl326 (rootArg leftArg rightArg)
open GeneralDeclarativePairCenters326 (pair project_first coordinate_ranges)
open GeneralDeclarativePairNames326 (Span)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeOutputOrigins323 (emit)
open GeneralDeclarativeEntailment320 (appendFacts model_append)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralDeclarativeRepeat320 (int int_top top_not_int)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty Equivalent subtype_refl common_pair_iff)

abbrev lo : Expr := pair (.variable 3) (.variable 3)
abbrev hi : Expr := pair (.variable 4) (.variable 4)
abbrev actual : Expr := pair (.variable 7) (.variable 8)
abbrev projected : Expr := pair (.variable 1) (.variable 3)
abbrev exposed : Expr := pair actual (.variable 3)
abbrev sourceRows : List Equation :=
  [⟨0,lo⟩,⟨2,hi⟩,⟨3,.primitive (.scalar .int) []⟩,⟨11,projected⟩,⟨11,exposed⟩]
abbrev parentRow : Equation := ⟨6,.variable 5⟩
abbrev childRow : Equation := ⟨5,.variable 7⟩
abbrev intervals : List (Nat × Nat) := [(0,1),(1,2),(3,7),(7,4),(3,8),(8,4)]
abbrev initial : State := ⟨⟨[],intervals⟩,sourceRows⟩
abbrev middle := appendFacts initial [parentRow]
abbrev final := appendFacts middle [childRow]

def support0 (done : Nat → Prop) : Supported initial done :=
  ⟨fun row origin => row ∈ sourceRows ∧ origin = .source,fun f => f.1⟩
abbrev support1 (done : Nat → Prop) := emit (support0 done) 1 [parentRow]
abbrev support2 (done : Nat → Prop) := emit (support1 done) 2 [childRow]

theorem old_row {row : Equation} (known : row ∈ sourceRows) : row ∈ final.equations :=
  List.mem_append_left _ (List.mem_append_left _ known)

theorem authorized (done : Nat → Prop) {row : Equation} (known : row ∈ sourceRows) :
    row ∈ (restriction (support2 done)).equations := from_source _ (.inl (.inl ⟨known,rfl⟩))

theorem no_direct_center : ¬ ∃ e, (⟨1,e⟩ : Equation) ∈ final.equations := by
  rintro ⟨e,known⟩
  simp only [final,middle,appendFacts,sourceRows,List.cons_append,List.nil_append,List.mem_cons,
    List.not_mem_nil,or_false] at known
  rcases known with h|h|h|h|h|h|h <;> have wrong := congrArg Equation.left h <;> cases wrong

theorem center : Derives final (.variable 1) actual :=
  project_first (host := 11) (spare := .variable 3) (second := .variable 3)
    (.row (old_row (by simp [sourceRows])))
    (.row (old_row (by simp [sourceRows])))

theorem low : Derives final (.variable 0) lo := .row (old_row List.mem_cons_self)
theorem high : Derives final (.variable 2) hi := .row (old_row (by simp [sourceRows]))
theorem root_range : Bounds final rootArg :=
  ⟨.interval (by change _ ∈ intervals; simp [intervals]),.interval (by change _ ∈ intervals; simp [intervals])⟩
theorem left_range : Bounds final leftArg :=
  ⟨.interval (by change _ ∈ intervals; simp [intervals]),.interval (by change _ ∈ intervals; simp [intervals])⟩
theorem right_range : Bounds final rightArg :=
  ⟨.interval (by change _ ∈ intervals; simp [intervals]),.interval (by change _ ∈ intervals; simp [intervals])⟩

abbrev firstValue (swap : Bool) : Ty := if swap then .top else int
abbrev lastValue (swap : Bool) : Ty := if swap then int else .top
abbrev middleType (swap : Bool) := CommonNominalFullCarrier.pair (firstValue swap) (lastValue swap)
def assignment (swap : Bool) : Assignment := fun n =>
  (if n = 0 then CommonNominalFullCarrier.pair int int else
   if n = 1 then middleType swap else if n = 2 then CommonNominalFullCarrier.pair .top .top else
   if n = 4 then .top else if n = 11 then CommonNominalFullCarrier.pair (middleType swap) int else
   if n = 5 ∨ n = 6 ∨ n = 7 then firstValue swap else if n = 8 then lastValue swap else int,Common.rowEmpty)

theorem initial_models (swap : Bool) : Models initial (assignment swap) := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,?_⟩,?_⟩
  · intro sp hit
    change sp ∈ intervals at hit
    simp only [intervals,List.mem_cons,List.not_mem_nil,or_false] at hit
    rcases hit with rfl|rfl|rfl|rfl|rfl|rfl
    · cases swap
      · exact (common_pair_iff ..).mpr ⟨subtype_refl _,int_top⟩
      · exact (common_pair_iff ..).mpr ⟨int_top,subtype_refl _⟩
    · cases swap
      · exact (common_pair_iff ..).mpr ⟨int_top,subtype_refl _⟩
      · exact (common_pair_iff ..).mpr ⟨subtype_refl _,int_top⟩
    · cases swap
      · exact subtype_refl _
      · exact int_top
    · cases swap
      · exact int_top
      · exact subtype_refl _
    · cases swap
      · exact int_top
      · exact subtype_refl _
    · cases swap
      · exact subtype_refl _
      · exact int_top
  · intro row known
    change row ∈ sourceRows at known
    simp only [sourceRows,List.mem_cons,List.not_mem_nil,or_false] at known
    rcases known with rfl|rfl|rfl|rfl|rfl <;> exact eqv_refl _

theorem models (swap : Bool) : Models final (assignment swap) := by
  apply (model_append _).mpr
  refine ⟨(model_append _).mpr ⟨initial_models swap,?_⟩,?_⟩
  all_goals
    intro row known
    cases List.mem_singleton.mp known
    exact eqv_refl _

theorem no_substitute_end (swap : Bool) :
    ¬ Equivalent ((assignment swap) 1).1 ((assignment swap) 0).1 ∧
      ¬ Equivalent ((assignment swap) 1).1 ((assignment swap) 2).1 := by
  constructor
  · intro e
    cases swap
    · exact top_not_int ((common_pair_iff ..).mp e.1).2
    · exact top_not_int ((common_pair_iff ..).mp e.1).1
  · intro e
    cases swap
    · exact top_not_int ((common_pair_iff ..).mp e.2).1
    · exact top_not_int ((common_pair_iff ..).mp e.2).2

end Yulang.GeneralDeclarativeCovariantState326
