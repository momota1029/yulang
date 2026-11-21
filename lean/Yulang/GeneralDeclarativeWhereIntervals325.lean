import Yulang.GeneralDeclarativeFreshWhere325
import Yulang.GeneralDeclarativeReadScope320

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWhereIntervals325
open GeneralDeclarations (DeclarationChecked)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture variables)
open GeneralDeclarativeBounds319 (Tracks bound_sound)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeClauseOrigins325 (Origin origin_reads)
open GeneralDeclarativeEqualities322 (semantic)
open GeneralDeclarativeSubstitution320 (logical logical_value)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralDeclarativeEntailment320 (model_append)
open GeneralDeclarativeSparseWhere325 (plan atPosition)
open GeneralDeclarativeFreshWhere325 (seed newState compound_reads projection)
open GeneralDeclarativeReadScope320 (tracked_from_declared_inputs)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralNominalExpressionIntervals237 (interval)
open GeneralDeclarationPatterns (normalize)
open CommonNominalFullCarrier (Subtype subtype_trans)
open GeneralNominalCommonBridge (Assignment)

def withInterval (s : State) (arg : Capture) : State :=
  ⟨⟨s.normal.ordinary,s.normal.intervals ++ [(arg.lower,arg.center),(arg.center,arg.upper)]⟩,s.equations⟩

theorem called_bounds (s : State) (arg : Capture) : Bounds (withInterval s arg) arg :=
  ⟨.interval (List.mem_append_right _ List.mem_cons_self),
    .interval (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩

theorem unchanged {s : State} {arg : Capture} (m : Assignment)
    (forced : Models s m → Subtype (m arg.lower).1 (m arg.center).1 ∧ Subtype (m arg.center).1 (m arg.upper).1) :
    Models (withInterval s arg) m ↔ Models s m := by
  constructor
  · intro valid
    exact ⟨⟨valid.1.1,fun link h => valid.1.2 link (List.mem_append_left _ h)⟩,valid.2⟩
  · intro valid
    have ok := forced valid
    refine ⟨⟨valid.1.1,?_⟩,valid.2⟩
    intro link h
    rcases List.mem_append.mp h with old|new
    · exact valid.1.2 link old
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at new
      rcases new with rfl|rfl
      · exact ok.1
      · exact ok.2

theorem semantic_bounds {s t : State} {cap : Nat → Capture} {arg : Capture}
    (tracked : Tracks s.normal cap code) (m : Assignment) (old : Models s m) (valid : Models t m)
    (lo : Origin t arg.lower (logical cap .lower code)) (center : Origin t arg.center (logical cap .actual code))
    (hi : Origin t arg.upper (logical cap .upper code)) :
    Subtype (m arg.lower).1 (m arg.center).1 ∧ Subtype (m arg.center).1 (m arg.upper).1 := by
  have low := semantic (origin_reads lo) m valid
  have mid := semantic (origin_reads center) m valid
  have high := semantic (origin_reads hi) m valid
  rw [logical_value] at low mid high
  have limits := interval (variables cap m) code
    (fun n used => ⟨bound_sound m old.1 (tracked n used).1,bound_sound m old.1 (tracked n used).2⟩)
  exact ⟨subtype_trans low.1 (subtype_trans limits.1 mid.2),
    subtype_trans mid.1 (subtype_trans limits.2 high.2)⟩

/-- For a genuinely compound operand emitted by the source, adding
explicit interval facts for its freshly defined triple is conservative.
It makes ordinary bounds available, not candidate-readiness or support
for an unfinished associated output. -/
theorem preserve_with_interval {s : State} {j : Nat}
    (check : DeclarationChecked c roles decl)
    (belongs : clause ∈ decl.requirements) (position : clause.arguments[j]? = some p)
    (decoded : codes[j]? = some code) (written : translate c i (normalize p) = some code)
    (needed : GeneralDeclarativeEmissionOperands322.Compound p)
    (captureRange : ∀ name ∈ decl.inputNames, Bounds s (cap name)) (protect : List Nat)
    (m : Assignment) :
    let jobs := plan clause.arguments codes
    let arg := atPosition (seed s protect cap jobs) jobs j
    let t := withInterval (newState s protect cap jobs) arg
    Bounds t arg ∧ (Models s m ↔
      ∃ next, Models t next ∧ ∀ n ∈ stateNames s ++ protect, next n = m n) := by
  dsimp
  refine ⟨called_bounds _ _,?_⟩
  have read := compound_reads s protect cap position decoded needed
  have tracked := tracked_from_declared_inputs check belongs (List.mem_of_getElem? position) written captureRange
  have now (next : Assignment) := unchanged next (fun model =>
    semantic_bounds tracked next ((model_append next).mp model).1 model read.1 read.2.1 read.2.2)
  constructor
  · intro valid
    obtain ⟨next,got,kept⟩ := (projection s protect cap _ m).mp valid
    exact ⟨next,(now next).mpr got,kept⟩
  · rintro ⟨next,got,kept⟩
    exact (projection s protect cap _ m).mpr ⟨next,(now next).mp got,kept⟩

end Yulang.GeneralDeclarativeWhereIntervals325
