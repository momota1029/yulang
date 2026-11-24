import Yulang.GeneralDeclarativeI65CompletionRead383
import Yulang.GeneralDeclarativeLowerKnown321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarativeHead320 (Equation Models)
open GeneralDeclarativeLowerKnown321 (Tag Knows constructorTag)
open GeneralDeclarativeBounds319 (Bound)

abbrev OrdinarySupport383 (rules : SelectedSourceRule383)
    (direct : DirectEquation383) (generated : LogicalOutputEquation383)
    (s : State) (row : Equation) : Prop :=
  Nonempty (SourceEquationRead383 rules direct generated s row)

theorem finite_supported_row_is_current383
    {rules direct generated s row}
    (h : OrdinarySupport383 rules direct generated s row) :
    row ∈ s.current.ordinary.equations := by
  obtain ⟨read⟩ := h
  cases read with
  | written _ actual => exact actual
  | output _ _ _ _ _ actual => exact actual

/-- Row support restricts only ordinary constructor and alias reads.
Normal bounds and the original ordinary graph are left alone. In
particular this is not the graph used for either form of K2. -/
noncomputable def finiteOrdinaryView383 (rules : SelectedSourceRule383)
    (direct : DirectEquation383) (generated : LogicalOutputEquation383)
    (s : State) : GeneralDeclarativeHead320.State := by
  classical
  exact ⟨s.current.ordinary.normal,s.current.ordinary.equations.filter fun row =>
    decide (OrdinarySupport383 rules direct generated s row)⟩

theorem finite_ordinary_row_exact383 {rules direct generated s row} :
    row ∈ (finiteOrdinaryView383 rules direct generated s).equations ↔
      OrdinarySupport383 rules direct generated s row := by
  classical
  simp only [finiteOrdinaryView383,List.mem_filter,decide_eq_true_eq]
  exact ⟨And.right,fun h => ⟨finite_supported_row_is_current383 h,h⟩⟩

theorem finite_ordinary_models_restrict383 {rules direct generated s m}
    (fit : Models s.current.ordinary m) :
    Models (finiteOrdinaryView383 rules direct generated s) m :=
  ⟨fit.1,fun row present => fit.2 row
    (finite_supported_row_is_current383 (finite_ordinary_row_exact383.mp present))⟩

/-- Bounds remain the same. Every explicit alias row on the path,
not merely the final revealing row, has finite logical support. The
recursive call here is on proof structure, not solver execution. -/
inductive LogicalAlias383 (rules : SelectedSourceRule383)
    (direct : DirectEquation383) (generated : LogicalOutputEquation383) (s : State) :
    Nat → Nat → Prop where
  | bounds : Bound s.current.ordinary.normal a b → Bound s.current.ordinary.normal b a →
      LogicalAlias383 rules direct generated s a b
  | forward : OrdinarySupport383 rules direct generated s ⟨a,.variable b⟩ →
      LogicalAlias383 rules direct generated s a b
  | backward : OrdinarySupport383 rules direct generated s ⟨b,.variable a⟩ →
      LogicalAlias383 rules direct generated s a b
  | trans : LogicalAlias383 rules direct generated s a b → LogicalAlias383 rules direct generated s b c →
      LogicalAlias383 rules direct generated s a c

theorem logical_alias_matches_supported_ordinary383 {rules direct generated s a b} :
    LogicalAlias383 rules direct generated s a b ↔ GeneralDeclarativeLowerKnown321.Alias (finiteOrdinaryView383 rules direct generated s) a b := by
  constructor
  · intro path
    induction path with
    | bounds lo hi => exact .bounds lo hi
    | forward e => exact .forward (finite_ordinary_row_exact383.mpr e)
    | backward e => exact .backward (finite_ordinary_row_exact383.mpr e)
    | trans _ _ l r => exact .trans l r
  · intro path
    induction path with
    | bounds lo hi => exact .bounds lo hi
    | forward e => exact .forward (finite_ordinary_row_exact383.mp e)
    | backward e => exact .backward (finite_ordinary_row_exact383.mp e)
    | trans _ _ l r => exact .trans l r

def LogicalKnows383 (rules : SelectedSourceRule383)
    (direct : DirectEquation383) (generated : LogicalOutputEquation383)
    (s : State) (name : Nat) (tag : Tag) : Prop :=
  ∃ row, OrdinarySupport383 rules direct generated s row ∧
    LogicalAlias383 rules direct generated s name row.left ∧ constructorTag row.right = some tag

theorem logical_knows_matches_supported_ordinary383 {rules direct generated s name tag} :
    LogicalKnows383 rules direct generated s name tag ↔
      Knows (finiteOrdinaryView383 rules direct generated s) name tag := by
  constructor
  · rintro ⟨row,present,link,shape⟩
    exact ⟨row,finite_ordinary_row_exact383.mpr present,
      logical_alias_matches_supported_ordinary383.mp link,shape⟩
  · rintro ⟨row,present,link,shape⟩
    exact ⟨row,finite_ordinary_row_exact383.mp present,
      logical_alias_matches_supported_ordinary383.mpr link,shape⟩

/-- Existing revealed ordinary-root fragment uses this exact lower read.
This is *not* all mixed/native readiness, nor an all-visible candidate
judgment. An original ordinary K2 still vetoes this fragment even when
every lower already has finite supported readback. -/
def LogicalOrdinaryRootReady383 (rules : SelectedSourceRule383)
    (direct : DirectEquation383) (generated : LogicalOutputEquation383)
    (s : State) (q : Request) : Prop :=
  ∀ arg ∈ q.demand.arguments, ∃ tag, LogicalKnows383 rules direct generated s arg.lower tag

theorem ordinary_logical_root_readiness_exact383 {rules direct generated s q} :
    LogicalOrdinaryRootReady383 rules direct generated s q ↔
      ∀ arg ∈ q.demand.arguments, ∃ tag, Knows (finiteOrdinaryView383 rules direct generated s) arg.lower tag := by
  constructor
  · intro ready arg found
    obtain ⟨tag,known⟩ := ready arg found
    exact ⟨tag,logical_knows_matches_supported_ordinary383.mp known⟩
  · intro ready arg found
    obtain ⟨tag,known⟩ := ready arg found
    exact ⟨tag,logical_knows_matches_supported_ordinary383.mpr known⟩

theorem original_root_k2_vetoes_logical_ordinary_ready383 {rules direct generated s q result}
    (cycle : RootCycle383 s q)
    (entry : RootEntry383 s q (LogicalOrdinaryRootReady383 rules direct generated s q) result) :
    result = .rootK2 := root_k2_precedes_unready_input383 cycle entry

end Yulang.GeneralDeclarativeI65
