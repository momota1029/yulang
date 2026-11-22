import Yulang.GeneralDeclarativeMixedSources339

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeMixedInputs339
open GeneralDeclarativeCompoundTree338
open GeneralDeclarativeCompoundInputs338 (models_back range)
open GeneralDeclarativeMixedTree339 (Node exact_tree)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeDemand320 (Bounds bounds_sound)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeGrowth327 (fits)
open GeneralDeclarativeClauseBatch327 (reflexive)
open GeneralDeclarativeWitnessHead334 (argument_sound)
open GeneralDeclarationPatterns (Pattern Constructors normalize normalizeArgs variablesArgs)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (All₂)

inductive Inputs {done : Nat → Prop} (c : Constructors) (i : Interpretation) (keep : List Nat) :
    World done → List Capture → List Pattern → World done → List Span → Prop where
  | nil : Inputs c i keep w [] [] w []
  | cons : Node c i keep w a (normalize p) mid first → Inputs c i keep mid as ps final rest →
      Inputs c i keep w (a::as) (p::ps) final (first++rest)

theorem input_exact (seen : Inputs c i keep w fields pats v spans) :
    Sound keep w v ∧ spans.map Prod.fst = variablesArgs (normalizeArgs pats) ∧
      ∀ u ∈ spans, Bounds v.state u.2 := by
  induction seen with
  | nil => exact ⟨identity _ _,rfl,fun _ h => False.elim (List.not_mem_nil h)⟩
  | cons one _ ih =>
    obtain ⟨earlier,a,first⟩ := exact_tree one
    obtain ⟨later,b,last⟩ := ih
    refine ⟨chain earlier later,by simp only [List.map_append,a,b,normalizeArgs,variablesArgs],?_⟩
    intro u h
    exact (List.mem_append.mp h).elim (fun f => fits later.1.1 (first u f)) (last u)

theorem initial_bound {w : World done} (seen : Node c i keep w a pat v spans) : Bounds w.state a := by
  cases seen with
  | binder fits => exact fits
  | record projected => exact projected.read.valid
  | projected old =>
    cases old with
    | named known => exact known.args
    | inline ready => exact ready
    | projected ready => exact ready

/-- An independently constructed mixed source derivation and each of
its genuine ordered captures are verified in the very same current
assignment. Imported approved-projection certificates remain tied to
their actual source model, not to an independently chosen assignment. -/
inductive Observed (c : Constructors) (i : Interpretation) (m : Assignment) : Capture → Pattern → Prop where
  | read {w v : World done} (source : Node c i keep w a (normalize p) v used) :
      fitsModel v m → range m a → (∀ u ∈ used, range m u.2) → Observed c i m a p

theorem observed (sources : Inputs c i keep w inputs pats v spans) (m : Assignment)
    (fit : fitsModel v m) : All₂ (Observed c i m) inputs pats := by
  induction sources with
  | nil => exact .nil
  | cons one rest ih =>
    have region := exact_tree one
    have output := models_back (input_exact rest).1.1 fit
    have input := models_back region.1.1 output
    exact .cons (.read one output (bounds_sound (initial_bound one) m input.1)
      (fun occ given => bounds_sound (region.2.2 occ given) m output.1)) (ih fit)

end Yulang.GeneralDeclarativeMixedInputs339
