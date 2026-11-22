import Yulang.GeneralDeclarativeStoppedRetarget341
import Yulang.GeneralDeclarativeStoppedPaired341

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStoppedOrdinal341
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralSourceState (Output)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeStoppedOutput339 (Receipt fixed_target)
open GeneralDeclarativeStoppedOrder339 (compileRequests checked_order)
open GeneralDeclarativeStoppedLeaf340 (committed receipt_holds)
open GeneralNominalVersionedMixedKernel234 (Step Installable)
open GeneralNominalSaturationState (Generated)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralDeclarativeStoppedPaired341 (Placement placement_targets)
open CommonRoleOutermostResolver (All₂)

theorem ordinal_aux {f : α → β → Prop} (paired : All₂ f xs ys) :
    ∀ (idx : Nat) (a : α) (b : β), xs[idx]? = some a → ys[idx]? = some b → f a b := by
  induction paired with
  | nil => intro idx a b missing _; simp at missing
  | @cons a b xs ys fHere _ tail =>
    intro idx x y gotX gotY
    cases idx with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at gotX gotY
      subst_vars
      exact fHere
    | succ n => exact tail n x y gotX gotY

/-- Positional rather than set-level. If the requests include two copies
of an output name, this theorem certifies each occurrence independently,
unchanged and without coalescing fixed output targets. -/
theorem at_ordinal {roles : Roles.RoleDecls} {s : State roles} {effect : Effect roles}
    {rows : List Equation} {idx : Nat} {output : Output} {row : Equation}
    (printed : compileRequests effect.plan (requests s.core effect.plan.packet.site.occurrence) = some rows)
    (atRequest : (requests s.core effect.plan.packet.site.occurrence)[idx]? = some output)
    (atRow : rows[idx]? = some row) :
    Receipt s effect output row ∧ row.left = output.target := by
  have wherePaired := (checked_order (s := s) (effect := effect) (fun _ h => h) printed).1
  have fact := ordinal_aux wherePaired idx output row atRequest atRow
  obtain ⟨body,which,found⟩ := fact.authored
  exact ⟨fact,fixed_target found⟩

/-- A positioned declarative request refers to precisely the same seen
alias-class request ordinal and fixed target. Only a genuine current
installable packet at an already stopped occurrence confers the model
witness; no artificial new journal install is introduced. -/
theorem placed_ordinal {roles : Roles.RoleDecls} {s : State roles} {e : Effect roles}
    {rows : List Equation} {idx : Nat} {output : Output} {row : Equation}
    {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}
    {view : GeneralDeclarativeHead320.State} {demand : GeneralDeclarativeDemand320.Demand}
    (place : Placement s view e.plan.packet.site.occurrence demand)
    (halt : ∀ next, ¬ Step registry root s next)
    (live : Generated s.core.erased.current root e.plan.packet.site.occurrence)
    (can : Installable registry s e)
    (printed : compileRequests e.plan demand.outputs = some rows)
    (atRequest : demand.outputs[idx]? = some output) (atRow : rows[idx]? = some row) :
    (requests s.core e.plan.packet.site.occurrence)[idx]? = some output ∧ row.left = output.target ∧
      ∀ m, Models s m → GeneralDeclarativeEntailment320.Holds m row := by
  have exact := placement_targets place
  have seen := at_ordinal (effect := e) (exact ▸ printed) (exact ▸ atRequest) atRow
  refine ⟨exact ▸ atRequest,seen.2,?_⟩
  intro m valid
  exact receipt_holds ((committed halt live can).1 m valid).2 seen.1

end Yulang.GeneralDeclarativeStoppedOrdinal341
