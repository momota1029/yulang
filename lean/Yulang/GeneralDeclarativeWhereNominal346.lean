import Yulang.GeneralDeclarativeWherePairView346
import Yulang.GeneralStoppedShape335

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWhereNominal346
open GeneralNominalState (State Models Descriptor)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralDictionaryBinderLocations (sourceSlot sourceSlot_exact)
open GeneralStoppedShape335 (point descriptorExpr descriptor_semantics)
open GeneralDeclarativeHead320 (environment)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedExpressionFrame236 (variableSource)
open GeneralNominalVersionedPlans231 (variables)
open GeneralWhereOriginDelta318 (Cell)
open GeneralNominalCenters (Plan)
open GeneralDeclarativeRawCapture344 (rawCap by_mode)
open GeneralDeclarativeSubstitution320 (logical logicals)
open GeneralDeclarativeWhereAttributed346 (literal model_exact)
open GeneralDeclarativeEntailment320 (Holds)
open CommonNominalFullCarrier (Equivalent)

def scan (s : State) (target key : Nat) (names : List Nat) : Option (Fin s.base.slots) := do
  let root ← sourceSlot s.base target
  let d ← s.nominals root
  let physical ← point d.arguments
  let inputs ← names.mapM (sourceSlot s.base)
  if d.declaration.name = key ∧ physical = inputs then some root else none

private theorem names_exact (s : State) (names : List Nat) {ks : List (Fin s.base.slots)}
    (located : names.mapM (sourceSlot s.base) = some ks) :
    ks.map s.base.source = names := by
  induction names generalizing ks with
  | nil =>
    have same : [] = ks := Option.some.inj located
    subst ks; rfl
  | cons first rest ih =>
    simp only [List.mapM_cons] at located
    obtain ⟨i,head,later⟩ := Option.bind_eq_some_iff.mp located
    obtain ⟨js,tail,eq⟩ := Option.bind_eq_some_iff.mp later
    have same : i::js = ks := Option.some.inj eq
    subst ks
    simp [(sourceSlot_exact ..).mp head,ih tail]

/-- Invariant nominal syntax is read through an actual registered
point descriptor, never through a fabricated TyTerm equality. The
scan checks the exact ordered physical argument names. -/
theorem observed {s : State} {target key : Nat} {names : List Nat} {slot : Fin s.base.slots}
    (ready : scan s target key names = some slot) (m : Assignment) (fit : Models s m) :
    Equivalent (m target).1 (value (environment m) .actual (.nominal key (names.map Expr.variable))) := by
  unfold scan at ready
  obtain ⟨root,atRoot,next⟩ := Option.bind_eq_some_iff.mp ready
  obtain ⟨d,stored,rest⟩ := Option.bind_eq_some_iff.mp next
  obtain ⟨ks,pointwise,ends⟩ := Option.bind_eq_some_iff.mp rest
  obtain ⟨inputs,positions,test⟩ := Option.bind_eq_some_iff.mp ends
  split at test
  · rename_i checked
    have namesEq := names_exact s names positions
    have printed : descriptorExpr s.base d = some (.nominal key (names.map Expr.variable)) := by
      simp [descriptorExpr,pointwise,checked.1,checked.2,List.map_map,← namesEq,Function.comp_def]
    have node := (descriptor_semantics s.base root d m printed).mp (fit.2.1 root d stored)
    rwa [(sourceSlot_exact ..).mp atRoot] at node
  · cases test

private theorem arguments (p : Plan rs) (ids : List Nat) :
    logicals (rawCap p) .actual (ids.map Expr.variable) =
      (ids.map (variableSource p .actual)).map Expr.variable := by
  induction ids with
  | nil => rfl
  | cons a as ih => simp [logicals,logical,by_mode,ih]

theorem actual_cell {p : Plan rs} (c : Cell p) (s : State) (key : Nat) (ids : List Nat)
    (shape : c.expression = .nominal key (ids.map Expr.variable))
    {slot : Fin s.base.slots}
    (ready : scan s c.row.target key (ids.map (variableSource p .actual)) = some slot)
    (m : Assignment) (fit : Models s m) : c.row.Holds (variables p m) m := by
  apply (model_exact c m).mp
  change Equivalent (m c.row.target).1
    (value (environment m) .actual (logical (rawCap p) c.side.mode c.expression))
  rw [shape]
  change Equivalent (m c.row.target).1 (value (environment m) .actual
    (.nominal key (logicals (rawCap p) .actual (ids.map Expr.variable))))
  rw [arguments]
  exact observed ready m fit

end Yulang.GeneralDeclarativeWhereNominal346
