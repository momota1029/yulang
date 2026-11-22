import Yulang.GeneralDeclarativeNestedSeekCases332

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNestedNegative332
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeNestedClash332 (Apart pairExpr from_lower)
open GeneralDeclarativeRecordPayloads330 (Field)
open GeneralDeclarativeRecordSpine330 (Terminal)
open GeneralDeclarativeNestedTail332 (peel exact_peel isTerminal)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeNestedView332 (Sources)
open GeneralDeclarativeRepeatedActual323 (eqAt)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarationPatterns (normalize)
open CommonRoleCanonicalRows (Row lookup)

theorem visible_field (showsField : lookup key fields = some content) : Field key fields content := by
  induction fields with
  | nil => cases showsField
  | cons first tail ih =>
    rcases first with ⟨label,raw⟩
    by_cases same : label = key
    · subst label
      have e : raw = content := by simpa [lookup] using showsField
      cases e
      exact .here
    · have notSame : key ≠ label := Ne.symm same
      exact .later same (ih (by simpa [lookup,same,notSame] using showsField))

def inspectField (key : Nat) (fields : Row Expr) : Option { e : Expr // Field key fields e } :=
  match seen : lookup key fields with
  | none => none
  | some e => some ⟨e,visible_field seen⟩

abbrev Certificate (raw wanted : Expr) := PLift (Apart raw wanted)

/-- Negative record evidence is searched only in required visible fields,
and only for a literal confirmed lower terminal. The recursive callback
is over payloads at exactly the same field, not every raw mention. -/
def inspectFields (raw wanted : Expr)
    (recur : ∀ a b, Option (Certificate a b)) : Option (Certificate raw wanted) := do
  let left := (peel raw).1
  let stop := (peel raw).2
  let right := (peel wanted).1
  let endWant := (peel wanted).2
  let ended ← isTerminal stop
  let cert ← (right.map Prod.fst).findSome? fun k => do
    let required ← inspectField k right
    match read : lookup k left with
    | none => pure (PLift.up (Apart.missing (wantTail := endWant) ended.down read required.property))
    | some a =>
      (recur a required.val).map fun nested =>
        PLift.up (Apart.field (leftTail := stop) (rightTail := endWant)
          (visible_field read) required.property nested.down)
  pure ⟨by
    rw [← exact_peel raw,← exact_peel wanted]
    exact cert.down⟩

/-- A positive certificate on a subset of finite structural cases.
None is not the opposite diagnosis, and this budget is not part of
selection semantics. Open/opaque records cannot produce a missing
field certificate from an unconfirmed terminal. -/
def detect : (fuel : Nat) → (raw wanted : Expr) → Option (Certificate raw wanted)
  | 0, _, _ => none
  | fuel+1, raw, wanted =>
    match raw,wanted with
    | .primitive .pair [a,x], .primitive .pair [b,y] =>
      ((detect fuel a b).map fun hit => PLift.up (.first (x := x) (y := y) hit.down)).or
        ((detect fuel x y).map fun hit => PLift.up (.second (x := a) (y := b) hit.down))
    | .variant t a,.variant u b =>
      if same : t = u then
        (detect fuel a b).map fun hit => PLift.up (same ▸ Apart.tagged (key := t) hit.down)
      else none
    | raw,wanted => inspectFields raw wanted (detect fuel)

/-- Only proved ordinary source rows from an authorized alias are used
for the lower obstruction. The normalized printed target is exposed. -/
theorem actual_obstruction {s : State} {p : Supported s done}
    (src : Sources (restriction p)) (box : Bounds s arg)
    (printed : translate c i (normalize pat) = some wanted)
    (opened : src.visible arg.lower = some raw) (detected : (detect fuel raw wanted).isSome = true)
    (m) (fit : Models s m) :
    ∃ wanted, translate c i (normalize pat) = some wanted ∧
      ¬eqAt m (.variable arg.center) wanted := by
  obtain ⟨owner,link,stored⟩ := src.authorized arg.lower raw opened
  obtain ⟨hit,_⟩ := Option.isSome_iff_exists.mp detected
  exact ⟨wanted,printed,from_lower (p := p) box (.trans (.congruent (.variable link)) (.row stored))
    hit.down m fit⟩

end Yulang.GeneralDeclarativeNestedNegative332
