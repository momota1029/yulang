import Yulang.CommonEffectFreshRows
import Yulang.CommonEffectRecursiveExact
import Yulang.AnnotationSnapshots

/-! Finite annotation syntax and its two boundary uses. Omission hides
incoming callback effects and adds no positive check. Explicit lists expose
only their keys; glob exposes all. Positive checks freeze only the concrete
visible row at the supplied completed inference boundary. This module does
not claim that source/SCC inference has reached that boundary. -/
namespace Yulang.CommonEffectAnnotations
open CommonEffectRequestGeneration (Permission Computation RowExpr)
open CommonEffectFormula (Formula)

inductive Annotation where
  | omitted
  | glob
  | only : List Nat → Annotation
  deriving DecidableEq, Repr

def Annotation.incoming : Annotation → Permission
  | .omitted => .only []
  | .glob => .all
  | .only keys => .only keys

def Annotation.positive : Annotation → Option Permission
  | .omitted => none
  | .glob => some .all
  | .only keys => some (.only keys)

inductive Permits : Annotation → Nat → Prop where
  | glob (key : Nat) : Permits .glob key
  | only : key ∈ keys → Permits (.only keys) key

theorem incoming_exact (annotation : Annotation) (key : Nat) :
    annotation.incoming.allows key = true ↔ Permits annotation key := by
  cases annotation with
  | omitted =>
    constructor
    · simp [Annotation.incoming, Permission.allows]
    · intro h; cases h
  | glob => exact ⟨fun _ => .glob key, fun _ => rfl⟩
  | only keys =>
    constructor
    · intro h
      exact .only (by simpa [Annotation.incoming, Permission.allows] using h)
    · intro h
      cases h with | only member => simpa [Annotation.incoming, Permission.allows] using member

theorem permission_capture_exact (annotation : Annotation) (key : Nat) :
    Permits annotation key ↔ ∃ occurrence : Common.Occurrence, occurrence.1 = key ∧
      CommonSignedRows.Capturable [key] (CommonEffectFreshRows.enterOccurrence annotation.incoming occurrence) := by
  rw [← incoming_exact]
  constructor
  · intro allowed
    exact ⟨(key, []), rfl, (CommonEffectFreshRows.enter_capture_iff _ _ _).mpr
      ⟨by simp [CommonSignedRows.Capturable], allowed⟩⟩
  · rintro ⟨occurrence, same, captured⟩
    simpa only [same] using ((CommonEffectFreshRows.enter_capture_iff _ _ _).mp captured).2

def translated : RowExpr scopes α → RowInference.RowExpr Nat (Fin scopes) α
  | .var name => .var name
  | .empty => .empty
  | .head key => .head key
  | .union first last => .union (translated first) (translated last)
  | .protect scope permission body => .protect scope permission.allows (translated body)
  | .release scope permission body => .release scope permission.allows (translated body)
  | .residual keys body => .residual keys (translated body)

theorem translated_exact (row : RowExpr scopes α) (assignment : α → Computation) :
    (translated row).eval (CommonSignedRows.commonAlgebra scopes) (fun name => (assignment name).2) = row.eval assignment := by
  induction row <;> simp_all only [translated, RowInference.RowExpr.eval, RowExpr.eval]
  all_goals rfl

def known (row : RowExpr scopes α) : Directed.Row scopes Nat :=
  (translated row).eval (RowInference.signedAlgebra scopes Nat) (fun _ => [])

theorem known_meaning (row : RowExpr scopes α) :
    CommonSignedRows.embedRow (known row) = row.eval (fun _ => Core.PresenceGeneration.Comp.pure Common.model (.base .unit)) := by
  rw [known, CommonSignedRows.rowExpr_interpretation_exact]
  have same : (fun _ : α => CommonSignedRows.embedRow ([] : Directed.Row scopes Nat)) =
      (fun name => ((fun _ : α => Core.PresenceGeneration.Comp.pure Common.model (.base .unit)) name).2) := by
    funext name
    exact CommonSignedRows.embedRow_empty
  rw [same]
  exact translated_exact row _

structure Frozen (scopes : Nat) where
  annotation : Annotation
  concrete : Directed.Row scopes Nat

def freeze (annotation : Annotation) (row : RowExpr scopes α) : Frozen scopes := ⟨annotation, known row⟩

def Frozen.check (snapshot : Frozen scopes) : Bool :=
  match snapshot.annotation.positive with
  | none => true
  | some permission => AnnotationSnapshots.Observation.check ⟨permission.allows, snapshot.concrete⟩

def Frozen.Admissible (snapshot : Frozen scopes) : Prop :=
  ∀ occurrence ∈ snapshot.concrete, AnnotationSnapshots.Visible occurrence →
    ∀ permission, snapshot.annotation.positive = some permission → permission.allows occurrence.key = true

theorem Frozen.check_exact (snapshot : Frozen scopes) : snapshot.check = true ↔ snapshot.Admissible := by
  cases found : snapshot.annotation.positive with
  | none => simp [Frozen.check, Frozen.Admissible, found]
  | some permission =>
    simp [Frozen.check, found, AnnotationSnapshots.Observation.check_exact,
      AnnotationSnapshots.Observation.Admissible, Frozen.Admissible]

def Frozen.CommonAdmissible (snapshot : Frozen scopes) : Prop :=
  ∀ occurrence, CommonSignedRows.embedRow snapshot.concrete occurrence →
    (∀ weight ∈ occurrence.2, weight = 0) →
    ∀ permission, snapshot.annotation.positive = some permission → permission.allows occurrence.1 = true

theorem visible_encode (occurrence : Directed.Occurrence scopes Nat) :
    (∀ weight ∈ (CommonSignedRows.encodeOccurrence occurrence).2, weight = 0) ↔ AnnotationSnapshots.Visible occurrence := by
  constructor
  · intro visible scope
    exact visible (occurrence.weights scope) (List.mem_ofFn.mpr ⟨scope, rfl⟩)
  · intro visible weight member
    obtain ⟨scope, same⟩ := List.mem_ofFn.mp member
    exact same ▸ visible scope

theorem Frozen.common_exact (snapshot : Frozen scopes) : snapshot.Admissible ↔ snapshot.CommonAdmissible := by
  constructor
  · intro valid occurrence member visible permission boundary
    obtain ⟨original, member, rfl⟩ := member
    exact valid original member ((visible_encode original).mp visible) permission boundary
  · intro valid occurrence member visible permission boundary
    exact valid (CommonSignedRows.encodeOccurrence occurrence) ⟨occurrence, member, rfl⟩
      ((visible_encode occurrence).mpr visible) permission boundary

def Frozen.emit (snapshot : Frozen scopes) (formula : Formula scopes α) : Formula scopes α :=
  if snapshot.check then formula else .core .bot

theorem Frozen.emit_exact (snapshot : Frozen scopes) (formula : Formula scopes α) (assignment : α → Computation) :
    (snapshot.emit formula).Holds assignment ↔ snapshot.CommonAdmissible ∧ formula.Holds assignment := by
  rw [← snapshot.common_exact, ← snapshot.check_exact]
  cases checked : snapshot.check <;> simp [Frozen.emit, checked, Formula.Holds, Core.PresenceGeneration.Formula.Holds]

theorem Frozen.emit_subst (snapshot : Frozen scopes) (formula : Formula scopes α) (substitution : α → Core.PresenceGeneration.CompTerm β) :
    (snapshot.emit formula).subst substitution = snapshot.emit (formula.subst substitution) := by
  cases checked : snapshot.check <;> simp [Frozen.emit, checked, Formula.subst, Core.PresenceGeneration.Formula.subst]

/-- Later instantiation changes the scheme, while the completed observation
is already discharged and contributes no new parameter condition. -/
theorem Frozen.later_instantiation (snapshot : Frozen scopes) (accepted : snapshot.check = true)
    (formula : Formula scopes α) (substitution : α → Core.PresenceGeneration.CompTerm β) (assignment : β → Computation) :
    ((snapshot.emit formula).subst substitution).Holds assignment ↔
      formula.Holds (fun name => (substitution name).eval Common.model assignment) := by
  simp only [Frozen.emit, accepted, ↓reduceIte, Formula.holds_subst]
end Yulang.CommonEffectAnnotations
