import Yulang.GeneralDeclarativeWitnessRecordResidual359
import Yulang.GeneralDeclarativeCompoundOpenFixture338

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessOpenSpine359
open CommonNominalFullCarrier (Ty Equivalent Subtype subtype_trans record)
open CommonRoleCanonicalRows (Row)
open GeneralDeclarativeHead320 (Equation State Models environment)
open GeneralDeclarativeWitnessAuthoredProjection358 (Source)
open GeneralDeclarativeRecordResidual323 (withTail prefix_congr)
open GeneralDeclarativeRepeatedActual323 (eqAt)
open GeneralDeclarativeBounds319 (Bound bound_sound)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_trans)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeExactDelete337 (subtract congruent monotone)

/-- A chunk contains the literal authored prefix, possibly several inline
fields, followed by a named continuation. Stopping does not make a
terminal claim or change the identity of the opaque remainder. -/
inductive Path where
  | stop
  | chunk (written : Row Expr) (next : Nat) (continuation : Path)

def Path.rows (root : Nat) : Path → List Equation
  | .stop => []
  | .chunk written next rest => ⟨root,withTail written (.variable next)⟩ :: rest.rows next

def Path.expand (root : Nat) : Path → Expr
  | .stop => .variable root
  | .chunk written next rest => withTail written (rest.expand next)

structure Read (source : Source) (s : State) (name : Nat) (path : Path) : Prop where
  authored : ∀ row ∈ path.rows name,row ∈ source.authored
  current : ∀ row ∈ path.rows name,row ∈ s.equations

def check (source : Source) (s : State) (name : Nat) (path : Path) : Bool :=
  (path.rows name).all (fun r => decide (r ∈ source.authored)) &&
  (path.rows name).all (fun r => decide (r ∈ s.equations))

theorem check_exact {source s name path} :
    check source s name path = true ↔ Read source s name path := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  exact ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.authored,h.current⟩⟩

def sem (m : Assignment) (expr : Expr) : Ty := value (environment m) .actual expr

theorem read_in_model {source s name path} (read : Read source s name path)
    (m : Assignment) (fit : Models s m) : Equivalent (m name).1 (sem m (path.expand name)) := by
  induction path generalizing name with
  | stop => exact eqv_refl _
  | chunk written next rest ih =>
    have here := fit.2 ⟨name,withTail written (.variable next)⟩ (read.current _ (by simp [Path.rows]))
    have there : Read source s next rest :=
      ⟨fun r h => read.authored r (List.mem_cons_of_mem _ h),
       fun r h => read.current r (List.mem_cons_of_mem _ h)⟩
    exact eqv_trans here (prefix_congr m written (ih there))

/-- A visible first authored field. The remainder can be fully inline,
a finite linked prefix ending in an unresolved name, or just that name. -/
structure Head where
  label : Nat
  payload : Expr
  inlineRest : Row Expr
  namedRest : Nat
  continuation : Path

def Head.path (h : Head) : Path :=
  .chunk ((h.label,h.payload)::h.inlineRest) h.namedRest h.continuation

def Head.tail (h : Head) : Expr := withTail h.inlineRest (h.continuation.expand h.namedRest)

/-- Use the old declarative bounds, not equality of endpoints. Both
endpoint residuals are exact standalone deletions of their authored
expressions in the very same model; neither fixes the center result. -/
theorem interval_of_open_heads {source : Source} {s : State} {capture : Capture} {low high : Head}
    (lo : Read source s capture.lower low.path) (hi : Read source s capture.upper high.path)
    (label : low.label = high.label)
    (left : Bound s.normal capture.lower capture.center) (right : Bound s.normal capture.center capture.upper)
    (m : Assignment) (fit : Models s m) :
    Subtype (sem m low.payload) (sem m high.payload) ∧
    ∀ keys,
      Equivalent (subtract keys (m capture.lower).1) (subtract keys (sem m (low.path.expand capture.lower))) ∧
      Equivalent (subtract keys (m capture.upper).1) (subtract keys (sem m (high.path.expand capture.upper))) ∧
      Subtype (subtract keys (sem m (low.path.expand capture.lower))) (subtract keys (m capture.center).1) ∧
      Subtype (subtract keys (m capture.center).1) (subtract keys (sem m (high.path.expand capture.upper))) := by
  have l := read_in_model lo m fit
  have h := read_in_model hi m fit
  have lower := subtype_trans l.2 (bound_sound m fit.1 left)
  have upper := subtype_trans (bound_sound m fit.1 right) h.1
  have both : Subtype (record low.label (sem m low.payload) (sem m low.tail))
      (record high.label (sem m high.payload) (sem m high.tail)) := subtype_trans lower upper
  rw [← label] at both
  exact ⟨GeneralNominalStructuralProjectionLaws.record_payload low.label (sem m low.payload)
    (sem m high.payload) (sem m low.tail) (sem m high.tail) both,fun keys =>
      ⟨congruent keys l,congruent keys h,monotone keys lower,monotone keys upper⟩⟩

end Yulang.GeneralDeclarativeWitnessOpenSpine359
