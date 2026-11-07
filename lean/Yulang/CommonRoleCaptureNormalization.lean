import Yulang.CommonRoleMergedExamples

/-! Local case analysis for B4r5. This is not an E2 for the approved rule:
the timing of Paterson validation relative to a deferred payload merge is
the question. The sole variable is captured directly from the first actual
role argument by the existing executable extractor, never chosen as a free
solution of a Common equivalence equation. -/
namespace Yulang.CommonRoleCaptureNormalization

inductive Form where
  | var : Nat → Form
  | int
  | pair : Form → Form → Form
  | join : Form → Form → Form
  | tick : Form → Form
  deriving DecidableEq, Repr

def Form.encode : Form → Roles.Term
  | .var name => .var name
  | .int => .app 0 []
  | .pair first last => .app 1 [first.encode, last.encode]
  | .join first last => .app 4 [first.encode, last.encode]
  | .tick payload => .app 3 [payload.encode]

def Form.eval (assignment : Nat → Common.Ty) : Form → Common.Ty
  | .var name => assignment name
  | .int => .base .int
  | .pair first last => Common.pair (first.eval assignment) (last.eval assignment)
  | .join first last => .union (first.eval assignment) (last.eval assignment)
  | .tick payload => Common.variant 0 (payload.eval assignment)

/-- The local idempotence stage used in the question. Record/alias/row
normalization is not redefined or claimed complete by this module. -/
def Form.normalize : Form → Form
  | .var name => .var name
  | .int => .int
  | .pair first last => .pair first.normalize last.normalize
  | .tick payload => .tick payload.normalize
  | .join first last =>
      let a := first.normalize
      let b := last.normalize
      if a = b then a else .join a b

def Form.subst (assignment : Nat → Form) : Form → Form
  | .var name => assignment name
  | .int => .int
  | .pair first last => .pair (first.subst assignment) (last.subst assignment)
  | .join first last => .join (first.subst assignment) (last.subst assignment)
  | .tick payload => .tick (payload.subst assignment)

theorem subst_encode (form : Form) (assignment : Nat → Form) :
    (form.subst assignment).encode = form.encode.subst (fun name => (assignment name).encode) := by
  induction form <;> simp_all [Form.subst, Form.encode, Roles.Term.subst, Roles.substArgs]

theorem subst_eval (form : Form) (assignment : Nat → Form) (semantic : Nat → Common.Ty) :
    (form.subst assignment).eval semantic = form.eval (fun name => (assignment name).eval semantic) := by
  induction form <;> simp_all [Form.subst, Form.eval]

theorem join_congr (a b c d : Common.Ty) (first : Common.Equivalent a b) (last : Common.Equivalent c d) :
    Common.Equivalent (.union a c) (.union b d) := by
  constructor
  · exact (Common.common_union_is_join _ _ _).mpr
      ⟨Common.subtype_trans first.1 (CommonBoundCoalescing.le_union_left _ _),
        Common.subtype_trans last.1 (CommonBoundCoalescing.le_union_right _ _)⟩
  · exact (Common.common_union_is_join _ _ _).mpr
      ⟨Common.subtype_trans first.2 (CommonBoundCoalescing.le_union_left _ _),
        Common.subtype_trans last.2 (CommonBoundCoalescing.le_union_right _ _)⟩

theorem normalize_meaning (form : Form) (assignment : Nat → Common.Ty) :
    Common.Equivalent (form.normalize.eval assignment) (form.eval assignment) := by
  induction form with
  | var name => exact Common.equivalent_refl _
  | int => exact Common.equivalent_refl _
  | pair first last ihFirst ihLast =>
      exact (CommonCanonicalShapes.pair_equivalent_iff _ _ _ _).mpr ⟨ihFirst, ihLast⟩
  | tick payload ih => exact (CommonCanonicalShapes.variant_equivalent_iff 0 _ _).mpr ih
  | join first last ihFirst ihLast =>
      change Common.Equivalent
        ((if first.normalize = last.normalize then first.normalize else .join first.normalize last.normalize).eval assignment) _
      split
      · rename_i same
        have merged := join_congr _ _ _ _ ihFirst ihLast
        rw [← same] at merged
        exact Common.equivalent_trans
          (Common.equivalent_symm (CommonRoleMergedPayload.padded_equivalent 1 _)) merged
      · exact join_congr _ _ _ _ ihFirst ihLast

def head : List Form :=
  [.var 0, .tick (.join (.pair .int (.var 0)) (.pair (.var 0) .int))]

def child : List Form := [.var 0, .tick (.pair (.var 0) (.var 0))]

def implementation : Roles.Impl :=
  ⟨1, head.map (fun form => form.normalize.encode), [⟨1, child.map (fun form => form.normalize.encode)⟩], 0⟩

def goal : Roles.Goal := ⟨1, [Form.int.encode, (Form.tick (.pair .int .int)).encode]⟩

/-- The first actual head argument captures the first determined goal
argument. Other names do not occur; their defaults are not observed. -/
def capture (name : Nat) : Form := if name = 0 then .int else .var name

theorem capture_zero_actual : Roles.matchingSubst implementation.head goal.args 0 = (capture 0).encode := rfl

theorem symbolic_checked : CheckedRoles.checkImpl implementation = true := by decide +kernel

theorem symbolic_sizes : Roles.argsSize implementation.head = 9 ∧
    Roles.argsSize (implementation.constraints[0]'(by decide)).args = 5 := by decide +kernel

theorem symbolic_occurrences : Roles.argsOccurrences 0 implementation.head = 3 ∧
    Roles.argsOccurrences 0 (implementation.constraints[0]'(by decide)).args = 3 := by decide +kernel

def captured (forms : List Form) : List Roles.Term :=
  forms.map (fun form => (form.subst capture).normalize.encode)

theorem captured_head : captured head = goal.args := by decide +kernel
theorem captured_child : captured child = goal.args := by decide +kernel

theorem captured_sizes : Roles.argsSize (captured head) = 5 ∧ Roles.argsSize (captured child) = 5 := by decide +kernel

theorem normalization_capture_noncommute :
    head.map (fun form => (form.normalize.subst capture).encode) ≠ captured head := by decide +kernel

theorem symbolic_check_does_not_imply_captured_descent :
    CheckedRoles.checkImpl implementation = true ∧
      ¬ Roles.argsSize (captured child) < Roles.argsSize (captured head) := by
  exact ⟨symbolic_checked, by rw [captured_head, captured_child]; omega⟩

def lateImplementation : Roles.Impl := ⟨1, captured head, [⟨1, captured child⟩], 0⟩

theorem late_check_rejects : CheckedRoles.checkImpl lateImplementation = false := by decide +kernel

/-- One possible additional declaration condition. It is not silently
substituted for the approved checker or asserted decidable. -/
def CaptureSafe : Prop :=
  ∀ assignment : Nat → Form,
    Roles.argsSize (child.map (fun form => (form.subst assignment).normalize.encode)) <
      Roles.argsSize (head.map (fun form => (form.subst assignment).normalize.encode))

theorem capture_safe_rejects : ¬ CaptureSafe := by
  intro safe
  have strict := safe capture
  change Roles.argsSize (captured child) < Roles.argsSize (captured head) at strict
  rw [captured_head, captured_child] at strict
  omega

def sourceRow : Variants.Merged.Row Nat Form :=
  Variants.Merged.normalize Form.join [(0, .pair .int (.var 0)), (0, .pair (.var 0) .int)]

theorem actual_merge_entries : sourceRow.entries = [(0, .join (.pair .int (.var 0)) (.pair (.var 0) .int))] := rfl
theorem actual_merge_unique : (sourceRow.entries.map Prod.fst).Nodup := sourceRow.unique

/-- Coalescing equal outer pair constructors, as in spec 4.7b, does not
remove the timing question: the two scalar joins still collapse at capture. -/
def coalescedHead : List Form :=
  [.var 0, .tick (.pair (.join .int (.var 0)) (.join (.var 0) .int))]

theorem coalesced_meaning (assignment : Nat → Common.Ty) :
    Common.Equivalent
      ((Form.tick (.join (.pair .int (.var 0)) (.pair (.var 0) .int))).eval assignment)
      ((Form.tick (.pair (.join .int (.var 0)) (.join (.var 0) .int))).eval assignment) :=
  (CommonCanonicalShapes.variant_equivalent_iff 0 _ _).mpr (CommonCanonicalShapes.pair_union_group ..)

def coalescedImplementation : Roles.Impl :=
  ⟨1, coalescedHead.map (fun form => form.normalize.encode), implementation.constraints, 0⟩

theorem coalesced_checked : CheckedRoles.checkImpl coalescedImplementation = true := by decide +kernel
theorem coalesced_size : Roles.argsSize coalescedImplementation.head = 9 := by decide +kernel
theorem coalesced_captured : captured coalescedHead = goal.args := by decide +kernel

theorem coalesced_late_check_rejects :
    CheckedRoles.checkImpl ⟨1, captured coalescedHead, [⟨1, captured child⟩], 0⟩ = false := by decide +kernel

end Yulang.CommonRoleCaptureNormalization
