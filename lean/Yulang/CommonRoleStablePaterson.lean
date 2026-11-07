import Yulang.CommonRoleCaptureNormalization

/-! A finite sufficient Paterson test for the recursive idempotence stage.
The head lower bound retains rigid positions and replaces a potentially
collapsing merge by a one-node constant. Child upper bounds retain its whole
normalized template. Soundness quantifies every substitution; no late
rejection or solver-success assumption is used. This module does not claim
the full source/record/regular matcher bridge. -/
namespace Yulang.CommonRoleStablePaterson

open CommonRoleCaptureNormalization (Form)

def lower : Form → Roles.Term
  | .var name => .var name
  | .int => .app 0 []
  | .pair first last => .app 1 [lower first, lower last]
  | .tick payload => .app 3 [lower payload]
  | .join _ _ => .app 0 []

def images (assignment : Nat → Form) : Roles.Subst := fun name => (assignment name).normalize.encode

theorem normalize_idempotent (form : Form) : form.normalize.normalize = form.normalize := by
  induction form with
  | var name => rfl
  | int => rfl
  | pair first last ihFirst ihLast => simp [Form.normalize, ihFirst, ihLast]
  | tick payload ih => simp [Form.normalize, ih]
  | join first last ihFirst ihLast =>
      simp only [Form.normalize]
      split
      · exact ihFirst
      · simp only [Form.normalize, ihFirst, ihLast]
        split <;> simp_all

theorem normalize_subst (form : Form) (assignment : Nat → Form) :
    (form.subst assignment).normalize =
      (form.subst (fun name => (assignment name).normalize)).normalize := by
  induction form with
  | var name => exact (normalize_idempotent _).symm
  | int => rfl
  | pair first last ihFirst ihLast => simp [Form.subst, Form.normalize, ihFirst, ihLast]
  | tick payload ih => simp [Form.subst, Form.normalize, ih]
  | join first last ihFirst ihLast => simp only [Form.subst, Form.normalize, ihFirst, ihLast]

theorem normalize_before_subst (form : Form) (assignment : Nat → Form) :
    (form.normalize.subst assignment).normalize = (form.subst assignment).normalize := by
  induction form with
  | var name => rfl
  | int => rfl
  | pair first last ihFirst ihLast => simp [Form.subst, Form.normalize, ihFirst, ihLast]
  | tick payload ih => simp [Form.subst, Form.normalize, ih]
  | join first last ihFirst ihLast =>
      simp only [Form.normalize]
      split
      · rename_i same
        have equal := congrArg (fun f => (f.subst assignment).normalize) same
        rw [ihFirst, ihLast] at equal
        simp [Form.subst, Form.normalize, ← equal, ihFirst]
      · simp only [Form.subst, Form.normalize, ihFirst, ihLast]

theorem normalize_size_le (form : Form) : form.normalize.encode.size ≤ form.encode.size := by
  induction form with
  | var name => exact Nat.le_refl _
  | int => exact Nat.le_refl _
  | pair first last ihFirst ihLast =>
      simp only [Form.normalize, Form.encode, Roles.Term.size, Roles.argsSize, Nat.add_zero]
      omega
  | tick payload ih =>
      simp only [Form.normalize, Form.encode, Roles.Term.size, Roles.argsSize, Nat.add_zero]
      omega
  | join first last ihFirst ihLast =>
      simp only [Form.normalize]
      split <;> simp only [Form.encode, Roles.Term.size, Roles.argsSize, Nat.add_zero] <;> omega

theorem normalize_occurrences_le (form : Form) (name : Nat) :
    form.normalize.encode.occurrences name ≤ form.encode.occurrences name := by
  induction form with
  | var variableName => exact Nat.le_refl _
  | int => exact Nat.le_refl _
  | pair first last ihFirst ihLast =>
      simp only [Form.normalize, Form.encode, Roles.Term.occurrences, Roles.argsOccurrences, Nat.add_zero]
      omega
  | tick payload ih =>
      simp only [Form.normalize, Form.encode, Roles.Term.occurrences, Roles.argsOccurrences, Nat.add_zero]
      omega
  | join first last ihFirst ihLast =>
      simp only [Form.normalize]
      split <;> simp only [Form.encode, Roles.Term.occurrences, Roles.argsOccurrences, Nat.add_zero] <;> omega

theorem lower_size (form : Form) (assignment : Nat → Form) :
    ((lower form).subst (images assignment)).size ≤ (form.subst assignment).normalize.encode.size := by
  induction form with
  | var name => exact Nat.le_refl _
  | int => exact Nat.le_refl _
  | pair first last ihFirst ihLast =>
      simp only [lower, Roles.Term.subst, Roles.substArgs, Roles.Term.size, Roles.argsSize,
        Form.subst, Form.normalize, Form.encode, Nat.add_zero]
      omega
  | tick payload ih =>
      simp only [lower, Roles.Term.subst, Roles.substArgs, Roles.Term.size, Roles.argsSize,
        Form.subst, Form.normalize, Form.encode, Nat.add_zero]
      omega
  | join first last ihFirst ihLast =>
      change 1 ≤ ((Form.join first last).subst assignment).normalize.encode.size
      exact Roles.Term.size_pos _

theorem lower_occurrences (form : Form) (assignment : Nat → Form) (name : Nat) :
    ((lower form).subst (images assignment)).occurrences name ≤
      (form.subst assignment).normalize.encode.occurrences name := by
  induction form with
  | var variableName => exact Nat.le_refl _
  | int => exact Nat.le_refl _
  | pair first last ihFirst ihLast =>
      simp only [lower, Roles.Term.subst, Roles.substArgs, Roles.Term.occurrences, Roles.argsOccurrences,
        Form.subst, Form.normalize, Form.encode, Nat.add_zero]
      omega
  | tick payload ih =>
      simp only [lower, Roles.Term.subst, Roles.substArgs, Roles.Term.occurrences, Roles.argsOccurrences,
        Form.subst, Form.normalize, Form.encode, Nat.add_zero]
      omega
  | join first last ihFirst ihLast => exact Nat.zero_le _

theorem upper_size (form : Form) (assignment : Nat → Form) :
    (form.subst assignment).normalize.encode.size ≤ (form.encode.subst (images assignment)).size := by
  rw [normalize_subst]
  change _ ≤ (form.encode.subst (fun name => (assignment name).normalize.encode)).size
  simpa only [CommonRoleCaptureNormalization.subst_encode, images] using
    normalize_size_le (form.subst (fun name => (assignment name).normalize))

theorem upper_occurrences (form : Form) (assignment : Nat → Form) (name : Nat) :
    (form.subst assignment).normalize.encode.occurrences name ≤
      (form.encode.subst (images assignment)).occurrences name := by
  rw [normalize_subst]
  change _ ≤ (form.encode.subst (fun name => (assignment name).normalize.encode)).occurrences name
  simpa only [CommonRoleCaptureNormalization.subst_encode, images] using
    normalize_occurrences_le (form.subst (fun name => (assignment name).normalize)) name

mutual
  theorem term_subst_occurrences (term : Roles.Term) (assignment : Roles.Subst) (bound : Nat)
      (bounded : term.bound ≤ bound) (name : Nat) :
      (term.subst assignment).occurrences name =
        Roles.sumBelow bound (fun variableName => term.occurrences variableName * (assignment variableName).occurrences name) := by
    cases term with
    | var variableName =>
        simp only [Roles.Term.bound] at bounded
        simp only [Roles.Term.subst, Roles.Term.occurrences]
        rw [Roles.sumBelow_single bound variableName _ (by omega)]
    | app tag args => exact args_subst_occurrences args assignment bound bounded name
  theorem args_subst_occurrences (args : List Roles.Term) (assignment : Roles.Subst) (bound : Nat)
      (bounded : Roles.argsBound args ≤ bound) (name : Nat) :
      Roles.argsOccurrences name (Roles.substArgs assignment args) =
        Roles.sumBelow bound (fun variableName => Roles.argsOccurrences variableName args * (assignment variableName).occurrences name) := by
    cases args with
    | nil =>
        simp only [Roles.substArgs, Roles.argsOccurrences, Nat.zero_mul]
        have zero : ∀ bound, Roles.sumBelow bound (fun _ => 0) = 0 := by
          intro bound; induction bound <;> simp_all [Roles.sumBelow]
        exact (zero bound).symm
    | cons term rest =>
        simp only [Roles.argsBound, Nat.max_le] at bounded
        simp only [Roles.substArgs, Roles.argsOccurrences, Nat.add_mul]
        rw [Roles.sumBelow_add, term_subst_occurrences term assignment bound bounded.1,
          args_subst_occurrences rest assignment bound bounded.2]
end

theorem occurrence_mono (head child : List Roles.Term)
    (covered : ∀ variableName, Roles.argsOccurrences variableName child ≤ Roles.argsOccurrences variableName head)
    (assignment : Roles.Subst) (name : Nat) :
    Roles.argsOccurrences name (Roles.substArgs assignment child) ≤
      Roles.argsOccurrences name (Roles.substArgs assignment head) := by
  let bound := max (Roles.argsBound child) (Roles.argsBound head)
  rw [args_subst_occurrences child assignment bound (Nat.le_max_left ..),
    args_subst_occurrences head assignment bound (Nat.le_max_right ..)]
  exact Roles.sumBelow_mono bound (fun variableName => Nat.mul_le_mul_right _ (covered variableName))

def instantiated (forms : List Form) (assignment : Nat → Form) : List Roles.Term :=
  forms.map (fun form => (form.subst assignment).normalize.encode)

def headBound (forms : List Form) : List Roles.Term := forms.map (fun form => lower form.normalize)
def childBound (forms : List Form) : List Roles.Term := forms.map (fun form => form.normalize.encode)

theorem head_size_bound (forms : List Form) (assignment : Nat → Form) :
    Roles.argsSize (Roles.substArgs (images assignment) (headBound forms)) ≤ Roles.argsSize (instantiated forms assignment) := by
  induction forms with
  | nil => exact Nat.le_refl _
  | cons form rest ih =>
      have bounded := lower_size form.normalize assignment
      rw [normalize_before_subst] at bounded
      simpa only [headBound, instantiated, List.map_cons, Roles.substArgs, Roles.argsSize] using Nat.add_le_add bounded ih

theorem child_size_bound (forms : List Form) (assignment : Nat → Form) :
    Roles.argsSize (instantiated forms assignment) ≤ Roles.argsSize (Roles.substArgs (images assignment) (childBound forms)) := by
  induction forms with
  | nil => exact Nat.le_refl _
  | cons form rest ih =>
      have bounded := upper_size form.normalize assignment
      rw [normalize_before_subst] at bounded
      simpa only [childBound, instantiated, List.map_cons, Roles.substArgs, Roles.argsSize] using Nat.add_le_add bounded ih

theorem head_occurrences_bound (forms : List Form) (assignment : Nat → Form) (name : Nat) :
    Roles.argsOccurrences name (Roles.substArgs (images assignment) (headBound forms)) ≤
      Roles.argsOccurrences name (instantiated forms assignment) := by
  induction forms with
  | nil => exact Nat.le_refl _
  | cons form rest ih =>
      have bounded := lower_occurrences form.normalize assignment name
      rw [normalize_before_subst] at bounded
      simpa only [headBound, instantiated, List.map_cons, Roles.substArgs, Roles.argsOccurrences] using Nat.add_le_add bounded ih

theorem child_occurrences_bound (forms : List Form) (assignment : Nat → Form) (name : Nat) :
    Roles.argsOccurrences name (instantiated forms assignment) ≤
      Roles.argsOccurrences name (Roles.substArgs (images assignment) (childBound forms)) := by
  induction forms with
  | nil => exact Nat.le_refl _
  | cons form rest ih =>
      have bounded := upper_occurrences form.normalize assignment name
      rw [normalize_before_subst] at bounded
      simpa only [childBound, instantiated, List.map_cons, Roles.substArgs, Roles.argsOccurrences] using Nat.add_le_add bounded ih

structure Declaration where
  role : Nat
  key : Nat
  head : List Form
  requirements : List (Nat × List Form)
  deriving DecidableEq, Repr

def Declaration.comparison (declaration : Declaration) : Roles.Impl :=
  ⟨declaration.role, headBound declaration.head,
    declaration.requirements.map (fun child => ⟨child.1, childBound child.2⟩), declaration.key⟩

def Declaration.toImpl (declaration : Declaration) : Roles.Impl :=
  ⟨declaration.role, childBound declaration.head,
    declaration.requirements.map (fun child => ⟨child.1, childBound child.2⟩), declaration.key⟩

def check (declaration : Declaration) : Bool := CheckedRoles.checkImpl declaration.comparison

theorem check_comparison_exact (declaration : Declaration) :
    check declaration = true ↔ declaration.comparison.WellFormed := CheckedRoles.checkImpl_exact _

theorem check_sound (declaration : Declaration) (accepted : check declaration = true)
    (child : Nat × List Form) (required : child ∈ declaration.requirements) (assignment : Nat → Form) :
    Roles.argsSize (instantiated child.2 assignment) < Roles.argsSize (instantiated declaration.head assignment) ∧
      ∀ name, Roles.argsOccurrences name (instantiated child.2 assignment) ≤
        Roles.argsOccurrences name (instantiated declaration.head assignment) := by
  have wellFormed := (CheckedRoles.checkImpl_exact _).mp accepted
  have member : (⟨child.1, childBound child.2⟩ : Roles.Goal) ∈ declaration.comparison.constraints :=
    List.mem_map.mpr ⟨child, required, rfl⟩
  constructor
  · have strict := Roles.size_decreases wellFormed member (images assignment)
    exact Nat.lt_of_le_of_lt (child_size_bound _ _) (Nat.lt_of_lt_of_le strict (head_size_bound _ _))
  · intro name
    have covered := occurrence_mono (headBound declaration.head) (childBound child.2)
      (wellFormed _ member).2 (images assignment) name
    exact Nat.le_trans (child_occurrences_bound _ _ _) (Nat.le_trans covered (head_occurrences_bound _ _ _))

theorem subst_identity (form : Form) : form.subst Form.var = form := by
  induction form <;> simp_all [Form.subst]

theorem instantiated_identity (forms : List Form) : instantiated forms Form.var = childBound forms := by
  simp [instantiated, childBound, subst_identity]

theorem accepted_wellFormed (declaration : Declaration) (accepted : check declaration = true) :
    declaration.toImpl.WellFormed := by
  intro requirement member
  obtain ⟨child, required, rfl⟩ := List.mem_map.mp member
  have sound := check_sound declaration accepted child required Form.var
  simpa only [instantiated_identity, Declaration.toImpl] using sound

def unaryDecrease : Declaration := ⟨1, 0, [.tick (.var 0)], [(1, [.var 0])]⟩
def rebuildingDecrease : Declaration :=
  ⟨1, 0, [.pair (.tick (.var 0)) (.var 1)], [(1, [.pair (.var 0) (.var 1)])]⟩
def previousExample : Declaration :=
  ⟨1, 0, CommonRoleCaptureNormalization.head, [(1, CommonRoleCaptureNormalization.child)]⟩

def repeatedDecrease : Declaration :=
  ⟨1, 0, [.tick (.join (.var 0) (.var 0))], [(1, [.var 0])]⟩
def constantDecrease : Declaration :=
  ⟨1, 0, [.tick (.join (.var 0) (.var 1))], [(1, [.int])]⟩

theorem unary_accepted : check unaryDecrease = true := by decide +kernel
theorem rebuilding_accepted : check rebuildingDecrease = true := by decide +kernel
theorem previous_rejected : check previousExample = false := by decide +kernel
theorem repeated_accepted : check repeatedDecrease = true := by decide +kernel
theorem constant_accepted : check constantDecrease = true := by decide +kernel
theorem terminal_accepted (role key : Nat) (head : List Form) : check ⟨role, key, head, []⟩ = true := rfl

end Yulang.CommonRoleStablePaterson
