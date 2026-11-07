import Yulang.CommonRoleAssociatedObstructions

/-!
# A decidable sufficient declaration check for associated head determination

This check operates on the fixed finite record-pattern grammar used by the
associated-type obstruction. It is a declaration check, independent of any
role resolver, and its soundness quantifies over arbitrary Common assignments.
It is not claimed complete for the semantic condition or the full language.
-/

namespace Yulang.CommonRoleHeadDetermination

open CommonRoleAssociatedObstructions (Pattern)
open Common (Ty Equivalent)

def variables : Pattern → List Nat
  | .var name => [name]
  | .int | .bool | .empty => []
  | .record _ payload rest => variables payload ++ variables rest

theorem eval_congr (pattern : Pattern) (first last : Nat → Ty)
    (agree : ∀ name ∈ variables pattern, Equivalent (first name) (last name)) :
    Equivalent (pattern.eval first) (pattern.eval last) := by
  induction pattern with
  | var name => exact agree name (by simp [variables])
  | int | bool | empty => exact Common.equivalent_refl _
  | record label payload rest ihp ihr =>
    have hp := ihp (fun name member => agree name (List.mem_append_left _ member))
    have hr := ihr (fun name member => agree name (List.mem_append_right _ member))
    exact ⟨Common.common_record_mono label hp.1 hr.1,
      Common.common_record_mono label hp.2 hr.2⟩

/-- The first payload of a record is observable even if its tail contains a
field with the same name. No whole-tail variable is inferred from masking. -/
def recoverable : Pattern → List Nat
  | .var name => [name]
  | .int | .bool | .empty => []
  | .record _ payload _ => recoverable payload

theorem recoverable_sound (pattern : Pattern) (first last : Nat → Ty)
    (same : Equivalent (pattern.eval first) (pattern.eval last)) :
    ∀ name ∈ recoverable pattern, Equivalent (first name) (last name) := by
  induction pattern with
  | var name =>
    intro query member
    have equality : query = name := by simpa [recoverable] using member
    subst query
    exact same
  | int | bool | empty => simp [recoverable]
  | record label payload rest ih _ =>
    apply ih
    exact ⟨(Common.common_record_iff label _ _ _ _).mp same.1 |>.1,
      (Common.common_record_iff label _ _ _ _).mp same.2 |>.1⟩

/-- The approved semantic condition, for one declaration's head arguments and
explicit associated bodies. No checking or solver result occurs in it. -/
def HeadDeterminesAssociated (head associated : List Pattern) : Prop :=
  ∀ first last : Nat → Ty,
    (∀ pattern ∈ head, Equivalent (pattern.eval first) (pattern.eval last)) →
    ∀ rhs ∈ associated, Equivalent (rhs.eval first) (rhs.eval last)

def checkAssociated (head associated : List Pattern) : Bool :=
  associated.all fun rhs =>
    (variables rhs).all fun name => (head.flatMap recoverable).contains name

theorem checkAssociated_sound (head associated : List Pattern)
    (accepted : checkAssociated head associated = true) :
    HeadDeterminesAssociated head associated := by
  intro first last same rhs member
  apply eval_congr rhs first last
  intro name occurs
  have found := List.all_eq_true.mp (List.all_eq_true.mp accepted rhs member) name occurs
  have present : name ∈ head.flatMap recoverable := by simpa using found
  obtain ⟨pattern, inHead, recovered⟩ := List.mem_flatMap.mp present
  exact recoverable_sound pattern first last (same pattern inHead) name recovered

/-- A finite declaration stores the exact finite patterns also compiled into
the existing first-order role representation. Ordinary declaration validity
is separate from the new associated-head check. -/
structure Declaration where
  role : Nat
  key : Nat
  head : List Pattern
  requirements : List (Nat × List Pattern)
  associated : List (Nat × Pattern)

def Declaration.toImpl (declaration : Declaration) : Roles.Impl :=
  ⟨declaration.role, declaration.head.map Pattern.encode,
    declaration.requirements.map (fun goal => ⟨goal.1, goal.2.map Pattern.encode⟩), declaration.key⟩

def Declaration.checkAssociated (declaration : Declaration) : Bool :=
  CommonRoleHeadDetermination.checkAssociated declaration.head (declaration.associated.map Prod.snd)

def RegistryHeadDeterminesAssociated (declarations : List Declaration) : Prop :=
  ∀ declaration ∈ declarations,
    HeadDeterminesAssociated declaration.head (declaration.associated.map Prod.snd)

def checkRegistry (declarations : List Declaration) : Bool :=
  declarations.all Declaration.checkAssociated

theorem checkRegistry_sound (declarations : List Declaration)
    (accepted : checkRegistry declarations = true) :
    RegistryHeadDeterminesAssociated declarations := by
  intro declaration member
  exact checkAssociated_sound declaration.head _ (List.all_eq_true.mp accepted declaration member)

/-- The new stage composes with the actual Paterson checker. Signature arity,
associated-name completeness and source method-body checks remain separate;
this stage does not silently replace them. -/
def Declaration.check (declaration : Declaration) : Bool :=
  CheckedRoles.checkImpl declaration.toImpl && declaration.checkAssociated

theorem declaration_check_sound (declaration : Declaration)
    (accepted : declaration.check = true) :
    declaration.toImpl.WellFormed ∧
      HeadDeterminesAssociated declaration.head (declaration.associated.map Prod.snd) := by
  simp only [Declaration.check, Bool.and_eq_true] at accepted
  exact ⟨(CheckedRoles.checkImpl_exact _).mp accepted.1,
    checkAssociated_sound _ _ accepted.2⟩

/-- The certificate is produced by declaration validation, rather than
postulated as a role solver's success premise. -/
structure VerifiedDeclaration where
  declaration : Declaration
  wellFormed : declaration.toImpl.WellFormed
  headDetermines : HeadDeterminesAssociated declaration.head (declaration.associated.map Prod.snd)

def verify (declaration : Declaration) : Option VerifiedDeclaration :=
  if accepted : declaration.check = true then
    some ⟨declaration, (declaration_check_sound declaration accepted).1,
      (declaration_check_sound declaration accepted).2⟩
  else none

theorem verify_isSome_iff (declaration : Declaration) :
    (verify declaration).isSome = true ↔ declaration.check = true := by
  unfold verify
  split <;> simp_all

theorem verify_preserves_declaration (declaration : Declaration) (verified : VerifiedDeclaration)
    (accepted : verify declaration = some verified) : verified.declaration = declaration := by
  unfold verify at accepted
  split at accepted
  · cases Option.some.inj accepted
    rfl
  · cases accepted

namespace Examples

def visible : Pattern := .record 0 (.var 0) .empty

theorem visible_associated_accepted : checkAssociated [visible] [.var 0] = true := by
  decide +kernel

theorem visible_associated_determined : HeadDeterminesAssociated [visible] [.var 0] :=
  checkAssociated_sound _ _ visible_associated_accepted

theorem hidden_associated_rejected :
    checkAssociated [CommonRoleAssociatedObstructions.headPattern] [.var 0] = false := by
  decide +kernel

theorem hidden_associated_not_determined :
    ¬ HeadDeterminesAssociated [CommonRoleAssociatedObstructions.headPattern] [.var 0] := by
  intro determines
  have same := determines (fun _ => .base .int) (fun _ => .base .bool)
    (by
      intro pattern member
      have equality : pattern = CommonRoleAssociatedObstructions.headPattern := by simpa using member
      subst pattern
      exact Common.equivalent_trans
        (CommonRoleAssociatedObstructions.every_head_instance _)
        (Common.equivalent_symm (CommonRoleAssociatedObstructions.every_head_instance _)))
    (.var 0) (by simp)
  exact CommonRoleAssociatedObstructions.int_not_bool same

theorem constant_associated_accepted (head : List Pattern) :
    checkAssociated head [.int] = true := by
  simp [checkAssociated, variables]

theorem constant_associated_determined (head : List Pattern) :
    HeadDeterminesAssociated head [.int] :=
  checkAssociated_sound _ _ (constant_associated_accepted head)

end Examples

end Yulang.CommonRoleHeadDetermination
