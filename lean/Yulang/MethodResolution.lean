import Yulang.Methods
import Yulang.StructuralBase

/-!
# Resolve a dot selection at the end of its SCC

For an unknown receiver, visible roles are searched by method name. No role
means a structural field requirement, one distinct role selects that method,
and two distinct roles are ambiguous. Repeated imports of the same role do not
create ambiguity, and list order does not choose a winner.

For an already known structural receiver, field lookup is computed from the
existing `StructuralBase.Ty`. A present field wins over the supplied remainder
of typed method lookup. Nominal/inherent/effect-method lookup and union-member
cast routing are not implemented by this module. The final receiver knowledge
is an input snapshot; this is not a solver that computes SCC stabilization.

The output is a reference with no receiver-type variable. `FrozenMethods`
lowers it to the existing qualified inference core and retains that selection
through subsequent type substitution.
-/

namespace Yulang.MethodResolution

open Methods (Selection)

structure Scope where
  visibleRoles : List Nat
  methodRef : Nat → Nat → Option Nat

inductive Reference where
  | field (label : Nat)
  | role (role declaration : Nat)
  | direct (declaration : Nat)
  deriving DecidableEq, Repr

structure Site (Row : Type) where
  name : Nat
  scope : Scope
  receiver : Option (StructuralBase.Ty Row)
  typedFallback : Selection Nat

def Candidate (scope : Scope) (name role declaration : Nat) : Prop :=
  role ∈ scope.visibleRoles ∧ scope.methodRef role name = some declaration

def candidates (scope : Scope) (name : Nat) : List (Nat × Nat) :=
  scope.visibleRoles.filterMap fun role => (scope.methodRef role name).map (role, ·)

theorem mem_candidates (scope : Scope) (name role declaration : Nat) :
    (role, declaration) ∈ candidates scope name ↔ Candidate scope name role declaration := by
  simp only [candidates, List.mem_filterMap, Candidate]
  constructor
  · rintro ⟨other, present, mapped⟩
    cases lookup : scope.methodRef other name with
    | none => simp [lookup] at mapped
    | some found =>
        have same : other = role ∧ found = declaration := by simpa [lookup] using mapped
        rcases same with ⟨rfl, rfl⟩
        exact ⟨present, lookup⟩
  · rintro ⟨present, lookup⟩
    exact ⟨role, present, by simp [lookup]⟩

theorem candidate_functional (scope : Scope) (name role left right : Nat)
    (first : Candidate scope name role left) (second : Candidate scope name role right) : left = right :=
  Option.some.inj (first.2.symm.trans second.2)

def NoRole (scope : Scope) (name : Nat) : Prop :=
  ∀ role declaration, ¬ Candidate scope name role declaration

def UniqueRole (scope : Scope) (name role declaration : Nat) : Prop :=
  Candidate scope name role declaration ∧
    ∀ other reference, Candidate scope name other reference → other = role

theorem missing_candidates (scope : Scope) (name : Nat) :
    Methods.select (candidates scope name) = .missing ↔ NoRole scope name := by
  rw [Methods.select_missing_iff]
  constructor
  · intro absent role declaration member
    exact absent (role, declaration) ((mem_candidates ..).mpr member)
  · intro absent pair member
    exact absent pair.1 pair.2 ((mem_candidates ..).mp member)

theorem unique_candidates (scope : Scope) (name role declaration : Nat) :
    Methods.select (candidates scope name) = .unique (role, declaration) ↔
      UniqueRole scope name role declaration := by
  rw [Methods.select_unique_iff]
  constructor
  · rintro ⟨present, unique⟩
    refine ⟨(mem_candidates ..).mp present, ?_⟩
    intro other reference candidate
    exact congrArg Prod.fst (unique (other, reference) ((mem_candidates ..).mpr candidate))
  · rintro ⟨present, unique⟩
    refine ⟨(mem_candidates ..).mpr present, ?_⟩
    rintro ⟨other, reference⟩ member
    have candidate := (mem_candidates ..).mp member
    have sameRole := unique other reference candidate
    subst other
    have sameReference := candidate_functional scope name role reference declaration candidate present
    exact Prod.ext rfl sameReference

theorem ambiguous_candidates (scope : Scope) (name : Nat) :
    Methods.select (candidates scope name) = .ambiguous ↔
      ∃ first firstRef second secondRef,
        Candidate scope name first firstRef ∧ Candidate scope name second secondRef ∧ first ≠ second := by
  rw [Methods.select_ambiguous_iff]
  constructor
  · rintro ⟨⟨first, firstRef⟩, firstMember, ⟨second, secondRef⟩, secondMember, different⟩
    have firstCandidate := (mem_candidates ..).mp firstMember
    have secondCandidate := (mem_candidates ..).mp secondMember
    refine ⟨first, firstRef, second, secondRef, firstCandidate, secondCandidate, ?_⟩
    intro same
    subst second
    exact different (Prod.ext rfl (candidate_functional scope name first firstRef secondRef
      firstCandidate secondCandidate))
  · rintro ⟨first, firstRef, second, secondRef, firstCandidate, secondCandidate, different⟩
    exact ⟨(first, firstRef), (mem_candidates ..).mpr firstCandidate,
      (second, secondRef), (mem_candidates ..).mpr secondCandidate,
      fun same => different (congrArg Prod.fst same)⟩

def unknown (scope : Scope) (name : Nat) : Selection Reference :=
  match Methods.select (candidates scope name) with
  | .missing => .unique (.field name)
  | .unique (role, declaration) => .unique (.role role declaration)
  | .ambiguous => .ambiguous

def known (receiver : StructuralBase.Ty Row) (name : Nat)
    (fallback : Selection Nat) : Selection Reference :=
  match receiver.lookup name with
  | some _ => .unique (.field name)
  | none => match fallback with
    | .missing => .missing
    | .unique declaration => .unique (.direct declaration)
    | .ambiguous => .ambiguous

def resolve (site : Site Row) : Selection Reference :=
  match site.receiver with
  | none => unknown site.scope site.name
  | some receiver => known receiver site.name site.typedFallback

theorem unknown_field_iff (scope : Scope) (name label : Nat) :
    unknown scope name = .unique (.field label) ↔ label = name ∧ NoRole scope name := by
  rw [← missing_candidates]
  cases selected : Methods.select (candidates scope name) with
  | missing => simp [unknown, selected, eq_comm]
  | unique pair => cases pair; simp [unknown, selected]
  | ambiguous => simp [unknown, selected]

theorem unknown_role_iff (scope : Scope) (name role declaration : Nat) :
    unknown scope name = .unique (.role role declaration) ↔ UniqueRole scope name role declaration := by
  rw [← unique_candidates]
  cases selected : Methods.select (candidates scope name) with
  | missing => simp [unknown, selected]
  | unique pair => cases pair; simp [unknown, selected]
  | ambiguous => simp [unknown, selected]

theorem unknown_ambiguous_iff (scope : Scope) (name : Nat) :
    unknown scope name = .ambiguous ↔
      ∃ first firstRef second secondRef,
        Candidate scope name first firstRef ∧ Candidate scope name second secondRef ∧ first ≠ second := by
  rw [← ambiguous_candidates]
  cases selected : Methods.select (candidates scope name) with
  | missing => simp [unknown, selected]
  | unique pair => cases pair; simp [unknown, selected]
  | ambiguous => simp [unknown, selected]

theorem unknown_ne_direct (scope : Scope) (name declaration : Nat) :
    unknown scope name ≠ .unique (.direct declaration) := by
  cases selected : Methods.select (candidates scope name) with
  | missing => simp [unknown, selected]
  | unique pair => cases pair; simp [unknown, selected]
  | ambiguous => simp [unknown, selected]

theorem known_field_priority (receiver : StructuralBase.Ty Row) (name : Nat)
    (value : StructuralBase.Ty Row) (present : receiver.lookup name = some value)
    (fallback : Selection Nat) : known receiver name fallback = .unique (.field name) := by
  simp [known, present]

theorem unknown_scope_ext (left right : Scope) (name : Nat)
    (same : ∀ role declaration, Candidate left name role declaration ↔ Candidate right name role declaration) :
    unknown left name = unknown right name := by
  have selected : Methods.select (candidates left name) = Methods.select (candidates right name) := by
    apply Methods.select_ext
    rintro ⟨role, declaration⟩
    simpa only [mem_candidates] using same role declaration
  simp only [unknown, selected]

/-- A declarative choice relation. It does not call `resolve`. -/
def Selects (site : Site Row) (reference : Reference) : Prop :=
  match site.receiver, reference with
  | none, .field label => label = site.name ∧ NoRole site.scope site.name
  | none, .role role declaration => UniqueRole site.scope site.name role declaration
  | none, .direct _ => False
  | some receiver, .field label =>
      label = site.name ∧ ∃ value, receiver.lookup site.name = some value
  | some receiver, .direct declaration =>
      receiver.lookup site.name = none ∧ site.typedFallback = .unique declaration
  | some _, .role _ _ => False

theorem resolve_exact (site : Site Row) (reference : Reference) :
    resolve site = .unique reference ↔ Selects site reference := by
  unfold resolve Selects
  cases receiver : site.receiver with
  | none =>
      cases reference with
      | field label => exact unknown_field_iff _ _ _
      | role role declaration => exact unknown_role_iff _ _ _ _
      | direct declaration =>
          exact ⟨fun impossible => unknown_ne_direct site.scope site.name declaration impossible,
            False.elim⟩
  | some type =>
      cases field : type.lookup site.name with
      | none =>
          cases fallback : site.typedFallback <;> cases reference <;> simp_all [known]
      | some value =>
          cases reference <;> simp [known, field, eq_comm]

def freeze (site : Site Row) : Option Reference :=
  match resolve site with
  | .unique reference => some reference
  | .missing | .ambiguous => none

theorem freeze_exact (site : Site Row) (reference : Reference) :
    freeze site = some reference ↔ Selects site reference := by
  rw [← resolve_exact]
  cases resolved : resolve site <;> simp [freeze, resolved]

theorem ambiguous_freeze_rejects (site : Site Row) (ambiguous : resolve site = .ambiguous) :
    freeze site = none := by simp [freeze, ambiguous]

end Yulang.MethodResolution
