import Yulang.CommonPatternSourcePresence

/-! Finite declared-presence checks before pattern constraint generation.

A resolved input record declaration is associated with each original pattern
position. Field lookup uses first-field-wins. A missing declaration or an
unresolved field stays `unknown`; it is neither optional nor an inferred
type error. Reports retain every required-field error and unresolved site.

These are checks of source metadata. Deriving all nested input declarations
from source typing is a separate obligation; ordinary semantic subtyping
cannot recover the distinction between a required field and an optional
demand. This module does not decide optional-field patterns without defaults.
-/

namespace Yulang.CommonPatternDeclaredPresence

open CasePatterns (Pattern)
open CasePresenceValidation (Presence DefaultAllowed)
open CommonPatternSourcePresence (Path Site sites DefaultAt sites_exact)

abbrev Fields := List (Nat × Presence)
abbrev Declarations := List (Path × Fields)

def field (fields : Fields) (name : Nat) : Presence :=
  match fields with
  | [] => .unknown
  | (label, presence) :: rest => if name = label then presence else field rest name

def record (declarations : Declarations) (path : Path) : Option Fields :=
  match declarations with
  | [] => none
  | (position, fields) :: rest => if path = position then some fields else record rest path

def resolve (declarations : Declarations) (site : Site) : Presence :=
  match record declarations site.1 with
  | none => .unknown
  | some fields => field fields site.2

def Legal (declarations : Declarations) (pattern : Pattern F D) : Prop :=
  ∀ path name, DefaultAt pattern path name → DefaultAllowed (resolve declarations (path, name))

def check (declarations : Declarations) (pattern : Pattern F D) : Bool :=
  (sites pattern).all fun site => decide (resolve declarations site = .optional)

theorem optional_exact (presence : Presence) : presence = .optional ↔ DefaultAllowed presence := by
  cases presence with
  | required => constructor <;> intro impossible <;> cases impossible
  | optional => exact ⟨fun _ => .optional, fun _ => rfl⟩
  | unknown => constructor <;> intro impossible <;> cases impossible

/-- The finite gate accepts exactly when every actual source default has a
resolved optional field. The original pattern, both branches and all source
positions remain fixed; no default evaluation is assumed. -/
theorem check_exact (declarations : Declarations) (pattern : Pattern F D) :
    check declarations pattern = true ↔ Legal declarations pattern := by
  simp only [check, List.all_eq_true, decide_eq_true_eq, optional_exact, Legal]
  constructor
  · intro accepted path name atSource
    exact accepted (path, name) ((sites_exact pattern path name).mpr atSource)
  · intro legal site member
    exact legal site.1 site.2 ((sites_exact pattern site.1 site.2).mp member)

structure Report where
  required : List Site
  unresolved : List Site
  deriving DecidableEq, Repr

def report (declarations : Declarations) (pattern : Pattern F D) : Report :=
  ⟨(sites pattern).filter fun site => decide (resolve declarations site = .required),
   (sites pattern).filter fun site => decide (resolve declarations site = .unknown)⟩

/-- Diagnostics name exactly the offending source occurrence, even when an
earlier branch will match at runtime. This does not choose an effect-row
policy for unreachable arms. -/
theorem required_report_exact (declarations : Declarations) (pattern : Pattern F D)
    (path : Path) (name : Nat) :
    (path, name) ∈ (report declarations pattern).required ↔
      DefaultAt pattern path name ∧ resolve declarations (path, name) = .required := by
  simp [report, sites_exact]

theorem unresolved_report_exact (declarations : Declarations) (pattern : Pattern F D)
    (path : Path) (name : Nat) :
    (path, name) ∈ (report declarations pattern).unresolved ↔
      DefaultAt pattern path name ∧ resolve declarations (path, name) = .unknown := by
  simp [report, sites_exact]

theorem required_not_legal (declarations : Declarations) (pattern : Pattern F D)
    (path : Path) (name : Nat) (atSource : DefaultAt pattern path name)
    (required : resolve declarations (path, name) = .required) :
    ¬ Legal declarations pattern := by
  intro legal
  have permitted := legal path name atSource
  rw [required] at permitted
  cases permitted

theorem unresolved_not_legal (declarations : Declarations) (pattern : Pattern F D)
    (path : Path) (name : Nat) (atSource : DefaultAt pattern path name)
    (unknown : resolve declarations (path, name) = .unknown) :
    ¬ Legal declarations pattern := by
  intro legal
  have permitted := legal path name atSource
  rw [unknown] at permitted
  cases permitted

/-- Hidden same-name field declarations cannot change the validation of the
first visible field. This holds for arbitrary tails and either presence. -/
theorem first_field_wins (path : Path) (name : Nat) (presence : Presence)
    (hidden : Fields) (later : Declarations) :
    resolve ((path, (name, presence) :: hidden) :: later) (path, name) = presence := by
  simp [resolve, record, field]

end Yulang.CommonPatternDeclaredPresence
