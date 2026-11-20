import Yulang.GeneralSourceMetadataBuildRoles291

/-! Interface for a deliberately small symbolic fragment. Numeric IDs are supplied
by independent name-resolution environments, not by syntax occurrences. -/
namespace Yulang.GeneralSourceRoleSpelling292
open GeneralSourceMetadataBareRole291 (BareRow)

structure Environment where
  role : String → Option Nat
  output : Nat → String → Option Nat
  nullaryConstructor : String → Option Nat

inductive Body where
  | required
  | binder : String → Body
  | nullary : String → Body
  deriving DecidableEq, Repr

structure Output where
  spelling : String
  body : Body
  deriving DecidableEq, Repr

structure Role where
  spelling : String
  binders : List String
  outputs : List Output
  deriving DecidableEq, Repr

inductive Position (s : String) : List String → Nat → Prop
  | first {xs} : Position s (s :: xs) 0
  | rest {x xs n} : x ≠ s → Position s xs n → Position s (x :: xs) (n+1)

def position (s : String) : List String → Option Nat
  | [] => none
  | x :: xs => if x = s then some 0 else (position s xs).map (·+1)

theorem position_exact (s : String) (xs : List String) (n : Nat) :
    position s xs = some n ↔ Position s xs n := by
  induction xs generalizing n with
  | nil => constructor <;> intro h <;> cases h
  | cons x xs ih =>
    constructor
    · intro h
      by_cases same : x = s
      · simp [position,same] at h
        subst x
        subst n
        exact .first
      · cases e : position s xs with
        | none => simp [position,same,e] at h
        | some k =>
          have eq : k+1 = n := by simpa [position,same,e] using h
          subst n
          exact .rest same ((ih k).mp e)
    · intro h
      cases h with
      | first => simp [position]
      | rest diff near => simp [position,diff,(ih _).mpr near]

theorem position_index {s : String} {xs : List String} {n : Nat}
    (located : Position s xs n) : xs[n]? = some s := by
  induction located with
  | first => rfl
  | rest _ _ ih => exact ih

theorem position_lt {s : String} {xs : List String} {n : Nat}
    (located : Position s xs n) : n < xs.length := by
  induction located with
  | first => simp
  | rest _ _ ih => simpa using Nat.succ_lt_succ ih

inductive ResolvedBody (env : Environment) (binders : List String) :
    Body → Option Roles.Term → Prop
  | required : ResolvedBody env binders .required none
  | binder {name index} : Position name binders index →
      ResolvedBody env binders (.binder name) (some (.var index))
  | nullary {name id} : env.nullaryConstructor name = some id →
      ResolvedBody env binders (.nullary name) (some (.app id []))

def body (env : Environment) (binders : List String) :
    Body → Option (Option Roles.Term)
  | .required => some none
  | .binder name => (position name binders).map fun i => some (.var i)
  | .nullary name => (env.nullaryConstructor name).map fun i => some (.app i [])

theorem body_exact (env : Environment) (binders : List String)
    (input : Body) (value : Option Roles.Term) :
    body env binders input = some value ↔ ResolvedBody env binders input value := by
  constructor
  · intro eq
    cases input with
    | required =>
      have h : none = value := Option.some.inj eq
      cases h
      exact .required
    | binder name =>
      cases h : position name binders with
      | none => simp [body,h] at eq
      | some i =>
        have h' : some (.var i) = value := by simpa [body,h] using eq
        cases h'
        exact .binder ((position_exact ..).mp h)
    | nullary name =>
      cases h : env.nullaryConstructor name with
      | none => simp [body,h] at eq
      | some i =>
        have h' : some (.app i []) = value := by simpa [body,h] using eq
        cases h'
        exact .nullary h
  · intro resolved
    cases resolved with
    | required => rfl
    | binder h => simp [body,(position_exact ..).mpr h]
    | nullary h => simp [body,h]

theorem body_scoped {env : Environment} {binders : List String}
    {input : Body} {term : Roles.Term} (h : ResolvedBody env binders input (some term)) :
    term.bound ≤ binders.length := by
  cases h with
  | binder h => exact position_lt h
  | nullary _ => simp [Roles.Term.bound,Roles.argsBound]

end Yulang.GeneralSourceRoleSpelling292
