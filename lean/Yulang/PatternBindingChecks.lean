import Yulang.CasePatterns

/-!
# Static pattern binding checks

Q7 rejects duplicate binders on one matching path, while Q6 allows the same
name in different or alternatives and requires equal name sets. The check
combines finite name summaries; it never enumerates the product of or paths.
Outer lexical names are deliberately not part of this check: shadowing them
is permitted by Q4.
-/

namespace Yulang.PatternBindingChecks

open CasePatterns

def Disjoint (left right : List Nat) : Prop :=
  ∀ name, name ∈ left → name ∉ right

def disjointCheck (left right : List Nat) : Bool :=
  left.all (fun name => decide (name ∉ right))

theorem disjointCheck_exact (left right : List Nat) :
    disjointCheck left right = true ↔ Disjoint left right := by
  simp [disjointCheck, List.all_eq_true, Disjoint]

inductive NamesValid : Pattern F D → Prop where
  | wildcard : NamesValid .wildcard
  | bind : NamesValid (.bind name)
  | literal : NamesValid (.literal value)
  | intRange : NamesValid (.intRange lower upper)
  | pair : NamesValid p → NamesValid q → Disjoint p.names q.names → NamesValid (.pair p q)
  | recordEnd : NamesValid .recordEnd
  | field : NamesValid p → NamesValid q → Disjoint p.names q.names → NamesValid (.field name p q)
  | defaultField : NamesValid p → NamesValid q → Disjoint p.names q.names →
      NamesValid (.defaultField name fallback p q)
  | nil : NamesValid .nil
  | cons : NamesValid p → NamesValid q → Disjoint p.names q.names → NamesValid (.cons p q)
  | snoc : NamesValid p → NamesValid q → Disjoint p.names q.names → NamesValid (.snoc p q)
  | variant : NamesValid p → NamesValid (.variant tag p)
  | nominal : NamesValid p → NamesValid (.nominal typeId ctorId p)
  | or : NamesValid p → NamesValid q → (∀ name, name ∈ p.names ↔ name ∈ q.names) →
      NamesValid (.or p q)
  | as : NamesValid p → name ∉ p.names → NamesValid (.as p name)

def check : Pattern F D → Bool
  | .wildcard | .bind _ | .literal _ | .intRange _ _ | .recordEnd | .nil => true
  | .pair p q | .field _ p q | .defaultField _ _ p q | .cons p q | .snoc p q =>
      check p && check q && disjointCheck p.names q.names
  | .variant _ p | .nominal _ _ p => check p
  | .or p q => check p && check q && sameNames p.names q.names
  | .as p name => check p && decide (name ∉ p.names)

theorem check_exact (pattern : Pattern F D) : check pattern = true ↔ NamesValid pattern := by
  induction pattern with
  | wildcard => exact ⟨fun _ => .wildcard, fun _ => rfl⟩
  | bind name => exact ⟨fun _ => .bind, fun _ => rfl⟩
  | literal value => exact ⟨fun _ => .literal, fun _ => rfl⟩
  | intRange lower upper => exact ⟨fun _ => .intRange, fun _ => rfl⟩
  | recordEnd => exact ⟨fun _ => .recordEnd, fun _ => rfl⟩
  | nil => exact ⟨fun _ => .nil, fun _ => rfl⟩
  | pair p q ihp ihq =>
      simp only [check, Bool.and_eq_true, ihp, ihq, disjointCheck_exact]
      exact ⟨fun ⟨⟨a, b⟩, c⟩ => .pair a b c, fun h => by cases h with | pair a b c => exact ⟨⟨a, b⟩, c⟩⟩
  | field name p q ihp ihq =>
      simp only [check, Bool.and_eq_true, ihp, ihq, disjointCheck_exact]
      exact ⟨fun ⟨⟨a, b⟩, c⟩ => .field a b c, fun h => by cases h with | field a b c => exact ⟨⟨a, b⟩, c⟩⟩
  | defaultField name fallback p q ihp ihq =>
      simp only [check, Bool.and_eq_true, ihp, ihq, disjointCheck_exact]
      exact ⟨fun ⟨⟨a, b⟩, c⟩ => .defaultField a b c,
        fun h => by cases h with | defaultField a b c => exact ⟨⟨a, b⟩, c⟩⟩
  | cons p q ihp ihq =>
      simp only [check, Bool.and_eq_true, ihp, ihq, disjointCheck_exact]
      exact ⟨fun ⟨⟨a, b⟩, c⟩ => .cons a b c, fun h => by cases h with | cons a b c => exact ⟨⟨a, b⟩, c⟩⟩
  | snoc p q ihp ihq =>
      simp only [check, Bool.and_eq_true, ihp, ihq, disjointCheck_exact]
      exact ⟨fun ⟨⟨a, b⟩, c⟩ => .snoc a b c, fun h => by cases h with | snoc a b c => exact ⟨⟨a, b⟩, c⟩⟩
  | variant tag p ih =>
      simp only [check, ih]
      exact ⟨.variant, fun h => by cases h with | variant a => exact a⟩
  | nominal typeId ctorId p ih =>
      simp only [check, ih]
      exact ⟨.nominal, fun h => by cases h with | nominal a => exact a⟩
  | or p q ihp ihq =>
      simp only [check, Bool.and_eq_true, ihp, ihq, sameNames_exact]
      exact ⟨fun ⟨⟨a, b⟩, c⟩ => .or a b c, fun h => by cases h with | or a b c => exact ⟨⟨a, b⟩, c⟩⟩
  | as p name ih =>
      simp only [check, Bool.and_eq_true, ih, decide_eq_true_eq]
      exact ⟨fun ⟨a, b⟩ => .as a b, fun h => by cases h with | as a b => exact ⟨a, b⟩⟩

/-- A syntactic matching path chooses one side of each or; this does not
assume the path is reachable for any particular input value. -/
inductive BindingPath : Pattern F D → List Nat → Prop where
  | wildcard : BindingPath .wildcard []
  | bind : BindingPath (.bind name) [name]
  | literal : BindingPath (.literal value) []
  | intRange : BindingPath (.intRange lower upper) []
  | pair : BindingPath p left → BindingPath q right → BindingPath (.pair p q) (left ++ right)
  | recordEnd : BindingPath .recordEnd []
  | field : BindingPath p left → BindingPath q right → BindingPath (.field name p q) (left ++ right)
  | defaultField : BindingPath p left → BindingPath q right →
      BindingPath (.defaultField name fallback p q) (left ++ right)
  | nil : BindingPath .nil []
  | cons : BindingPath p left → BindingPath q right → BindingPath (.cons p q) (left ++ right)
  | snoc : BindingPath p left → BindingPath q right → BindingPath (.snoc p q) (left ++ right)
  | variant : BindingPath p names → BindingPath (.variant tag p) names
  | nominal : BindingPath p names → BindingPath (.nominal typeId ctorId p) names
  | orLeft : BindingPath p names → BindingPath (.or p q) names
  | orRight : BindingPath q names → BindingPath (.or p q) names
  | as : BindingPath p names → BindingPath (.as p name) (name :: names)

theorem BindingPath.names {pattern : Pattern F D} {boundNames : List Nat}
    (path : BindingPath pattern boundNames) (valid : NamesValid pattern) :
    ∀ name, name ∈ boundNames ↔ name ∈ pattern.names := by
  induction path with
  | wildcard | bind | literal | intRange | recordEnd | nil => intro name; rfl
  | pair a b iha ihb | field a b iha ihb | defaultField a b iha ihb
    | cons a b iha ihb | snoc a b iha ihb =>
      cases valid
      rename_i av bv apart
      intro name
      simp only [Pattern.names, List.mem_append, iha av name, ihb bv name]
  | variant child ih | nominal child ih =>
      cases valid
      rename_i good
      exact ih good
  | orLeft child ih =>
      cases valid with
      | or left right same => exact ih left
  | orRight child ih =>
      cases valid with
      | or left right same =>
          intro name
          exact (ih right name).trans (same name).symm
  | as child ih =>
      cases valid with
      | as good fresh =>
          intro name
          simp only [Pattern.names, List.mem_cons, ih good name]

theorem NamesValid.path_nodup (valid : NamesValid pattern) (path : BindingPath pattern names) :
    names.Nodup := by
  induction path with
  | wildcard | bind | literal | intRange | recordEnd | nil => simp
  | pair a b iha ihb | field a b iha ihb | defaultField a b iha ihb
    | cons a b iha ihb | snoc a b iha ihb =>
      cases valid
      rename_i av bv apart
      rw [List.nodup_append]
      refine ⟨iha av, ihb bv, ?_⟩
      intro name member other present equal
      subst other
      exact apart name ((a.names av name).mp member) ((b.names bv name).mp present)
  | variant child ih | nominal child ih =>
      cases valid
      rename_i good
      exact ih good
  | orLeft child ih =>
      cases valid with
      | or left right same => exact ih left
  | orRight child ih =>
      cases valid with
      | or left right same => exact ih right
  | as child ih =>
      cases valid with
      | as good fresh =>
          exact List.nodup_cons.mpr ⟨fun member => fresh ((child.names good _).mp member), ih good⟩

theorem checked_path_nodup (pattern : Pattern F D) (accepted : check pattern = true)
    (path : BindingPath pattern names) : names.Nodup :=
  ((check_exact pattern).mp accepted).path_nodup path

theorem duplicate_pair_rejected (name : Nat) :
    check (Pattern.pair (F := F) (Default := D) (.bind name) (.bind name)) = false := by
  simp [check, disjointCheck, Pattern.names]

theorem duplicate_as_rejected (name : Nat) :
    check (Pattern.as (F := F) (Default := D) (.bind name) name) = false := by
  simp [check, Pattern.names]

theorem same_name_in_alternatives_allowed (name : Nat) :
    check (Pattern.or (F := F) (Default := D) (.bind name) (.bind name)) = true := by
  simp [check, sameNames, Pattern.names]

end Yulang.PatternBindingChecks
