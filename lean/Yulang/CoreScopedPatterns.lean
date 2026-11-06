import Yulang.CorePatterns

/-! The scoped pattern AST is already polymorphic in its default-code type.
This bridge instantiates that type with Core expressions and preserves the
preceding-binding scope, without changing historical CaseTree defaults. -/
namespace Yulang.Core.Scoped
open CaseValues CasePatterns
variable {F : Type}
def embed (scope : List Nat) : Pattern F (CaseDataTerms.Expr F) → Pattern F (Data.Term F)
  | .wildcard => .wildcard
  | .bind a => .bind a
  | .literal a => .literal a
  | .intRange a b => .intRange a b
  | .pair a b => .pair (embed scope a) (embed (a.names ++ scope) b)
  | .recordEnd => .recordEnd
  | .field a b c => .field a (embed scope b) (embed (b.names ++ scope) c)
  | .defaultField a b c d => .defaultField a (Data.embed scope b) (embed scope c) (embed (c.names ++ scope) d)
  | .nil => .nil
  | .cons a b => .cons (embed scope a) (embed (a.names ++ scope) b)
  | .snoc a b => .snoc (embed scope a) (embed (a.names ++ scope) b)
  | .variant a b => .variant a (embed scope b)
  | .nominal a b c => .nominal a b (embed scope c)
  | .or a b => .or (embed scope a) (embed scope b)
  | .as a b => .as (embed scope a) b


@[simp] theorem names_embed (scope : List Nat) (p : Pattern F (CaseDataTerms.Expr F)) :
    (embed scope p).names = p.names := by
  induction p generalizing scope <;> simp [embed, Pattern.names, *]

def DefaultTyped (types : List (Nat × Ty F)) (code : Data.Term F) (type : Ty F) : Prop :=
  Data.Typing (types.map Prod.snd) code type

abbrev Typing := ScopedCasePatterns.Typing (F := F) DefaultTyped

theorem preserved
    (h : ScopedCasePatterns.Typing CaseDataTerms.DefaultTyped types pattern input bindings) :
    Typing types (embed (types.map Prod.fst) pattern) input bindings := by
  induction h
  all_goals try simp only [embed] at *
  case pair p q ihp ihq =>
    exact .pair ihp (by simpa [List.map_append, Patterns.scoped_names p] using ihq)
  case field below p rest ihp ihr =>
    exact .field below ihp (by simpa [List.map_append, Patterns.scoped_names p] using ihr)
  case defaultField below default p rest ihp ihr =>
    exact .defaultField below (Data.preserved default) ihp
      (by simpa [List.map_append, Patterns.scoped_names p] using ihr)
  case cons p rest ihp ihr =>
    exact .cons ihp (by simpa [List.map_append, Patterns.scoped_names p] using ihr)
  case snoc init last ihi ihl =>
    exact .snoc ihi (by simpa [List.map_append, Patterns.scoped_names init] using ihl)
  all_goals first
    | apply ScopedCasePatterns.Typing.wildcard <;> assumption
    | apply ScopedCasePatterns.Typing.bind <;> assumption
    | apply ScopedCasePatterns.Typing.literal <;> assumption
    | apply ScopedCasePatterns.Typing.intRange <;> assumption
    | apply ScopedCasePatterns.Typing.recordEnd <;> assumption
    | apply ScopedCasePatterns.Typing.nil <;> assumption
    | apply ScopedCasePatterns.Typing.variant <;> assumption
    | apply ScopedCasePatterns.Typing.mergedVariant <;> assumption
    | apply ScopedCasePatterns.Typing.nominal <;> assumption
    | apply ScopedCasePatterns.Typing.mergedNominal <;> assumption
    | apply ScopedCasePatterns.Typing.or <;> assumption
    | apply ScopedCasePatterns.Typing.as <;> assumption
    | apply ScopedCasePatterns.Typing.narrow <;> assumption

theorem reflected (h : Typing types pattern input bindings) :
    ∀ source, embed (types.map Prod.fst) source = pattern →
      ScopedCasePatterns.Typing CaseDataTerms.DefaultTyped types source input bindings := by
  induction h
  all_goals intro source syntaxEq
  case narrow below h ih => exact .narrow below (ih source syntaxEq)
  all_goals cases source <;> simp only [embed] at syntaxEq
  all_goals cases syntaxEq
  case pair.pair.refl =>
    rename_i types a left b right p q hp ihp hq ihq
    have names : left.map Prod.fst = p.names := by simpa using Patterns.scoped_names hp
    exact .pair (ihp p rfl) (ihq q (by simp [List.map_append, names]))
  case field.field.refl =>
    rename_i input name payload types left right below p q hp ihp hq ihq
    have names : left.map Prod.fst = p.names := by simpa using Patterns.scoped_names hp
    exact .field below (ihp p rfl) (ihq q (by simp [List.map_append, names]))
  case cons.cons.refl =>
    rename_i types element left right p q hp ihp hq ihq
    have names : left.map Prod.fst = p.names := by simpa using Patterns.scoped_names hp
    exact .cons (ihp p rfl) (ihq q (by simp [List.map_append, names]))
  case snoc.snoc.refl =>
    rename_i types element left right p q hp ihp hq ihq
    have names : left.map Prod.fst = p.names := by simpa using Patterns.scoped_names hp
    exact .snoc (ihp p rfl) (ihq q (by simp [List.map_append, names]))
  case defaultField.defaultField.refl =>
    rename_i input name payload types fallbackType left right below fallback p q default hp ihp hq ihq
    have names : left.map Prod.fst = p.names := by simpa using Patterns.scoped_names hp
    exact .defaultField below (Data.reflected default types fallback rfl rfl)
      (ihp p rfl) (ihq q (by simp [List.map_append, names]))
  all_goals first
    | apply ScopedCasePatterns.Typing.wildcard
    | apply ScopedCasePatterns.Typing.bind
    | apply ScopedCasePatterns.Typing.literal
    | apply ScopedCasePatterns.Typing.intRange
    | apply ScopedCasePatterns.Typing.recordEnd
    | apply ScopedCasePatterns.Typing.nil
    | apply ScopedCasePatterns.Typing.variant
    | apply ScopedCasePatterns.Typing.mergedVariant
    | apply ScopedCasePatterns.Typing.nominal
    | apply ScopedCasePatterns.Typing.mergedNominal
    | apply ScopedCasePatterns.Typing.or
    | apply ScopedCasePatterns.Typing.as
  all_goals solve_by_elim


theorem conservative (types : List (Nat × Ty F))
    (pattern : Pattern F (CaseDataTerms.Expr F)) (input : Ty F)
    (bindings : List (Nat × Ty F)) :
    ScopedCasePatterns.Typing CaseDataTerms.DefaultTyped types pattern input bindings ↔
      Typing types (embed (types.map Prod.fst) pattern) input bindings := by
  constructor
  · exact preserved
  · intro h; exact reflected h pattern rfl

end Yulang.Core.Scoped
