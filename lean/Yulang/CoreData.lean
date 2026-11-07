import Yulang.CoreExpr
import Yulang.CaseDataTerms

/-! Named data leaves are translated relative to an explicit lexical stack.
Unbound resolved names remain `free`; they cannot acquire a local type. -/
namespace Yulang.Core.Data
open CaseValues
abbrev Term (F : Type) := Core.Expr ⟨Empty, Empty, Empty, F, Empty⟩

def resolve (name : Nat) : List Nat → Option Nat
  | [] => none
  | key :: rest => if name = key then some 0 else (resolve name rest).map Nat.succ

def localVar (scope : List Nat) (name : Nat) : Term F :=
  match resolve name scope with
  | some index => .var index
  | none => .free name

def embed (scope : List Nat) : CaseDataTerms.Expr F → Term F
  | .value value => .data value
  | .var name => localVar scope name
  | .pair a b => .pair (embed scope a) (embed scope b)
  | .fst a => .fst (embed scope a)
  | .snd a => .snd (embed scope a)
  | .emptyRecord => .emptyRecord
  | .record name a b => .record name (embed scope a) (embed scope b)
  | .recordDefault name a b => .recordDefault name (embed scope a) (embed scope b)
  | .field name a => .field name (embed scope a)
  | .variant name a => .variant name (embed scope a)
  | .nominal ty ctor a => .nominal ty ctor (embed scope a)
  | .nil => .nil
  | .cons a b => .cons (embed scope a) (embed scope b)
  | .letE name a b => .letE (some name) (embed scope a) (embed (name :: scope) b)


/-- Binder identities are retained only as hints, making the named presentation
recoverable while all variable occurrences remain positional. -/
def decode (scope : List Nat) : Term F → CaseDataTerms.Expr F
  | .data value => .value value
  | .var index => .var ((scope[index]?).getD 0)
  | .free name => .var name
  | .pair a b => .pair (decode scope a) (decode scope b)
  | .fst a => .fst (decode scope a)
  | .snd a => .snd (decode scope a)
  | .emptyRecord => .emptyRecord
  | .record name a b => .record name (decode scope a) (decode scope b)
  | .recordDefault name a b => .recordDefault name (decode scope a) (decode scope b)
  | .field name a => .field name (decode scope a)
  | .variant name a => .variant name (decode scope a)
  | .nominal ty ctor a => .nominal ty ctor (decode scope a)
  | .nil => .nil
  | .cons a b => .cons (decode scope a) (decode scope b)
  | .letE (some name) a b => .letE name (decode scope a) (decode (name :: scope) b)
  | _ => .value (.literal .unit)

theorem resolve_at {scope : List Nat} (h : resolve name scope = some index) :
    scope[index]? = some name := by
  induction scope generalizing index with
  | nil => simp [resolve] at h
  | cons key rest ih =>
    by_cases same : name = key
    · simp [resolve, same] at h
      subst index; simp [same]
    · simp only [resolve, same, ↓reduceIte] at h
      cases found : resolve name rest with
      | none => simp [found] at h
      | some i =>
        simp only [found, Option.map_some, Option.some.injEq] at h
        subst index
        exact ih found

@[simp] theorem decode_embed (scope : List Nat) (expression : CaseDataTerms.Expr F) :
    decode scope (embed scope expression) = expression := by
  induction expression generalizing scope <;> simp [embed, decode, *]
  rename_i name
  unfold localVar
  cases found : resolve name scope with
  | none => rfl
  | some index => simp [decode, resolve_at found]

open CaseDataTerms (recordType defaultType consType)

inductive Typing : List (Ty F) → Term F → Ty F → Prop where
  | value : Typing types (.data value) (Ty.exact value)
  | var : types[name]? = some type → Typing types (.var name) type
  | pair : Typing types left a → Typing types right b → Typing types (.pair left right) (Ty.pair a b)
  | fst : Typing types pair (Ty.pair a b) → Typing types (.fst pair) a
  | snd : Typing types pair (Ty.pair a b) → Typing types (.snd pair) b
  | emptyRecord : Typing types .emptyRecord (Ty.exact (.record []))
  | record : Typing types head headType → Typing types tail tailType → Ty.Le tailType Ty.records →
      Typing types (.record name head tail) (recordType name headType tailType)
  | recordDefault : Typing types source sourceType → Typing types fallback fallbackType →
      Ty.Le sourceType Ty.records →
      Typing types (.recordDefault name source fallback) (defaultType name sourceType fallbackType)
  | field : Typing types source input → Ty.Le input (Ty.required name payload) →
      Typing types (.field name source) payload
  | variant : Typing types payload type → Typing types (.variant tag payload) (Ty.variant tag type)
  | nominal : Typing types payload type →
      Typing types (.nominal typeId ctorId payload) (Ty.nominal typeId ctorId type)
  | nil : Typing types .nil (Ty.exact (.list []))
  | cons : Typing types head headType → Typing types tail tailType → Ty.Le tailType (Ty.list Ty.any) →
      Typing types (.cons head tail) (consType headType tailType)
  | letE : Typing types value input → Typing (input :: types) body output →
      Typing types (.letE (some name) value body) output
  | widen : Typing types expression input → Ty.Le input output → Typing types expression output

def model (F : Type) : TypingModel ⟨Empty, Empty, Empty, F, Empty⟩ :=
  ⟨List (Ty F), Ty F, Typing⟩

theorem lookup_resolve (types : List (Nat × Ty F)) (name : Nat) :
    (resolve name (types.map Prod.fst)).bind (fun i => (types.map Prod.snd)[i]?) =
      CaseDataTerms.lookupType name types := by
  induction types with
  | nil => rfl
  | cons head rest ih =>
    rcases head with ⟨key, type⟩
    by_cases eq : name = key
    · simp [resolve, CaseDataTerms.lookupType, eq]
    · simp only [List.map_cons, resolve, eq, ↓reduceIte, CaseDataTerms.lookupType,
        Option.bind_map, List.getElem?_cons_succ, Function.comp_def]
      exact ih

theorem variable_preserved (h : CaseDataTerms.lookupType name types = some type) :
    Typing (types.map Prod.snd) (localVar (types.map Prod.fst) name) type := by
  have found := lookup_resolve types name
  rw [h] at found
  cases eq : resolve name (types.map Prod.fst) with
  | none => simp [eq] at found
  | some index =>
    simp only [eq, Option.bind_some] at found
    simp only [localVar, eq]
    exact .var found

theorem preserved (h : CaseDataTerms.Typing types expression target) :
    Typing (types.map Prod.snd) (embed (types.map Prod.fst) expression) target := by
  induction h
  all_goals try simp only [embed, List.map_cons] at *
  case var h => exact variable_preserved h
  all_goals first
    | apply Typing.value <;> assumption
    | apply Typing.pair <;> assumption
    | apply Typing.fst <;> assumption
    | apply Typing.snd <;> assumption
    | apply Typing.emptyRecord <;> assumption
    | apply Typing.record <;> assumption
    | apply Typing.recordDefault <;> assumption
    | apply Typing.field <;> assumption
    | apply Typing.variant <;> assumption
    | apply Typing.nominal <;> assumption
    | apply Typing.nil <;> assumption
    | apply Typing.cons <;> assumption
    | apply Typing.letE <;> assumption
    | apply Typing.widen <;> assumption


theorem reflected {context : List (Ty F)} {expression : Term F} {target : Ty F}
    (h : Typing context expression target) :
    ∀ (types : List (Nat × Ty F)) (source : CaseDataTerms.Expr F),
      types.map Prod.snd = context → embed (types.map Prod.fst) source = expression →
      CaseDataTerms.Typing types source target := by
  induction h
  all_goals intro types source contextEq syntaxEq
  case widen h compatible ih => exact .widen (ih types source contextEq syntaxEq) compatible
  case var found =>
    cases source <;> simp only [embed] at syntaxEq
    all_goals try cases syntaxEq
    rename_i name
    unfold localVar at syntaxEq
    cases resolved : resolve name (types.map Prod.fst) with
    | none => simp [resolved] at syntaxEq
    | some index =>
      simp only [resolved] at syntaxEq
      cases syntaxEq
      apply CaseDataTerms.Typing.var
      have lookup := lookup_resolve types name
      simpa [resolved, contextEq, found] using lookup.symm
  all_goals cases source <;> simp only [embed] at syntaxEq
  all_goals try { unfold localVar at syntaxEq; split at syntaxEq <;> cases syntaxEq }
  all_goals cases syntaxEq
  all_goals first
    | apply CaseDataTerms.Typing.value
    | apply CaseDataTerms.Typing.pair
    | apply CaseDataTerms.Typing.fst
    | apply CaseDataTerms.Typing.snd
    | apply CaseDataTerms.Typing.emptyRecord
    | apply CaseDataTerms.Typing.record
    | apply CaseDataTerms.Typing.recordDefault
    | apply CaseDataTerms.Typing.field
    | apply CaseDataTerms.Typing.variant
    | apply CaseDataTerms.Typing.nominal
    | apply CaseDataTerms.Typing.nil
    | apply CaseDataTerms.Typing.cons
    | apply CaseDataTerms.Typing.letE
  all_goals try solve_by_elim
  all_goals try simp only [List.map_cons]
  all_goals try solve_by_elim
  all_goals apply_assumption <;> simp_all only [List.map_cons]

theorem conservative (types : List (Nat × Ty F))
    (expression : CaseDataTerms.Expr F) (target : Ty F) :
    CaseDataTerms.Typing types expression target ↔
      Core.Typing (model F) (types.map Prod.snd)
        (embed (types.map Prod.fst) expression) target := by
  constructor
  · exact preserved
  · intro h; exact reflected h types expression rfl rfl

end Yulang.Core.Data
