import Yulang.DirectedBounds
import Yulang.RowInference
import Yulang.SignedStructural

/-!
# Checked resolved programs have their declared operational effects

This is the monomorphic, shape-resolved fragment of the computation-argument
calculus. The syntax carries lambda input annotations and handler result types;
the executable checker discovers the remaining latent rows. Its independent
typing judgement mentions neither evaluation nor a semantic effect bound.

Evaluation uses the existing signed request trees and shallow handler. An
application passes its argument as a suspended computation, and a resumption
keeps the action's original row. Handler-arm effects lie outside subtraction.
Boundary nodes have the existing `RowInference.Boundary` meaning: they transform
immediate requests, not opaque data or latent functions returned by the body.

The atoms form one fixed carrier, also used for operation payloads and responses.
Products can store higher-order functions. Structural subtyping within a resolved
shape includes contravariant computation inputs and covariant outputs. The
fragment does not add source syntax, infer unresolved shapes, choose recursive
types, or claim whole-language elaboration, termination or progress.
-/

namespace Yulang.OperationalTyping

open Directed

inductive Shape where
  | atom
  | pair : Shape → Shape → Shape
  | arrow : Shape → Shape → Shape
  deriving DecidableEq, Repr

inductive VTy (n : Nat) (Key : Type) : Shape → Type where
  | atom : VTy n Key .atom
  | pair : VTy n Key a → VTy n Key b → VTy n Key (.pair a b)
  | arrow : VTy n Key a → Row n Key → VTy n Key b → Row n Key →
      VTy n Key (.arrow a b)

structure CTy (n : Nat) (Key : Type) (shape : Shape) where
  value : VTy n Key shape
  row : Row n Key

def CTy.pure (value : VTy n Key shape) : CTy n Key shape := ⟨value, []⟩

def CTy.arrow (input : CTy n Key a) (output : CTy n Key b) : VTy n Key (.arrow a b) :=
  .arrow input.value input.row output.value output.row

abbrev RowLe {n : Nat} {Key : Type} := @SignedStructural.RowLe n Key

def VLe : VTy n Key s → VTy n Key s → Prop
  | .atom, .atom => True
  | .pair a b, .pair c d => VLe a c ∧ VLe b d
  | .arrow a ea b eb, .arrow c ec d ed =>
      VLe c a ∧ RowLe ec ea ∧ VLe b d ∧ RowLe eb ed

def CLe (left right : CTy n Key shape) : Prop :=
  VLe left.value right.value ∧ RowLe left.row right.row

def checkRow [DecidableEq Key] (left right : Row n Key) : Bool :=
  left.all (fun occurrence => decide (occurrence ∈ right))

def checkV [DecidableEq Key] : VTy n Key s → VTy n Key s → Bool
  | .atom, .atom => true
  | .pair a b, .pair c d => checkV a c && checkV b d
  | .arrow a ea b eb, .arrow c ec d ed =>
      checkV c a && checkRow ec ea && checkV b d && checkRow eb ed

def checkC [DecidableEq Key] (left right : CTy n Key shape) : Bool :=
  checkV left.value right.value && checkRow left.row right.row

@[simp] theorem checkRow_exact [DecidableEq Key] (left right : Row n Key) :
    checkRow left right = true ↔ RowLe left right := by
  simp [checkRow, SignedStructural.RowLe]

@[simp] theorem checkV_exact [DecidableEq Key] (left right : VTy n Key s) :
    checkV left right = true ↔ VLe left right := by
  induction s with
  | atom => cases left; cases right; simp [checkV, VLe]
  | pair a b iha ihb =>
      cases left; cases right
      simp [checkV, VLe, iha, ihb]
  | arrow a b iha ihb =>
      cases left; cases right
      simp [checkV, VLe, iha, ihb, and_assoc]

@[simp] theorem checkC_exact [DecidableEq Key] (left right : CTy n Key shape) :
    checkC left right = true ↔ CLe left right := by
  simp [checkC, CLe]

inductive Var : List Shape → Shape → Type where
  | here : Var (s :: Γ) s
  | there : Var Γ s → Var (t :: Γ) s

structure Env (F : Shape → Type) (Γ : List Shape) where
  get : ∀ {s}, Var Γ s → F s

instance : CoeFun (Env F Γ) (fun _ => ∀ {s}, Var Γ s → F s) := ⟨Env.get⟩

def Env.nil : Env F [] := ⟨fun v => nomatch v⟩

def Env.cons (first : F s) (rest : Env F Γ) : Env F (s :: Γ) :=
  ⟨fun {_} index => match index with
    | .here => first
    | .there index => rest index⟩

@[simp] theorem Env.cons_here (first : F s) (rest : Env F Γ) :
    Env.cons first rest .here = first := rfl

@[simp] theorem Env.cons_there (first : F s) (rest : Env F Γ) (index : Var Γ t) :
    Env.cons first rest (.there index) = rest index := rfl

def Value (n : Nat) (Key Atom : Type) : Shape → Type
  | .atom => Atom
  | .pair a b => Value n Key Atom a × Value n Key Atom b
  | .arrow a b =>
      Computation n Key Atom Atom (Value n Key Atom a) →
        Computation n Key Atom Atom (Value n Key Atom b)

abbrev Tree (n : Nat) (Key Atom : Type) (s : Shape) :=
  Computation n Key Atom Atom (Value n Key Atom s)

def AllReturns (predicate : ValueType → Prop) :
    Computation n Key Payload Response ValueType → Prop
  | .pure value => predicate value
  | .request _ _ resume => ∀ response, AllReturns predicate (resume response)

def ValidValue : (t : VTy n Key s) → Value n Key Atom s → Prop
  | .atom, _ => True
  | .pair a b, value => ValidValue a value.1 ∧ ValidValue b value.2
  | .arrow a ea b eb, function =>
      ∀ argument, Computation.BoundedBy ea argument → AllReturns (ValidValue a) argument →
        Computation.BoundedBy eb (function argument) ∧ AllReturns (ValidValue b) (function argument)

def Valid (t : CTy n Key s) (computation : Tree n Key Atom s) : Prop :=
  Computation.BoundedBy t.row computation ∧ AllReturns (ValidValue t.value) computation

def EnvValid (types : Env (CTy n Key) Γ) (runtime : Env (Tree n Key Atom) Γ) : Prop :=
  ∀ {s} (index : Var Γ s), Valid (types index) (runtime index)

abbrev Boundary (n : Nat) (Key : Type) := RowInference.Boundary Key (Fin n)

def Boundary.transform : Boundary n Key → Occurrence n Key → Occurrence n Key
  | .protect scope permission => Directed.protect scope permission
  | .release scope permission => Directed.release scope permission

def Boundary.row (boundary : Boundary n Key) (row : Row n Key) : Row n Key :=
  row.map boundary.transform

@[simp] theorem Boundary.row_agrees [DecidableEq Key] (boundary : Boundary n Key)
    (row : Row n Key) :
    boundary.row row = RowInference.Boundary.row (RowInference.signedAlgebra n Key) boundary row := by
  cases boundary <;> rfl

inductive Expr (n : Nat) (Key Atom : Type) : List Shape → Shape → Type where
  | var : Var Γ s → Expr n Key Atom Γ s
  | lit : Atom → Expr n Key Atom Γ .atom
  | lam : CTy n Key a → Expr n Key Atom (a :: Γ) b → Expr n Key Atom Γ (.arrow a b)
  | app : Expr n Key Atom Γ (.arrow a b) → Expr n Key Atom Γ a → Expr n Key Atom Γ b
  | pair : Expr n Key Atom Γ a → Expr n Key Atom Γ b → Expr n Key Atom Γ (.pair a b)
  | fst : Expr n Key Atom Γ (.pair a b) → Expr n Key Atom Γ a
  | snd : Expr n Key Atom Γ (.pair a b) → Expr n Key Atom Γ b
  | letE : Expr n Key Atom Γ a → Expr n Key Atom (a :: Γ) b → Expr n Key Atom Γ b
  | request : Key → Expr n Key Atom Γ .atom → Expr n Key Atom Γ .atom
  | boundary : Boundary n Key → Expr n Key Atom Γ s → Expr n Key Atom Γ s
  | handler : Key → VTy n Key b → Expr n Key Atom Γ a →
      Expr n Key Atom (a :: Γ) b →
      Expr n Key Atom (.atom :: .arrow .atom a :: Γ) b → Expr n Key Atom Γ b
  | widen : CTy n Key s → Expr n Key Atom Γ s → Expr n Key Atom Γ s

def operationTypes (types : Env (CTy n Key) Γ) (input : CTy n Key a) :
    Env (CTy n Key) (.atom :: .arrow .atom a :: Γ) :=
  Env.cons (CTy.pure .atom)
    (Env.cons (CTy.pure (CTy.arrow (CTy.pure .atom) input)) types)

def eval [DecidableEq Key] (runtime : Env (Tree n Key Atom) Γ) :
    Expr n Key Atom Γ s → Tree n Key Atom s
  | .var index => runtime index
  | .lit value => .pure value
  | .lam _ body => .pure (fun argument => eval (Env.cons argument runtime) body)
  | .app function argument => (eval runtime function).bind fun f => f (eval runtime argument)
  | .pair left right => (eval runtime left).bind fun a =>
      (eval runtime right).bind fun b => .pure (a, b)
  | .fst pair => (eval runtime pair).bind fun value => .pure value.1
  | .snd pair => (eval runtime pair).bind fun value => .pure value.2
  | .letE value body => (eval runtime value).bind fun v => eval (Env.cons (.pure v) runtime) body
  | .request key payload => (eval runtime payload).bind fun value =>
      .request (raw key) value (fun response => .pure response)
  | .boundary boundary body => Computation.mapRequests boundary.transform (eval runtime body)
  | .handler key _ action onReturn onOperation =>
      Computation.shallowHandle [key]
        (fun value => eval (Env.cons (.pure value) runtime) onReturn)
        (fun _ payload resume =>
          eval (Env.cons (s := .atom) (.pure payload)
            (Env.cons (s := .arrow .atom _) (.pure (fun argument => argument.bind resume)) runtime))
            onOperation)
        (eval runtime action)
  | .widen _ body => eval runtime body

inductive Typing [DecidableEq Key] : {Γ : List Shape} →
    Env (CTy n Key) Γ → {s : Shape} → Expr n Key Atom Γ s → CTy n Key s → Prop where
  | var : Typing types (.var index) (types index)
  | lit : Typing types (.lit value) (CTy.pure .atom)
  | lam : Typing (Env.cons input types) body output →
      Typing types (.lam input body) (CTy.pure (CTy.arrow input output))
  | app : Typing types function ⟨CTy.arrow input output, functionRow⟩ →
      Typing types argument actual → CLe actual input →
      Typing types (.app function argument) ⟨output.value, functionRow ++ output.row⟩
  | pair : Typing types left a → Typing types right b →
      Typing types (.pair left right) ⟨.pair a.value b.value, a.row ++ b.row⟩
  | fst : Typing types pair ⟨.pair a b, row⟩ → Typing types (.fst pair) ⟨a, row⟩
  | snd : Typing types pair ⟨.pair a b, row⟩ → Typing types (.snd pair) ⟨b, row⟩
  | letE : Typing types value input → Typing (Env.cons (CTy.pure input.value) types) body output →
      Typing types (.letE value body) ⟨output.value, input.row ++ output.row⟩
  | request : Typing types payload ⟨.atom, row⟩ →
      Typing types (.request key payload) ⟨.atom, row ++ [raw key]⟩
  | boundary : Typing types body input →
      Typing types (.boundary boundary body) ⟨input.value, boundary.row input.row⟩
  | handler : Typing types action input →
      Typing (Env.cons (CTy.pure input.value) types) onReturn returned →
      Typing (operationTypes types input) onOperation operated →
      VLe returned.value target → VLe operated.value target →
      Typing types (.handler key target action onReturn onOperation)
        ⟨target, residual [key] input.row ++ (returned.row ++ operated.row)⟩
  | widen : Typing types body input → CLe input target →
      Typing types (.widen target body) target

def infer [DecidableEq Key] (types : Env (CTy n Key) Γ) :
    Expr n Key Atom Γ s → Option (CTy n Key s)
  | .var index => some (types index)
  | .lit _ => some (CTy.pure .atom)
  | .lam input body => do
      let output ← infer (Env.cons input types) body
      return CTy.pure (CTy.arrow input output)
  | .app function argument => do
      let ⟨.arrow a ea b eb, functionRow⟩ ← infer types function
      let actual ← infer types argument
      if checkC actual ⟨a, ea⟩ then return ⟨b, functionRow ++ eb⟩ else none
  | .pair left right => do
      let a ← infer types left
      let b ← infer types right
      return ⟨.pair a.value b.value, a.row ++ b.row⟩
  | .fst pair => do
      let ⟨.pair a _, row⟩ ← infer types pair
      return ⟨a, row⟩
  | .snd pair => do
      let ⟨.pair _ b, row⟩ ← infer types pair
      return ⟨b, row⟩
  | .letE value body => do
      let input ← infer types value
      let output ← infer (Env.cons (CTy.pure input.value) types) body
      return ⟨output.value, input.row ++ output.row⟩
  | .request key payload => do
      let input ← infer types payload
      return ⟨.atom, input.row ++ [raw key]⟩
  | .boundary boundary body => do
      let input ← infer types body
      return ⟨input.value, boundary.row input.row⟩
  | .handler key target action onReturn onOperation => do
      let input ← infer types action
      let returned ← infer (Env.cons (CTy.pure input.value) types) onReturn
      let operated ← infer (operationTypes types input) onOperation
      if checkV returned.value target && checkV operated.value target then
        return ⟨target, residual [key] input.row ++ (returned.row ++ operated.row)⟩
      else none
  | .widen target body => do
      let input ← infer types body
      if checkC input target then return target else none

/-! ## The executable checker and the independent typing judgement -/

theorem infer_complete [DecidableEq Key] {types : Env (CTy n Key) Γ}
    {expression : Expr n Key Atom Γ s} {output : CTy n Key s}
    (typed : Typing types expression output) : infer types expression = some output := by
  induction typed with
  | var => rfl
  | lit => rfl
  | lam _ ih => simp [infer, ih]
  | app _ _ compatible ihf iha =>
      simp [infer, ihf, iha, CTy.arrow, (checkC_exact _ _).mpr compatible]
  | pair _ _ iha ihb => simp [infer, iha, ihb]
  | fst _ ih => simp [infer, ih]
  | snd _ ih => simp [infer, ih]
  | letE _ _ ihv ihb => simp [infer, ihv, ihb]
  | request _ ih => simp [infer, ih]
  | boundary _ ih => simp [infer, ih]
  | handler _ _ _ returned operated iha ihr iho =>
      simp [infer, iha, ihr, iho, (checkV_exact _ _).mpr returned,
        (checkV_exact _ _).mpr operated]
  | widen _ compatible ih => simp [infer, ih, (checkC_exact _ _).mpr compatible]

theorem infer_sound [DecidableEq Key] (expression : Expr n Key Atom Γ s)
    (types : Env (CTy n Key) Γ) (output : CTy n Key s)
    (accepted : infer types expression = some output) : Typing types expression output := by
  induction expression with
  | var index =>
      cases Option.some.inj accepted
      exact .var
  | lit value =>
      cases Option.some.inj accepted
      exact .lit
  | lam input body ih =>
      simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at accepted
      obtain ⟨result, success, equal⟩ := accepted
      cases Option.some.inj equal
      exact .lam (ih _ _ success)
  | app function argument ihf iha =>
      cases hf : infer types function with
      | none => simp [infer, hf] at accepted
      | some functionType =>
          rcases functionType with ⟨functionType, functionRow⟩
          cases functionType with
          | arrow a ea b eb =>
              cases ha : infer types argument with
              | none => simp [infer, hf, ha] at accepted
              | some actual =>
                  cases compatible : checkC actual ⟨a, ea⟩ with
                  | false => simp [infer, hf, ha, compatible] at accepted
                  | true =>
                      have equal : (⟨b, functionRow ++ eb⟩ : CTy n Key _) = output := by
                        simpa [infer, hf, ha, compatible] using accepted
                      cases equal
                      exact .app (input := ⟨a, ea⟩) (output := ⟨b, eb⟩)
                        (ihf _ _ hf) (iha _ _ ha) ((checkC_exact _ _).mp compatible)
  | pair left right ihl ihr =>
      cases hl : infer types left with
      | none => simp [infer, hl] at accepted
      | some a =>
          cases hr : infer types right with
          | none => simp [infer, hl, hr] at accepted
          | some b =>
              have equal : (⟨.pair a.value b.value, a.row ++ b.row⟩ : CTy n Key _) = output := by
                simpa [infer, hl, hr] using accepted
              cases equal
              exact .pair (ihl _ _ hl) (ihr _ _ hr)
  | fst pair ih =>
      cases hp : infer types pair with
      | none => simp [infer, hp] at accepted
      | some pairType =>
          rcases pairType with ⟨pairType, row⟩
          cases pairType with
          | pair a b =>
              have equal : (⟨a, row⟩ : CTy n Key _) = output := by
                simpa [infer, hp] using accepted
              cases equal
              exact .fst (ih _ _ hp)
  | snd pair ih =>
      cases hp : infer types pair with
      | none => simp [infer, hp] at accepted
      | some pairType =>
          rcases pairType with ⟨pairType, row⟩
          cases pairType with
          | pair a b =>
              have equal : (⟨b, row⟩ : CTy n Key _) = output := by
                simpa [infer, hp] using accepted
              cases equal
              exact .snd (ih _ _ hp)
  | letE value body ihv ihb =>
      cases hv : infer types value with
      | none => simp [infer, hv] at accepted
      | some input =>
          cases hb : infer (Env.cons (CTy.pure input.value) types) body with
          | none => simp [infer, hv, hb] at accepted
          | some result =>
              have equal : (⟨result.value, input.row ++ result.row⟩ : CTy n Key _) = output := by
                simpa [infer, hv, hb] using accepted
              cases equal
              exact .letE (ihv _ _ hv) (ihb _ _ hb)
  | request key payload ih =>
      cases hp : infer types payload with
      | none => simp [infer, hp] at accepted
      | some input =>
          rcases input with ⟨input, row⟩
          cases input
          have equal : (⟨.atom, row ++ [raw key]⟩ : CTy n Key _) = output := by
            simpa [infer, hp] using accepted
          cases equal
          exact .request (ih _ _ hp)
  | boundary boundary body ih =>
      cases hb : infer types body with
      | none => simp [infer, hb] at accepted
      | some input =>
          have equal : (⟨input.value, boundary.row input.row⟩ : CTy n Key _) = output := by
            simpa [infer, hb] using accepted
          cases equal
          exact .boundary (ih _ _ hb)
  | handler key target action onReturn onOperation iha ihr iho =>
      cases ha : infer types action with
      | none => simp [infer, ha] at accepted
      | some input =>
          cases hr : infer (Env.cons (CTy.pure input.value) types) onReturn with
          | none => simp [infer, ha, hr] at accepted
          | some returned =>
              cases ho : infer (operationTypes types input) onOperation with
              | none => simp [infer, ha, hr, ho] at accepted
              | some operated =>
                  cases compatible : checkV returned.value target && checkV operated.value target with
                  | false => simp [infer, ha, hr, ho, compatible] at accepted
                  | true =>
                      have equal : (⟨target,
                          residual [key] input.row ++ (returned.row ++ operated.row)⟩ : CTy n Key _) =
                            output := by
                        simpa [infer, ha, hr, ho, compatible] using accepted
                      cases equal
                      have both : checkV returned.value target = true ∧
                          checkV operated.value target = true := by simpa only [Bool.and_eq_true] using compatible
                      obtain ⟨hrt, hot⟩ := both
                      exact .handler (iha _ _ ha) (ihr _ _ hr) (iho _ _ ho)
                        ((checkV_exact _ _).mp hrt) ((checkV_exact _ _).mp hot)
  | widen target body ih =>
      cases hb : infer types body with
      | none => simp [infer, hb] at accepted
      | some input =>
          cases compatible : checkC input target with
          | false => simp [infer, hb, compatible] at accepted
          | true =>
              have equal : target = output := by simpa [infer, hb, compatible] using accepted
              cases equal
              exact .widen (ih _ _ hb) ((checkC_exact _ _).mp compatible)

theorem infer_exact [DecidableEq Key] (expression : Expr n Key Atom Γ s)
    (types : Env (CTy n Key) Γ) (output : CTy n Key s) :
    infer types expression = some output ↔ Typing types expression output :=
  ⟨infer_sound expression types output, infer_complete⟩

/-! ## The logical relation and operational composition -/

theorem allReturns_mono (left right : A → Prop) (implies : ∀ value, left value → right value)
    (computation : Computation n Key Payload Response A)
    (valid : AllReturns left computation) : AllReturns right computation := by
  induction computation with
  | pure value => exact implies value valid
  | request occurrence payload resume ih => exact fun response => ih response (valid response)

theorem allReturns_mapRequests (transform : Occurrence n Key → Occurrence n Other)
    (predicate : A → Prop) (computation : Computation n Key Payload Response A) :
    AllReturns predicate (Computation.mapRequests transform computation) ↔
      AllReturns predicate computation := by
  induction computation with
  | pure => rfl
  | request occurrence payload resume ih =>
      simp only [Computation.mapRequests, AllReturns, ih]

theorem bind_bounds_returns (left right : Row n Key) (source : A → Prop) (target : B → Prop)
    (computation : Computation n Key Payload Response A)
    (next : A → Computation n Key Payload Response B)
    (bounded : Computation.BoundedBy left computation)
    (returned : AllReturns source computation)
    (nextValid : ∀ value, source value →
      Computation.BoundedBy right (next value) ∧ AllReturns target (next value)) :
    Computation.BoundedBy (left ++ right) (computation.bind next) ∧
      AllReturns target (computation.bind next) := by
  induction computation with
  | pure value =>
      have good := nextValid value returned
      exact ⟨Computation.bounded_mono (SignedStructural.row_join_right left right) good.1, good.2⟩
  | request occurrence payload resume ih =>
      refine ⟨⟨List.mem_append.mpr (Or.inl bounded.1), ?_⟩, ?_⟩
      · intro response
        exact (ih response (bounded.2 response) (returned response)).1
      · intro response
        exact (ih response (bounded.2 response) (returned response)).2

theorem valid_pure (type : VTy n Key s) (value : Value n Key Atom s)
    (valid : ValidValue type value) : Valid (CTy.pure type) (.pure value) := ⟨trivial, valid⟩

theorem valid_mono_values {left right : CTy n Key s} {computation : Tree n Key Atom s}
    (values : ∀ value : Value n Key Atom s, ValidValue left.value value → ValidValue right.value value)
    (rows : RowLe left.row right.row) (valid : Valid left computation) : Valid right computation :=
  ⟨Computation.bounded_mono rows valid.1, allReturns_mono _ _ values computation valid.2⟩

theorem value_subtype_sound (left right : VTy n Key s) (subtype : VLe left right)
    (value : Value n Key Atom s) (valid : ValidValue left value) : ValidValue right value := by
  induction s with
  | atom => cases left; cases right; trivial
  | pair a b iha ihb =>
      cases left with
      | pair l₁ l₂ =>
          cases right with
          | pair r₁ r₂ =>
              exact ⟨iha l₁ r₁ subtype.1 value.1 valid.1,
                ihb l₂ r₂ subtype.2 value.2 valid.2⟩
  | arrow a b iha ihb =>
      cases left with
      | arrow l₁ le₁ l₂ le₂ =>
          cases right with
          | arrow r₁ re₁ r₂ re₂ =>
              intro argument bounded returned
              have adjusted : Valid (⟨l₁, le₁⟩ : CTy n Key a) argument :=
                valid_mono_values (fun v hv => iha r₁ l₁ subtype.1 v hv) subtype.2.1
                  (show Valid (⟨r₁, re₁⟩ : CTy n Key a) argument from ⟨bounded, returned⟩)
              have result := valid argument adjusted.1 adjusted.2
              exact valid_mono_values (left := ⟨l₂, le₂⟩) (right := ⟨r₂, re₂⟩)
                (fun v hv => ihb l₂ r₂ subtype.2.2.1 v hv) subtype.2.2.2 result

theorem subtype_sound {left right : CTy n Key s} (subtype : CLe left right)
    {computation : Tree n Key Atom s} (valid : Valid left computation) : Valid right computation :=
  valid_mono_values (fun value hv => value_subtype_sound _ _ subtype.1 value hv) subtype.2 valid

theorem EnvValid.cons {types : Env (CTy n Key) Γ} {runtime : Env (Tree n Key Atom) Γ}
    (valid : EnvValid types runtime) {type : CTy n Key s} {value : Tree n Key Atom s}
    (first : Valid type value) : EnvValid (Env.cons type types) (Env.cons value runtime) := by
  intro shape index
  cases index with
  | here => exact first
  | there index => exact valid index

theorem valid_bind {input : CTy n Key a} {output : CTy n Key b}
    {computation : Tree n Key Atom a} {next : Value n Key Atom a → Tree n Key Atom b}
    (valid : Valid input computation)
    (nextValid : ∀ value, ValidValue input.value value → Valid output (next value)) :
    Valid (⟨output.value, input.row ++ output.row⟩ : CTy n Key b) (computation.bind next) :=
  bind_bounds_returns _ _ _ _ _ _ valid.1 valid.2 nextValid

theorem valid_mapRequests (boundary : Boundary n Key) {input : CTy n Key s}
    {computation : Tree n Key Atom s} (valid : Valid input computation) :
    Valid (⟨input.value, boundary.row input.row⟩ : CTy n Key s)
      (Computation.mapRequests boundary.transform computation) :=
  ⟨Computation.mapRequests_bounded _ _ _ valid.1,
    (allReturns_mapRequests _ _ _).mpr valid.2⟩

theorem valid_pair {leftType : CTy n Key a} {rightType : CTy n Key b}
    {left : Tree n Key Atom a} {right : Tree n Key Atom b}
    (leftValid : Valid leftType left) (rightValid : Valid rightType right) :
    Valid (⟨.pair leftType.value rightType.value, leftType.row ++ rightType.row⟩ : CTy n Key _)
      (left.bind fun a => right.bind fun b => .pure (a, b)) := by
  apply valid_bind (output := ⟨.pair leftType.value rightType.value, rightType.row⟩) leftValid
  intro a ha
  have paired := valid_bind (output := CTy.pure (.pair leftType.value rightType.value)) rightValid
    (fun b hb => valid_pure (.pair leftType.value rightType.value) (a, b) ⟨ha, hb⟩)
  simpa [CTy.pure] using paired

theorem valid_fst {leftType : VTy n Key a} {rightType : VTy n Key b} {row : Row n Key}
    {pair : Tree n Key Atom (.pair a b)}
    (valid : Valid (⟨.pair leftType rightType, row⟩ : CTy n Key _) pair) :
    Valid (⟨leftType, row⟩ : CTy n Key a) (pair.bind fun value => .pure value.1) := by
  have projected := valid_bind (output := CTy.pure leftType) valid
    (fun value good => valid_pure _ value.1 good.1)
  simpa [CTy.pure] using projected

theorem valid_snd {leftType : VTy n Key a} {rightType : VTy n Key b} {row : Row n Key}
    {pair : Tree n Key Atom (.pair a b)}
    (valid : Valid (⟨.pair leftType rightType, row⟩ : CTy n Key _) pair) :
    Valid (⟨rightType, row⟩ : CTy n Key b) (pair.bind fun value => .pure value.2) := by
  have projected := valid_bind (output := CTy.pure rightType) valid
    (fun value good => valid_pure _ value.2 good.2)
  simpa [CTy.pure] using projected

theorem valid_request (key : Key) {row : Row n Key} {payload : Tree n Key Atom .atom}
    (valid : Valid (⟨.atom, row⟩ : CTy n Key .atom) payload) :
    Valid (⟨.atom, row ++ [raw key]⟩ : CTy n Key .atom)
      (payload.bind fun value => .request (raw key) value (fun response => .pure response)) := by
  apply valid_bind (output := ⟨.atom, [raw key]⟩) valid
  intro value _
  exact ⟨⟨by simp, fun _ => trivial⟩, fun _ => trivial⟩

theorem valid_resumption (input : CTy n Key a)
    (resume : Atom → Tree n Key Atom a) (valid : ∀ response, Valid input (resume response)) :
    ValidValue (CTy.arrow (CTy.pure .atom) input) (fun argument => argument.bind resume) := by
  intro argument bounded returned
  have resumed := valid_bind (input := CTy.pure .atom) (output := input)
    (computation := argument) ⟨bounded, returned⟩ (fun response _ => valid response)
  simpa [CTy.pure, Valid] using resumed

theorem shallowHandle_valid [DecidableEq Key]
    (handled : List Key) (input : CTy n Key a) (output : VTy n Key b)
    (returnRow operationRow : Row n Key)
    (onReturn : Value n Key Atom a → Tree n Key Atom b)
    (onOperation : Occurrence n Key → Atom →
      (Atom → Tree n Key Atom a) → Tree n Key Atom b)
    (returnValid : ∀ value, ValidValue input.value value →
      Valid (⟨output, returnRow⟩ : CTy n Key b) (onReturn value))
    (operationValid : ∀ occurrence payload resume, Capturable handled occurrence →
      (∀ response, Valid input (resume response)) →
      Valid (⟨output, operationRow⟩ : CTy n Key b) (onOperation occurrence payload resume))
    (computation : Tree n Key Atom a) (inputValid : Valid input computation) :
    Valid (⟨output, residual handled input.row ++ (returnRow ++ operationRow)⟩ : CTy n Key b)
      (Computation.shallowHandle handled onReturn onOperation computation) := by
  induction computation with
  | pure value =>
      have good := returnValid value inputValid.2
      exact valid_mono_values (left := ⟨output, returnRow⟩)
        (right := ⟨output, residual handled input.row ++ (returnRow ++ operationRow)⟩) (fun _ h => h)
        (fun _ member => List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl member)))) good
  | request occurrence payload resume ih =>
      have resumeValid (response : Atom) : Valid input (resume response) :=
        ⟨inputValid.1.2 response, inputValid.2 response⟩
      by_cases captured : Capturable handled occurrence
      · simp only [Computation.shallowHandle, captured, ↓reduceIte]
        have good := operationValid occurrence payload resume captured resumeValid
        exact valid_mono_values (left := ⟨output, operationRow⟩)
          (right := ⟨output, residual handled input.row ++ (returnRow ++ operationRow)⟩) (fun _ h => h)
          (fun _ member => List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr member)))) good
      · simp only [Computation.shallowHandle, captured, ↓reduceIte]
        refine ⟨⟨?_, fun response => (ih response (resumeValid response)).1⟩,
          fun response => (ih response (resumeValid response)).2⟩
        apply List.mem_append.mpr
        left
        simpa [residual, captured] using inputValid.1.1

/-- Every premise about an action, arm or application is obtained recursively
from its syntax typing. Only an open program's external environment is assumed
to satisfy its declared interface. -/
theorem typing_sound [DecidableEq Key] {types : Env (CTy n Key) Γ}
    {expression : Expr n Key Atom Γ s} {output : CTy n Key s}
    (typed : Typing types expression output) :
    ∀ runtime : Env (Tree n Key Atom) Γ, EnvValid types runtime →
      Valid output (eval runtime expression) := by
  induction typed with
  | var => intro runtime good; exact good _
  | lit => intro runtime good; exact valid_pure _ _ trivial
  | lam bodyTyped ih =>
      intro runtime good
      apply valid_pure
      intro argument bounded returned
      exact ih _ (good.cons ⟨bounded, returned⟩)
  | app functionTyped argumentTyped compatible ihf iha =>
      intro runtime good
      apply valid_bind (ihf runtime good)
      intro function functionValid
      have argumentValid := subtype_sound compatible (iha runtime good)
      exact functionValid _ argumentValid.1 argumentValid.2
  | pair leftTyped rightTyped ihl ihr =>
      intro runtime good
      exact valid_pair (ihl runtime good) (ihr runtime good)
  | fst pairTyped ih =>
      intro runtime good
      exact valid_fst (ih runtime good)
  | snd pairTyped ih =>
      intro runtime good
      exact valid_snd (ih runtime good)
  | letE valueTyped bodyTyped ihv ihb =>
      intro runtime good
      apply valid_bind (ihv runtime good)
      intro value valueValid
      exact ihb _ (good.cons (valid_pure _ _ valueValid))
  | request payloadTyped ih =>
      intro runtime good
      exact valid_request _ (ih runtime good)
  | boundary bodyTyped ih =>
      intro runtime good
      exact valid_mapRequests _ (ih runtime good)
  | handler actionTyped returnTyped operationTyped returnSubtype operationSubtype iha ihr iho =>
      intro runtime good
      apply shallowHandle_valid
      · intro value valueValid
        exact valid_mono_values (fun v hv => value_subtype_sound _ _ returnSubtype v hv)
          (SignedStructural.row_refl _) (ihr _ (good.cons (valid_pure _ _ valueValid)))
      · intro occurrence payload resume captured resumeGood
        have continuation := valid_pure _ _ (valid_resumption _ resume resumeGood)
        have payloadGood := valid_pure (.atom : VTy n Key .atom) payload trivial
        exact valid_mono_values (fun v hv => value_subtype_sound _ _ operationSubtype v hv)
          (SignedStructural.row_refl _)
          (iho _ (EnvValid.cons (EnvValid.cons good continuation) payloadGood))
      · exact iha runtime good
  | widen bodyTyped compatible ih =>
      intro runtime good
      exact subtype_sound compatible (ih runtime good)

/-- Checker success gives a bound on every request in every response branch;
no action/arm bound is an input to this result. -/
theorem inferred_operationally_valid [DecidableEq Key]
    (expression : Expr n Key Atom Γ s) (types : Env (CTy n Key) Γ)
    (output : CTy n Key s) (accepted : infer types expression = some output)
    (runtime : Env (Tree n Key Atom) Γ) (environment : EnvValid types runtime) :
    Valid output (eval runtime expression) :=
  typing_sound (infer_sound expression types output accepted) runtime environment

theorem closed_inferred_bound [DecidableEq Key]
    (expression : Expr n Key Atom [] s) (output : CTy n Key s)
    (accepted : infer Env.nil expression = some output) :
    Computation.BoundedBy output.row (eval Env.nil expression) :=
  (inferred_operationally_valid expression Env.nil output accepted Env.nil
    (fun index => nomatch index)).1

theorem closed_inferred_values [DecidableEq Key]
    (expression : Expr n Key Atom [] s) (output : CTy n Key s)
    (accepted : infer Env.nil expression = some output) :
    AllReturns (ValidValue output.value) (eval Env.nil expression) :=
  (inferred_operationally_valid expression Env.nil output accepted Env.nil
    (fun index => nomatch index)).2

end Yulang.OperationalTyping
