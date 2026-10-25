import YulangClosure.CallNativeLiteralResponse

/-! Candidate partial interpretation of retained native declarations. Native
source authentication, retention and actual-trace correspondence are separate
obligations. No Rust transition is established by these constructors. -/
namespace YulangClosure.PrimitiveOperation

/-- First occurrence numbering of complete identities; duplicates are allowed. -/
def number {Key : Type} [DecidableEq Key] : List Key → Key → Option Nat
  | [], _ => none
  | k :: ks, x => if x = k then some 0 else (number ks x).map Nat.succ

theorem number_coverage {Key : Type} [DecidableEq Key]
    {ks : List Key} {x : Key} (h : x ∈ ks) : ∃ n, number ks x = some n := by
  induction ks with
  | nil => cases h
  | cons k ks ih =>
      by_cases hx : x = k
      · subst x; exact ⟨0, by simp [number]⟩
      · have hm : x ∈ ks := (List.mem_cons.mp h).resolve_left hx
        obtain ⟨n, hn⟩ := ih hm
        exact ⟨n + 1, by simp [number, hx, hn]⟩

/-- A successful index retrieves precisely the complete input key. -/
theorem number_get {Key : Type} [DecidableEq Key]
    {ks : List Key} {x : Key} {n : Nat} (h : number ks x = some n) :
    ks[n]? = some x := by
  induction ks generalizing n with
  | nil => simp [number] at h
  | cons k ks ih =>
      by_cases hx : x = k
      · subst x
        simp [number] at h
        subst n
        rfl
      · cases hn : number ks x with
        | none => simp [number, hx, hn] at h
        | some j =>
            simp [number, hx, hn] at h
            subst n
            simpa using ih hn

theorem number_collision_free {Key : Type} [DecidableEq Key]
    {ks : List Key} {x y : Key} {n : Nat}
    (hx : number ks x = some n) (hy : number ks y = some n) : x = y := by
  exact Option.some.inj ((number_get hx).symm.trans (number_get hy))

theorem number_repeat_consistent {Key : Type} [DecidableEq Key]
    {ks : List Key} {x : Key} {i j : Nat}
    (hi : number ks x = some i) (hj : number ks x = some j) : i = j :=
  Option.some.inj (hi.symm.trans hj)

inductive Primitive where
  | unit | int | bool | string
  deriving DecidableEq

def Primitive.base : Primitive → Original.Base
  | .unit => .unit | .int => .int | .bool => .bool | .string => .string

/-- A structural observation of SourceAnnotationType. Effect and hole payloads
are retained abstractly, never replaced by spellings or hashes. -/
inductive Annotation (Effect Hole : Type) where
  | primitive (effects : Option Effect) (base : Primitive)
  | variable (effects : Option Effect) (name : String)
  | hole (effects : Option Effect) (position : Hole)
  | function (effects : Option Effect) (argument result : Annotation Effect Hole)
  | tuple (effects : Option Effect) (elements : List (Annotation Effect Hole))

def primitive {E H : Type} : Annotation E H → Option Primitive
  | .primitive none p => some p
  | _ => none

theorem primitive_exact {E H : Type} {a : Annotation E H} {p : Primitive}
    (h : primitive a = some p) : a = .primitive none p := by
  cases a with
  | primitive e b =>
      cases e with
      | none =>
          have hb : b = p := Option.some.inj h
          subst p
          rfl
      | some row => cases h
  | «variable» e s => simp [primitive] at h
  | hole e s => simp [primitive] at h
  | function e a b => simp [primitive] at h
  | tuple e xs => simp [primitive] at h

def decode {E H : Type} : Annotation E H → Option (Primitive × Primitive)
  | .function none a b => do
      let p ← primitive a
      let r ← primitive b
      pure (p, r)
  | _ => none

/-- Successful decoding establishes groundness by recovering the exact syntax:
no type variable, hole, callable endpoint, tuple or effect row survives. -/
theorem decode_exact {E H : Type} {a : Annotation E H} {p r : Primitive}
    (h : decode a = some (p, r)) :
    a = .function none (.primitive none p) (.primitive none r) := by
  cases a with
  | primitive e b => simp [decode] at h
  | «variable» e s => simp [decode] at h
  | hole e s => simp [decode] at h
  | tuple e xs => simp [decode] at h
  | function e a b =>
      cases e with
      | some row => simp [decode] at h
      | none =>
          cases ha : primitive a with
          | none => simp [decode, ha] at h
          | some x =>
              cases hb : primitive b with
              | none => simp [decode, ha, hb] at h
              | some y =>
                  have hp : x = p ∧ y = r := by simpa [decode, ha, hb] using h
                  obtain ⟨rfl, rfl⟩ := hp
                  rw [primitive_exact ha, primitive_exact hb]

structure Declaration (Key Effect Hole : Type) where
  identity : Key
  spelling : String
  signature : Annotation Effect Hole

/-- Ground signature construction supplies an empty instantiation vector. -/
def instanceOf (n : Nat) (p r : Primitive) : TypedCall.OperationInstance :=
  ⟨n, [], .base p.base, .base r.base⟩

def interpret {K E H : Type} [DecidableEq K] (keys : List K)
    (d : Declaration K E H) : Option TypedCall.OperationInstance := do
  let n ← number keys d.identity
  let pr ← decode d.signature
  pure (instanceOf n pr.1 pr.2)

/-- Request and template use the same declaration interpreter. Their connection
to actual native request/capture records remains a source bridge. -/
def request {K E H : Type} [DecidableEq K] := @interpret K E H _
def template {K E H : Type} [DecidableEq K] := @interpret K E H _

/-- Coverage and successful syntax decoding construct the formal instance. -/
theorem interpret_exists {K E H : Type} [DecidableEq K]
    {keys : List K} {d : Declaration K E H} {p r : Primitive}
    (hm : d.identity ∈ keys) (hd : decode d.signature = some (p, r)) :
    ∃ n, number keys d.identity = some n ∧
      interpret keys d = some (instanceOf n p r) := by
  obtain ⟨n, hn⟩ := number_coverage hm
  exact ⟨n, hn, by simp [interpret, hn, hd]⟩

theorem interpret_fields {K E H : Type} [DecidableEq K]
    {keys : List K} {d : Declaration K E H} {op : TypedCall.OperationInstance}
    (h : interpret keys d = some op) :
    ∃ n p r, number keys d.identity = some n ∧
      d.signature = .function none (.primitive none p) (.primitive none r) ∧
      op = instanceOf n p r := by
  cases hn : number keys d.identity with
  | none => simp [interpret, hn] at h
  | some n =>
      cases hd : decode d.signature with
      | none => simp [interpret, hn, hd] at h
      | some pr =>
          rcases pr with ⟨p, r⟩
          have ho : instanceOf n p r = op := by simpa [interpret, hn, hd] using h
          exact ⟨n, p, r, rfl, decode_exact hd, ho.symm⟩

def expected {K E H : Type} (d : Declaration K E H) : Option Original.Base :=
  (decode d.signature).map (fun pr => pr.2.base)

theorem interpret_response {K E H : Type} [DecidableEq K]
    {keys : List K} {d : Declaration K E H} {op : TypedCall.OperationInstance}
    {b : Original.Base} (hi : interpret keys d = some op)
    (he : expected d = some b) : op.responseType = .base b := by
  obtain ⟨n, p, r, hn, hd, rfl⟩ := interpret_fields hi
  have hb : r.base = b := by simpa [expected, hd, decode, primitive] using he
  simp [instanceOf, hb]

theorem interpret_ground {K E H : Type} [DecidableEq K]
    {keys : List K} {d : Declaration K E H} {op : TypedCall.OperationInstance}
    (hi : interpret keys d = some op) :
    op.typeArguments = [] ∧ ∃ p r,
      d.signature = .function none (.primitive none p) (.primitive none r) ∧
      op.payloadType = .base p.base ∧ op.responseType = .base r.base := by
  obtain ⟨n, p, r, hn, hd, rfl⟩ := interpret_fields hi
  exact ⟨rfl, p, r, hd, rfl, rfl⟩

theorem request_template_same {K E H : Type} [DecidableEq K]
    {keys : List K} {d : Declaration K E H} {op captured : TypedCall.OperationInstance}
    (hr : request keys d = some op) (ht : template keys d = some captured) :
    op = captured := Option.some.inj (hr.symm.trans ht)

/-- Equal spelling has no role in numbering complete identities. -/
example : number [ (3, "read"), (9, "read") ] (3, "read") ≠
    number [ (3, "read"), (9, "read") ] (9, "read") := by decide

example : decode (Annotation.function (Effect := Unit) (Hole := Nat) none
    (.primitive none .unit) (.primitive none .bool)) = some (.unit, .bool) := rfl

example : decode (Annotation.function (Effect := Unit) (Hole := Nat) none
    (.primitive none .unit) (.primitive none .bool)) ≠ some (.unit, .int) := by
  intro h
  cases h

example : number [4, 4, 7] 4 = some 0 := by decide
example : number [4, 4, 7] 7 = some 2 := by decide
example : number [4, 4, 7] 9 = none := by decide
example : decode (Annotation.function (Effect := Unit) (Hole := Nat) none
    (.variable none "a") (.primitive none .int)) = none := rfl
example : decode (Annotation.function (Effect := Unit) (Hole := Nat) none
    (.hole none 0) (.primitive none .int)) = none := rfl
example : decode (Annotation.function (Effect := Unit) (Hole := Nat) (some ())
    (.primitive none .unit) (.primitive none .int)) = none := rfl
example : decode (Annotation.function (Effect := Unit) (Hole := Nat) none
    (.primitive (some ()) .unit) (.primitive none .int)) = none := rfl
example : decode (Annotation.function (Effect := Unit) (Hole := Nat) none
    (.primitive none .unit) (.primitive (some ()) .int)) = none := rfl
example : decode (Annotation.function (Effect := Unit) (Hole := Nat) none
    (.function none (.primitive none .int) (.primitive none .int))
    (.primitive none .int)) = none := rfl
example : decode (Annotation.tuple (Effect := Unit) (Hole := Nat) none []) = none := rfl

end YulangClosure.PrimitiveOperation
