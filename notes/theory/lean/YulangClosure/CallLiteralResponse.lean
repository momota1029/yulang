import YulangClosure.CallRequestBoundaryComposition

/-! Candidate literal representation and application to actual Call requests.
All existing Literal payload domains are retained, including arbitrary char
strings and path bytes. Lexical validity and native encoding remain separate
obligations. No operation-instance or source-host typing is inferred here. -/
namespace YulangClosure.Original

@[simp] theorem Literal.toVal_raw (l : Literal) :
    l.toVal.raw = .atom (.literal l) := by
  cases l <;> rfl

theorem Literal.toVal_typed (l : Literal) (env : Context) :
    ValTyped env l.toVal (.base l.base) := by
  cases l <;> constructor

theorem Literal.toVal_injective {l r : Literal}
    (h : l.toVal = r.toVal) : l = r := by
  cases l <;> cases r <;> cases h <;> rfl

/-- This is uniqueness of all typing, hence also of base typing. -/
theorem Literal.toVal_type_unique {l : Literal} {env : Context} {a : Ty}
    (h : ValTyped env l.toVal a) : a = .base l.base := by
  cases l <;> cases h <;> rfl

theorem Literal.toVal_base_unique {l : Literal} {env : Context} {b : Base}
    (h : ValTyped env l.toVal (.base b)) : b = l.base := by
  exact Ty.base.inj (Literal.toVal_type_unique h)

@[simp] theorem Literal.rename_toVal (l : Literal) (r : Nat → Nat) :
    renameVal r l.toVal = l.toVal := by
  cases l <;> rfl

@[simp] theorem Literal.subst_toVal (l : Literal) (s : Nat → Val) :
    substVal s l.toVal = l.toVal := by
  cases l <;> rfl

@[simp] theorem Literal.rename_raw (l : Literal) (r : Renaming) :
    renameRaw r l.toVal.raw = .atom (.literal l) := by
  rw [Literal.toVal_raw]
  rfl

@[simp] theorem Literal.substitute_raw (l : Literal) (s : Substitution) :
    substituteRaw s l.toVal.raw = .atom (.literal l) := by
  rw [Literal.toVal_raw]
  rfl

end YulangClosure.Original

namespace YulangClosure.TypedCall

open YulangClosure.Original

def literalResponse (l : Literal) : Value := .original l.toVal

theorem literalResponse_typed (l : Literal) (env : Original.Context) :
    ValueTyped env (literalResponse l) (.base l.base) :=
  .original (l.toVal_typed Original.emptyContext)

theorem literalResponse_operation_typed (l : Literal) (op : OperationInstance)
    (hresponse : op.responseType = .base l.base) :
    ValueTyped Original.emptyContext (literalResponse l) op.responseType := by
  rw [hresponse]
  exact literalResponse_typed l _

@[simp] theorem rename_literalResponse (l : Literal) (r : Nat → Nat) :
    renameCallValue r (literalResponse l) = literalResponse l := rfl

@[simp] theorem substitute_literalResponse (l : Literal) (s : Nat → Value) :
    substituteCallValue s (literalResponse l) = literalResponse l := rfl

end YulangClosure.TypedCall

namespace YulangClosure.Control

/-- Construct the closed response typing from its literal datum and apply the
accepted actual-prefix theorem with all original frame/suffix quantifiers. -/
theorem initial_call_request_boundary_literal_response
    {W : Type} {sig : Signature} {md : Metadata W}
    {term : TypedCall.CallTerm} {world : W} {suffix : List Frame}
    {result : Ty} {n : Nat} {s : CallState W}
    {op : TypedCall.OperationInstance} {payload : TypedCall.Value}
    {k : TypedCall.Comp} {observed : List TypedCall.ViewOccurrence}
    (hsuffix : FramesTyped sig suffix (.original term.resultType) result)
    (hp : YulangClosure.Prefix (CallControlStep md) n
      (CallState.initial term world suffix) s)
    (hhead : s.head = .requesting op payload k observed)
    (l : Original.Literal)
    (hresponse : op.responseType = .base l.base) :
    let t := s.requestBoundary md (s.frames.length + 1)
    YulangClosure.Prefix (CallControlStep md) (n + (s.frames.length + 1))
      (CallState.initial term world suffix) t ∧
    CallStateTyped sig t result ∧
    t.head = .requested op payload (CallState.captureFrames s.frames k) ∧
    t.frames = [] ∧
    t.resultType = term.resultType ∧
    t.literalSuffix = suffix ∧
    TypedCall.ValueTyped Original.emptyContext payload op.payloadType ∧
    TypedCall.CompTyped (Original.extend Original.emptyContext op.responseType)
      (CallState.captureFrames s.frames k) term.resultType ∧
    TypedCall.CompTyped Original.emptyContext
      (plugResponse (CallState.captureFrames s.frames k) (TypedCall.literalResponse l)) term.resultType ∧
    plugResponse (CallState.captureFrames s.frames k) (TypedCall.literalResponse l) =
      TypedCall.plugFrames s.frames (plugResponse k (TypedCall.literalResponse l)) ∧
    TypedCall.CompTyped Original.emptyContext
      (TypedCall.plugFrames s.frames (plugResponse k (TypedCall.literalResponse l))) term.resultType := by
  exact initial_call_request_boundary_response hsuffix hp hhead
    (TypedCall.literalResponse_operation_typed l op hresponse)

/-- Construct the closed response typing from its literal datum and apply the
accepted actual-prefix theorem with all original frame/suffix quantifiers. -/
theorem actual_call_request_completed_literal_response
    {W : Type} {sig : Signature} {md : Metadata W}
    {term : TypedCall.CallTerm} {world : W} {suffix : List Frame}
    {result : Ty} {n m : Nat} {s t : CallState W}
    {op : TypedCall.OperationInstance} {payload : TypedCall.Value}
    {k : TypedCall.Comp} {observed : List TypedCall.ViewOccurrence}
    (hsuffix : FramesTyped sig suffix (.original term.resultType) result)
    (hp : YulangClosure.Prefix (CallControlStep md) n
      (CallState.initial term world suffix) s)
    (hhead : s.head = .requesting op payload k observed)
    (hpost : YulangClosure.Prefix (CallControlStep md) m s t)
    (hcomplete : ∃ op' payload' k', t.head = .requested op' payload' k')
    (l : Original.Literal)
    (hresponse : op.responseType = .base l.base) :
    m = s.frames.length + 1 ∧
    t = s.requestBoundary md (s.frames.length + 1) ∧
    t.head = .requested op payload (CallState.captureFrames s.frames k) ∧
    CallStateTyped sig t result ∧ t.literalSuffix = suffix ∧
    TypedCall.CompTyped Original.emptyContext
      (plugResponse (CallState.captureFrames s.frames k) (TypedCall.literalResponse l)) term.resultType ∧
    TypedCall.CompTyped Original.emptyContext
      (TypedCall.plugFrames s.frames (plugResponse k (TypedCall.literalResponse l))) term.resultType := by
  exact actual_call_request_completed_response hsuffix hp hhead hpost hcomplete
    (TypedCall.literalResponse_operation_typed l op hresponse)

/-- Explicit two-frame binder discriminator: the integer response replaces
only the response binder, leaving both saved frame bodies intact. -/
example (k left right : TypedCall.Comp) (a b : Original.Ty) :
    plugResponse (CallState.captureFrames [.bind left, .adapter a b right] k)
        (TypedCall.literalResponse (.int 11)) =
      TypedCall.plugFrames [.bind left, .adapter a b right]
        (plugResponse k (TypedCall.literalResponse (.int 11))) :=
  plugResponse_captureFrames _ _ _

end YulangClosure.Control

namespace YulangClosure.Original

/-! Kernel examples for payload distinctions. Universal lemmas above also cover
all bit patterns, negative integers, empty strings and arbitrary binder maps. -/
example : Literal.toVal .unit = Val.unit := rfl
example : (Literal.int 11).toVal ≠ (Literal.int 23).toVal := by
  intro h
  have he := Literal.toVal_injective h
  cases he
example : (Literal.bool true).toVal ≠ (Literal.int 1).toVal := by
  intro h
  cases h
example : (Literal.int (-7)).toVal.raw = .atom (.literal (.int (-7))) := rfl
example : (Literal.string "").toVal.raw = .atom (.literal (.string "")) := rfl
example : (Literal.string "λ雪").toVal.raw = .atom (.literal (.string "λ雪")) := rfl
example : (Literal.bytes [0, 255]).toVal ≠ (Literal.path [0, 255]).toVal := by
  intro h
  cases h
example (bits : UInt64) :
    (Literal.floatBits bits).toVal.raw = .atom (.literal (.floatBits bits)) := rfl
example (payload : String) :
    (Literal.char payload).toVal.raw = .atom (.literal (.char payload)) := rfl

end YulangClosure.Original
