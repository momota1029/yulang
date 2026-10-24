import YulangClosure.ControlSyntax

namespace YulangClosure.Control

inductive Ty where
  | base (identity : Nat)
  | attempt (result : Ty)
  deriving DecidableEq

inductive ValueTyped : Value → Ty → Prop
  | atom : ValueTyped (.atom t v) (.base t)
  | no : ValueTyped .no (.attempt t)
  | yes : ValueTyped v t → ValueTyped (.yes v) (.attempt t)

/-- Extrinsic registered-body signature, not a whole-machine safety premise. -/
structure Signature where
  code : Nat → List Ty → Option (Ty × Ty) → Ty → Prop

mutual
  inductive FrameTyped (sig : Signature) : Frame → Ty → Ty → Prop
    | bind : sig.code c [a] none b → FrameTyped sig (.bind (.code c)) a b
    | scope : FrameTyped sig (.scope u) a a
    | view : FrameTyped sig (.view u) a a
    | release : FrameTyped sig (.release u) a a
    | handle : HandlerTyped sig h → FrameTyped sig (.handle h) (.base h.input) (.base h.output)
    | mapper : MapperTyped sig m → FrameTyped sig (.mapop m) a a
    | wait : HandlerTyped sig h → SearchTyped sig h p arms → FrameTyped sig (.wait h p arms) (.attempt (.base h.output)) (.base h.output)
    | mapped : MapperTyped sig m → PacketTyped sig (.mk e m.source p k) a →
        FrameTyped sig (.bind (.mapped m (.mk e m.source p k))) (.base m.target.payload) a
    | response : MapperTyped sig m → KontTyped sig k (.base m.source.response) a →
        FrameTyped sig (.bind (.response m k)) (.base m.target.response) a
    | enterSaved : MapperTyped sig m → KontTyped sig k (.base m.source.response) a →
        FrameTyped sig (.bind (.enterSaved m k)) (.base m.source.response) a
  inductive FramesTyped (sig : Signature) : List Frame → Ty → Ty → Prop
    | nil : FramesTyped sig [] a a
    | cons : FrameTyped sig f a b → FramesTyped sig fs b c → FramesTyped sig (f::fs) a c
  inductive KontTyped (sig : Signature) : Kont → Ty → Ty → Prop
    | mk : FramesTyped sig fs (.base q) a → KontTyped sig (.mk q fs) (.base q) a
  inductive PacketTyped (sig : Signature) : Packet → Ty → Prop
    | mk : ValueTyped p (.base q.payload) → KontTyped sig k (.base q.response) a →
        PacketTyped sig (.mk e q p k) a
  inductive ArmsTyped (sig : Signature) : Handler → List Arm → Prop
    | nil : ArmsTyped sig h []
    | cons : sig.code a.code [.base a.operation.payload]
          (some (.base a.operation.response, .base h.input)) (.attempt (.base h.output)) →
        ArmsTyped sig h as → ArmsTyped sig h (a::as)
  inductive ValueArmsTyped (sig : Signature) : Handler → List Nat → Prop
    | nil : ValueArmsTyped sig h []
    | cons : sig.code c [.base h.input] none (.attempt (.base h.output)) →
        ValueArmsTyped sig h cs → ValueArmsTyped sig h (c::cs)
  /-- Value and operation candidates have different raw positions and
      signatures. This is a raw-shape invariant, not a safety premise. -/
  inductive SearchTyped (sig : Signature) : Handler → Pending → List Arm → Prop
    | value : ValueTyped v (.base h.input) → ValueArmsTyped sig h cs →
        SearchTyped sig h (.value v cs) []
    | request : PacketTyped sig p (.base h.input) → ArmsTyped sig h arms →
        SearchTyped sig h (.request p) arms
  inductive HandlerTyped (sig : Signature) : Handler → Prop
    | mk : ValueArmsTyped sig h h.valueArms →
        ArmsTyped sig h h.arms → HandlerTyped sig h
  inductive MapperTyped (sig : Signature) : Mapper → Prop
    | mk : m.source.family = m.target.family →
        sig.code m.payloadCode [.base m.source.payload] none (.base m.target.payload) →
        sig.code m.responseCode [.base m.target.response] none (.base m.source.response) →
        MapperTyped sig m
end

inductive ArgsTyped : List Value → List Ty → Prop
  | nil : ArgsTyped [] []
  | cons : ValueTyped v a → ArgsTyped vs as → ArgsTyped (v::vs) (a::as)

inductive SavedTyped (sig : Signature) : Option Kont → Option (Ty × Ty) → Prop
  | none : SavedTyped sig none none
  | some : KontTyped sig k a b → SavedTyped sig (some k) (some (a,b))

inductive HeadTyped (sig : Signature) : Head → Ty → Prop
  | ret : ValueTyped v a → HeadTyped sig (.ret v) a
  | req : PacketTyped sig p a → HeadTyped sig (.req p) a
  | fail : HeadTyped sig (.fail r) a
  | run : ArgsTyped args ts → SavedTyped sig saved st → sig.code c ts st a →
      HeadTyped sig (.run c args saved) a
  | search : HandlerTyped sig h → SearchTyped sig h p arms →
      HeadTyped sig (.search h p arms) (.base h.output)

def StateTyped (sig : Signature) (s : State W) (result : Ty) : Prop :=
  ∃ hole, HeadTyped sig s.head hole ∧ FramesTyped sig s.stack hole result

theorem frames_append {sig : Signature} (h : FramesTyped sig fs a b)
    (k : FramesTyped sig gs b c) : FramesTyped sig (fs ++ gs) a c := by
  induction fs generalizing a b with
  | nil => cases h; exact k
  | cons f fs ih =>
    cases h with | cons hf ht => exact .cons hf (ih ht k)

theorem capture_typed {sig : Signature} (hk : KontTyped sig k q a)
    (hf : FrameTyped sig f a b) : KontTyped sig (k.append f) q b := by
  cases hk with
  | mk hs => exact .mk (frames_append hs (.cons hf .nil))

theorem packet_capture_typed {sig : Signature} (hp : PacketTyped sig p a)
    (hf : FrameTyped sig f a b) : PacketTyped sig (p.capture f) b := by
  cases hp with
  | mk hv hk => exact .mk hv (capture_typed hk hf)

theorem typed_not_bad {sig : Signature} {s : State W}
    (ht : StateTyped sig s a) : ∀ r, s.head ≠ .bad r := by
  obtain ⟨hole, hh, hs⟩ := ht
  intro r he
  rw [he] at hh
  cases hh

/-- Independent body-only obligations; no frame/search transfer is included. -/
structure BodyLaws {W : Type} (sig : Signature)
    (body : W → Nat → List Value → Option Kont → W → Head → Prop) where
  preservation : ∀ w c vs k w' h a,
    HeadTyped sig (.run c vs k) a → body w c vs k w' h → HeadTyped sig h a
  progress : ∀ w c vs k a, HeadTyped sig (.run c vs k) a →
    ∃ w' h, body w c vs k w' h

end YulangClosure.Control
