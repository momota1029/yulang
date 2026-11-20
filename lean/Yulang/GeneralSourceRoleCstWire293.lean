import Yulang.GeneralSourceRoleCstWireTags293

/-! Portable unresolved wire input: a complete mixed child list with exact
Rust SyntaxKind names. Rust emission of this input is outside this module. -/
namespace Yulang.GeneralSourceRoleCstWire293
open GeneralSourceRoleCstTree293 (Kind Tree)
open GeneralSourceRoleCstWireTags293 (kind)
open GeneralSourceRoleCstLossless293 (render renderList)
open GeneralSourceMetadataExprDomain291 (bind_success two_success)

inductive Wire where
  | token (label text : String)
  | node (label : String) (children : List Wire)
  deriving Repr

mutual
def decode : Wire → Option Tree
  | .token label body => (kind label).map (fun k => .token k body)
  | .node label children => (kind label).bind fun k =>
    (decodeList children).map (Tree.node k)
def decodeList : List Wire → Option (List Tree)
  | [] => some []
  | head::tail => (decode head).bind fun t =>
    (decodeList tail).map (t :: ·)
end

mutual
inductive Transfer : Wire → Tree → Prop
  | token {label value k} : kind label = some k → Transfer (.token label value) (.token k value)
  | node {label k ws ts} : kind label = some k → TransferList ws ts → Transfer (.node label ws) (.node k ts)
inductive TransferList : List Wire → List Tree → Prop
  | nil : TransferList [] []
  | cons {w ws t ts} : Transfer w t → TransferList ws ts → TransferList (w::ws) (t::ts)
end

mutual
theorem decode_exact (wire : Wire) (tree : Tree) : decode wire = some tree ↔ Transfer wire tree := by
  constructor
  · intro h
    cases wire with
    | token label text =>
      cases tag : kind label with
      | none => simp [decode,tag] at h
      | some k =>
        have e : Tree.token k text = tree := by simpa [decode,tag] using h
        subst tree
        exact .token tag
    | node label ws =>
      cases tag : kind label with
      | none => simp [decode,tag] at h
      | some k =>
        cases next : decodeList ws with
        | none => simp [decode,tag,next] at h
        | some ts =>
          have e : Tree.node k ts = tree := by simpa [decode,tag,next] using h
          subst tree
          exact .node tag ((decode_list_exact ws ts).mp next)
  · intro h
    cases h with
    | token whereAt => simp [decode,whereAt]
    | node whereAt cs => simp [decode,whereAt,(decode_list_exact ..).mpr cs]
theorem decode_list_exact (wire : List Wire) (tree : List Tree) :
    decodeList wire = some tree ↔ TransferList wire tree := by
  constructor
  · intro h
    cases wire with
    | nil =>
      have e : [] = tree := Option.some.inj h
      subst tree
      exact .nil
    | cons w ws =>
      cases front : decode w with
      | none => simp [decodeList,front] at h
      | some t =>
        cases rear : decodeList ws with
        | none => simp [decodeList,front,rear] at h
        | some ts =>
          have e : t::ts = tree := by simpa [decodeList,front,rear] using h
          subst tree
          exact .cons ((decode_exact w t).mp front) ((decode_list_exact ws ts).mp rear)
  · intro h
    cases h with
    | nil => rfl
    | cons front tail => simp [decodeList,(decode_exact ..).mpr front,(decode_list_exact ..).mpr tail]
end

mutual
def spelling : Wire → String
  | .token _ s => s
  | .node _ ws => spellings ws
def spellings : List Wire → String
  | [] => ""
  | x::xs => spelling x ++ spellings xs
end

mutual
theorem transfer_preserves_text {w : Wire} {t : Tree} (e : Transfer w t) :
    render t = spelling w := by
  cases e with
  | token => rfl
  | node tag cs => exact transfer_list_preserves_text cs
theorem transfer_list_preserves_text {w : List Wire} {t : List Tree} (e : TransferList w t) :
    renderList t = spellings w := by
  cases e with
  | nil => rfl
  | cons front tail =>
    simp only [renderList,spellings,transfer_preserves_text front,transfer_list_preserves_text tail]
end

end Yulang.GeneralSourceRoleCstWire293
