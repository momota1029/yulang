import Yulang.GeneralSourceRoleCstDiagnosticFixture294

/-! Retain original wire labels when a compact recovery kind merges several
Rust labels. The serialized tree is still supplied, not authenticated. -/
namespace Yulang.GeneralSourceRoleCstOriginalMarks294
open GeneralSourceRoleCstTree293 (Tree Kind)
open GeneralSourceRoleCstMarkSpans294 (Entry entries entry_exact)
open GeneralSourceRoleCstWire293 (Wire Transfer spelling transfer_preserves_text)
open GeneralSourceRoleCstWirePaths293 (atWire transfer_path)
open GeneralSourceRoleCstLossless293 (render_width)
open GeneralSourceRoleCstSpan293 (locate_tree locate_bounds)
open GeneralSourceRoleCstRecovery293 (Plain)
open GeneralSourceRoleCstWireTags293 (kind)

inductive Element where
  | node | token
  deriving DecidableEq, Repr

def tagAndMode : Wire → String × Element
  | .node tag _ => (tag,.node)
  | .token tag _ => (tag,.token)

structure Origin where
  occurrence : Entry
  originalTag : String
  originalMode : Element
  deriving DecidableEq, Repr

def attachOriginal (wire : Wire) (e : Entry) : Option Origin :=
  (atWire e.path wire).map fun w => ⟨e,(tagAndMode w).1,(tagAndMode w).2⟩

def original (wire : Wire) (tree : Tree) : List Origin :=
  (entries tree).filterMap (attachOriginal wire)

theorem decoded_label {w : Wire} {t : Tree} (matched : Transfer w t) :
    kind (tagAndMode w).1 = some t.kind := by
  cases matched with
  | token h => exact h
  | node h _ => exact h

theorem original_exact (wire : Wire) (tree : Tree) (conversion : Transfer wire tree) (o : Origin) :
    o ∈ original wire tree ↔ ∃ raw node,
      atWire o.occurrence.path wire = some raw ∧
      GeneralSourceRoleCstSpan293.locate o.occurrence.path tree 0 = some (node,o.occurrence.extent) ∧
      Transfer raw node ∧ node.kind = o.occurrence.kind ∧ ¬ Plain node.kind ∧
      tagAndMode raw = (o.originalTag,o.originalMode) := by
  constructor
  · intro h
    obtain ⟨entry,belongs,read⟩ := List.mem_filterMap.mp h
    obtain ⟨node,extent,tag,bad⟩ := (entry_exact ..).mp belongs
    have here : GeneralSourceRoleCstPath293.follow entry.path tree = some node := by
      rw [←locate_tree _ _ 0,extent]
      rfl
    obtain ⟨raw,source,transfer⟩ := (transfer_path conversion entry.path node).mp here
    have eq : (⟨entry,(tagAndMode raw).1,(tagAndMode raw).2⟩ : Origin) = o := by
      simpa [attachOriginal,source] using read
    subst o
    exact ⟨raw,node,source,extent,transfer,tag,tag.symm ▸ bad,by cases tagAndMode raw; rfl⟩
  · rintro ⟨raw,node,source,extent,transfer,classification,bad,label⟩
    refine List.mem_filterMap.mpr
      ⟨o.occurrence,(entry_exact ..).mpr ⟨node,extent,classification,classification ▸ bad⟩,?_⟩
    cases o
    simp_all [attachOriginal]

theorem original_byte_width (wire : Wire) (tree : Tree) (conversion : Transfer wire tree) (o : Origin)
    (member : o ∈ original wire tree) :
    ∃ raw, atWire o.occurrence.path wire = some raw ∧
      o.occurrence.extent.high = o.occurrence.extent.low + (spelling raw).utf8ByteSize := by
  obtain ⟨raw,node,lookup,extent,transfer,classification,bad,label⟩ :=
    (original_exact wire tree conversion o).mp member
  have h := (locate_bounds extent).2.1
  have b := (render_width node).symm.trans (congrArg String.utf8ByteSize (transfer_preserves_text transfer))
  exact ⟨raw,lookup,b ▸ h⟩

end Yulang.GeneralSourceRoleCstOriginalMarks294
