import Yulang.GeneralSourceRoleCstVisibleReceipt294

/-! A supplied Missing-node receipt uses an explicit mixed child path, not
a range-only surrogate or an unchecked Rust diagnostic ID. -/
namespace Yulang.GeneralSourceRoleCstMissingReceipt294
open GeneralSourceRoleCstTree293 (Tree Path)
open GeneralSourceRoleCstWire293 (Wire Transfer decode decode_exact)
open GeneralSourceRoleCstOriginalMarks294 (Element Origin original)
open GeneralSourceRoleCstSpan293 (Extent)
open GeneralSourceRoleCstMarkScope294 (Zone classify unrelated_exact)
open GeneralSourceRoleCstRunVisibility294 (enters)

structure MissingAnchor where
  path : Path
  span : Extent

def visitPath : Path → Wire → Bool
  | [i],.node _ cs =>
    match cs[i]? with
    | some (.node "Missing" _) => true
    | _ => false
  | i::j::p,.node _ cs =>
    match cs[i]? with
    | some (.node tag inner) => enters tag && visitPath (j::p) (.node tag inner)
    | _ => false
  | _,_ => false

def rowMatches (e : MissingAnchor) (o : Origin) : Bool :=
  o.originalTag == "Missing" && o.originalMode == .node &&
    o.occurrence.path == e.path && o.occurrence.extent == e.span

theorem row_matches_exact (e : MissingAnchor) (o : Origin) : rowMatches e o = true ↔
    o.originalTag = "Missing" ∧ o.originalMode = .node ∧
      o.occurrence.path = e.path ∧ o.occurrence.extent = e.span := by
  simp [rowMatches,Bool.and_eq_true,and_assoc]

def verified (wire : Wire) (candidate : MissingAnchor) : Bool :=
  match wire with
  | .node "Root" _ =>
    match decode wire with
    | none => false
    | some root =>
      candidate.span.low == candidate.span.high && visitPath candidate.path wire &&
        (original wire root).any (rowMatches candidate)
  | _ => false

theorem verified_exact (wire : Wire) (e : MissingAnchor) :
    verified wire e = true ↔
    ∃ cs root o, wire = .node "Root" cs ∧ Transfer wire root ∧
      e.span.low = e.span.high ∧ visitPath e.path wire = true ∧
      o ∈ original wire root ∧ rowMatches e o = true := by
  have recognized (cs : List Wire) :
      verified (.node "Root" cs) e = true ↔
        ∃ root o, Transfer (.node "Root" cs) root ∧
          e.span.low = e.span.high ∧ visitPath e.path (.node "Root" cs) = true ∧
          o ∈ original (.node "Root" cs) root ∧ rowMatches e o = true := by
    cases decoded : decode (.node "Root" cs) with
    | none => simp [verified,←decode_exact,decoded]
    | some root =>
      simp only [verified,←decode_exact,decoded,Option.some.injEq,Bool.and_eq_true,
        beq_iff_eq,List.any_eq_true]
      constructor
      · rintro ⟨⟨a,b⟩,⟨o,m,q⟩⟩; exact ⟨root,o,rfl,a,b,m,q⟩
      · rintro ⟨_,o,rfl,a,b,m,q⟩; exact ⟨⟨a,b⟩,o,m,q⟩
  cases wire with
  | token k text => simp [verified]
  | node k cs =>
    by_cases root : k = "Root"
    · subst k; simpa using recognized cs
    · have reject : verified (.node k cs) e = false := by
        unfold verified
        split
        · rename_i subs eq
          exact False.elim (root (Wire.node.inj eq).1)
        · rfl
      simp [reject,root]

theorem verified_names_original_missing (wire : Wire) (e : MissingAnchor)
    (h : verified wire e = true) :
      ∃ body, GeneralSourceRoleCstWirePaths293.atWire e.path wire = some (.node "Missing" body) := by
  obtain ⟨_,root,o,_,mapping,width,path,mem,tests⟩ := (verified_exact ..).mp h
  obtain ⟨tag,mode,address,span⟩ := (row_matches_exact ..).mp tests
  obtain ⟨atom,_,whereAt,_,_,_,_,original⟩ :=
     (GeneralSourceRoleCstOriginalMarks294.original_exact wire root mapping o).mp mem
  cases atom with
  | token k s =>
    have contradiction := (Prod.mk.inj original).2.trans mode
    cases contradiction
  | node label body =>
    have same := (Prod.mk.inj original).1.trans tag
    change label = "Missing" at same
    exact ⟨body,by simpa only [address,same] using whereAt⟩

def independentlyOutside (wire : Wire) (p : Path) (e : MissingAnchor) : Bool :=
  verified wire e && classify p e.path == .unrelated

theorem outside_exact (wire : Wire) (p : Path) (e : MissingAnchor) :
    independentlyOutside wire p e = true ↔ verified wire e = true ∧
      (¬ p <+: e.path) ∧ (¬ e.path <+: p) := by
  simp [independentlyOutside,unrelated_exact]

end Yulang.GeneralSourceRoleCstMissingReceipt294
