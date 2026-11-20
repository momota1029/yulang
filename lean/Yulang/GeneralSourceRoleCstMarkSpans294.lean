import Yulang.GeneralSourceRoleCstMarks294

/-! Locate each raw mark without discarding zero-width nodes or conflating marks
with diagnostic runs. Ranges are for the supplied complete token stream. -/
namespace Yulang.GeneralSourceRoleCstMarkSpans294
open GeneralSourceRoleCstTree293 (Tree Path Kind)
open GeneralSourceRoleCstMarks294 (Mark marks marks_exact)
open GeneralSourceRoleCstPath293 (follow)
open GeneralSourceRoleCstRecovery293 (Plain)
open GeneralSourceRoleCstSpan293 (Extent locate width locate_bounds locate_tree)

structure Entry where
  path : Path
  kind : Kind
  extent : Extent
  deriving DecidableEq, Repr

def attach (root : Tree) (mark : Mark) : Option Entry :=
  (locate mark.1 root 0).map fun x => ⟨mark.1,mark.2,x.2⟩

def entries (root : Tree) : List Entry := (marks root).filterMap (attach root)

theorem reach_has_extent {root : Tree} {p : Path} {t : Tree}
    (h : follow p root = some t) :
    ∃ span, locate p root 0 = some (t,span) := by
  rw [← locate_tree _ _ 0] at h
  cases loc : locate p root 0 with
  | none => simp [loc] at h
  | some x =>
    rcases x with ⟨node,span⟩
    have e : node = t := by simpa [loc] using h
    subst node
    exact ⟨span,rfl⟩

theorem entry_exact (root : Tree) (e : Entry) :
    e ∈ entries root ↔
      ∃ node, locate e.path root 0 = some (node,e.extent) ∧
        node.kind = e.kind ∧ ¬ Plain e.kind := by
  unfold entries
  constructor
  · intro h
    obtain ⟨⟨p,k⟩,raw,attached⟩ := List.mem_filterMap.mp h
    obtain ⟨node,found,tag,bad⟩ := (marks_exact ..).mp raw
    obtain ⟨extent,there⟩ := reach_has_extent found
    have equal : (⟨p,k,extent⟩ : Entry) = e := by simpa [attach,there] using attached
    subst e
    exact ⟨node,there,tag,bad⟩
  · rintro ⟨node,there,tag,bad⟩
    have f : follow e.path root = some node := by
      rw [←locate_tree _ _ 0,there]
      rfl
    refine List.mem_filterMap.mpr ⟨(e.path,e.kind),
      (marks_exact ..).mpr ⟨node,f,tag,bad⟩,?_⟩
    cases e
    simp [attach,there]

theorem mark_has_entry (root : Tree) (p : Path) (k : Kind)
    (here : (p,k) ∈ marks root) : ∃ e ∈ entries root, e.path = p ∧ e.kind = k := by
  obtain ⟨node,f,tag,bad⟩ := (marks_exact root p k).mp here
  obtain ⟨span,lo⟩ := reach_has_extent f
  let e : Entry := ⟨p,k,span⟩
  exact ⟨e,(entry_exact root e).mpr ⟨node,lo,tag,bad⟩,rfl,rfl⟩

theorem entry_bounds (root : Tree) (e : Entry) (h : e ∈ entries root) :
    e.extent.low ≤ e.extent.high ∧ e.extent.high ≤ width root := by
  obtain ⟨node,span,tag,mark⟩ := (entry_exact root e).mp h
  have bounds := locate_bounds span
  exact ⟨by omega,by simpa using bounds.2.2⟩

end Yulang.GeneralSourceRoleCstMarkSpans294
