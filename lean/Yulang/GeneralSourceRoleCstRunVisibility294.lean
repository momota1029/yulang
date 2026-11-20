import Yulang.GeneralSourceRoleCstEqualSpans294

/-! A conservative check against three source-visible barriers to the plain
Rust raw-token grouping case. This is not the full structural walk, does not
infer any diagnostic, and assumes its start is the retained Root node. -/
namespace Yulang.GeneralSourceRoleCstRunVisibility294
open GeneralSourceRoleCstTree293 (Path)
open GeneralSourceRoleCstWire293 (Wire)
open GeneralSourceRoleCstWirePaths293 (atWire)

def enters (label : String) : Bool := label != "Missing" && label != "NestingTooDeep"

def visible : Path → Wire → Bool
  | i::p,.node k children =>
    match children[i]?,p with
    | some (.token t src),[] => k != "Error" && t == "Error" && !(src.isEmpty)
    | some (.node c cs),_::_ => enters c && visible p (.node c cs)
    | _,_ => false
  | _,_ => false

/-- The subset of the walk for visiting a literal nonempty Error token, with
no opaque subtree on its path and no suppressing immediate parent. -/
inductive Visible : Path → Wire → Prop
  | direct {i : Nat} {label src : String} {cs : List Wire} :
      cs[i]? = some (.token "Error" src) → label ≠ "Error" → src.isEmpty = false →
      Visible [i] (.node label cs)
  | descend {i : Nat} {p : Path} {par label : String} {cs inner : List Wire} :
      p ≠ [] → cs[i]? = some (.node label inner) → label ≠ "Missing" →
      label ≠ "NestingTooDeep" → Visible p (.node label inner) →
      Visible (i::p) (.node par cs)

theorem visible_exact (p : Path) (w : Wire) : visible p w = true ↔ Visible p w := by
  induction p generalizing w with
  | nil =>
    constructor
    · intro h; cases w <;> cases h
    · intro h; cases h
  | cons i p ih =>
    constructor
    · intro h
      cases w with
      | token k s => simp [visible] at h
      | node k cs =>
        cases child : cs[i]? with
        | none => cases p <;> simp [visible,child] at h
        | some c =>
          cases p with
          | nil =>
            cases c with
            | node label kids => simp [visible,child] at h
            | token label txt =>
              have tests : (k ≠ "Error" ∧ label = "Error") ∧ txt.isEmpty = false := by
                simpa [visible,child] using h
              rcases tests with ⟨⟨pk,rfl⟩,ne⟩
              exact .direct child pk ne
          | cons j tail =>
            cases c with
            | token label txt => simp [visible,child] at h
            | node label kids =>
              have tests : (label ≠ "Missing" ∧ label ≠ "NestingTooDeep") ∧
                  visible (j::tail) (.node label kids) = true := by
                simpa [visible,child,enters] using h
              exact .descend (List.cons_ne_nil _ _) child tests.1.1 tests.1.2 (ih _ |>.mp tests.2)
    · intro h
      cases h with
      | direct child pk ne => simp [visible,child,pk,ne]
      | descend nonempty child hm hn below =>
        cases p with
        | nil => exact False.elim (nonempty rfl)
        | cons j tail =>
          have done := (ih _).mpr below
          simpa [visible,child,enters,hm,hn] using done

theorem visible_points_to_error {p : Path} {w : Wire} (h : Visible p w) :
    ∃ src, atWire p w = some (.token "Error" src) ∧ src.isEmpty = false := by
  induction h with
  | direct child label nonempty =>
    exact ⟨_,by simp [atWire,child],nonempty⟩
  | descend _ child _ _ _ ih =>
    obtain ⟨src,atPath,nonempty⟩ := ih
    exact ⟨src,by simp [atWire,child,atPath],nonempty⟩

end Yulang.GeneralSourceRoleCstRunVisibility294
