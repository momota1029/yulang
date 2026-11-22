import Yulang.GeneralDeclarativeWitnessCovariantInterval353

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessCovariantWrittenState353
open GeneralDeclarativeWitnessCovariantMetadata353 (Input Checked check)
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem Row)
open GeneralDeclarationPatterns (Pattern)

structure Line where
  root : Nat
  rhs : Pattern

def printRow (r : Row) : Line :=
  ⟨r.root,.variant r.tag (.app r.box [.var r.valueName])⟩

structure Parsed (p : Input) (l : Line) where
  row : Row
  literal : printRow row = l
  checked : Checked p row.box

/-- Rebuild typed metadata from an independent literal written source.
Reserved roots and opaque fallbacks cannot be selected by the witness. -/
def parse (p : Input) (l : Line) : Option (Parsed p l) :=
  match exact : l.rhs with
  | .variant tag (.app box [.var valueName]) => do
    let confirmed ← check p box
    let r : Row := ⟨l.root,tag,box,valueName⟩
    have literal : printRow r = l := by
      cases l with
      | mk root rhs =>
        change rhs = _ at exact
        cases exact
        rfl
    pure ⟨r,literal,confirmed⟩
  | _ => none

inductive AllParsed (p : Input) : List Line → List Row → Type where
  | nil : AllParsed p [] []
  | cons (root : Parsed p l) : AllParsed p ls rs → AllParsed p (l::ls) (root.row::rs)

def all (p : Input) : (ls : List Line) → Option (Σ rs, AllParsed p ls rs)
  | [] => some ⟨[],.nil⟩
  | head::tail => do
    let parsed ← parse p head
    let ⟨rs,proven⟩ ← all p tail
    pure ⟨parsed.row::rs,.cons parsed proven⟩

theorem exact_list {p : Input} {lines : List Line} {rows : List Row}
    (a : AllParsed p lines rows) : rows.map printRow = lines := by
  induction a with
  | nil => rfl
  | cons p tail ih => simp only [List.map_cons,p.literal,ih]

theorem original_ordinal {p : Input} {lines : List Line} {rows : List Row}
    (a : AllParsed p lines rows) (i : Nat) :
    lines[i]? = (rows[i]?).map printRow := by
  rw [← exact_list a,List.getElem?_map]

/-- The typed rows in the solver-free problem are computed from the
fixed written lines, not supplied again inside a proof receipt. -/
def rebuild (p : Problem) (lines : List Line) : Option (Σ q : Problem, AllParsed p.metadata lines q.rows) := do
  let ⟨rs,proof⟩ ← all p.metadata lines
  pure ⟨{p with rows := rs},proof⟩

end Yulang.GeneralDeclarativeWitnessCovariantWrittenState353
