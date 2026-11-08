import Yulang.CasePresenceValidation

/-! Source positions for presence validation of actual pattern defaults.

The finite collector does not identify two occurrences merely because their
field names agree. A position follows written syntax, including both or
branches and both the payload and the whole-record rest. Its independent
meaning is lookup of an actual default node in the original pattern.

This module does not infer presence from semantic optional subtyping: a
required field satisfies that weaker demand too. Resolved declaration
metadata is connected separately, before ordinary constraint solving. -/

namespace Yulang.CommonPatternSourcePresence

open CasePatterns (Pattern)

inductive Step where
  | first | last | child
  deriving DecidableEq, Repr

abbrev Path := List Step
abbrev Site := Path × Nat

/-- A finite path reads the original source node, without erasing defaults
or changing the order of either branch. Invalid paths have no node. -/
def node (pattern : Pattern F D) : Path → Option (Pattern F D)
  | [] => some pattern
  | .first :: rest => match pattern with
    | .pair first _ | .field _ first _ | .defaultField _ _ first _ |
      .cons first _ | .snoc first _ | .or first _ => node first rest
    | _ => none
  | .last :: rest => match pattern with
    | .pair _ last | .field _ _ last | .defaultField _ _ _ last |
      .cons _ last | .snoc _ last | .or _ last => node last rest
    | _ => none
  | .child :: rest => match pattern with
    | .variant _ child | .nominal _ _ child | .as child _ => node child rest
    | _ => none

def prepend (step : Step) (sites : List Site) : List Site :=
  sites.map fun site => (step :: site.1, site.2)

def sites : Pattern F D → List Site
  | .wildcard | .bind _ | .literal _ | .intRange _ _ | .recordEnd | .nil => []
  | .pair first last | .field _ first last | .cons first last | .snoc first last | .or first last =>
      prepend .first (sites first) ++ prepend .last (sites last)
  | .defaultField name _ first last =>
      ([], name) :: (prepend .first (sites first) ++ prepend .last (sites last))
  | .variant _ child | .nominal _ _ child | .as child _ => prepend .child (sites child)

/-- A source occurrence, specified by direct node lookup rather than by
membership in the collector or acceptance by a presence checker. -/
def DefaultAt (pattern : Pattern F D) (path : Path) (name : Nat) : Prop :=
  ∃ fallback first last, node pattern path = some (.defaultField name fallback first last)

@[simp] theorem mem_prepend (step : Step) (entries : List Site) (path : Path) (name : Nat) :
    (path, name) ∈ prepend step entries ↔
      ∃ rest, path = step :: rest ∧ (rest, name) ∈ entries := by
  simp only [prepend, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨rest, label⟩, member, equal, same⟩
    change label = name at same
    change step :: rest = path at equal
    subst label
    exact ⟨rest, equal.symm, member⟩
  · rintro ⟨rest, rfl, member⟩
    exact ⟨(rest, name), member, rfl, rfl⟩

/-- Every collected occurrence is exactly an original source default, and
every original default is collected, including defaults in an unselected
or branch. No execution or successful match is assumed. -/
theorem sites_exact (pattern : Pattern F D) (path : Path) (name : Nat) :
    (path, name) ∈ sites pattern ↔ DefaultAt pattern path name := by
  induction pattern generalizing path <;> cases path with
  | nil => simp [sites, DefaultAt, node, eq_comm]
  | cons step rest => cases step <;> simp_all [sites, DefaultAt, node]

end Yulang.CommonPatternSourcePresence
