import Yulang.GeneralDeclarativeI65I74WrittenPath460
import Yulang.GeneralDeclarations

namespace Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
open Yulang.GeneralDeclarations (Declaration Clause)
open Yulang.GeneralDeclarationPatterns (Pattern normalize)

/-- Resolved addresses, not lexed text. Child positions retain both the
original zero-based ordinal and the separately authored stable identifier. -/
inductive Site where
  | head (arg : Nat)
  | clause (ordinal clauseId arg : Nat)
  deriving DecidableEq

def readSite (d : Declaration) : Site → Option Term
  | .head arg => d.head[arg]?.map readTerm
  | .clause ordinal id arg => do
      let w ← d.requirements[ordinal]?
      if w.id = id then w.arguments[arg]?.map readTerm else none

inductive OriginalAt (d : Declaration) : Site → Term → Prop
  | head : d.head[i]? = some p → OriginalAt d (.head i) (readTerm p)
  | clause :
      d.requirements[i]? = some w → w.arguments[j]? = some p →
      OriginalAt d (.clause i w.id j) (readTerm p)

theorem original_at_iff_site_read {d : Declaration} {a p} :
    readSite d a = some p ↔ OriginalAt d a p := by
  constructor
  · intro h
    cases a with
    | head i =>
      obtain ⟨orig,row,eq⟩ := Option.map_eq_some_iff.mp h
      rw [← eq]
      exact .head row
    | clause i id j =>
      cases hp : d.requirements[i]? with
      | none => simp [readSite,hp,Option.bind] at h
      | some clause =>
        by_cases same : clause.id = id
        · subst id
          have out : clause.arguments[j]?.map readTerm = some p := by
            simpa [readSite,hp,Option.bind] using h
          obtain ⟨orig,row,eq⟩ := Option.map_eq_some_iff.mp out
          rw [← eq]
          exact .clause hp row
        · simp [readSite,hp,same,Option.bind] at h
  · intro how
    cases how with
    | head eq => simp [readSite,eq]
    | clause clause arg => simp [readSite,clause,arg,Option.bind]

/-- All source nodes are retained. Normalization is separately and
explicitly transported from the old compiler; it is not a rewritten declaration. -/
def normalized (p : Term) : Term := readTerm (normalize (writeTerm p))

theorem normalized_of_original (p : Pattern) :
    normalized (readTerm p) = readTerm (normalize p) := by
  simp [normalized]

theorem normalized_reencodes_exactly (p : Term) :
    writeTerm (normalized p) = normalize (writeTerm p) := by
  simp [normalized]

/-- The whole normalizer is an adjacent typed step; a lexical path is not
constructed by choosing a branch of an original join. No state fields are changed. -/
def readNormalizedPath (keys : KeyRead) (d : Declaration) (site : Site)
    (as : List Address) : Option Term := do
  let src ← readSite d site
  readWalk keys (normalized src) as

def OriginalNormalizedPath (keys : KeyRead) (d : Declaration) (site : Site)
    (as : List Address) (q : Term) : Prop :=
  ∃ src, OriginalAt d site src ∧ Walk keys (normalized src) as q

theorem normalized_path_iff_from_unchanged_source {keys d site as q} :
    readNormalizedPath keys d site as = some q ↔ OriginalNormalizedPath keys d site as q := by
  unfold readNormalizedPath OriginalNormalizedPath
  change ((readSite d site).bind fun src => readWalk keys (normalized src) as) = some q ↔ _
  rw [Option.bind_eq_some_iff]
  simp only [original_at_iff_site_read,read_walk_iff]

end Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
