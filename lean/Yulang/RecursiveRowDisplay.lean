import Yulang.CyclicRowDecisions

/-!
# Least fixed-point meaning of the inferred `as` row binder

A single bound row variable is represented by the already established finite
row-expression syntax. Its meaning is the least solution, not an arbitrary
fixed point. Folding and unfolding preserve the possibly infinite set of
occurrences. Any finite problem with one row slot can be collected into this
one binder without changing its least solution, even if it has several cycles.

The textual printer below implements the three current one-tail spellings
at an already determined boundary: `'e`, `'e?`, and `'e[io]`, followed by `as`.
It prints no numerical weights. It is an inferred display payload, not a new
source annotation grammar. General formatting across several boundaries and
the spelling of mutually recursive variables remain outside this module.

Membership, inclusion and equality for the printed one-step cycles connect to
the existing executable cycle solvers. The general folding theorem by itself
does not supply a solver for arbitrary recursive binder bodies.
-/

namespace Yulang.RecursiveRowDisplay

open Directed
open RowInference (RowExpr)
open RecursiveRows (SetRow Problem Models Derives)

variable {n : Nat} {Key : Type}

structure AsRow (n : Nat) (Key : Type) where
  name : String
  body : RowExpr Key (Fin n) Unit

def AsRow.problem (display : AsRow n Key) : Problem n Key Unit :=
  [⟨(), display.body⟩]

def AsRow.Meaning (display : AsRow n Key) : SetRow n Key :=
  Derives display.problem ()

theorem AsRow.unfold (display : AsRow n Key) (occurrence : Occurrence n Key) :
    display.Meaning occurrence ↔
      display.body.eval (RecursiveRows.algebra n Key) (fun _ => display.Meaning) occurrence := by
  constructor
  · intro derived
    cases derived with
    | rule declared expression =>
        have same := List.mem_singleton.mp declared
        cases same
        exact (RecursiveRows.expr_exact display.problem display.body occurrence).mp expression
  · intro member
    exact RecursiveRows.least_models display.problem ⟨(), display.body⟩ (by simp [AsRow.problem])
      occurrence member

theorem AsRow.unfold_set (display : AsRow n Key) :
    display.Meaning =
      display.body.eval (RecursiveRows.algebra n Key) (fun _ => display.Meaning) :=
  funext (fun occurrence => propext (display.unfold occurrence))

/-- The binder is below every prefixed point, including infinite ones. -/
theorem AsRow.least (display : AsRow n Key) (row : SetRow n Key)
    (closed : ∀ occurrence,
      display.body.eval (RecursiveRows.algebra n Key) (fun _ => row) occurrence → row occurrence) :
    ∀ occurrence, display.Meaning occurrence → row occurrence := by
  apply RecursiveRows.least_below display.problem (fun _ => row)
  intro rule declared occurrence member
  have same := List.mem_singleton.mp declared
  cases same
  exact closed occurrence member

theorem AsRow.rename_meaning (display : AsRow n Key) (name : String) :
    ({ display with name := name } : AsRow n Key).Meaning = display.Meaning := rfl

/-- The finite union of all lower bounds; the only target slot is `()`. -/
def collectBody : Problem n Key Unit → RowExpr Key (Fin n) Unit
  | [] => .empty
  | rule :: rest => .union rule.lower (collectBody rest)

theorem collectBody_exact (problem : Problem n Key Unit)
    (rows : Unit → SetRow n Key) (occurrence : Occurrence n Key) :
    (collectBody problem).eval (RecursiveRows.algebra n Key) rows occurrence ↔
      ∃ rule ∈ problem, rule.lower.eval (RecursiveRows.algebra n Key) rows occurrence := by
  induction problem with
  | nil => simp [collectBody, RowExpr.eval, RecursiveRows.algebra]
  | cons rule rest ih =>
      change (rule.lower.eval (RecursiveRows.algebra n Key) rows occurrence ∨
        (collectBody rest).eval (RecursiveRows.algebra n Key) rows occurrence) ↔ _
      rw [ih]
      simp only [List.mem_cons]
      constructor
      · intro member
        rcases member with first | ⟨selected, declared, fact⟩
        · exact ⟨rule, Or.inl rfl, first⟩
        · exact ⟨selected, Or.inr declared, fact⟩
      · rintro ⟨selected, declared, fact⟩
        rcases declared with rfl | declared
        · exact Or.inl fact
        · exact Or.inr ⟨selected, declared, fact⟩

def AsRow.ofProblem (name : String) (problem : Problem n Key Unit) : AsRow n Key :=
  ⟨name, collectBody problem⟩

theorem AsRow.ofProblem_models (name : String) (problem : Problem n Key Unit)
    (rows : Unit → SetRow n Key) :
    Models (AsRow.ofProblem name problem).problem rows ↔ Models problem rows := by
  constructor
  · intro model rule declared occurrence member
    have fact := model ⟨(), collectBody problem⟩ (by simp [AsRow.problem, AsRow.ofProblem]) occurrence
      ((collectBody_exact problem rows occurrence).mpr ⟨rule, declared, member⟩)
    cases rule.target
    exact fact
  · intro model rule declared occurrence member
    have same := List.mem_singleton.mp declared
    cases same
    obtain ⟨selected, present, fact⟩ := (collectBody_exact problem rows occurrence).mp member
    have result := model selected present occurrence fact
    cases selected.target
    exact result

/-- Collecting all lower rules into an `as` body preserves the original least
set solution, rather than only preserving some chosen fixed point. -/
theorem AsRow.ofProblem_exact (name : String) (problem : Problem n Key Unit)
    (occurrence : Occurrence n Key) :
    (AsRow.ofProblem name problem).Meaning occurrence ↔ Derives problem () occurrence := by
  unfold AsRow.Meaning
  rw [RecursiveRows.derives_iff_forced, RecursiveRows.derives_iff_forced]
  exact ⟨fun forced rows model => forced rows ((AsRow.ofProblem_models name problem rows).mpr model),
    fun forced rows model => forced rows ((AsRow.ofProblem_models name problem rows).mp model)⟩

theorem AsRow.ofProblem_least (name : String) (problem : Problem n Key Unit) :
    RecursiveRows.IsLeastModel problem (fun _ => (AsRow.ofProblem name problem).Meaning) := by
  have same : (fun _ : Unit => (AsRow.ofProblem name problem).Meaning) = Derives problem := by
    funext slot occurrence
    cases slot
    exact propext (AsRow.ofProblem_exact name problem occurrence)
  rw [same]
  exact RecursiveRows.least_principal problem

/-- Only the current single-tail display forms are printed here. The `as`
binder is settled; the surrounding surface notation follows current spec 7.3. -/
inductive TailMode (Key : Type) where
  | defaultProtect
  | defaultRelease
  | masked (allowed : List Key)

def TailMode.action [DecidableEq Key] (scope : Fin n) : TailMode Key → RecursiveRowGraph.Action n Key
  | .defaultProtect => .protect scope allowNone
  | .defaultRelease => .release scope allowNone
  | .masked allowed => .protect scope (fun key => decide (key ∈ allowed))

def TailMode.render (keyName : Key → String) (name : String) : TailMode Key → String
  | .defaultProtect => name
  | .defaultRelease => name ++ "?"
  | .masked allowed => name ++ "[" ++ String.intercalate "," (allowed.map keyName) ++ "]"

/-- The boundary is contextual semantic information, not a numerical weight
printed in the public row. The binder name is only an alpha-renaming label. -/
structure Display (n : Nat) (Key : Type) where
  key : Key
  scope : Fin n
  mode : TailMode Key
  binder : String

def Display.cycle [DecidableEq Key] (display : Display n Key) : CyclicRows.SeededCycle n Key :=
  ⟨display.key, [], [display.mode.action display.scope]⟩

def Display.asRow [DecidableEq Key] (display : Display n Key) : AsRow n Key :=
  AsRow.ofProblem display.binder display.cycle.problem

def Display.render (keyName : Key → String) (display : Display n Key) : String :=
  "[" ++ keyName display.key ++ ", " ++ display.mode.render keyName display.binder ++
    "] as " ++ display.binder

theorem Display.meaning_exact [DecidableEq Key] (display : Display n Key)
    (occurrence : Occurrence n Key) :
    display.asRow.Meaning occurrence ↔ Derives display.cycle.problem () occurrence :=
  AsRow.ofProblem_exact _ _ _

def Display.check [DecidableEq Key] (display : Display n Key) (occurrence : Occurrence n Key) : Bool :=
  display.cycle.check occurrence

theorem Display.check_exact [DecidableEq Key] (display : Display n Key)
    (occurrence : Occurrence n Key) :
    display.check occurrence = true ↔ display.asRow.Meaning occurrence :=
  (display.cycle.check_exact occurrence).trans (display.meaning_exact occurrence).symm

def Display.checkSubset [DecidableEq Key] (source target : Display n Key) : Bool :=
  CyclicRowDecisions.checkSubset source.cycle target.cycle

theorem Display.checkSubset_exact [DecidableEq Key] (source target : Display n Key) :
    source.checkSubset target = true ↔
      ∀ occurrence, source.asRow.Meaning occurrence → target.asRow.Meaning occurrence := by
  rw [Display.checkSubset, CyclicRowDecisions.checkSubset_exact]
  constructor
  · intro included occurrence member
    exact (target.meaning_exact occurrence).mpr (included occurrence ((source.meaning_exact occurrence).mp member))
  · intro included occurrence member
    exact (target.meaning_exact occurrence).mp (included occurrence ((source.meaning_exact occurrence).mpr member))

def Display.checkEqual [DecidableEq Key] (left right : Display n Key) : Bool :=
  CyclicRowDecisions.checkEqual left.cycle right.cycle

theorem Display.checkEqual_exact [DecidableEq Key] (left right : Display n Key) :
    left.checkEqual right = true ↔ left.asRow.Meaning = right.asRow.Meaning := by
  rw [Display.checkEqual, CyclicRowDecisions.checkEqual_exact]
  constructor
  · intro same
    funext occurrence
    exact propext ((left.meaning_exact occurrence).trans ((same occurrence).trans (right.meaning_exact occurrence).symm))
  · intro same occurrence
    rw [← left.meaning_exact occurrence, ← right.meaning_exact occurrence, same]

theorem Display.rename_meaning [DecidableEq Key] (display : Display n Key) (binder : String) :
    ({ display with binder := binder } : Display n Key).asRow.Meaning = display.asRow.Meaning := rfl

namespace Examples

def growing : Display 1 Unit := ⟨(), 0, .defaultProtect, "'e"⟩
def falling : Display 1 Unit := ⟨(), 0, .defaultRelease, "'e"⟩
def allowed : Display 1 Unit := ⟨(), 0, .masked [()], "'e"⟩
def point (weight : Int) : Occurrence 1 Unit := ⟨(), fun _ => weight⟩

example : growing.render (fun _ => "k") = "[k, 'e] as 'e" := by decide
example : falling.render (fun _ => "k") = "[k, 'e?] as 'e" := by decide
example : allowed.render (fun _ => "io") = "[io, 'e[io]] as 'e" := by decide
example : growing.check (point 1000000) = true := by decide
example : growing.check (point (-1)) = false := by decide
example : falling.check (point (-1000000)) = true := by decide
example : falling.check (point 1) = false := by decide
example : allowed.check (point 0) = true := by decide
example : allowed.check (point 1) = false := by decide
example : growing.checkEqual { growing with binder := "'r" } = true := by decide
example : allowed.checkSubset growing = true := by decide
example : growing.checkSubset allowed = false := by decide

/-- A self-reference without any seed denotes the empty least solution,
although many nonempty rows are also fixed points of this body. -/
def noSeed : AsRow 0 Unit := ⟨"'e", .var ()⟩

theorem noSeed_empty (occurrence : Occurrence 0 Unit) : ¬ noSeed.Meaning occurrence := by
  exact noSeed.least (fun _ => False) (fun _ member => member) occurrence

end Examples

end Yulang.RecursiveRowDisplay
