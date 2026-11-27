import Yulang.GeneralDeclarativeI65I74AliasedFieldReification472
import Yulang.CommonRoleGraphBisimulation
import Yulang.GeneralDeclarativeI65I74AliasedObservationCone472

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ObservationAlternatives473
open ObservationSyntax471 (NodeTicket GraphTicket Label Slot readDescription codeLabel descend)
open ObservationAliasHead472 (allDefinitions)
open ObservationRawAlias471 (ClassWire checkWholeClass connectedKeys checked_class_is_exact_for_every_name)
open QuotientObservation471 (ConeWire Wire ExactCone ReturnsUpToEquality replayCone cone_replay_sound embedded)
open CommonRoleRegularGraph (Node Graph)
open CommonRoleGraphBisimulation (ObservationallyEqual checkBisimulation check_bisimulation_exact
  bisimulation_observations)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeHead320 (Equation)

inductive Place where
  | logical (name : Nat)
  | rowPos (oldOrdinal : Nat) (path : List Slot)
  deriving DecidableEq

structure Position where
  tag : Place
  oldOrdinal : Nat

structure Positions (n : Nat) where
  cells : Vector Position n
  signs : List GeneralNormalizedObservation.Shape
  classes : Vector ClassWire n

def oldPosition (tables : Positions n) (i : Fin n) : Place := (tables.cells.get i).tag

def findPosition (tables : Positions n) (site : Place) : Option (Fin n) :=
  (List.finRange n).find? fun i => oldPosition tables i == site

theorem found_position_is_literal {tables : Positions n} {site i}
    (read : findPosition tables site = some i) : oldPosition tables i = site :=
  beq_iff_eq.mp (List.find?_some (p := fun i => oldPosition tables i == site) read)

def anchorFor (p : Position) (selector : Slot) (child : Expr) : Place :=
  match child with
  | .variable n => .logical n
  | _ =>
    match p.tag with
    | .logical _ => .rowPos p.oldOrdinal [selector]
    | .rowPos ord older => .rowPos ord (older ++ [selector])

/-- Only the particular literal description at the indicated ordinal.
Agreement of all actual definitions is dealt with *after* constructing
the finite graph; this first read is not source authority. -/
def readTermAt (s : GeneralDeclarativeI65.State) (tables : Positions n) (i : Fin n) : Option Expr := do
  let p := tables.cells.get i
  let row ← s.current.ordinary.equations[p.oldOrdinal]?
  match p.tag with
  | .logical root =>
    let cw := tables.classes.get i
    if checkWholeClass s.current.ordinary root cw &&
      decide (row.left ∈ connectedKeys cw) && ObservationSyntax471.isDefinedAt row.left row
    then some row.right else none
  | .rowPos ordinal path =>
    if ordinal = p.oldOrdinal then descend s row.right path else none

def readNodeAt (s : GeneralDeclarativeI65.State) (tables : Positions n) (i : Fin n) : Option (Node n) := do
  let term ← readTermAt s tables i
  let (label,children) ← readDescription s term
  let indices ← children.mapM (fun x => findPosition tables (anchorFor (tables.cells.get i) x.1 x.2))
  codeLabel tables.signs label indices

def graphOf (s : GeneralDeclarativeI65.State) (tables : Positions n) : Graph n :=
  fun i => (readNodeAt s tables i).getD .unresolved

def includesOldDefinition (tables : Positions n) (relation : List (Fin n × Fin n))
    (selected : Fin n) (ordinal : Nat) : Bool :=
  match findPosition tables (.rowPos ordinal []) with
  | none => false
  | some another => decide ((selected,another) ∈ relation)

def checkAlternatives (s : GeneralDeclarativeI65.State) (tables : Positions n)
    (relation : List (Fin n × Fin n)) (selected : Fin n) : Bool :=
  match oldPosition tables selected with
  | .rowPos _ _ => true
  | .logical name =>
    let old := s.current.ordinary
    let c := tables.classes.get selected
    checkWholeClass old name c &&
      (List.range old.equations.length).all fun ordinal =>
        match old.equations[ordinal]? with
        | none => false
        | some eq =>
          if decide (eq.left ∈ connectedKeys c) && ObservationSyntax471.isDefinedAt eq.left eq then
            includesOldDefinition tables relation selected ordinal
          else true

def readAlternatives (s : GeneralDeclarativeI65.State) (tables : Positions n)
    (relation : List (Fin n × Fin n)) (root : Fin n) (scope : ConeWire n m) (q : Wire m k) : Option Bool :=
  if (decide (tables.signs.Nodup ∧ (List.ofFn (oldPosition tables)).Nodup) &&
      checkBisimulation (graphOf s tables) relation &&
      (List.finRange m).all (fun j => checkAlternatives s tables relation (embedded scope j))) &&
      relation.all (fun (left,right) => checkAlternatives s tables relation left &&
        checkAlternatives s tables relation right) then
    replayCone (graphOf s tables) root scope q
  else none

theorem old_lexical_row_root_never_guesses_its_ordinal
    {s : GeneralDeclarativeI65.State} {tables : Positions n} {i : Fin n} {ordinal term}
    (literal : oldPosition tables i = .rowPos ordinal []) (read : readTermAt s tables i = some term) :
    ∃ row, s.current.ordinary.equations[ordinal]? = some row ∧ row.right = term := by
  unfold oldPosition at literal
  cases found : s.current.ordinary.equations[(tables.cells.get i).oldOrdinal]? with
  | none => simp [readTermAt,literal,found,bind,Option.bind] at read
  | some row =>
    by_cases key : ordinal = (tables.cells.get i).oldOrdinal
    · subst ordinal
      exact ⟨row,found,by simpa [readTermAt,literal,found,bind,Option.bind,descend] using read⟩
    · simp [readTermAt,literal,found,key,bind,Option.bind] at read

theorem all_actual_alternatives_have_a_real_bisimilar_source_coordinate
    {s : GeneralDeclarativeI65.State} {tables : Positions n} {rel : List (Fin n × Fin n)}
    {root : Fin n} {scope : ConeWire n m} {q : Wire m k} {b}
    (read : readAlternatives s tables rel root scope q = some b) :
    (b = true ↔ ReturnsUpToEquality (graphOf s tables) root) ∧
    ∀ (j : Fin m) (name ordinal : Nat) (row : Equation),
      oldPosition tables (embedded scope j) = .logical name →
      s.current.ordinary.equations[ordinal]? = some row →
      GeneralDeclarativeLowerKnown321.Alias s.current.ordinary name row.left →
      ObservationSyntax471.isDefinedAt row.left row = true →
      ∃ target, oldPosition tables target = .rowPos ordinal [] ∧
        ObservationallyEqual (graphOf s tables) (embedded scope j) target := by
  unfold readAlternatives at read
  split at read
  · rename_i accepted
    obtain ⟨both,guard⟩ := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp accepted).1
    have bisim := (check_bisimulation_exact ..).mp (Bool.and_eq_true_iff.mp both).2
    refine ⟨(cone_replay_sound read).2,?_⟩
    intro j name ordinal row coord actual alias constructor
    have scanned := List.all_eq_true.mp guard j (List.mem_finRange _)
    simp only [checkAlternatives,coord] at scanned
    obtain ⟨whole,all⟩ := Bool.and_eq_true_iff.mp scanned
    have inClass := (checked_class_is_exact_for_every_name whole _).mpr alias
    have within := List.getElem?_eq_some_iff.mp actual
    have one := List.all_eq_true.mp all ordinal (List.mem_range.mpr within.1)
    have listed : (decide (row.left ∈ connectedKeys (tables.classes.get (embedded scope j))) &&
      ObservationSyntax471.isDefinedAt row.left row) = true :=
      Bool.and_eq_true_iff.mpr ⟨decide_eq_true inClass,constructor⟩
    have matchProof : includesOldDefinition tables rel (embedded scope j) ordinal = true := by
      simpa [actual,listed] using one
    cases looked : findPosition tables (.rowPos ordinal []) with
    | none => simp [includesOldDefinition,looked] at matchProof
    | some target =>
      have mem : (embedded scope j,target) ∈ rel := by
        simpa [includesOldDefinition,looked] using matchProof
      exact ⟨target,found_position_is_literal looked,fun depth =>
        bisimulation_observations _ _ bisim depth _ _ mem⟩
  · cases read

open CommonRoleGraphBisimulation (observe)

theorem proved_same_observation_cannot_replace_a_resolved_alternative_with_unknown
    (g : Graph n) (left right : Fin n) (equal : ObservationallyEqual g left right)
    (resolved : g left ≠ .unresolved) : g right ≠ .unresolved := by
  intro unknown
  have depth := equal 1
  cases known : g left <;> simp_all [observe]

theorem a_successful_cone_never_leaves_an_actual_alternative_unread
    {s : GeneralDeclarativeI65.State} {tables : Positions n} {rel : List (Fin n × Fin n)}
    {root : Fin n} {scope : ConeWire n m} {q : Wire m k} {b}
    (read : readAlternatives s tables rel root scope q = some b)
    (j : Fin m) (name ordinal : Nat) (row : Equation)
    (coord : oldPosition tables (embedded scope j) = .logical name)
    (physical : s.current.ordinary.equations[ordinal]? = some row)
    (alias : GeneralDeclarativeLowerKnown321.Alias s.current.ordinary name row.left)
    (defn : ObservationSyntax471.isDefinedAt row.left row = true) :
    ∃ alt, oldPosition tables alt = .rowPos ordinal [] ∧ readTermAt s tables alt = some row.right ∧
      ObservationallyEqual (graphOf s tables) (embedded scope j) alt := by
  obtain ⟨alt,position,equal⟩ :=
    (all_actual_alternatives_have_a_real_bisimilar_source_coordinate read).2
      j name ordinal row coord physical alias defn
  have exactScope : ExactCone (graphOf s tables) root scope := by
    unfold readAlternatives at read
    split at read
    · exact (cone_replay_sound read).1
    · cases read
  have knownHere : graphOf s tables (embedded scope j) ≠ .unresolved := by
    rw [exactScope.2.2.2]
    have support := exactScope.2.2.1 j
    cases atNode : QuotientObservation471.cone scope j <;>
      simp_all [QuotientObservation471.projectNode]
  have notUnknown := proved_same_observation_cannot_replace_a_resolved_alternative_with_unknown
    (graphOf s tables) _ _ equal knownHere
  cases existsTerm : readTermAt s tables alt with
  | none => exact (notUnknown (by simp [graphOf,readNodeAt,existsTerm,bind,Option.bind])).elim
  | some term =>
    obtain ⟨actual,atPos,spelling⟩ := old_lexical_row_root_never_guesses_its_ordinal position existsTerm
    have same : actual = row := Option.some.inj (atPos.symm.trans physical)
    exact ⟨alt,position,by rw [same] at spelling; exact spelling ▸ existsTerm,equal⟩

theorem accepted_bisimulation_checks_both_endpoints_of_every_supplied_pair
    {s : GeneralDeclarativeI65.State} {tables : Positions n} {rel : List (Fin n × Fin n)}
    {root : Fin n} {scope : ConeWire n m} {q : Wire m k} {b}
    (read : readAlternatives s tables rel root scope q = some b)
    {first last : Fin n} (given : (first,last) ∈ rel) :
    checkAlternatives s tables rel first = true ∧
    checkAlternatives s tables rel last = true := by
  unfold readAlternatives at read
  split at read
  · rename_i accepted
    exact Bool.and_eq_true_iff.mp (List.all_eq_true.mp (Bool.and_eq_true_iff.mp accepted).2 _ given)
  · cases read

open ObservationSyntax471
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table attach)

def observedInputPlace : ObservationSyntax471.Address → Place
  | .named n => .logical n
  | .inline i path => .rowPos i path

def readAlternativeInputField (p : FullProblem) (authored : Table) (gd : CheckedTable p.old.state.core.current)
    (input : AttachedFieldWire472) (positions : Positions n) (pairs : List (Fin n × Fin n))
    (start : Fin n) (scope : ConeWire n m) (q : Wire m k) : Option CheckedFieldBit := do
  let a ← attach p.state.base.core.current.ordinary authored
  let f ← readFieldOrigin (gateFromAttachedAuthor472 (p := p) a) gd (input.atGate a)
  let _ ← readTyping f
  if observedInputPlace (confirmedAddress f) = oldPosition positions start then
    let bit ← readAlternatives p.old.state.core positions pairs start scope q
    pure ⟨p.root.occurrence,f.head.orig.declaration.id,input.declarationOrdinal,input.path,input.label,bit⟩
  else none

end Yulang.GeneralDeclarativeI65.I72.ObservationAlternatives473
