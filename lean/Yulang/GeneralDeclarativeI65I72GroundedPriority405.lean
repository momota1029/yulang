import Yulang.GeneralDeclarativeI65I72ActualInversion404

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeK2Graph321 (View)

/-- The actual candidate tape, not a list of proposed addresses.
This slice represents each original variable position of each matched
candidate, with exactly the written binder and arity. An unrepresented
assessment is not turned into a miss or omitted from the tape. -/
inductive VariableScan405 {s : State} {q : Request} :
    {rows : List Declaration} → CandidateTape s.core q rows → Type where
  | nil : VariableScan405 .nil
  | matched {pick : AuthoredCandidate s.core q row} :
      RepeatedRow403 q row → VariableScan405 tail →
      VariableScan405 (.next (.matched pick) tail)

/-- Keep the visible row ordinal, original argument ordinal and binder;
do not sort, deduplicate, or replace authored order with proof order. -/
structure VariablePosition405 where
  visibleOrdinal : Nat
  argumentOrdinal : Nat
  binder : Nat
  deriving DecidableEq

def VariableScan405.positions {s : State} {q rows} {t : CandidateTape s.core q rows}
    (scan : VariableScan405 t) (firstRow : Nat := 0) : List VariablePosition405 :=
  match scan with
  | .nil => []
  | .matched input tail =>
    input.binders.mapIdx (fun i n => ⟨firstRow,i,n⟩) ++ tail.positions (firstRow+1)

def VariableScan405.visits {s : State} {q rows} {t : CandidateTape s.core q rows}
    (scan : VariableScan405 t) : List CandidateVisit :=
  match scan with
  | .nil => []
  | .matched _ tail => tail.visits

theorem variable_scan_visits_exact405 {s : State} {q rows} {t : CandidateTape s.core q rows}
    (scan : VariableScan405 t) : scan.visits = [] := by
  induction scan with
  | nil => rfl
  | matched _ _ ih => exact ih

theorem variable_scan_is_total405 {s : State} {q rows} {t : CandidateTape s.core q rows}
    (scan : VariableScan405 t) :
    t.live = rows ∧ t.waits = false ∧
    ∀ row ∈ rows, ∀ p ∈ row.head, ∃ n, p = Pattern.var n ∧
      ∀ (view : View) (root site : Nat),
        ¬ GeneralDeclarativeInspect321.Visit view root (.variable n) site := by
  induction scan with
  | nil => simp [CandidateTape.live,CandidateTape.waits]
  | matched row _ ih =>
    refine ⟨by simp [CandidateTape.live,ih.1],ih.2.1,?_⟩
    intro d atRow p written
    rcases List.mem_cons.mp atRow with same|later
    · subst d
      rw [row.literal] at written
      obtain ⟨n,_,same⟩ := List.mem_map.mp written
      exact ⟨n,same.symm,fun _ _ _ => GeneralDeclarativeInspect321.variable_has_no_visit⟩
    · exact ih.2.2 d later p written

def single_variable_scan405 {s : State} {q d}
    (rows : List Declaration) (eq : rows = [d])
    (pick : AuthoredCandidate s.core q d) (input : RepeatedRow403 q d) :
    VariableScan405 (eq.symm ▸ (.next (.matched pick) .nil : CandidateTape s.core q [d])) := by
  subst rows
  exact .matched input .nil

/-- Exact same-event inversion: the binding is not by dictionary key.
The data constructor requires a derivation for the actual tape; there
is no visits list to set or update. -/
structure GroundedSelection405 (R : SourcePrimitives) {s q} (e : Event s q)
    (needs : List (OutputNeed s)) (_support : SupportForest R s needs) where
  tape : CandidateTape s.core q (visible s.core q)
  origin : SelectedHeadOrigin395 (row := e.frame.decl) tape
  exactOrdinal : origin.rawOrdinal = e.frame.ordinal
  exactHead : origin.pick.head = e.head
  scan : VariableScan405 tape
  sole : visible s.core q = [e.frame.decl]

def GroundedSelection405.toSelectedSource {R s q e needs support}
    (actual : GroundedSelection405 (s := s) (q := q) R e needs support) :
    SelectedSource R e needs support :=
  ⟨actual.tape,actual.origin,actual.exactOrdinal,actual.scan.visits⟩

/-- The raw root rule is a premise of the original selected inference,
and refers to all ordinary rows. Constructor visits, if any, must be
justified separately; variables add none even if they carry a cycle. -/
theorem grounded_selected_priority405 {R s q e needs support}
    (actual : GroundedSelection405 (s := s) (q := q) R e needs support)
    (raw : ¬ RootCycle s q) :
    (¬ RootCycle s q) ∧ actual.scan.visits = [] ∧ actual.tape.waits = false ∧
    actual.tape.live = [e.frame.decl] := by
  have exactScan := variable_scan_is_total405 actual.scan
  exact ⟨raw,variable_scan_visits_exact405 actual.scan,exactScan.2.1,
    exactScan.1.trans actual.sole⟩

def GroundedInversion405 (R : SourcePrimitives) : Prop :=
  ∀ s q (e : Event s q) needs, ¬ RootCycle s q → R.elected s q e needs →
    ∀ support : SupportForest R s needs, Nonempty (GroundedSelection405 R e needs support)

theorem actual_completed_choice_grounds_visits405 : GroundedInversion405 completedChoiceSource404 := by
  intro s q e needs safe choice support
  rcases choice with old|new
  · obtain ⟨source⟩ := old.2.1
    exact ⟨⟨selectedRepeatedTape403 source.elected source.retained,source.origin,
      (congrArg AuthoredBodyFrame393.ordinal source.sameFrame).symm,source.sameHead.symm,
      single_variable_scan405 _ source.elected.sole
        (selectedRepeatedCandidate403 source.elected source.retained) source.elected.row,
      source.elected.sole⟩⟩
  · obtain ⟨source⟩ := new.1
    exact ⟨⟨supportedTape404 source.choice source.retained,source.origin,
      (congrArg AuthoredBodyFrame393.ordinal source.frame).symm,source.head.symm,
      single_variable_scan405 _ source.choice.sole
        (supportedCandidate404 source.choice source.retained) source.choice.row,
      source.choice.sole⟩⟩

/-- Exact scoped replacement for provisional S03. Unlike C402 S03,
it quantifies over actual replay of the ordered candidate derivation.
The positive case is the actual variable selection, not a presumed
state coverage theorem for structural guards. -/
def GroundedS03_405 (R : SourcePrimitives) : Prop :=
  ∀ s q (e : Event s q) needs support (actual : GroundedSelection405 R e needs support),
    ¬ RootCycle s q → R.elected s q e needs →
    (¬ RootCycle s q) ∧ actual.scan.visits = [] ∧ actual.tape.waits = false ∧
    actual.tape.live = [e.frame.decl]

theorem groundedS03_of_actual_variable_scan405 (R : SourcePrimitives) :
    GroundedS03_405 R :=
  fun _ _ _ _ _ actual safe _ => grounded_selected_priority405 actual safe

end Yulang.GeneralDeclarativeI65.I72
