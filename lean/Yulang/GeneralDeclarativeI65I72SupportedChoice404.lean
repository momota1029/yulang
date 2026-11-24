import Yulang.GeneralDeclarativeI65I72CompletedInput404

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (All₂)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarations (Declaration Checked)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr)

/-- Reading a completed output uses the fixed dependency position,
and exactly its output at the actual unnamed input's lower name.
The corresponding proof tree must be provided as a strict child of
the selected SourceTrace; this syntax alone never grants eligibility. -/
inductive InputAccess404 (s : State) (needs : List (OutputNeed s)) (a : Capture) : Type where
  | authored : SourceArgument403 s a → InputAccess404 s needs a
  | viaOutput (slot : Nat) (atNeed : needs[slot]? = some need)
      (literal : LiteralInputNeed404 s a need)
      (bounds : Bounds s.core.current.ordinary a) : InputAccess404 s needs a

theorem InputAccess404.bounds {s needs a} (reading : InputAccess404 s needs a) :
    Bounds s.core.current.ordinary a :=
  match reading with
  | .authored original => original.bounds
  | .viaOutput _ _ _ proof => proof

/-- Model-free authentic support, distinct from the syntactic access
request. Neither a shape-only ordinary equation nor an unfinished
producer can construct the second case. -/
inductive ReadyInput404 (R : SourcePrimitives) (s : State) (a : Capture) : Type where
  | authored : SourceArgument403 s a → ReadyInput404 R s a
  | output {need : OutputNeed s} (literal : LiteralInputNeed404 s a need)
      (supported : ExactOutputSupport R s need)
      (retained : (⟨a.lower,.nominal literal.key literal.arguments⟩ : Equation) ∈
        s.core.current.ordinary.equations)
      (bounds : Bounds s.core.current.ordinary a) : ReadyInput404 R s a

def recover_original_input404 {R s needs a} (keeps : KeepsFixedOutputs404 R)
    (proof : SupportForest R s needs) (reading : InputAccess404 s needs a) :
    ReadyInput404 R s a :=
  match reading with
  | .authored original => .authored original
  | .viaOutput slot atNeed literal bounds =>
    let support := proof.atOriginal slot atNeed
    .output literal support (completed_input_owns_retained_nominal404 keeps literal support) bounds

/-- Actual original input positions and the complete visible source.
This data precedes both B6 lookup and post-election center ties. -/
structure SupportedChoice404 (s : State) (q : Request) (d : Declaration)
    (needs : List (OutputNeed s)) where
  input : ∀ a ∈ q.demand.arguments, InputAccess404 s needs a
  checked : Checked (authoredRegistry s.core.current)
  covered : ∀ d ∈ visible s.core q, DeclarationCovered s.core.current.environment d
  rowShape : ∀ d ∈ visible s.core q, RepeatedRow403 q d
  sole : visible s.core q = [d]

theorem SupportedChoice404.inScope {s q d needs} (choice : SupportedChoice404 s q d needs) :
    d ∈ visible s.core q := by rw [choice.sole]; exact List.mem_cons_self

def SupportedChoice404.row {s q d needs} (choice : SupportedChoice404 s q d needs) :
    RepeatedRow403 q d :=
  choice.rowShape d choice.inScope

def SupportedCenters404 {s q d needs} (choice : SupportedChoice404 s q d needs) : Prop :=
  ∀ eq ∈ selectedCenterRows403 q choice.row, eq ∈ s.core.current.ordinary.equations

private theorem variable_reads_from_certified_inputs404 (s : State) (capture : Nat → Capture)
    (ns : List Nat) (as : List Capture) (len : ns.length = as.length)
    (bounds : ∀ a ∈ as, Bounds s.core.current.ordinary a)
    (center : ∀ x ∈ ns.zip as,
      GeneralDeclarativeNormalized320.Center s.core.current.ordinary capture x.2 (.variable x.1)) :
    All₂ (DeepHead s.core capture) as (ns.map Pattern.var) := by
  induction ns generalizing as with
  | nil =>
    cases as with
    | nil => exact .nil
    | cons => simp at len
  | cons n ns ih =>
    cases as with
    | nil => simp at len
    | cons a as =>
      refine .cons (.ordinary ⟨bounds a List.mem_cons_self,.variable n,rfl,
        center (n,a) (by simp)⟩) (ih as (Nat.succ.inj len) ?_ ?_)
      · exact fun b seen => bounds b (List.mem_cons_of_mem _ seen)
      · exact fun b seen => center b (List.mem_cons_of_mem _ seen)

theorem retained_centers_support_exact_original404 {s q d needs}
    (choice : SupportedChoice404 s q d needs)
    (retained : SupportedCenters404 choice) {n a}
    (atPos : (n,a) ∈ selectedInputSpans403 q choice.row) :
    GeneralDeclarativeNormalized320.Center s.core.current.ordinary
      (selectedInput403 q choice.row) a (.variable n) := by
  by_cases same : a.center = (selectedInput403 q choice.row n).center
  · apply GeneralDeclarativeNormalized320.Center.direct
    apply GeneralDeclarativeSubstitution320.EquationRead.structural
    apply GeneralDeclarativeHead320.Read.capture
    · change GeneralDeclarativeBounds319.Bound _ a.center (selectedInput403 q choice.row n).center
      rw [same]
      exact .refl _
    · change GeneralDeclarativeBounds319.Bound _ (selectedInput403 q choice.row n).center a.center
      rw [same]
      exact .refl _
  · exact .direct (.whole (retained _ ((binder_center_batch_exact403 choice.row).mpr
      ⟨n,a,atPos,same,rfl⟩)))

def supportedCandidate404 {s q d needs} (choice : SupportedChoice404 s q d needs)
    (retained : SupportedCenters404 choice) : AuthoredCandidate s.core q d :=
  ⟨choice.inScope,choice.covered d choice.inScope,
    (choice.checked.2 d ((visible_exact s.core q d).mp choice.inScope).1).signature,
    .ordered (selectedInput403 q choice.row) (by
      rw [choice.row.literal]
      exact variable_reads_from_certified_inputs404 s _ choice.row.binders q.demand.arguments
        choice.row.sameArity (fun a atArg => (choice.input a atArg).bounds)
        (fun ⟨n,a⟩ atPos => retained_centers_support_exact_original404 choice retained atPos))⟩

def supportedTape404 {s q d needs} (choice : SupportedChoice404 s q d needs)
    (retained : SupportedCenters404 choice) : CandidateTape s.core q (visible s.core q) :=
  choice.sole.symm ▸ .next (.matched (supportedCandidate404 choice retained)) .nil

theorem actual_supported_tape404 {s q d needs} (choice : SupportedChoice404 s q d needs)
    (rawSafe : ¬ RootCycle s q) (retained : SupportedCenters404 choice) :
    TapedMatch s.core q (supportedTape404 choice retained) d := by
  have scan : ∀ rows (eq : rows = [d]),
      let t : CandidateTape s.core q rows := eq.symm ▸ .next
        (.matched (supportedCandidate404 choice retained)) .nil
      t.waits = false ∧ t.live = [d] := by
    intro rows eq
    subst rows
    exact ⟨rfl,rfl⟩
  exact ⟨rawSafe,(scan _ choice.sole).1,(scan _ choice.sole).2⟩

def supportedFrame404 {s q d needs} {choice : SupportedChoice404 s q d needs}
    {retained : SupportedCenters404 choice}
    (origin : SelectedHeadOrigin395 (row := d) (supportedTape404 choice retained)) :
    AuthoredBodyFrame393 s.core q :=
  preoutputFrameOfOrigin399 origin unusedPlacement403 (fun _ => emptyCapture403)

structure SupportedEvent404 {s q} (needs : List (OutputNeed s)) (e : Event s q) where
  choice : SupportedChoice404 s q e.frame.decl needs
  retained : SupportedCenters404 choice
  origin : SelectedHeadOrigin395 (row := e.frame.decl) (supportedTape404 choice retained)
  frame : e.frame = supportedFrame404 origin
  head : e.head = origin.pick.head
  sourceClauses : LiteralVariableWhere403 e.frame.decl

end Yulang.GeneralDeclarativeI65.I72
