import Yulang.GeneralDeclarativeI65I74RepeatedCentersSource421

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RepeatedCenters421
open GeneralDeclarativeI65
open Checker408 (Problem)
open GeneralDeclarativeHead320 (Equation Models environment)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)
open CommonNominalFullCarrier (Ty Equivalent Subtype variant subtype_trans)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans variant_congr)
open GeneralDeclarativeEntailment320 (appendFacts model_append)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)

inductive Color where
  | integer | boolean
  deriving DecidableEq

def Color.base : Color → Inference.Base
  | .integer => .int
  | .boolean => .bool

def colorExpr (x : Color) : Expr := .primitive (.scalar x.base) []

def eqRow (a b : Equation) : Bool := (a.left == b.left) && eqExpr a.right b.right

theorem eq_row421 (a b : Equation) : eqRow a b = true ↔ a = b := by
  cases a
  cases b
  simp only [eqRow,Bool.and_eq_true,beq_iff_eq,eq_expr,Equation.mk.injEq]

def retainedAt (s : GeneralDeclarativeHead320.State) (i : Nat) (e : Equation) :
    Option (PLift (s.equations[i]? = some e)) :=
  match s.equations[i]? with
  | none => none
  | some row =>
    if same : eqRow row e = true then some ⟨congrArg some ((eq_row421 _ _).mp same)⟩ else none

def Color.read : Inference.Base → Option Color
  | .int => some .integer
  | .bool => some .boolean
  | _ => none

theorem read_color_exact421 {b c} (h : Color.read b = some c) : c.base = b := by
  cases b <;> cases c <;> simp_all [Color.read,Color.base]

structure CenterWitness (s : GeneralDeclarativeHead320.State) (slot tag : Nat) where
  child : Nat
  color : Color
  atCenter : variantRow slot tag child ∈ s.equations
  atPayload : (⟨child,colorExpr color⟩ : Equation) ∈ s.equations

structure CenterWire where
  shape : Nat
  scalar : Nat

def readCenter (s : GeneralDeclarativeHead320.State) (slot tag : Nat) (w : CenterWire) :
    Option (CenterWitness s slot tag) := do
  match center : s.equations[w.shape]? with
  | some ⟨n,.variant l (.variable u)⟩ =>
    if found : n = slot ∧ l = tag then
      match payload : s.equations[w.scalar]? with
      | some ⟨v,.primitive (.scalar base) []⟩ =>
        if atPayload : v = u then
          match typed : Color.read base with
          | none => none
          | some color =>
            have C : s.equations[w.shape]? = some (variantRow slot tag u) := by
              simpa only [found.1,found.2,variantRow] using center
            have P : s.equations[w.scalar]? = some ⟨u,colorExpr color⟩ := by
              simpa only [atPayload,colorExpr,read_color_exact421 typed] using payload
            pure ⟨u,color,List.mem_of_getElem? C,List.mem_of_getElem? P⟩
        else none
      | _ => none
    else none
  | _ => none

theorem original_center_type_in_same_model421 {s slot tag}
    (a : CenterWitness s slot tag) (m : I72.Model) (fit : Models s m.assignment) :
    Equivalent (m.assignment slot).1 (variant tag (.base a.color.base)) := by
  have head := fit.2 _ a.atCenter
  have payload := fit.2 _ a.atPayload
  change Equivalent (m.assignment slot).1 (variant tag (m.assignment a.child).1) at head
  change Equivalent (m.assignment a.child).1 (.base a.color.base) at payload
  exact eqv_trans head (variant_congr tag payload)

theorem distinct_scalars_in_same_tick_cannot_be_subtypes421 {tag a b}
    (different : a ≠ b) : ¬ Subtype (variant tag (.base a)) (variant tag (.base b)) := by
  intro relation
  have atDepth := relation 1
  change CommonNominalFullDemand.ProducerLe Common.rowLe
    (.variant tag (.base a)) (.variant tag (.base b)) at atDepth
  have scalar := (CommonNominalFullDemand.producerLe_variant_iff tag (.base a) (.base b)).mp atDepth
  let env : CommonNominalFullDemand.Environment Common.Row := ⟨fun _ => .bottom,fun _ => [.base b]⟩
  have yes : CommonNominalFullDemand.ProbeAt Common.rowLe 0 env (.base b) (.role 0) := by
    simp [CommonNominalFullDemand.ProbeAt,CommonNominalFullDemand.ProbeStep,
      CommonNominalFullDemand.MaskedProbeStep,env]
  have no := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp scalar 0 env (.role 0) yes
  simp [CommonNominalFullDemand.ProbeAt,CommonNominalFullDemand.ProbeStep,
    CommonNominalFullDemand.MaskedProbeStep,env,different] at no

theorem different_colors421 {a b : Color} (h : a ≠ b) : a.base ≠ b.base := by
  cases a <;> cases b <;> simp_all [Color.base]

def noTie (s : GeneralDeclarativeHead320.State) (tie : Equation) : Bool :=
  !(s.equations.any fun row => eqRow row tie)

theorem no_tie_exact421 {s e} (absent : noTie s e = true) : e ∉ s.equations := by
  intro here
  have present : (s.equations.any fun row => eqRow row e) = true :=
    List.any_eq_true.mpr ⟨e,here,(eq_row421 _ _).mpr rfl⟩
  simp [noTie,present] at absent

structure Compared {p : Problem} (a : Choice p) where
  apart : a.second.center ≠ a.first.center
  firstCenter : CenterWitness p.state.core.current.ordinary a.first.center a.lowerFirst.tag
  secondCenter : CenterWitness p.state.core.current.ordinary a.second.center a.lowerFirst.tag

structure Accepted {p : Problem} (a : Choice p) where
  read : Compared a
  sameType : read.firstCenter.color = read.secondCenter.color
  retained : a.tie ∈ p.state.core.current.ordinary.equations

structure Conflict {p : Problem} (a : Choice p) where
  read : Compared a
  different : read.firstCenter.color ≠ read.secondCenter.color
  absent : a.tie ∉ p.state.core.current.ordinary.equations

/-- The preselected request is checked against its actual centers. No
assignment of this same state can survive appending the exact tie. -/
theorem actual_conflict_makes_selected_batch_unsatisfiable421 {p} {a : Choice p}
    (bad : Conflict a) (m : I72.Model) :
    ¬ Models (appendFacts p.state.core.current.ordinary [a.tie]) m.assignment := by
  intro appended
  obtain ⟨before,kept⟩ := (model_append m.assignment).mp appended
  have left := original_center_type_in_same_model421 bad.read.firstCenter m before
  have right := original_center_type_in_same_model421 bad.read.secondCenter m before
  have eq := kept _ List.mem_cons_self
  change Equivalent (m.assignment a.second.center).1 (m.assignment a.first.center).1 at eq
  exact distinct_scalars_in_same_tick_cannot_be_subtypes421 (different_colors421 bad.different)
    (subtype_trans left.2 (subtype_trans eq.2 right.1))

def Choice.capture {p} (a : Choice p) (binder : Nat) :=
  if binder = a.binder then a.first else emptyCapture403

def tied_selected_head_uses_the_actual_first_capture421 {p} {a : Choice p}
    (accepted : Accepted a) : SourceHead p.state.core p.root a.decl := by
  have code : GeneralNominalCenteredHeadMatExpressions.translate
      (authoredRegistry p.state.core.current).constructors
      (GeneralSourceMetadataRows291.interpretation p.state.core.current.environment.source.snapshot)
      (.var a.binder) = some (.variable a.binder) := rfl
  refine .ordered a.capture ?_
  rw [a.originalArgs,a.literal]
  apply CommonRoleOutermostResolver.All₂.cons
  · refine .ordinary ⟨a.firstRange,_,code,.direct (.structural (.capture ?_ ?_))⟩
    · simpa [Choice.capture,GeneralDeclarativeHead320.byMode] using
        GeneralDeclarativeBounds319.Bound.refl (s := p.state.core.current.ordinary.normal) a.first.center
    · simpa [Choice.capture,GeneralDeclarativeHead320.byMode] using
        GeneralDeclarativeBounds319.Bound.refl (s := p.state.core.current.ordinary.normal) a.first.center
  · refine .cons (.ordinary ⟨a.secondRange,_,code,.direct (.whole ?_)⟩) .nil
    simpa [Choice.capture,Choice.tie,GeneralDeclarativeSubstitution320.logical,GeneralDeclarativeHead320.byMode] using accepted.retained

def Choice.frame {p} (a : Choice p) : AuthoredBodyFrame393 p.state.core p.root :=
  ⟨a.ordinal,a.decl,a.authored,by simp [a.only],unusedPlacement403,a.capture⟩

def acceptedEvent {p} {a : Choice p} (b : Accepted a) : Event p.state p.root :=
  ⟨a.frame,tied_selected_head_uses_the_actual_first_capture421 b,fun i =>
    False.elim (by have h := i.isLt; simp [a.noOutputs] at h)⟩

theorem acceptedEvent_has_no_where421 {p} {a : Choice p} (b : Accepted a) :
    (acceptedEvent b).kids = [] := by
  simp [acceptedEvent,Choice.frame,Event.kids,frameWhereKids400,
    AuthoredBodyFrame393.clauses,children,a.noWhere]

inductive Outcome {p : Problem} (a : Choice p) where
  | accepted : Accepted a → Outcome a
  | incompatible : Conflict a → Outcome a

structure PostWire where
  first : CenterWire
  second : CenterWire
  tieRow : Nat

def readAfterChoice421 {p} (a : Choice p) (w : PostWire) : Option (Outcome a) := do
  if apart : a.second.center ≠ a.first.center then
    let ordinary := p.state.core.current.ordinary
    let first ← readCenter ordinary a.first.center a.lowerFirst.tag w.first
    let second ← readCenter ordinary a.second.center a.lowerFirst.tag w.second
    let observed : Compared a := ⟨apart,first,second⟩
    if same : first.color = second.color then
      let kept ← retainedAt ordinary w.tieRow a.tie
      pure (.accepted ⟨observed,same,List.mem_of_getElem? kept.down⟩)
    else if missing : noTie ordinary a.tie = true then
      pure (.incompatible ⟨observed,same,no_tie_exact421 missing⟩)
    else none
  else none

end Yulang.GeneralDeclarativeI65.I72.RepeatedCenters421
