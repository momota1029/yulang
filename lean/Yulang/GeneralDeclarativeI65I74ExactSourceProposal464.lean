import Yulang.GeneralDeclarativeI65I74NamedProjection464

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.NamedProjection464
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)
open GeneralDeclarativeK2Graph321.AddAtOneSource
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeGraphRows321 (shapeOf observed structural)
open GeneralDeclarativeK2Graph321 (Path)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeLowerKnown321 (Alias)
open Derivation (EqWire checkEq exact_finite_data_eq_check_iff_independent_Derives453)

private abbrev RawState := GeneralDeclarativeHead320.State

/-- Constructor frames of a selected closed-pattern occurrence. These are
syntax equality frames, not raw graph permission or mode validation. In
particular they never descend through a join or an open record tail. -/
inductive SelectedFrame where
  | recordPayload (label : Nat) (tail : Expr)
  | variantPayload (tag : Nat)
  | pairFirst (right : Expr)
  | pairSecond (left : Expr)
  | unaryNominal (key : Nat)

def plugOne : SelectedFrame → Expr → Expr
  | .recordPayload label tail, x => .record label x tail
  | .variantPayload tag, x => .variant tag x
  | .pairFirst y, x => .primitive .pair [x,y]
  | .pairSecond y, x => .primitive .pair [y,x]
  | .unaryNominal key, x => .nominal key [x]

def plugFrames : List SelectedFrame → Expr → Expr
  | [], x => x
  | c::cs,x => plugOne c (plugFrames cs x)

theorem derive_at_selected_frame {s : RawState} {u v : Expr}
    (f : SelectedFrame) (step : Derives s u v) :
    Derives s (plugOne f u) (plugOne f v) := by
  cases f with
  | recordPayload => exact .record step (.refl _)
  | variantPayload => exact .variant step
  | pairFirst => exact .primitive (.cons step (.cons (.refl _) .nil))
  | pairSecond => exact .primitive (.cons (.refl _) (.cons step .nil))
  | unaryNominal => exact .nominal (.cons step .nil)

theorem every_finite_selected_context_preserves_ordinary_derivation
    {s : RawState} {u v : Expr} (ctx : List SelectedFrame) (step : Derives s u v) :
    Derives s (plugFrames ctx u) (plugFrames ctx v) := by
  induction ctx with
  | nil => exact step
  | cons c cs ih => exact derive_at_selected_frame c ih

structure SourceRowSelection where
  ownerOrdinal : Nat
  payloadOrdinal : Nat
  frames : List SelectedFrame

/-- A proposal reads two old physical equation ordinals. It never picks a new
slot, reads unregistered origins, rewrites the graph, or asserts that a
shape can be visited. The optional proposal only records source text. -/
def readSourceProposal (s : RawState) (w : SourceRowSelection) : Option Equation := do
  let parent ← s.equations[w.ownerOrdinal]?
  let payload ← s.equations[w.payloadOrdinal]?
  if eqExpr parent.right (plugFrames w.frames payload.right) then
    some ⟨parent.left,plugFrames w.frames (.variable payload.left)⟩
  else none

def ExactSourceProposal (s : RawState) (w : SourceRowSelection) (out : Equation) : Prop :=
  ∃ parent payload, s.equations[w.ownerOrdinal]? = some parent ∧
    s.equations[w.payloadOrdinal]? = some payload ∧
    parent.right = plugFrames w.frames payload.right ∧
    out = ⟨parent.left,plugFrames w.frames (.variable payload.left)⟩

theorem checked_proposal_is_exact_original_syntax_and_ordinals
    (s : RawState) (w : SourceRowSelection) (e : Equation) :
    readSourceProposal s w = some e ↔ ExactSourceProposal s w e := by
  constructor
  · intro found
    cases hp : s.equations[w.ownerOrdinal]? with
    | none => simp [readSourceProposal,hp,Option.bind] at found
    | some parent =>
      cases hc : s.equations[w.payloadOrdinal]? with
      | none => simp [readSourceProposal,hp,hc,Option.bind] at found
      | some payload =>
        by_cases eq : parent.right = plugFrames w.frames payload.right
        · have out : (⟨parent.left,plugFrames w.frames (.variable payload.left)⟩ : Equation) = e := by
            simpa [readSourceProposal,hp,hc,(eq_expr ..).mpr eq,Option.bind] using found
          exact ⟨parent,payload,hp,hc,eq,out.symm⟩
        · have fail : eqExpr parent.right (plugFrames w.frames payload.right) = false := by
            cases h : eqExpr parent.right (plugFrames w.frames payload.right)
            · rfl
            · exact (eq ((eq_expr ..).mp h)).elim
          simp [readSourceProposal,hp,hc,fail,Option.bind] at found
  · rintro ⟨parent,payload,hp,hc,same,rfl⟩
    simp [readSourceProposal,hp,hc,(eq_expr ..).mpr same,Option.bind]

theorem exact_literal_source_proposal_has_an_old_derivation
    {s : RawState} {w : SourceRowSelection} {out : Equation}
    (authored : ExactSourceProposal s w out) : Derives s (.variable out.left) out.right := by
  obtain ⟨parent,payload,seen,child,literal,rfl⟩ := authored
  have oldOwner : Derives s (.variable parent.left) parent.right :=
    .row (List.mem_of_getElem? seen)
  have oldChild : Derives s (.variable payload.left) payload.right :=
    .row (List.mem_of_getElem? child)
  rw [literal] at oldOwner
  exact .trans oldOwner (every_finite_selected_context_preserves_ordinary_derivation _ (.symm oldChild))

theorem proposal_has_finite_original_equational_proof
    {s : RawState} {w : SourceRowSelection} {out : Equation}
    (found : readSourceProposal s w = some out) :
    ∃ d, checkEq s (.variable out.left) out.right d = true :=
  (exact_finite_data_eq_check_iff_independent_Derives453 ..).mpr
    (exact_literal_source_proposal_has_an_old_derivation
      ((checked_proposal_is_exact_original_syntax_and_ordinals ..).mp found))

/-- Separately supplying a successful cut specifies a conservative named
projection. This still does not issue native origin/route tokens, nor choose
which old source occurrence or physical child is authorised for G04. -/
theorem actual_source_proposal_and_safe_cut_give_exact_scoped_projection
    {s : RawState} {w : SourceRowSelection} {out : Equation}
    (found : readSourceProposal s w = some out)
    {cut : Yulang.GeneralDeclarativeI65.I72.List410.ExactEscapeWire}
    (safe : checksNamedProjectionCut s out.left out.right cut = true) :
    ProjectionAt s (extendedRows s out) out.left := by
  have derived := exact_literal_source_proposal_has_an_old_derivation
    ((checked_proposal_is_exact_original_syntax_and_ordinals ..).mp found)
  cases f : shapeOf out.right with
  | none => simp [checksNamedProjectionCut,f] at safe
  | some h =>
    obtain ⟨old,cutShape⟩ := (original_projection_cut_has_finite_wire_exactly_when_safe f).mp ⟨cut,safe⟩
    rcases out with ⟨site,expr⟩
    exact ⟨expr,h,rfl,f,derived,old,cutShape⟩


open Derivation (readEq readArgs)
open GeneralDeclarativeWitnessEquation349 (Checked replay)

/-- Construct data, not a Prop witness by choice: every constructor frame
has one ordinary equality constructor, and the unchanged siblings use refl. -/
def frameData : SelectedFrame → EqWire → EqWire
  | .recordPayload label tail, q => .record label q (.old (.refl tail))
  | .variantPayload tag, q => .variant tag q
  | .pairFirst right, q => .primitive .pair (.cons q (.cons (.old (.refl right)) .nil))
  | .pairSecond left, q => .primitive .pair (.cons (.old (.refl left)) (.cons q .nil))
  | .unaryNominal key, q => .nominal key (.cons q .nil)

def framesData : List SelectedFrame → EqWire → EqWire
  | [], q => q
  | c::cs, q => frameData c (framesData cs q)

theorem data_for_one_frame_replays_the_same_two_subterms {s : RawState} {w : EqWire}
    (f : SelectedFrame) {eq : Checked s} (checked : readEq s w = some eq) :
    readEq s (frameData f w) =
      some ⟨plugOne f eq.left,plugOne f eq.right,derive_at_selected_frame f eq.derivation⟩ := by
  cases f <;> simp [frameData,plugOne,readEq,readArgs,checked,replay,Bind.bind,Option.bind]

theorem data_for_every_finite_frame_list_replays_exactly {s : RawState} {w : EqWire}
    (fs : List SelectedFrame) {eq : Checked s} (checked : readEq s w = some eq) :
    readEq s (framesData fs w) =
      some ⟨plugFrames fs eq.left,plugFrames fs eq.right,
        every_finite_selected_context_preserves_ordinary_derivation fs eq.derivation⟩ := by
  induction fs with
  | nil => exact checked
  | cons c cs ih => exact data_for_one_frame_replays_the_same_two_subterms _ ih

private theorem ordinary_replay_reads_the_exact_old_slot {s : RawState} {i : Nat} {e : Equation}
    (hit : s.equations[i]? = some e) :
    replay s (.currentRow i) = some ⟨.variable e.left,e.right,.row (List.mem_of_getElem? hit)⟩ := by
  simp only [replay]
  split
  · rename_i none
    rw [hit] at none
    cases none
  · rename_i out found
    cases Option.some.inj (found.symm.trans hit)
    rfl

def literalSourceProofData (w : SourceRowSelection) : EqWire :=
  .compose (.old (.currentRow w.ownerOrdinal))
    (framesData w.frames (.reverse (.old (.currentRow w.payloadOrdinal))))

/-- The algorithm emits a specific finite source proof for the exact two old
ordinal reads. No existential witness selection and no candidate election. -/
theorem source_proposal_emits_its_exact_finite_ordinary_proof
    {s : RawState} {w : SourceRowSelection} {out : Equation}
    (found : readSourceProposal s w = some out) :
    checkEq s (.variable out.left) out.right (literalSourceProofData w) = true := by
  obtain ⟨parent,payload,hp,hc,source,rfl⟩ :=
    (checked_proposal_is_exact_original_syntax_and_ordinals ..).mp found
  have oldChild : readEq s (.reverse (.old (.currentRow w.payloadOrdinal))) =
      some ⟨payload.right,.variable payload.left,.symm (.row (List.mem_of_getElem? hc))⟩ := by
    simp [readEq,ordinary_replay_reads_the_exact_old_slot hc]
  have placed := data_for_every_finite_frame_list_replays_exactly w.frames oldChild
  have middle : eqExpr parent.right (plugFrames w.frames payload.right) = true := (eq_expr ..).mpr source
  have left : eqExpr (.variable parent.left) (.variable parent.left) = true := (eq_expr ..).mpr rfl
  have right : eqExpr (plugFrames w.frames (.variable payload.left))
      (plugFrames w.frames (.variable payload.left)) = true := (eq_expr ..).mpr rfl
  simp [literalSourceProofData,checkEq,readEq,ordinary_replay_reads_the_exact_old_slot hp,
    placed,middle,left,right,Bind.bind,Option.bind]

end Yulang.GeneralDeclarativeI65.I72.NamedProjection464
