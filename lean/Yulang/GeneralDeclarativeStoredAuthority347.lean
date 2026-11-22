import Yulang.GeneralDeclarativeObservedRecordPair347

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStoredAuthority347
open GeneralNominalState (State)
open GeneralDictionaryBinderLocations (sourceSlot sourceSlot_exact)
open GeneralSourceState (equationAtoms)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeOrigins321 (Origin)
open GeneralDeclarativeObservedSupport347 (Record)
open GeneralDeclarativeObservedSyntax347 (rawHead)
open GeneralDeclarativeStoppedStructural339 (encode)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open Core.PresenceGeneration (TyTerm)

/-- The source authority below comes from a designated input's own
literal ordinary equalities and recorded syntax. It is not derived
from the fact that a final assignment happens to satisfy a head.
Use it only for the caller's verified original source state. -/
structure Author (raw : State) (row : Equation) : Prop where
  written : ∃ (i : Fin raw.base.slots) (t : TyTerm (Fin raw.base.slots)),
    raw.base.source i = row.left ∧ (raw.base.heads i).equation = some t ∧
    encode raw.base t = some row.right ∧ equationAtoms i t ⊆ raw.base.ordinary

def admits (input : State) (row : Equation) (origin : Origin) : Prop :=
  origin = .source ∧ Author input row

theorem exact_author {input : State} {row : Equation} (authored : Author input row) :
    rawHead input row.left = some row := by
  obtain ⟨i,t,name,head,print,_⟩ := authored.written
  have place := (sourceSlot_exact input.base row.left i).mpr name
  unfold rawHead
  rw [place]
  change (do let y ← (input.base.heads i).equation; let e ← encode input.base y; pure (Equation.mk row.left e)) = _
  rw [head]
  change (do let e ← encode input.base t; pure (Equation.mk row.left e)) = _
  rw [print]
  cases row
  rfl

theorem same_input {input : State} {row : Equation} (authored : Author input row) :
    Record input (admits input) row .source :=
  ⟨.rawHead (exact_author authored),rfl,authored⟩

theorem current_reobservation {input live : State} {row : Equation}
    (authored : Author input row) (observed : GeneralDeclarativeObservedSyntax347.Appears live row) :
    Record live (admits input) row .source :=
  ⟨observed,rfl,authored⟩

end Yulang.GeneralDeclarativeStoredAuthority347
