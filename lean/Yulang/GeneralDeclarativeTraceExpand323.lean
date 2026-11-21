import Yulang.GeneralDeclarativeTermOccurrences322
import Yulang.GeneralDeclarativeTrace321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeTraceExpand323
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeTrace321 (Trace TraceArgs)
open GeneralDeclarativeTermWalk322 (Occurrence Walk WalkMany)
open GeneralDeclarativeEqualities322 (Derives Forest)
open GeneralNominalCenteredHeadMatExpressions (Expr)

def convert (o : GeneralDeclarativeTrace321.Occurrence) : Occurrence :=
  ⟨o.binder,o.mode,.variable o.argument⟩

/-- Ordinary expansion of a finite actual source trace. Every capture
retains the logical name found at that position before sharing occurs.
No global substitution or compiler output is needed to justify this
independent observation. -/
theorem expands {s : State} (read : Trace s mode name code raw) :
    ∃ term, Derives s (.variable name) term ∧ Walk mode term code (raw.map convert) :=
  Trace.rec
    (motive_1 := fun mode name code raw _ =>
      ∃ term, Derives s (.variable name) term ∧ Walk mode term code (raw.map convert))
    (motive_2 := fun mode names code raw _ =>
      ∃ terms, Forest s (names.map Expr.variable) terms ∧ WalkMany mode terms code (raw.map convert))
    (by intro _ n _; exact ⟨.variable n,.refl _,.capture⟩)
    (by
      intro _ _ tag _ _ _ _ alias stored _ ih
      obtain ⟨terms,observed,walk⟩ := ih
      exact ⟨.primitive tag terms,
        .trans (.congruent (.variable alias)) (.trans (.row stored) (.primitive observed)),
        .primitive walk⟩)
    (by
      intro _ _ tag _ _ _ _ alias stored _ ih
      obtain ⟨terms,observed,walk⟩ := ih
      exact ⟨.nominal tag terms,
        .trans (.congruent (.variable alias)) (.trans (.row stored) (.nominal observed)),
        .nominal walk⟩)
    (by
      intro _ _ label _ _ _ _ _ _ _ alias stored _ _ ih jh
      obtain ⟨a,left,walk1⟩ := ih
      obtain ⟨b,right,walk2⟩ := jh
      exact ⟨.record label a b,
        .trans (.congruent (.variable alias)) (.trans (.row stored) (.record left right)),
        by simpa only [List.map_append] using Walk.record walk1 walk2⟩)
    (by
      intro _ _ tag _ _ _ _ alias stored _ ih
      obtain ⟨term,shown,walk⟩ := ih
      exact ⟨.variant tag term,
        .trans (.congruent (.variable alias)) (.trans (.row stored) (.variant shown)),
        .variant walk⟩)
    (by
      intro _ _ _ _ _ _ _ _ _ alias stored _ _ ih jh
      obtain ⟨a,left,walk1⟩ := ih
      obtain ⟨b,right,walk2⟩ := jh
      exact ⟨.join a b,
        .trans (.congruent (.variable alias)) (.trans (.row stored) (.join left right)),
        by simpa only [List.map_append] using Walk.join walk1 walk2⟩)
    (by intro _; exact ⟨[],.nil,.nil⟩)
    (by
      intro _ _ _ _ _ _ _ _ _ ih jh
      obtain ⟨term,one,walk⟩ := ih
      obtain ⟨terms,two,walks⟩ := jh
      exact ⟨term::terms,.cons one two,by simpa only [List.map_append] using WalkMany.cons walk walks⟩)
    read

end Yulang.GeneralDeclarativeTraceExpand323
