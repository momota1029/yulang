import Yulang.GeneralDeclarativeI65I75ProjectedCoreOutput425

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDeclarativeI65.ProjectedCore425
open Core.PresenceGeneration (TyTerm)
open PresenceNormalForm (Atom)
open CommonNominalFullCarrier (Ty Subtype Equivalent record)
open GeneralDeclarativeRecordChannel330 (project)
open GeneralDeclarativeRecordIntervals330 (direct projected_below)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)
open GeneralDeclarativeHead320 (Equation)

def retentionFieldShape426 (label field : Nat) : TyTerm Nat :=
  .record label (.var field) .exactEmpty

def retentionLower426 (label field center : Nat) : Atom Nat :=
  .tyLe (.inter (retentionFieldShape426 label field) .exactEmpty) (.var center)

def retentionUpper426 (label field center : Nat) : Atom Nat :=
  .tyLe (.var center) (retentionFieldShape426 label field)

/-- Required-only retention is indexed by the exact low, original B6
output (including State, atlas, request, and ordinal). It depends on
three existing ordinary rows in that State, not an I72 proof,
checker verdict, submitted model value, or new logical slot. -/
structure RequiredRetention426 {s atlas q i} (o : Output s atlas q i) where
  field : Nat
  targetOrdinal : Nat
  lowerOrdinal : Nat
  upperOrdinal : Nat
  targetFound : s.current.ordinary.equations[targetOrdinal]? =
    some ⟨q.demand.outputs[i].target,.variable field⟩
  lowerFound : s.current.ordinary.normal.ordinary[lowerOrdinal]? =
    some (retentionLower426 o.label field o.arg.center)
  upperFound : s.current.ordinary.normal.ordinary[upperOrdinal]? =
    some (retentionUpper426 o.label field o.arg.center)

structure RequiredRows426 where
  targetOrdinal : Nat
  lowerOrdinal : Nat
  upperOrdinal : Nat

/-- Only checks the provided addresses against unchanged actual rows. -/
def readRequiredRetention426 {s atlas q i} (o : Output s atlas q i) (w : RequiredRows426) :
    Option (RequiredRetention426 o) := do
  let st := s.current.ordinary
  match found : st.equations[w.targetOrdinal]? with
  | some ⟨target,.variable field⟩ =>
    if same : target = q.demand.outputs[i].target then
      if lo : st.normal.ordinary[w.lowerOrdinal]? =
          some (retentionLower426 o.label field o.arg.center) then
        if up : st.normal.ordinary[w.upperOrdinal]? =
            some (retentionUpper426 o.label field o.arg.center) then
          pure ⟨field,w.targetOrdinal,w.lowerOrdinal,w.upperOrdinal,
            by simpa only [same] using found,lo,up⟩
        else none
      else none
    else none
  | _ => none

/-- The exact three addressed rows are sufficient for readback;
the returned certificate is this one by proof irrelevance, not
because different retained address data may be identified. -/
theorem exact_required_rows_are_read426 {s atlas q i} {o : Output s atlas q i}
    (retained : RequiredRetention426 o) :
    readRequiredRetention426 o
      ⟨retained.targetOrdinal,retained.lowerOrdinal,retained.upperOrdinal⟩ = some retained := by
  rcases retained with ⟨field,target,lo,up,atTarget,atLo,atUp⟩
  unfold readRequiredRetention426
  dsimp only
  split
  next lhs f hit =>
    rw [atTarget] at hit
    cases Option.some.inj hit
    simp [atLo,atUp]
  next wrong => exact (wrong _ _ atTarget).elim

private theorem retention_lower_projects_required426 (label : Nat) (v : Ty) :
    project label false [] (.inter (record label v .exactEmpty) .exactEmpty) = some v := by
  simp [project,direct,GeneralDeclarativeOpaqueChannel328.meet]

/-- The very same fitting model yields both endpoint channels and mask,
the literal original B6 output, and its required-only fixed target.
No optional-projection equality is used. -/
theorem original_core_and_required_rows_produce_same_model_meaning426 {s atlas q i}
    (o : Output s atlas q i) (keep : RequiredRetention426 o) (m : Model) (fit : Fits s m) :
    EndpointHead423.Meaning o.head m ∧
      ∃ v : Ty, project o.label false [] (m.assignment o.arg.center).1 = some v ∧
        o.valueAt m = some (q.occurrence,o.ordinal,i.val,q.demand.outputs[i].target,v) ∧
        Equivalent (m.assignment q.demand.outputs[i].target).1 v := by
  obtain ⟨head,v,projected,meaning⟩ :=
    projected_core_original_B6_uses_actual_required_field425 o m fit
  have lo := fit.1.1.1.1 _ (List.mem_of_getElem? keep.lowerFound)
  have hi := fit.1.1.1.1 _ (List.mem_of_getElem? keep.upperFound)
  change Subtype (.inter (record o.label (m.assignment keep.field).1 .exactEmpty) .exactEmpty)
    (m.assignment o.arg.center).1 at lo
  change Subtype (m.assignment o.arg.center).1
    (record o.label (m.assignment keep.field).1 .exactEmpty) at hi
  have targetEq : Equivalent (m.assignment q.demand.outputs[i].target).1
      (m.assignment keep.field).1 := fit.1.1.2 _ (List.mem_of_getElem? keep.targetFound)
  exact ⟨head,v,projected,meaning,eqv_trans targetEq
    ⟨projected_below o.label false (retention_lower_projects_required426 ..) projected lo,
     projected_below o.label false projected (direct ..) hi⟩⟩

end Yulang.GeneralDeclarativeI65.ProjectedCore425
