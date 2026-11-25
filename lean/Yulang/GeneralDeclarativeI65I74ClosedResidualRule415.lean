import Yulang.GeneralDeclarativeI65I74ClosedResidualEvents415

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ClosedResidual415
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (All₂ Dictionary Summarizes Result)

inductive ResidualElection (s : I72.State) : (q : I72.Request) → Event s q → Type where
  | parent {q : I72.Request} (rows : ClosedRows s q) (p : ClosedParent rows) :
      ResidualElection s q p.event
  | leaf {parent : I72.Request} (rows : ClosedRows s parent) (p : ClosedParent rows)
      (c : ClosedChild p) : ResidualElection s (query415 parent p.childRole rows.residual) c.event

def residualLocal415 : SourcePrimitives where
  elected := fun s q event needs => needs = [] ∧ Nonempty (ResidualElection s q event)
  other := fun _ _ _ _ => False

def R7 : SourcePrimitives where
  elected := fun s q e needs => OpenTail414.R6.elected s q e needs ∨ residualLocal415.elected s q e needs
  other := OpenTail414.R6.other

theorem selected_residual_local_sound415 {s q e needs}
    (sound : R7.elected s q e needs) (m : I72.Model) (fit : Fits s m) :
    LocalMeaning m e ∧ FixedTargets m e := by
  rcases sound with old|new
  · have prev := WhereCycle411.R3_local_evidence411 s q e needs old
    exact ⟨semantic_node_in_signature s q e prev.1 m fit,
      prev.2.elim (fun a => retained_variable_targets_sound403 a m fit)
        (fun a => retained_typed_rows_satisfy_fixed_targets403 a m fit)⟩
  · obtain ⟨data⟩ := new.2
    cases data with
    | parent rows read =>
      refine ⟨⟨source_head_sound read.event.head m fit,?_⟩,?_⟩ <;>
        (intro i; have bound := i.isLt; simp [rows.noOutputs] at bound)
    | leaf rows read child =>
      refine ⟨⟨source_head_sound child.event.head m fit,?_⟩,?_⟩ <;>
        (intro i; exact Fin.elim0 i)

/-- Soundness uses the fixed same-state DictionaryEvidence constructor
on the actual ordered where forest. No blanket arbitrary-substitution
descent test is used for a record with a concrete computed remainder. -/
theorem selected_trace_is_dictionary_sound415 {s q t e} (trace : SourceTrace R7 s q t e)
    (m : I72.Model) (fit : Fits s m) :
    ∀ d, Summarizes t (.selected d) → DictionaryEvidence s m q d := by
  exact SourceTrace.rec (R := R7) (s := s)
    (motive_1 := fun q t _ _ => ∀ d, Summarizes t (.selected d) → DictionaryEvidence s m q d)
    (motive_2 := fun qs ts _ => ∀ ds, All₂ Summarizes ts (ds.map Result.selected) →
      DictionaryEvidenceForest s m qs ds)
    (motive_3 := fun _ _ => True)
    (fun _ _ evidence => by cases evidence)
    (fun v _ _ _ _ _ evidence => by cases v <;> cases evidence)
    (fun event _ decision _ _ _ proveKids d actual => by
      have semantics := selected_residual_local_sound415 decision m fit
      cases actual with
      | selected ordered combine =>
        cases combine with
        | selected exactEach =>
          rw [exactEach] at ordered
          exact .node event semantics.1 semantics.2 (proveKids _ ordered))
    (fun ds pair => by
      cases ds with
      | nil => exact .nil
      | cons => cases pair)
    (fun _ _ first rest ds ordered => by
      cases ds with
      | nil => cases ordered
      | cons d ds =>
        cases ordered with
        | cons head tail => exact .cons (first d head) (rest ds tail))
    True.intro (fun _ _ _ _ _ _ => True.intro) trace

theorem dictionary_sound_R7 : DictionarySound R7 := by
  rintro s q d ⟨t,e,⟨trace⟩,result⟩ m fit
  exact selected_trace_is_dictionary_sound415 trace m fit d result

end Yulang.GeneralDeclarativeI65.I72.ClosedResidual415
