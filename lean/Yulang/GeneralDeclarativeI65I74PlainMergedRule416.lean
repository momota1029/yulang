import Yulang.GeneralDeclarativeI65I74PlainMergedEvents416

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.PlainMerged416
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (All₂ Dictionary Summarizes Result)

inductive PlainElection (s : I72.State) : (q : I72.Request) → Event s q → Type where
  | actual {q : I72.Request} (rows : PlainRows s q) (r : PlainRead rows) :
      PlainElection s q r.event

def plainLocal416 : SourcePrimitives where
  elected := fun s q event needs => needs = [] ∧ Nonempty (PlainElection s q event)
  other := fun _ _ _ _ => False

def R8 : SourcePrimitives where
  elected := fun s q e needs => ClosedResidual415.R7.elected s q e needs ∨ plainLocal416.elected s q e needs
  other := ClosedResidual415.R7.other

theorem selected_plain_local_sound416 {s q e needs}
    (sound : R8.elected s q e needs) (m : I72.Model) (fit : Fits s m) :
    LocalMeaning m e ∧ FixedTargets m e := by
  rcases sound with old|new
  · exact ClosedResidual415.selected_residual_local_sound415 old m fit
  · obtain ⟨data⟩ := new.2
    cases data with
    | actual rows r =>
      refine ⟨⟨source_head_sound r.event.head m fit,?_⟩,?_⟩ <;>
        (intro i; have h := i.isLt; simp [rows.noOutputs] at h)

theorem selected_trace_is_dictionary_sound416 {s q t e} (trace : SourceTrace R8 s q t e)
    (m : I72.Model) (fit : Fits s m) :
    ∀ d, Summarizes t (.selected d) → DictionaryEvidence s m q d := by
  exact SourceTrace.rec (R := R8) (s := s)
    (motive_1 := fun q t _ _ => ∀ d, Summarizes t (.selected d) → DictionaryEvidence s m q d)
    (motive_2 := fun qs ts _ => ∀ ds, All₂ Summarizes ts (ds.map Result.selected) →
      DictionaryEvidenceForest s m qs ds)
    (motive_3 := fun _ _ => True)
    (fun _ _ evidence => by cases evidence)
    (fun v _ _ _ _ _ evidence => by cases v <;> cases evidence)
    (fun event _ decision _ _ _ proveKids d actual => by
      have semantics := selected_plain_local_sound416 decision m fit
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

theorem dictionary_sound_R8 : DictionarySound R8 := by
  rintro s q d ⟨t,e,⟨trace⟩,result⟩ m fit
  exact selected_trace_is_dictionary_sound416 trace m fit d result

end Yulang.GeneralDeclarativeI65.I72.PlainMerged416
