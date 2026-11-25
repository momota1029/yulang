import Yulang.GeneralDeclarativeI65I74RoleDefaultReplay420

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RoleDefault420
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (All₂ Dictionary Summarizes Result)

inductive DefaultElection (s : I72.State) : (q : I72.Request) → Event s q → Type where
  | actual {q} (a : DefaultPacket ⟨s,q⟩) : DefaultElection s q a.event

def R12 : SourcePrimitives where
  elected := fun s q e needs => ExplicitPick419.R11.elected s q e needs ∨
    needs = [] ∧ Nonempty (DefaultElection s q e)
  other := ExplicitPick419.R11.other

theorem selected_default_local_sound420 {s q e needs}
    (sound : R12.elected s q e needs) (m : I72.Model) (fit : Fits s m) :
    LocalMeaning m e ∧ FixedTargets m e := by
  rcases sound with old|new
  · exact ExplicitPick419.selected_pick_local_sound419 old m fit
  · obtain ⟨data⟩ := new.2
    cases data with
    | actual a =>
      exact ⟨⟨source_head_sound a.event.head m fit,
        fun i => original_named_mixed_output_meaning401 m (a.event.outputs i) a.declaration.checked⟩,
        retained_typed_rows_satisfy_fixed_targets403 (default_uses_exact_retained_typed_row420 a) m fit⟩

theorem selected_trace_is_dictionary_sound420 {s q t e} (trace : SourceTrace R12 s q t e)
    (m : I72.Model) (fit : Fits s m) :
    ∀ d, Summarizes t (.selected d) → DictionaryEvidence s m q d := by
  exact SourceTrace.rec (R := R12) (s := s)
    (motive_1 := fun q t _ _ => ∀ d, Summarizes t (.selected d) → DictionaryEvidence s m q d)
    (motive_2 := fun qs ts _ => ∀ ds, All₂ Summarizes ts (ds.map Result.selected) →
      DictionaryEvidenceForest s m qs ds)
    (motive_3 := fun _ _ => True)
    (fun _ _ evidence => by cases evidence)
    (fun v _ _ _ _ _ evidence => by cases v <;> cases evidence)
    (fun event _ decision _ _ _ proveKids d actual => by
      have semantics := selected_default_local_sound420 decision m fit
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

theorem dictionary_sound_R12 : DictionarySound R12 := by
  rintro s q d ⟨t,e,⟨trace⟩,result⟩ m fit
  exact selected_trace_is_dictionary_sound420 trace m fit d result

end Yulang.GeneralDeclarativeI65.I72.RoleDefault420
