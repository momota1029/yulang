import Yulang.GeneralDeclarativeI65I74ExplicitPickReplay419

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ExplicitPick419
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (All₂ Dictionary Summarizes Result)

inductive PickElection (s : I72.State) : (q : I72.Request) → Event s q → Type where
  | actual {q} (a : PickPacket ⟨s,q⟩) : PickElection s q a.event

def R11 : SourcePrimitives where
  elected := fun s q e needs => RigidRival418.R10.elected s q e needs ∨
    needs = [] ∧ Nonempty (PickElection s q e)
  other := RigidRival418.R10.other

theorem selected_pick_local_sound419 {s q e needs}
    (sound : R11.elected s q e needs) (m : I72.Model) (fit : Fits s m) :
    LocalMeaning m e ∧ FixedTargets m e := by
  rcases sound with old|new
  · exact RigidRival418.selected_rigid_local_sound418 old m fit
  · obtain ⟨data⟩ := new.2
    cases data with
    | actual a =>
      exact ⟨⟨source_head_sound a.event.head m fit,
        fun i => original_named_mixed_output_meaning401 m (a.event.outputs i) a.declaration.checked⟩,
        retained_typed_rows_satisfy_fixed_targets403 (pick_uses_exact_retained_typed_row419 a) m fit⟩

theorem selected_trace_is_dictionary_sound419 {s q t e} (trace : SourceTrace R11 s q t e)
    (m : I72.Model) (fit : Fits s m) :
    ∀ d, Summarizes t (.selected d) → DictionaryEvidence s m q d := by
  exact SourceTrace.rec (R := R11) (s := s)
    (motive_1 := fun q t _ _ => ∀ d, Summarizes t (.selected d) → DictionaryEvidence s m q d)
    (motive_2 := fun qs ts _ => ∀ ds, All₂ Summarizes ts (ds.map Result.selected) →
      DictionaryEvidenceForest s m qs ds)
    (motive_3 := fun _ _ => True)
    (fun _ _ evidence => by cases evidence)
    (fun v _ _ _ _ _ evidence => by cases v <;> cases evidence)
    (fun event _ decision _ _ _ proveKids d actual => by
      have semantics := selected_pick_local_sound419 decision m fit
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

theorem dictionary_sound_R11 : DictionarySound R11 := by
  rintro s q d ⟨t,e,⟨trace⟩,result⟩ m fit
  exact selected_trace_is_dictionary_sound419 trace m fit d result

end Yulang.GeneralDeclarativeI65.I72.ExplicitPick419
