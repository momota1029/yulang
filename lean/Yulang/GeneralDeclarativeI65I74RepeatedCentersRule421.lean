import Yulang.GeneralDeclarativeI65I74RepeatedCentersPost421

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RepeatedCenters421
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (All₂ Dictionary Summarizes Result)

inductive TiedElection (s : I72.State) : (q : I72.Request) → Event s q → Type where
  | actual {q} {a : Choice ⟨s,q⟩} (tied : Accepted a) : TiedElection s q (acceptedEvent tied)

structure RejectedElection (s : I72.State) (q : I72.Request) where
  choice : Choice ⟨s,q⟩
  conflict : Conflict choice

def R13 : SourcePrimitives where
  elected := fun s q e needs => RoleDefault420.R12.elected s q e needs ∨
    needs = [] ∧ Nonempty (TiedElection s q e)
  other := fun s q v needs => RoleDefault420.R12.other s q v needs ∨
    v = .rejected ∧ needs = [] ∧ Nonempty (RejectedElection s q)

theorem selected_repeated_local_sound421 {s q e needs}
    (sound : R13.elected s q e needs) (m : I72.Model) (fit : Fits s m) :
    LocalMeaning m e ∧ FixedTargets m e := by
  rcases sound with old|new
  · exact RoleDefault420.selected_default_local_sound420 old m fit
  · obtain ⟨data⟩ := new.2
    cases data with
    | actual tied =>
      rename_i a
      have len : q.demand.outputs.length = 0 := congrArg List.length a.noOutputs
      refine ⟨⟨source_head_sound (acceptedEvent tied).head m fit,?_⟩,?_⟩ <;>
        (intro i; exact Fin.elim0 (Fin.cast len i))

theorem selected_trace_is_dictionary_sound421 {s q t e} (trace : SourceTrace R13 s q t e)
    (m : I72.Model) (fit : Fits s m) :
    ∀ d, Summarizes t (.selected d) → DictionaryEvidence s m q d := by
  exact SourceTrace.rec (R := R13) (s := s)
    (motive_1 := fun q t _ _ => ∀ d, Summarizes t (.selected d) → DictionaryEvidence s m q d)
    (motive_2 := fun qs ts _ => ∀ ds, All₂ Summarizes ts (ds.map Result.selected) →
      DictionaryEvidenceForest s m qs ds)
    (motive_3 := fun _ _ => True)
    (fun _ _ evidence => by cases evidence)
    (fun v _ _ _ _ _ evidence => by cases v <;> cases evidence)
    (fun event _ decision _ _ _ proveKids d actual => by
      have semantics := selected_repeated_local_sound421 decision m fit
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

theorem dictionary_sound_R13 : DictionarySound R13 := by
  rintro s q d ⟨t,e,⟨trace⟩,result⟩ m fit
  exact selected_trace_is_dictionary_sound421 trace m fit d result

end Yulang.GeneralDeclarativeI65.I72.RepeatedCenters421
