import Yulang.GeneralDeclarativeEndpointProbe321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOutputOrigins323
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeEntailment320 (Entails literal appendFacts)
open GeneralDeclarativeOrigins321 (Supported Origin Available restriction backed_iff)
open GeneralDeclarativeLowerKnown321 (Ready knows_mono)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeTrace321 (Trace TraceArgs)
open GeneralDeclarativeEndpointProbe321 (Matches HeadMatches)
open CommonRoleOutermostResolver (All₂)

/-- The approved distinction in spec 6.3: an associated equation is
ordinary immediately, but a new occurrence only justifies probing after
its producer completed. Existing source origins remain intact. -/
def emit {s : State} (p : Supported s completed) (owner : Nat) (rows : List Equation) :
    Supported (appendFacts s rows) completed :=
  ⟨fun eq origin => p.derivesFrom eq origin ∨ eq ∈ rows ∧ origin = .output owner, by
    intro eq origin proof
    rcases proof with old|new
    · exact List.mem_append_left _ (p.ordinary old)
    · exact List.mem_append_right _ new.1⟩

theorem immediate_truth {s : State} (rows : List Equation)
    (there : e ∈ rows) : Entails (appendFacts s rows) e :=
  literal (List.mem_append_right _ there)

theorem backed_unchanged {s : State} (p : Supported s completed) (rows : List Equation)
    (pending : ¬completed owner) (eq : Equation) :
    eq ∈ (restriction (emit p owner rows)).equations ↔ eq ∈ (restriction p).equations := by
  rw [backed_iff,backed_iff]
  constructor
  · rintro ⟨origin,source,available⟩
    rcases source with old|⟨new,rfl⟩
    · exact ⟨origin,old,available⟩
    · cases available with
      | completed known => exact False.elim (pending known)
  · rintro ⟨origin,old,available⟩
    exact ⟨origin,.inl old,available⟩

theorem ready_unchanged {s : State} (p : Supported s completed) (rows : List Equation)
    (pending : ¬completed owner) :
    Ready (emit p owner rows) d ↔ Ready p d :=
  ⟨fun known arg used =>
    let ⟨tag,read⟩ := known arg used
    ⟨tag,knows_mono (s := restriction (emit p owner rows)) (t := restriction p) rfl (fun {eq} h => (backed_unchanged p rows pending eq).mp h) read⟩,
    fun known arg used =>
    let ⟨tag,read⟩ := known arg used
    ⟨tag,knows_mono (s := restriction p) (t := restriction (emit p owner rows)) rfl (fun {eq} h => (backed_unchanged p rows pending eq).mpr h) read⟩⟩

theorem trace_mono {s t : State} (normal : s.normal = t.normal) (rows : s.equations ⊆ t.equations)
    (proof : Trace s mode name expr seen) : Trace t mode name expr seen := by
  have alias : ∀ {a b : Nat}, GeneralDeclarativeLowerKnown321.Alias s a b →
      GeneralDeclarativeLowerKnown321.Alias t a b := GeneralDeclarativeLowerKnown321.alias_mono normal rows
  induction proof using Trace.rec (motive_2 := fun mode args exprs seen _ => TraceArgs t mode args exprs seen) with
  | capture => exact .capture
  | primitive equal found _ ih => exact .primitive (alias equal) (rows found) ih
  | nominal equal found _ ih => exact .nominal (alias equal) (rows found) ih
  | record equal found _ _ ih jh => exact .record (alias equal) (rows found) ih jh
  | variant equal found _ ih => exact .variant (alias equal) (rows found) ih
  | join equal found _ _ ih jh => exact .join (alias equal) (rows found) ih jh
  | nil => exact .nil
  | cons _ _ ih jh => exact .cons ih jh

theorem match_mono {s t : State} (normal : s.normal = t.normal) (rows : s.equations ⊆ t.equations)
    (choice : Matches s c interp arg pat) : Matches t c interp arg pat := by
  obtain ⟨argBounds,code,lo,hi,translates,low,high⟩ := choice
  refine ⟨?_,code,lo,hi,translates,trace_mono normal rows low,trace_mono normal rows high⟩
  unfold Bounds at argBounds ⊢
  rwa [← normal]

theorem head_mono {s t : State} (normal : s.normal = t.normal) (rows : s.equations ⊆ t.equations)
    (choice : HeadMatches s c interp d impl) : HeadMatches t c interp d impl :=
  GeneralDeclarativeNormalized320.ordered_map choice (fun _ _ _ _ evidence => match_mono normal rows evidence)

theorem probing_unchanged {s : State} (p : Supported s completed) (rows : List Equation)
    (pending : ¬completed owner) :
    HeadMatches (restriction (emit p owner rows)) c interp d impl ↔ HeadMatches (restriction p) c interp d impl :=
  ⟨head_mono rfl (fun {eq} => (backed_unchanged p rows pending eq).mp),
    head_mono rfl (fun {eq} => (backed_unchanged p rows pending eq).mpr)⟩

theorem completed_enables {s : State} (p : Supported s completed) (rows : List Equation)
    (ready : completed owner) (new : e ∈ rows) :
    e ∈ (restriction (emit p owner rows)).equations :=
  (backed_iff ..).mpr ⟨.output owner,.inr ⟨new,rfl⟩,.completed ready⟩

end Yulang.GeneralDeclarativeOutputOrigins323
