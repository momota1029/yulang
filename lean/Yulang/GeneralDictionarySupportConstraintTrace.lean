import Yulang.GeneralNominalSupportSteps

/-! Exact semantic obligations of actual finite guarded support traces.
This is an auxiliary model-set characterization, not a general V5 bridge or an
existence theorem for schedules. In particular, survival of an old assignment additionally requires the packet constraint,
whereas installability witnesses some surviving assignment. -/
namespace Yulang.GeneralDictionarySupportConstraintTrace
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSteps
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalDemandMerging (Site outputAtoms)
variable {roles : Roles.RoleDecls}

inductive Event (roles : Roles.RoleDecls) where
  | installation (packet : Packet roles)
  | merging (first last : Site roles)

def Event.Holds (event : Event roles) (model : Assignment) : Prop :=
  match event with
  | .installation packet => packet.Holds model
  | .merging first last =>
    PresenceNormalForm.All CommonNominalFullCarrier.model model (outputAtoms first last)

def Satisfies (events : List (Event roles)) (model : Assignment) : Prop :=
  ∀ event ∈ events, event.Holds model

/-- A record contains only constraints actually emitted by a guarded update. -/
inductive Recorded (registry : Registry) :
    Tracked roles → Occurrence roles → Tracked roles → List (Event roles) → Prop where
  | administrative {before : Tracked roles} {focus : Occurrence roles} {after : State roles}
      (step : Administrative registry before.current focus after) :
      Recorded registry before focus {before with current := after} []
  | installation {before : Tracked roles} {packet : Packet roles}
      {support : List (Occurrence roles)}
      (enabled : GeneralNominalFeedbackSteps.Installable registry before.current packet)
      (fresh : ¬ GeneralNominalFeedbackSteps.Committed before.current packet)
      (guard : PacketGuard before packet support) :
      Recorded registry before packet.site.occurrence (GeneralNominalSupportSteps.install before packet support)
        [.installation packet]
  | merging {before : Tracked roles} {first last : Site roles}
      {support : List (Occurrence roles)}
      (left : first ∈ before.current.sites) (right : last ∈ before.current.sites)
      (same : GeneralNominalFeedbackSites.SameInputs before.current first last)
      (fresh : ¬ Alias before.current first.occurrence.identity last.occurrence.identity)
      (guard : GeneralNominalSupportChoices.MergeGuard before first last support) :
      Recorded registry before first.occurrence (GeneralNominalSupportSteps.merge before first last support)
        [.merging first last]

theorem recorded_models {registry : Registry} {before after : Tracked roles}
    {focus : Occurrence roles} {events : List (Event roles)}
    (record : Recorded registry before focus after events)
    (model : Assignment) :
    Models after.current model ↔ Models before.current model ∧ Satisfies events model := by
  cases record with
  | administrative step =>
    simpa [Satisfies] using administrative_models step model
  | installation enabled fresh guard =>
    simpa [GeneralNominalSupportSteps.install, Satisfies, Event.Holds] using
      GeneralNominalFeedbackSites.install_models _ _ _ enabled.1.2.1 model
  | merging left right same fresh guard =>
    simpa [GeneralNominalSupportSteps.merge, Satisfies, Event.Holds] using
      merge_models _ _ _ model

theorem at_recorded {registry : Registry} {before after : Tracked roles}
    {focus : Occurrence roles} (step : At registry before focus after) :
    ∃ events, Recorded registry before focus after events := by
  cases step with
  | administrative focus after step => exact ⟨[],.administrative step⟩
  | install packet support enabled fresh guard =>
    exact ⟨[.installation packet],.installation enabled fresh guard⟩
  | merge first last support left right same fresh guard =>
    exact ⟨[.merging first last],.merging left right same fresh guard⟩

theorem recorded_at {registry : Registry} {before after : Tracked roles}
    {focus : Occurrence roles} {events : List (Event roles)}
    (record : Recorded registry before focus after events) : At registry before focus after := by
  cases record with
  | administrative step => exact .administrative _ _ step
  | installation enabled fresh guard => exact .install _ _ enabled fresh guard
  | merging left right same fresh guard => exact .merge _ _ _ left right same fresh guard

/-- Each edge is an actual generated-focus support step, not just a model-set
inclusion or a freely chosen event. -/
inductive Trace (registry : Registry) (root : Occurrence roles)
    (start : Tracked roles) : Tracked roles → List (Event roles) → Prop where
  | refl : Trace registry root start start []
  | tail {middle finish : Tracked roles} {earlier current : List (Event roles)}
      (prior : Trace registry root start middle earlier)
      {focus : Occurrence roles}
      (generated : Generated middle.current root focus)
      (record : Recorded registry middle focus finish current) :
      Trace registry root start finish (earlier ++ current)

theorem satisfies_append (first last : List (Event roles)) (model : Assignment) :
    Satisfies (first ++ last) model ↔ Satisfies first model ∧ Satisfies last model := by
  simp only [Satisfies, List.mem_append]
  constructor
  · intro all; exact ⟨fun e h => all e (Or.inl h),fun e h => all e (Or.inr h)⟩
  · rintro ⟨left,right⟩ e (h | h)
    · exact left e h
    · exact right e h

theorem trace_models {registry : Registry} {root : Occurrence roles}
    {start finish : Tracked roles} {events : List (Event roles)}
    (trace : Trace registry root start finish events) (model : Assignment) :
    Models finish.current model ↔ Models start.current model ∧ Satisfies events model := by
  induction trace with
  | refl => simp [Satisfies]
  | tail prior generated record ih =>
    rw [recorded_models record, ih, satisfies_append]
    exact and_assoc

theorem steps_recorded {registry : Registry} {root : Occurrence roles}
    {start finish : Tracked roles} (path : B4Target.Steps (Step registry root) start finish) :
    ∃ events, Trace registry root start finish events := by
  induction path with
  | refl => exact ⟨[],.refl⟩
  | tail path step ih =>
    obtain ⟨earlier,prior⟩ := ih
    obtain ⟨focus,generated,update⟩ := step
    obtain ⟨current,record⟩ := at_recorded update
    exact ⟨earlier ++ current,.tail prior generated record⟩

theorem trace_steps {registry : Registry} {root : Occurrence roles}
    {start finish : Tracked roles} {events : List (Event roles)}
    (trace : Trace registry root start finish events) :
    B4Target.Steps (Step registry root) start finish := by
  induction trace with
  | refl => exact .refl
  | tail prior generated record ih => exact .tail ih ⟨_,generated,recorded_at record⟩

/-- For a fixed original assignment, failure is precisely a failed actual
constraint. This does not assert any such failure is reachable. -/
theorem assignment_lost_iff {registry : Registry} {root : Occurrence roles}
    {start finish : Tracked roles} {events : List (Event roles)}
    (trace : Trace registry root start finish events) (model : Assignment)
    (original : Models start.current model) :
    ¬ Models finish.current model ↔ ∃ event ∈ events, ¬ event.Holds model := by
  classical
  rw [trace_models trace]
  constructor
  · intro missing
    apply Classical.byContradiction
    intro none
    apply missing
    refine ⟨original,?_⟩
    intro event member
    apply Classical.byContradiction
    intro bad
    exact none ⟨event,member,bad⟩
  · rintro ⟨event,member,bad⟩ ⟨_,all⟩
    exact bad (all event member)

/-- An actual finite trace that rejects an original assignment has a first
rejecting edge, with real prefix/suffix and a failed emitted constraint. This
locates a loss of that assignment, not necessarily a loss of every model. -/
theorem trace_rejection_edge {registry : Registry} {root : Occurrence roles}
    {start finish : Tracked roles} {events : List (Event roles)}
    (trace : Trace registry root start finish events) (model : Assignment)
    (original : Models start.current model) (rejected : ¬ Models finish.current model) :
    ∃ before after : Tracked roles, ∃ focus : Occurrence roles,
      ∃ current : List (Event roles), ∃ event : Event roles,
        B4Target.Steps (Step registry root) start before ∧
        Generated before.current root focus ∧ Recorded registry before focus after current ∧
        B4Target.Steps (Step registry root) after finish ∧
        Models before.current model ∧ ¬ Models after.current model ∧
        event ∈ current ∧ ¬ event.Holds model := by
  classical
  induction trace with
  | refl => exact False.elim (rejected original)
  | @tail middle finish earlier current prior focus generated record ih =>
    by_cases valid : Models middle.current model
    · have failed : ∃ event ∈ current, ¬ event.Holds model := by
        apply Classical.byContradiction
        intro none
        apply rejected
        apply (recorded_models record model).mpr
        refine ⟨valid,?_⟩
        intro event member
        apply Classical.byContradiction
        intro bad
        exact none ⟨event,member,bad⟩
      obtain ⟨event,member,bad⟩ := failed
      exact ⟨middle,finish,focus,current,event,trace_steps prior,generated,record,
        .refl,valid,rejected,member,bad⟩
    · obtain ⟨before,after,focus,events,event,one,two,three,four,five,six,seven,eight⟩ := ih valid
      exact ⟨before,after,focus,events,event,one,two,three,
        .tail four ⟨_,generated,recorded_at record⟩,five,six,seven,eight⟩

/-- No operational permutation theorem is claimed: both traces must already
exist and have the same constraints up to permutation. -/
theorem permuted_trace_models {registry : Registry} {root : Occurrence roles}
    {start left right : Tracked roles} {first last : List (Event roles)}
    (one : Trace registry root start left first) (two : Trace registry root start right last)
    (permutation : first.Perm last) (model : Assignment) :
    Models left.current model ↔ Models right.current model := by
  rw [trace_models one, trace_models two]
  have same : Satisfies first model ↔ Satisfies last model := by
    constructor
    · intro holds e member; exact holds e (permutation.mem_iff.mpr member)
    · intro holds e member; exact holds e (permutation.mem_iff.mp member)
  rw [same]

end Yulang.GeneralDictionarySupportConstraintTrace
