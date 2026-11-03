import YulangClosure.OriginalSourcePrefixBridgeR332

/-!
R333. The complete admission domain of R331's conservative extension is the
image of the original domain at every embedded original environment. In the
invocation case this follows from the ACTUAL R328 punctured-context clause:
generated interfaces are not inlets. All original raw operands, occurrences,
source parents and same-extension witnesses are retained.

Authority: SG §§3.3–5.2, original source environment §§2–6, and EI §§2,4.
This is a theorem about the specified conservative Inputs/readout/admissions,
not an authenticated interpretation of an arbitrary native environment.
-/
namespace YulangClosure.OriginalSourceAdmittedImageR333
open OriginalSource OriginalScopedClosure OriginalSourceEnvironment
open OriginalSourceInterpretation OriginalInterfacePreservationR328
open OriginalSourceViewRegistrationR330 OriginalSourceEnvironmentTransportR331
open OriginalSourcePrefixBridgeR332
open OriginalCheckingAdmission

variable {s : Sorts} {View G : Type}

/-- Retain all raw fields while recovering an original view token. -/
def downInvocation (raw : Invocation (extended s G) (Sum View Unit)) (view : View) :
    Invocation s View :=
  ⟨downCurrent raw.current, raw.value, raw.valueRoot, raw.context, raw.continuation,
    raw.carrier, raw.carrierRoot, view, raw.receipt, raw.path, raw.consumer, raw.incidence⟩

theorem invocation_image (raw : Invocation (extended s G) (Sum View Unit))
    (view : View) (original : raw.view = .inl view) :
    invocation (downInvocation raw view) = raw := by
  cases raw
  cases original
  rfl

/-- The new view case is impossible by the original extension's independent
challenge law, before provider acceptance or recursive family membership. -/
theorem admitted_invocation_has_original_view (g : G) (base : Inputs s)
    (gen : Generated s G) (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (state : Decoded s View) (b : Binder)
    (raw : Invocation (extended s G) (Sum View Unit))
    (valid : DataAdmitted (inputs base gen) (readout g ro) (admissions g adm)
      (decoded g state) b (.runtime (.invocation raw))) :
    ∃ view, raw.view = .inl view := by
  have punctured := valid.2.2.2.2.1
  cases original : raw.view with
  | inl view => exact ⟨view, rfl⟩
  | inr generated =>
      change (inputs base gen).puncturedContext (raw.challenge
        ((readout g ro).event (decoded g state).fixedFrames
          (decoded g state).assignment.event b (.invocation raw))
        ((decoded g state).callRow b).descriptor (views g state.viewMeaning)) at punctured
      simp only [inputs, Invocation.challenge, views, original] at punctured

/-- No payload class is omitted: four logical kinds, Shared, and all six
runtime kinds. Root is rejected by the actual DataAdmitted definition. -/
theorem data_has_original_image (g : G) (base : Inputs s) (gen : Generated s G)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (state : Decoded s View) (b : Binder)
    (data : Payload (extended s G) (Sum View Unit))
    (valid : DataAdmitted (inputs base gen) (readout g ro) (admissions g adm)
      (decoded g state) b data) :
    ∃ original, payload g original = data := by
  cases data with
  | root data => exact False.elim valid
  | logical kind data =>
      obtain ⟨before, original, _, same, _⟩ := valid.2
      exact ⟨.logical kind original, congrArg (Payload.logical kind) same⟩
  | shared data =>
      obtain ⟨before, original, _, same, _⟩ := valid.2
      exact ⟨.shared original, congrArg Payload.shared same⟩
  | runtime data =>
      cases data with
      | invocation raw =>
          obtain ⟨view, same⟩ := admitted_invocation_has_original_view g base gen ro adm state b raw valid
          exact ⟨.runtime (.invocation (downInvocation raw view)),
            congrArg (fun d => Payload.runtime (Runtime.invocation d)) (invocation_image raw view same)⟩
      | receipt data =>
          obtain ⟨before, original, _, same, _⟩ := valid.2
          exact ⟨.runtime (.receipt original), congrArg (fun d => Payload.runtime (Runtime.receipt d)) same⟩
      | returnRebind data =>
          obtain ⟨before, original, _, same, _⟩ := valid.2
          exact ⟨.runtime (.returnRebind original), congrArg (fun d => Payload.runtime (Runtime.returnRebind d)) same⟩
      | response data =>
          obtain ⟨before, original, _, same, _⟩ := valid.2
          exact ⟨.runtime (.response original), congrArg (fun d => Payload.runtime (Runtime.response d)) same⟩
      | rigidOperation data =>
          obtain ⟨before, original, _, same, _⟩ := valid.2
          exact ⟨.runtime (.rigidOperation original), congrArg (fun d => Payload.runtime (Runtime.rigidOperation d)) same⟩
      | oneShot data =>
          obtain ⟨before, original, _, same, _⟩ := valid.2
          exact ⟨.runtime (.oneShot original), congrArg (fun d => Payload.runtime (Runtime.oneShot d)) same⟩

theorem data_admitted_image_iff (g : G) (base : Inputs s) (gen : Generated s G)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (state : Decoded s View) (b : Binder)
    (data : Payload (extended s G) (Sum View Unit)) :
    DataAdmitted (inputs base gen) (readout g ro) (admissions g adm) (decoded g state) b data ↔
      ∃ original, payload g original = data ∧ DataAdmitted base ro adm state b original := by
  constructor
  · intro valid
    obtain ⟨original, rfl⟩ := data_has_original_image g base gen ro adm state b data valid
    exact ⟨original, rfl, (data_admission_preserved g base gen ro adm state b original).mp valid⟩
  · rintro ⟨original, rfl, valid⟩
    exact (data_admission_preserved g base gen ro adm state b original).mpr valid

/-- Exact equality, including event parents and occurrence, rather than a
projection that forgets raw identity. The recovered original is unique. -/
theorem admitted_image_iff (g : G) (base : Inputs s) (gen : Generated s G)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (env : Environment (Payload s View)) (b : Binder)
    (candidate : ScopedValue (Payload (extended s G) (Sum View Unit))) :
    Admitted (inputs base gen) (readout g ro) (admissions g adm) (environment g env) b candidate ↔
      ∃ original, scopedValue g original = candidate ∧ Admitted base ro adm env b original := by
  constructor
  · rintro ⟨parents, after, found, valid⟩
    rw [decode_commutes] at found
    obtain ⟨before, decodedBefore, rfl⟩ := Option.map_eq_some_iff.mp found
    obtain ⟨original, same, oldValid⟩ :=
      (data_admitted_image_iff g base gen ro adm before b candidate.data).mp valid
    refine ⟨scopeCandidate env candidate.event.occurrence original, ?_, rfl, before, decodedBefore, oldValid⟩
    rcases candidate with ⟨data, ⟨path, occurrence⟩⟩
    change payload g original = data at same
    change path = env.eventPath.map (step g) at parents
    cases same
    cases parents
    rfl
  · rintro ⟨original, rfl, valid⟩
    exact (admission_preserved g base gen ro adm env b original).mpr valid

theorem admitted_original_unique (g : G)
    {first second : ScopedValue (Payload s View)}
    {candidate : ScopedValue (Payload (extended s G) (Sum View Unit))}
    (one : scopedValue g first = candidate) (two : scopedValue g second = candidate) :
    first = second := scopedValue_injective g (one.trans two.symm)

/-- All admitted alternatives, including universal invocation and open return,
can now be transported without assuming the candidate was already an image. -/
theorem all_admitted_iff (g : G) (base : Inputs s) (gen : Generated s G)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (env : Environment (Payload s View)) (b : Binder)
    (P : ScopedValue (Payload (extended s G) (Sum View Unit)) → Prop) :
    (∀ candidate, Admitted (inputs base gen) (readout g ro) (admissions g adm)
      (environment g env) b candidate → P candidate) ↔
    ∀ original, Admitted base ro adm env b original → P (scopedValue g original) := by
  constructor
  · intro all original valid
    exact all _ ((admission_preserved g base gen ro adm env b original).mpr valid)
  · intro all candidate valid
    obtain ⟨original, rfl, originalValid⟩ := (admitted_image_iff g base gen ro adm env b candidate).mp valid
    exact all original originalValid

/-- Checking retains its own current target descriptor. No alignment with the
source binder descriptor is assumed or derived. -/
theorem goal_data_admission_preserved (g : G) (base : Inputs s) (gen : Generated s G)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (state : Decoded s View) (goal : CheckGoal) (b : Binder) (data : Payload s View) :
    GoalDataAdmitted (inputs base gen) (readout g ro) (admissions g adm)
      (decoded g state) goal b (payload g data) ↔ GoalDataAdmitted base ro adm state goal b data := by
  cases data with
  | root data => exact data_admission_preserved g base gen ro adm state b (.root data)
  | logical kind data => exact data_admission_preserved g base gen ro adm state b (.logical kind data)
  | shared data => exact data_admission_preserved g base gen ro adm state b (.shared data)
  | runtime data =>
      cases data with
      | invocation raw =>
          simp only [payload, runtime, GoalDataAdmitted]
          have evt := event_commutes g ro state.fixedFrames state.assignment.event b (.invocation raw)
          change _ ∧ _ ∧ _ ∧ CheckedDomain (inputs base gen)
            ((invocation raw).challenge
              ((readout g ro).event (state.fixedFrames.map (frame g))
                (upEvent state.assignment.event) b (runtime (.invocation raw)))
              (state.assignment.descriptor goal.upper) (views g state.viewMeaning)) ↔ _
          rw [evt]
          exact Iff.rfl
      | receipt data => exact data_admission_preserved g base gen ro adm state b (.runtime (.receipt data))
      | returnRebind data => exact data_admission_preserved g base gen ro adm state b (.runtime (.returnRebind data))
      | response data => exact data_admission_preserved g base gen ro adm state b (.runtime (.response data))
      | rigidOperation data => exact data_admission_preserved g base gen ro adm state b (.runtime (.rigidOperation data))
      | oneShot data => exact data_admission_preserved g base gen ro adm state b (.runtime (.oneShot data))

theorem goal_data_has_original_image (g : G) (base : Inputs s) (gen : Generated s G)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (state : Decoded s View) (goal : CheckGoal) (b : Binder)
    (data : Payload (extended s G) (Sum View Unit))
    (valid : GoalDataAdmitted (inputs base gen) (readout g ro) (admissions g adm)
      (decoded g state) goal b data) :
    ∃ original, payload g original = data := by
  cases data with
  | root data => exact data_has_original_image g base gen ro adm state b (.root data) valid
  | logical kind data => exact data_has_original_image g base gen ro adm state b (.logical kind data) valid
  | shared data => exact data_has_original_image g base gen ro adm state b (.shared data) valid
  | runtime data =>
      cases data with
      | invocation raw =>
          have punctured := valid.2.2.2.2.1
          cases original : raw.view with
          | inl view =>
              exact ⟨.runtime (.invocation (downInvocation raw view)),
                congrArg (fun d => Payload.runtime (Runtime.invocation d)) (invocation_image raw view original)⟩
          | inr generated =>
              change (inputs base gen).puncturedContext (raw.challenge
                ((readout g ro).event (decoded g state).fixedFrames
                  (decoded g state).assignment.event b (.invocation raw))
                ((decoded g state).assignment.descriptor goal.upper) (views g state.viewMeaning)) at punctured
              simp only [inputs, Invocation.challenge, views, original] at punctured
      | receipt data => exact data_has_original_image g base gen ro adm state b (.runtime (.receipt data)) valid
      | returnRebind data => exact data_has_original_image g base gen ro adm state b (.runtime (.returnRebind data)) valid
      | response data => exact data_has_original_image g base gen ro adm state b (.runtime (.response data)) valid
      | rigidOperation data => exact data_has_original_image g base gen ro adm state b (.runtime (.rigidOperation data)) valid
      | oneShot data => exact data_has_original_image g base gen ro adm state b (.runtime (.oneShot data)) valid

theorem goal_data_admitted_image_iff (g : G) (base : Inputs s) (gen : Generated s G)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (state : Decoded s View) (goal : CheckGoal) (b : Binder)
    (data : Payload (extended s G) (Sum View Unit)) :
    GoalDataAdmitted (inputs base gen) (readout g ro) (admissions g adm) (decoded g state) goal b data ↔
      ∃ original, payload g original = data ∧ GoalDataAdmitted base ro adm state goal b original := by
  constructor
  · intro valid
    obtain ⟨original, rfl⟩ := goal_data_has_original_image g base gen ro adm state goal b data valid
    exact ⟨original, rfl, (goal_data_admission_preserved g base gen ro adm state goal b original).mp valid⟩
  · rintro ⟨original, rfl, valid⟩
    exact (goal_data_admission_preserved g base gen ro adm state goal b original).mpr valid

theorem goal_admitted_image_iff (g : G) (base : Inputs s) (gen : Generated s G)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (env : Environment (Payload s View)) (goal : CheckGoal) (b : Binder)
    (candidate : ScopedValue (Payload (extended s G) (Sum View Unit))) :
    GoalAdmitted (inputs base gen) (readout g ro) (admissions g adm)
      (environment g env) goal b candidate ↔
      ∃ original, scopedValue g original = candidate ∧ GoalAdmitted base ro adm env goal b original := by
  constructor
  · rintro ⟨parents, after, found, valid⟩
    rw [decode_commutes] at found
    obtain ⟨before, decodedBefore, rfl⟩ := Option.map_eq_some_iff.mp found
    obtain ⟨original, same, oldValid⟩ :=
      (goal_data_admitted_image_iff g base gen ro adm before goal b candidate.data).mp valid
    refine ⟨scopeCandidate env candidate.event.occurrence original, ?_, rfl, before, decodedBefore, oldValid⟩
    rcases candidate with ⟨data, ⟨path, occurrence⟩⟩
    change payload g original = data at same
    change path = env.eventPath.map (step g) at parents
    cases same
    cases parents
    rfl
  · rintro ⟨original, rfl, parents, before, found, valid⟩
    refine ⟨congrArg (List.map (step g)) parents, decoded g before, ?_, ?_⟩
    · rw [decode_commutes, found]; rfl
    · exact (goal_data_admission_preserved g base gen ro adm before goal b original.data).mpr valid

theorem all_goal_admitted_iff (g : G) (base : Inputs s) (gen : Generated s G)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (env : Environment (Payload s View)) (goal : CheckGoal) (b : Binder)
    (P : ScopedValue (Payload (extended s G) (Sum View Unit)) → Prop) :
    (∀ candidate, GoalAdmitted (inputs base gen) (readout g ro) (admissions g adm)
      (environment g env) goal b candidate → P candidate) ↔
    ∀ original, GoalAdmitted base ro adm env goal b original → P (scopedValue g original) := by
  constructor
  · intro all original valid
    exact all _ ((goal_admitted_image_iff g base gen ro adm env goal b _).mpr ⟨original,rfl,valid⟩)
  · intro all candidate valid
    obtain ⟨original, rfl, originalValid⟩ := (goal_admitted_image_iff g base gen ro adm env goal b candidate).mp valid
    exact all original originalValid

/-- Apply the all-domain result to the ACTUAL R332/R315/R159 source consumer.
Every extended admitted call is covered by the original source continuation,
at the image of precisely that call's original extension. The returned parent
facts and both child judgments remain in the original kernel: transport of
Local/Checking/Boundary and whole source judgments is a separate obligation. -/
theorem original_source_parent_all_extended_calls
    {origin : Declaration} {declared : ComputedCallTypedFormationR310.Key → Prop}
    (definition : Definition origin declared) (base : Inputs s) (gen : Generated s Code)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (original : Kernel (Payload s View)) (initial : Environment (Payload s View))
    (state : Decoded s View) (found : decode ro initial = some state)
    (sourceProof : SourceJudgment (admissionKernel base ro adm original) initial
      OriginalModuleContextBindingR315.externalContext OriginalScopedSourceEventMapR314.Fixture.root) :
    ∃ description outerView,
      Admitted base ro adm initial ⟨98,.description,0⟩ description ∧
      let afterDescription := initial.extend ⟨98,.description,0⟩ description
      Admitted base ro adm afterDescription ⟨0,.viewLogic,0⟩ outerView ∧
      let afterView := afterDescription.extend ⟨0,.viewLogic,0⟩ outerView
      ∀ extendedCall, Admitted (inputs base gen) (readout definition.code ro)
        (admissions definition.code adm) (environment definition.code afterView)
          ⟨0,.invocation,0⟩ extendedCall →
        ∃ call, scopedValue definition.code call = extendedCall ∧
          Admitted base ro adm afterView ⟨0,.invocation,0⟩ call ∧
          environment definition.code (afterView.extend ⟨0,.invocation,0⟩ call) =
            (environment definition.code afterView).extend ⟨0,.invocation,0⟩ extendedCall ∧
          let afterCall := afterView.extend ⟨0,.invocation,0⟩ call
          ∃ received, Admitted base ro adm afterCall ⟨98,.receipt,0⟩ received ∧
            ReturnParentRegistered definition base gen ro adm original initial
              (afterCall.extend ⟨98,.receipt,0⟩ received) := by
  obtain ⟨description,outerView,hDescription,hView,calls⟩ :=
    original_source_parent_registered_alternatives definition base gen ro adm original initial state found sourceProof
  refine ⟨description,outerView,hDescription,hView,?_⟩
  dsimp only
  intro extendedCall valid
  obtain ⟨call,same,oldValid⟩ := (admitted_image_iff definition.code base gen ro adm
    ((initial.extend ⟨98,.description,0⟩ description).extend ⟨0,.viewLogic,0⟩ outerView)
      ⟨0,.invocation,0⟩ extendedCall).mp valid
  refine ⟨call,same,oldValid,?_,calls call oldValid⟩
  rw [extension_commutes, same]

end YulangClosure.OriginalSourceAdmittedImageR333
