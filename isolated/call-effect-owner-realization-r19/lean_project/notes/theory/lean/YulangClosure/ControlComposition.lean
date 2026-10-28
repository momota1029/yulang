import YulangClosure.ControlTyping
import YulangClosure.CoreComposition

namespace YulangClosure.Control

/-- Every raw control rule preserves the independent frame judgment. -/
theorem control_preservation {sig : Signature} {md : Metadata W}
    (ht : StateTyped sig s result) (step : ControlStep md s t) :
    StateTyped sig t result := by
  obtain ⟨hole, hh, hs⟩ := ht
  cases step with
  | bindCode =>
    cases hh with | ret hv =>
      cases hs with | cons hf tail =>
        cases hf with | bind hc =>
          exact ⟨_, .run (.cons hv .nil) .none hc, tail⟩
  | scopeRet =>
    cases hs with | cons hf tail =>
      cases hf
      exact ⟨_, hh, tail⟩
  | viewRet =>
    cases hs with | cons hf tail =>
      cases hf
      exact ⟨_, hh, tail⟩
  | releaseRet =>
    cases hs with | cons hf tail =>
      cases hf
      exact ⟨_, hh, tail⟩
  | mapRet =>
    cases hs with | cons hf tail =>
      cases hf
      exact ⟨_, hh, tail⟩
  | handleRet =>
    cases hs with | cons hf tail =>
      cases hf with | handle handler =>
        cases hh with | ret hv =>
          cases handler with | mk values arms =>
            exact ⟨_, .search (.mk values arms) (.value hv values), tail⟩
  | waitYes =>
    cases hs with | cons hf tail =>
      cases hf with | wait handler search =>
        cases hh with | ret hv =>
          cases hv with | yes hv => exact ⟨_, .ret hv, tail⟩
  | waitNo =>
    cases hs with | cons hf tail =>
      cases hf with | wait handler search =>
        exact ⟨_, .search handler search, tail⟩
  | waitBad =>
    cases hs with | cons hf tail =>
      cases hf with | wait handler search =>
        cases hh with | ret hv => cases hv
  | bindReq =>
    cases hh with | req hp =>
      cases hs with | cons hf tail =>
        exact ⟨_, .req (packet_capture_typed hp hf), tail⟩
  | scopeReq =>
    cases hh with | req hp =>
      cases hs with | cons hf tail =>
        exact ⟨_, .req (packet_capture_typed hp hf), tail⟩
  | viewReq =>
    cases hh with | req hp =>
      cases hs with | cons hf tail =>
        exact ⟨_, .req (packet_capture_typed hp hf), tail⟩
  | waitReq =>
    cases hh with | req hp =>
      cases hs with | cons hf tail =>
        exact ⟨_, .req (packet_capture_typed hp hf), tail⟩
  | releaseReq =>
    cases hh with | req hp =>
      cases hs with | cons hf tail =>
        exact ⟨_, .req (packet_capture_typed hp hf), tail⟩
  | handleReq =>
    cases hs with | cons hf tail =>
      cases hf with | handle handler =>
        cases hh with | req hp =>
          cases handler with | mk hc arms =>
            exact ⟨_, .search (.mk hc arms) (.request hp arms), tail⟩
  | mapMiss =>
    cases hh with | req hp =>
      cases hs with | cons hf tail =>
        exact ⟨_, .req (packet_capture_typed hp hf), tail⟩
  | mapHit =>
    cases hs with | cons hf tail =>
      cases hf with | mapper mapper =>
        cases hh with | req hp =>
          cases hp with | mk hv hk =>
            cases mapper with | mk family payload response =>
              exact ⟨_, .run (.cons hv .nil) .none payload,
                .cons (.mapped (.mk family payload response) (.mk hv hk)) tail⟩
  | mappedRet =>
    cases hs with | cons hf tail =>
      cases hf with | mapped mapper hp =>
        cases hh with | ret hv =>
          cases hp with | mk old hk =>
            exact ⟨_, .req (.mk hv (.mk (.cons (.response mapper hk) .nil))), tail⟩
  | responseRet =>
    cases hs with | cons hf tail =>
      cases hf with | response mapper hk =>
        cases hh with | ret hv =>
          cases mapper with | mk family payload response =>
            exact ⟨_, .run (.cons hv .nil) .none response,
              .cons (.enterSaved (.mk family payload response) hk) tail⟩
  | enterSavedRet =>
    cases hs with | cons hf tail =>
      cases hf with | enterSaved mapper hk =>
        cases hk with | mk saved =>
          exact ⟨_, hh, frames_append saved (.cons (.mapper mapper) tail)⟩
  | searchValueTry =>
    cases hh with | search handler search =>
      cases search with | value hv values =>
        cases values with | cons code rest =>
          exact ⟨_, .run (.cons hv .nil) .none code,
            .cons (.wait handler (.value hv rest)) hs⟩
  | searchValueEnd =>
    exact ⟨_, .fail, hs⟩
  | searchRequestEnd =>
    cases hh with | search handler search =>
      cases search with | request hp arms =>
        exact ⟨_, .req (packet_capture_typed hp (.handle handler)), hs⟩
  | skip test =>
    cases hh with | search handler search =>
      cases search with | request hp arms =>
        cases arms with | cons hc rest =>
          exact ⟨_, .search handler (.request hp rest), hs⟩
  | select eq yes =>
    cases hh with | search handler search =>
      cases search with | request hp arms =>
        cases arms with | cons hc rest =>
          cases hp with | mk hv hk =>
            rw [eq] at hc
            exact ⟨_, .run (.cons hv .nil) (.some hk) hc,
              .cons (.wait handler (.request (.mk hv hk) rest)) hs⟩
  | failRelease =>
    cases hs with | cons hf tail => exact ⟨_, .fail, tail⟩
  | failFrame =>
    cases hs with | cons hf tail => exact ⟨_, .fail, tail⟩
  | badFrame => cases hh
  | originalEnter => cases hh
  | originalReturnBind => cases hh
  | originalPrincipal => cases hh
  | originalExit => cases hh


/-- Raw states admit bad responses; typing of the saved stack excludes them
only when the supplied response has its paired declared base tag. -/
theorem resume_atom_typed {sig : Signature} {k : Kont} {q data : Nat}
    (hk : KontTyped sig k (.base q) a) (w : W) :
    StateTyped sig (resume k (.atom q data) w) a := by
  cases hk with
  | mk hs =>
    simpa [resume, responseOK, Kont.input, Kont.frames] using
      (show StateTyped sig ⟨w, .ret (.atom q data), _⟩ a from
        ⟨.base q, .ret .atom, hs⟩)

/-- No equality between the two CURRENT worlds is required. -/
theorem resume_reusable {sig : Signature} {k : Kont} {q n₁ n₂ : Nat}
    (hk : KontTyped sig k (.base q) a) (w₁ w₂ : W) :
    StateTyped sig (resume k (.atom q n₁) w₁) a ∧
    StateTyped sig (resume k (.atom q n₂) w₂) a := by
  exact ⟨resume_atom_typed hk w₁, resume_atom_typed hk w₂⟩

/-- Failure propagation never enters search or manufactures No/Ret. -/
theorem control_fail_absorbing {md : Metadata W} {s t : State W}
    (h : ControlStep md s t) (hf : s.head = .fail reason) :
    t.head = .fail reason := by
  cases h <;> simp_all

theorem step_fail_absorbing {md : Metadata W}
    {body : W → Nat → List Value → Option Kont → W → Head → Prop}
    {s t : State W} (h : Step md body s t) (hf : s.head = .fail reason) :
    t.head = .fail reason := by
  cases h with
  | control hc => exact control_fail_absorbing hc hf
  | body hb => cases hf

/-- All finite raw traces, with no typing assumption, preserve a failure tag. -/
theorem prefix_fail_absorbing {md : Metadata W}
    {body : W → Nat → List Value → Option Kont → W → Head → Prop}
    {s t : State W} (h : Prefix (Step md body) n s t)
    (hf : s.head = .fail reason) : t.head = .fail reason := by
  induction h with
  | refl => exact hf
  | snoc hp hs ih => exact step_fail_absorbing hs (ih hf)

/-- Body execution preservation composes with an EXTRINSIC typed stack.
The body law covers only Head.run, never seven-frame dispatch. -/
theorem body_step_typed {sig : Signature}
    {body : W → Nat → List Value → Option Kont → W → Head → Prop}
    (bl : BodyLaws sig body)
    (ht : StateTyped sig ⟨w,.run code args saved,fs⟩ a)
    (hb : body w code args saved w' head) :
    StateTyped sig ⟨w',head,fs⟩ a := by
  obtain ⟨hole, hh, hs⟩ := ht
  exact ⟨hole, bl.preservation _ _ _ _ _ _ _ hh hb, hs⟩

theorem internal_preservation {sig : Signature} {md : Metadata W}
    {body : W → Nat → List Value → Option Kont → W → Head → Prop}
    (bl : BodyLaws sig body) (ht : StateTyped sig s a) (step : Step md body s t) :
    StateTyped sig t a := by
  cases step with
  | control hc => exact control_preservation ht hc
  | body hb => exact body_step_typed bl ht hb

theorem ret_progress {sig : Signature} {md : Metadata W}
    (hv : ValueTyped v a) (hf : FrameTyped sig f a b) (w : W) (fs : List Frame) :
    ∃ t, ControlStep md ⟨w,.ret v,f::fs⟩ t := by
  cases hf with
  | bind => exact ⟨_, .bindCode⟩
  | scope => exact ⟨_, .scopeRet⟩
  | view => exact ⟨_, .viewRet⟩
  | release => exact ⟨_, .releaseRet⟩
  | handle => exact ⟨_, .handleRet⟩
  | mapper => exact ⟨_, .mapRet⟩
  | wait =>
    cases hv with
    | no => exact ⟨_, .waitNo⟩
    | yes hv => exact ⟨_, .waitYes⟩
  | mapped => exact ⟨_, .mappedRet⟩
  | response => exact ⟨_, .responseRet⟩
  | enterSaved => exact ⟨_, .enterSavedRet⟩

theorem request_progress {sig : Signature} {md : Metadata W} {f : Frame}
    (hf : FrameTyped sig f a b) (p : Packet) (w : W) (fs : List Frame) :
    ∃ t, ControlStep md ⟨w,.req p,f::fs⟩ t := by
  cases f with
  | bind _ =>
    cases hf with
    | bind => exact ⟨_, .bindReq⟩
    | mapped => exact ⟨_, .bindReq⟩
    | response => exact ⟨_, .bindReq⟩
    | enterSaved => exact ⟨_, .bindReq⟩
  | scope _ => cases hf with | scope => exact ⟨_, .scopeReq⟩
  | view _ => cases hf with | view => exact ⟨_, .viewReq⟩
  | release _ => cases hf with | release => exact ⟨_, .releaseReq⟩
  | handle _ => cases hf with | handle => exact ⟨_, .handleReq⟩
  | wait _ _ _ => cases hf with | wait => exact ⟨_, .waitReq⟩
  | mapop mapper =>
    cases hf with
    | mapper _ =>
      cases p with | mk e q p k =>
        by_cases he : q = mapper.source
        · subst q; exact ⟨_, .mapHit⟩
        · exact ⟨_, .mapMiss he⟩
  | originalBind _ => cases hf
  | typedCallBind _ => cases hf
  | typedCallAdapter _ _ _ => cases hf
  | originalBoundary => cases hf

theorem fail_progress {sig : Signature} {md : Metadata W} {f : Frame}
    (hf : FrameTyped sig f a b) (r : Nat) (w : W) (fs : List Frame) :
    ∃ t, ControlStep md ⟨w,.fail r,f::fs⟩ t := by
  have other (g : Frame) (hne : ∀ target, g ≠ .release target) :
      ∃ t, ControlStep md ⟨w,.fail r,g::fs⟩ t := by
    obtain ⟨w', hw⟩ := md.failWorld_total w g
    exact ⟨_, .failFrame hne hw⟩
  cases hf with
  | release => exact ⟨_, .failRelease⟩
  | bind => exact other _ (by intro target he; cases he)
  | scope => exact other _ (by intro target he; cases he)
  | view => exact other _ (by intro target he; cases he)
  | handle => exact other _ (by intro target he; cases he)
  | mapper => exact other _ (by intro target he; cases he)
  | wait => exact other _ (by intro target he; cases he)
  | mapped => exact other _ (by intro target he; cases he)
  | response => exact other _ (by intro target he; cases he)
  | enterSaved => exact other _ (by intro target he; cases he)

theorem search_progress {sig : Signature} {md : Metadata W}
    (search : SearchTyped sig h p arms) (w : W) (fs : List Frame) :
    ∃ t, ControlStep md ⟨w,.search h p arms,fs⟩ t := by
  cases search with
  | value hv values =>
    cases values with
    | nil => exact ⟨_, .searchValueEnd⟩
    | cons => exact ⟨_, .searchValueTry⟩
  | request hp ha =>
    rename_i packet
    cases arms with
    | nil => exact ⟨_, .searchRequestEnd⟩
    | cons arm rest =>
      cases packet with | mk e q p k =>
        by_cases he : arm.operation = q
        · cases ht : md.eligible w h arm (.mk e q p k) with
          | false => exact ⟨_, .skip (.inr ht)⟩
          | true => exact ⟨_, .select he ht⟩
        · exact ⟨_, .skip (.inl he)⟩

/-- A delimited syntax-bearing segment progresses by the original fragment's
actual progress proof; only a source return at the boundary uses originalExit. -/
theorem segment_progress {sig : Signature} {md : Metadata W}
    (hs : SegmentTyped sig s result) : ∃ t, ControlStep md s t := by
  obtain ⟨sourceResult, source, suffix, hhead, hstack, hsource, hsuffix⟩ := hs
  cases s with | mk world head stack =>
    change head = .original source.current at hhead
    change stack = sourceStackEmbedding source.stack suffix at hstack
    cases hhead
    cases hstack
    cases Original.progress hsource with
    | inl terminal =>
      obtain ⟨value, hstate, hvalue⟩ := terminal
      cases source with
      | mk current frames =>
        cases hstate
        simp [sourceStackEmbedding, sourceFramesControl]
        exact ⟨_, .originalExit⟩
    | inr sourceStep =>
      obtain ⟨next, hstep⟩ := sourceStep
      cases hstep with
      | enter =>
        simp [sourceStackEmbedding, sourceFramesControl]
        exact ⟨_, .originalEnter⟩
      | returnBind =>
        simp [sourceStackEmbedding, sourceFramesControl, sourceFrameControl]
        exact ⟨_, .originalReturnBind⟩
      | principal hp =>
        simp [sourceStackEmbedding, sourceFramesControl]
        exact ⟨_, .originalPrincipal hp⟩

/-- Concrete root adapter. No Analysis or permissive dummy certificate is supplied. -/
def machine (md : Metadata W)
    (body : W → Nat → List Value → Option Kont → W → Head → Prop) :
    YulangClosure.Machine (State W) Kont W Value Packet where
  internal := Step md body
  suspended := fun s k => ∃ e q p, s.head = .req (.mk e q p k) ∧ s.stack = []
  current := fun s w => s.world = w
  admissible := fun k _ v => responseOK k.input v = true
  resume := fun k w v s => s = Control.resume k v w
  returned := fun s => (∃ v, s.head = .ret v) ∧ s.stack = []
  requested := fun s => (∃ p, s.head = .req p) ∧ s.stack = []
  failed := fun s => (∃ r, s.head = .fail r) ∧ s.stack = []
  bad := fun s => ∃ r, s.head = .bad r
  exposed := fun s p => s.head = .req p ∧ s.stack = []

/-- Body progress is needed only at registered run heads. All control cases
are discharged by the concrete rules above. -/
theorem progress {sig : Signature} {md : Metadata W}
    {body : W → Nat → List Value → Option Kont → W → Head → Prop}
    (bl : BodyLaws sig body) (ht : StateTyped sig s a) :
    (machine md body).returned s ∨ (machine md body).requested s ∨
    (machine md body).failed s ∨ ∃ t, Step md body s t := by
  cases s with | mk w head stack =>
    obtain ⟨hole, hh, hs⟩ := ht
    cases hh with
    | ret hv =>
      cases hs with
      | nil => exact .inl ⟨⟨_, rfl⟩, rfl⟩
      | cons hf tail =>
        obtain ⟨t, hx⟩ := ret_progress hv hf w _
        exact .inr (.inr (.inr ⟨t, .control hx⟩))
    | req hp =>
      cases hs with
      | nil => exact .inr (.inl ⟨⟨_, rfl⟩, rfl⟩)
      | cons hf tail =>
        obtain ⟨t, hx⟩ := request_progress hf _ w _
        exact .inr (.inr (.inr ⟨t, .control hx⟩))
    | fail =>
      cases hs with
      | nil => exact .inr (.inr (.inl ⟨⟨_, rfl⟩, rfl⟩))
      | cons hf tail =>
        obtain ⟨t, hx⟩ := fail_progress hf _ w _
        exact .inr (.inr (.inr ⟨t, .control hx⟩))
    | run ha hk hc =>
      obtain ⟨w', head', hb⟩ := bl.progress w _ _ _ _ (.run ha hk hc)
      exact .inr (.inr (.inr ⟨_, .body hb⟩))
    | search handler search =>
      obtain ⟨t, hx⟩ := search_progress (md := md) search w _
      exact .inr (.inr (.inr ⟨t, .control hx⟩))

theorem admissible_resume_typed {sig : Signature} {k : Kont}
    (hk : KontTyped sig k q a) (hr : responseOK k.input v = true) (w : W) :
    StateTyped sig (resume k v w) a := by
  cases hk with | mk hs =>
    cases v with
    | atom tag data =>
      simp only [responseOK, Kont.input, beq_iff_eq] at hr
      subst tag
      exact resume_atom_typed (.mk hs) w
    | no => cases hr
    | yes v => cases hr
    | originalValue value => cases hr

/-- This fills the actual root resume-formation field, retaining the current
world and the suspended packet's paired response type. -/
theorem resume_formation {sig : Signature} {md : Metadata W}
    {body : W → Nat → List Value → Option Kont → W → Head → Prop}
    (ht : StateTyped sig s a) (hsp : (machine md body).suspended s k)
    (_hc : (machine md body).current s w) (ha : (machine md body).admissible k w v)
    (hr : (machine md body).resume k w v t) : StateTyped sig t a := by
  obtain ⟨e, q, p, he, hs⟩ := hsp
  obtain ⟨hole, hh, hfs⟩ := ht
  rw [hs] at hfs
  cases hfs
  rw [he] at hh
  cases hh with | req hp =>
    cases hp with | mk hv hk =>
      rw [hr]
      exact admissible_resume_typed hk ha w

theorem machine_preservation {sig : Signature} {md : Metadata W}
    {body : W → Nat → List Value → Option Kont → W → Head → Prop}
    (bl : BodyLaws sig body) (ht : StateTyped sig s a)
    (hx : YulangClosure.Step (machine md body) s t) : StateTyped sig t a := by
  cases hx with
  | internal hi => exact internal_preservation bl ht hi
  | resume hsp hc ha hr => exact resume_formation ht hsp hc ha hr

/-- All finite machine traces include arbitrary legal responses at every
terminal request, without a bound on the number of resumptions. -/
theorem finite_trace_safety {sig : Signature} {md : Metadata W}
    {body : W → Nat → List Value → Option Kont → W → Head → Prop}
    (bl : BodyLaws sig body) (ht : StateTyped sig s a)
    (trace : Prefix (YulangClosure.Step (machine md body)) n s t) :
    StateTyped sig t a ∧ ¬ (machine md body).bad t ∧
      ((machine md body).returned t ∨ (machine md body).requested t ∨
       (machine md body).failed t ∨ ∃ u, (machine md body).internal t u) := by
  have typed : StateTyped sig t a := by
    induction trace with
    | refl => exact ht
    | snoc hp hx ih => exact machine_preservation bl (ih ht) hx
  exact ⟨typed, fun ⟨r, hr⟩ => typed_not_bad typed r hr, progress bl typed⟩

/-- Remaining effect-analysis obligations. These contain no control typing,
preservation, progress, or Bad-exclusion assumptions. They must be supplied by
the actual finite-cell construction; no singleton/all-output instance is made. -/
structure AnalysisLaws (sig : Signature) (md : Metadata W)
    (body : W → Nat → List Value → Option Kont → W → Head → Prop)
    (analysis : Analysis (State W) Cell Packet) (result : Ty)
    (initial : State W → Prop) : Prop where
  initial_seed : ∀ s, initial s → ∃ b, analysis.seed s b ∧ analysis.represents s b
  internal_simulation : ∀ s t b, StateTyped sig s result → analysis.represents s b →
    Step md body s t → ∃ b', analysis.edge b b' ∧ analysis.represents t b'
  resume_simulation : ∀ s t b k w v, StateTyped sig s result → analysis.represents s b →
    (machine md body).suspended s k → (machine md body).current s w →
    (machine md body).admissible k w v → (machine md body).resume k w v t →
    ∃ b', analysis.edge b b' ∧ analysis.represents t b'
  observation : ∀ s b p, StateTyped sig s result → analysis.represents s b →
    (machine md body).exposed s p → analysis.observes b p

/-- The four actual safety fields are proved above, not passed by the caller.
Only registered bodies, initial formation and actual analysis remain parameters. -/
def localLaws (sig : Signature) (md : Metadata W)
    (body : W → Nat → List Value → Option Kont → W → Head → Prop)
    (bl : BodyLaws sig body) (analysis : Analysis (State W) Cell Packet)
    (result : Ty) (initial : State W → Prop)
    (hinit : ∀ s, initial s → StateTyped sig s result)
    (al : AnalysisLaws sig md body analysis result initial) :
    LocalLaws (machine md body) analysis where
  Result := Ty
  result := result
  typing := fun a s => StateTyped sig s a
  initial := initial
  initial_typing := hinit
  initial_seed := al.initial_seed
  internal_preservation := fun _ _ ht hs => internal_preservation bl ht hs
  resume_formation := fun _ _ _ _ _ ht hsp hc ha hr => resume_formation ht hsp hc ha hr
  internal_simulation := al.internal_simulation
  resume_simulation := al.resume_simulation
  observation := al.observation
  no_bad := fun _ ht ⟨r, hr⟩ => typed_not_bad ht r hr
  progress := fun _ ht => progress bl ht

/-- Application to the unchanged root composition theorem with concrete
seven-frame safety, retaining the explicit, uninstantiated analysis boundary. -/
theorem finite_prefix_control (sig : Signature) (md : Metadata W)
    (body : W → Nat → List Value → Option Kont → W → Head → Prop)
    (bl : BodyLaws sig body) (analysis : Analysis (State W) Cell Packet)
    (result : Ty) (initial : State W → Prop)
    (hinit : ∀ s, initial s → StateTyped sig s result)
    (al : AnalysisLaws sig md body analysis result initial)
    (cert : Certificate analysis) (hs : initial s)
    (trace : Prefix (YulangClosure.Step (machine md body)) n s t) :
    Conclusion (machine md body) analysis
      (localLaws sig md body bl analysis result initial hinit al) cert t := by
  exact finite_prefix_composition _ _ _ cert hs trace

/-!
LEAN-CONTROL-20261024/r1, coauthored primary integration after actual producer STOP.

Concrete raw seven-frame rules and independent typing now have exhaustive
control preservation/progress, stack capture, reusable response plugging,
finite raw failure absorption and all-finite-machine-trace safety, including
external responses. Value and operation candidate lists have explicit search
rules. Four safety fields of the unchanged root LocalLaws are constructed;
finite_prefix_control actually applies the existing root composition theorem.

Concrete boundaries (not removed by kernel checking):
* Base value/response tags stand for the declared instance payload/response
  slots. Full recursive/nominal/evidence values and typed graph extension remain.
* Each candidate body is registered Head.run. Pattern/body compilation, direct
  result adapters before Yes, substitution and all principal redexes remain
  BodyLaws obligations. BodyLaws has no frame/search source state.
* Scope/view/release metadata preserve value constructors in this abstraction.
  Actual immutable evidence/current-world laws, release Ret result-route
  transport, L-Enter borrowed/fresh activation and CM/H simulation remain.
* Metadata.failWorld represents unobserved post-Fail cleanup, not a restored
  snapshot. Release.Fail is world identity; failure never becomes No.
* Mapper adapters use ordinary Head.run and bind outside the mapper; their
  effects/failures are not swallowed. The paired target retains event identity.
* Machine.current uses the source state's world. Independently evolved host
  worlds require lawful host-state formation. Kont stores no world and is not
  consumed; resume_reusable allows the same K at arbitrary two current worlds.
* Exposed outputs are terminal requests only. Actual Ret/latent/reentry/event
  output families and AnalysisLaws/certificates have no concrete instance yet.
* Source initial formation, original inference A/B, source/native correspondence,
  principality and inference termination remain open, with the original scope.

Frozen Contracts/CoreComposition definitions are unchanged. Producer was not
kernel-checked; primary owns checking and records exact receipts separately.
No project axioms, sorry/admit, compiler changes, tests or descendants.
-/
end YulangClosure.Control
