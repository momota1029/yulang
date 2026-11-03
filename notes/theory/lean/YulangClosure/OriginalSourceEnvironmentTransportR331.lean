import YulangClosure.OriginalSourceViewRegistrationR330

/-!
R331. Structural transport of original environment data. The new presentation
token names the independently formed R330 definition. Old admission predicates
remain independent. No generated logical admission or source typing is asserted.
Authority: SG §§3.3–5.2; EI §§2,4; generated result correspondence GR1,GR5,GR6.
-/
namespace YulangClosure.OriginalSourceEnvironmentTransportR331
open OriginalSource OriginalScopedClosure OriginalSourceEnvironment
open OriginalSourceInterpretation OriginalInterfacePreservationR328
open OriginalSourceViewRegistrationR330

variable {s : Sorts} {View G : Type}

def views (g : G) (old : View → s.Interface) : Sum View Unit → (extended s G).Interface
  | .inl v => .inl (old v)
  | .inr _ => .inr g

def invocation (d : Invocation s View) : Invocation (extended s G) (Sum View Unit) :=
  ⟨upCurrent d.current, d.value, d.valueRoot, d.context, d.continuation,
    d.carrier, d.carrierRoot, .inl d.view, d.receipt, d.path, d.consumer, d.incidence⟩
def receipt (d : ReceiptData s View) : ReceiptData (extended s G) (Sum View Unit) :=
  ⟨d.receipt, .inl d.view, d.path, d.consumer, d.incidence, upCurrent d.after⟩
def response (d : ResponseData s View) : ResponseData (extended s G) (Sum View Unit) :=
  ⟨d.observation, receipt d.receipt⟩
def runtime : Runtime s View → Runtime (extended s G) (Sum View Unit)
  | .invocation d => .invocation (invocation d)
  | .receipt d => .receipt (receipt d)
  | .returnRebind d => .returnRebind (upOutcome d)
  | .response d => .response (response d)
  | .rigidOperation d => .rigidOperation (upRigid d)
  | .oneShot d => .oneShot (upOutcome d)
def root (g : G) (d : Root s View) : Root (extended s G) (Sum View Unit) :=
  ⟨upAssignment d.assignment, fun e => .inl (d.interfaces e), d.carriers,
    views g d.viewMeaning, fun n => (d.installed n).map upInstalled, d.callOwners⟩
def logical (g : G) (d : Logical s View) : Logical (extended s G) (Sum View Unit) :=
  ⟨d.descriptors, d.interfaces.map (fun e => (e.1, .inl e.2)),
    views g d.viewMeaning, d.eta, d.witness⟩
def payload (g : G) : Payload s View → Payload (extended s G) (Sum View Unit)
  | .root d => .root (root g d)
  | .logical k d => .logical k (logical g d)
  | .shared d => .shared (upShared d)
  | .runtime d => .runtime (runtime d)

theorem views_injective (g : G) : Function.Injective (views (s := s) (View := View) g) := by
  intro a b same
  funext v
  exact Sum.inl.inj (congrFun same (.inl v))

theorem post_injective {A B C : Type} (f : A → B) (inj : Function.Injective f) :
    Function.Injective (fun k : C → A => fun c => f (k c)) := by
  intro a b same
  funext c
  exact inj (congrFun same c)

theorem option_injective {A B : Type} (f : A → B) (inj : Function.Injective f) :
    Function.Injective (Option.map f) := by
  intro a b same
  cases a <;> cases b <;> simp_all [inj.eq_iff]

theorem list_injective {A B : Type} (f : A → B) (inj : Function.Injective f) :
    Function.Injective (List.map f) := by
  intro a
  induction a with
  | nil => intro b same; cases b <;> simp_all
  | cons a rest ih =>
      intro b same
      cases b with
      | nil => simp at same
      | cons b tail =>
          simp only [List.map_cons, List.cons.injEq] at same
          rw [inj same.1, ih same.2]

theorem assignment_injective : Function.Injective (upAssignment (s := s) (G := G)) := by
  intro a b same
  cases a; cases b
  dsimp only [upAssignment] at same
  injection same with event descriptors values roots bindings
  subst_vars
  have event' := congrArg downEvent event
  simp only [down_up_event] at event'
  cases event'
  rfl

theorem root_injective (g : G) : Function.Injective (root (s := s) (View := View) g) := by
  intro a b same
  cases a; cases b
  dsimp only [root] at same
  injection same with assignment interfaces carriers meaning installed owners
  subst_vars
  have assignment' := assignment_injective assignment
  have interfaces' := post_injective Sum.inl (fun _ _ h => Sum.inl.inj h) interfaces
  have meaning' := views_injective g meaning
  have installed' := post_injective _ (option_injective upInstalled installed_injective) installed
  cases assignment'; cases interfaces'; cases meaning'; cases installed'
  rfl

theorem logical_injective (g : G) : Function.Injective (logical (s := s) (View := View) g) := by
  intro a b same
  cases a; cases b
  dsimp only [logical] at same
  injection same with descriptors interfaces meaning eta witness
  subst_vars
  have pairInj : Function.Injective (fun e : Endpoint × s.Interface => (e.1, (Sum.inl e.2 : Sum s.Interface G))) := by
    intro a b h
    cases a; cases b
    simp_all
  have interfaces' := list_injective _ pairInj interfaces
  have meaning' := views_injective g meaning
  cases interfaces'; cases meaning'
  rfl

def downCurrent (d : Current (extended s G)) : Current s := ⟨d.history, d.configuration⟩
@[simp] theorem current_roundtrip (d : Current s) : downCurrent (upCurrent (G := G) d) = d := rfl
theorem current_injective : Function.Injective (upCurrent (s := s) (G := G)) :=
  fun _ _ h => congrArg downCurrent h

theorem invocation_injective : Function.Injective (invocation (s := s) (View := View) (G := G)) := by
  intro a b same
  cases a; cases b
  dsimp only [invocation] at same
  injection same
  all_goals first
    | (apply current_injective; assumption)
    | simp_all [upCurrent]
  all_goals exact congrArg downCurrent (by assumption)
theorem receipt_injective : Function.Injective (receipt (s := s) (View := View) (G := G)) := by
  intro a b same
  cases a; cases b
  dsimp only [receipt] at same
  injection same
  all_goals first
    | (apply current_injective; assumption)
    | simp_all [upCurrent]
  all_goals exact congrArg downCurrent (by assumption)
theorem response_injective : Function.Injective (response (s := s) (View := View) (G := G)) := by
  intro a b same
  cases a; cases b
  dsimp only [response] at same
  injection same with observation rec
  have := receipt_injective rec
  simp_all
theorem object_injective : Function.Injective (upObject (s := s) (G := G)) := by
  intro a b same
  cases a <;> cases b <;> dsimp only [upObject] at same
  all_goals first | contradiction | (injection same; simp_all)
theorem outcome_injective : Function.Injective (upOutcome (s := s) (G := G)) := by
  intro a b same
  cases a; cases b
  dsimp only [upOutcome] at same
  injection same with observation result after endpoints bindings
  subst_vars
  have result' := option_injective _ object_injective result
  have pairInj : Function.Injective (fun e : Endpoint × Object s => (e.1, upObject (G := G) e.2)) := by
    intro a b h
    have := congrArg Prod.fst h
    have := object_injective (congrArg Prod.snd h)
    exact Prod.ext ‹_› ‹_›
  have endpoints' := list_injective _ pairInj endpoints
  cases result'; cases endpoints'
  have after' := current_injective after
  cases after'
  rfl
theorem rigid_injective : Function.Injective (upRigid (s := s) (G := G)) := by
  intro a b same
  cases a; cases b
  dsimp only [upRigid] at same
  injection same
  all_goals first
    | (apply current_injective; assumption)
    | simp_all [upCurrent]
  all_goals exact congrArg downCurrent (by assumption)
theorem shared_injective : Function.Injective (upShared (s := s) (G := G)) := by
  intro a b same
  cases a; cases b
  dsimp only [upShared] at same
  injection same with bindings installed witness
  subst_vars
  have pairInj : Function.Injective (fun e : Nat × Installed s => (e.1, upInstalled (G := G) e.2)) := by
    intro a b h
    have fst : a.1 = b.1 := congrArg (fun e : Nat × Installed (extended s G) => e.1) h
    have snd : a.2 = b.2 := installed_injective (congrArg (fun e : Nat × Installed (extended s G) => e.2) h)
    exact Prod.ext fst snd
  have := list_injective _ pairInj installed
  cases this
  rfl
theorem runtime_injective : Function.Injective (runtime (s := s) (View := View) (G := G)) := by
  intro a b same
  cases a <;> cases b <;> simp only [runtime, Runtime.invocation.injEq,
    Runtime.receipt.injEq, Runtime.returnRebind.injEq, Runtime.response.injEq,
    Runtime.rigidOperation.injEq, Runtime.oneShot.injEq, reduceCtorEq] at same
  all_goals first
    | contradiction
    | exact congrArg _ (invocation_injective same)
    | exact congrArg _ (receipt_injective same)
    | exact congrArg _ (response_injective same)
    | exact congrArg _ (outcome_injective same)
    | exact congrArg _ (rigid_injective same)
theorem payload_injective (g : G) : Function.Injective (payload (s := s) (View := View) g) := by
  intro a b same
  cases a <;> cases b <;> simp only [payload, Payload.root.injEq, Payload.logical.injEq,
    Payload.shared.injEq, Payload.runtime.injEq, reduceCtorEq] at same
  all_goals first
    | contradiction
    | exact congrArg _ (root_injective g same)
    | (rcases same with ⟨rfl, same⟩; exact congrArg _ (logical_injective g same))
    | exact congrArg _ (shared_injective same)
    | exact congrArg _ (runtime_injective same)

def step (g : G) (d : EventStep (Payload s View)) : EventStep (Payload (extended s G) (Sum View Unit)) :=
  ⟨d.source, d.kind, d.occurrence, payload g d.data⟩
def actualEvent (g : G) (d : ActualEvent (Payload s View)) : ActualEvent (Payload (extended s G) (Sum View Unit)) :=
  ⟨d.parents.map (step g), d.occurrence⟩
def scopedValue (g : G) (d : ScopedValue (Payload s View)) : ScopedValue (Payload (extended s G) (Sum View Unit)) :=
  ⟨payload g d.data, actualEvent g d.event⟩
def frame (g : G) (d : Frame (Payload s View)) : Frame (Payload (extended s G) (Sum View Unit)) :=
  ⟨d.binder, scopedValue g d.value, d.entryPath.map (step g)⟩
def anchorKey (g : G) (d : AnchorKey (Payload s View)) : AnchorKey (Payload (extended s G) (Sum View Unit)) :=
  ⟨d.origin, d.path.map (step g), d.binder⟩
def publicationId (g : G) (d : PublicationId (Payload s View)) : PublicationId (Payload (extended s G) (Sum View Unit)) :=
  ⟨d.origin, d.site, d.path.map (step g)⟩
def names (g : G) (d : List (Name × PublicationId (Payload s View))) :=
  d.map (fun e => (e.1, publicationId g e.2))
def initializer (g : G) (d : InitializerEntry (Payload s View)) : InitializerEntry (Payload (extended s G) (Sum View Unit)) :=
  ⟨d.site, d.path.map (step g), names g d.names, d.frames.map (frame g)⟩
def publicationRecord (g : G) (d : PublicationRecord (Payload s View)) : PublicationRecord (Payload (extended s G) (Sum View Unit)) :=
  ⟨publicationId g d.identity, d.entryPath.map (step g), names g d.entryNames,
    d.entryFrames.map (frame g), names g d.captures, d.fixedFrames.map (frame g),
    d.initializers.map (initializer g)⟩

theorem step_injective (g : G) : Function.Injective (step (s := s) (View := View) g) := by
  intro a b h
  cases a; cases b
  dsimp only [step] at h
  injection h with source kind occurrence data
  have := payload_injective g data
  simp_all

theorem actualEvent_injective (g : G) : Function.Injective (actualEvent (s := s) (View := View) g) := by
  intro a b h
  cases a; cases b
  dsimp only [actualEvent] at h
  injection h with parents occurrence
  have := list_injective _ (step_injective g) parents
  simp_all

theorem scopedValue_injective (g : G) : Function.Injective (scopedValue (s := s) (View := View) g) := by
  intro a b h
  cases a; cases b
  dsimp only [scopedValue] at h
  injection h with data event
  have := payload_injective g data
  have := actualEvent_injective g event
  simp_all

theorem frame_injective (g : G) : Function.Injective (frame (s := s) (View := View) g) := by
  intro a b h
  cases a; cases b
  dsimp only [frame] at h
  injection h with binder value path
  have := scopedValue_injective g value
  have := list_injective _ (step_injective g) path
  simp_all

theorem anchorKey_injective (g : G) : Function.Injective (anchorKey (s := s) (View := View) g) := by
  intro a b h
  cases a; cases b
  dsimp only [anchorKey] at h
  injection h with origin path binder
  have := list_injective _ (step_injective g) path
  simp_all

theorem publicationId_injective (g : G) : Function.Injective (publicationId (s := s) (View := View) g) := by
  intro a b h
  cases a; cases b
  dsimp only [publicationId] at h
  injection h with origin site path
  have := list_injective _ (step_injective g) path
  simp_all

/-- Partial inverse on the exact structural image. No old sort inhabitant is
chosen for a generated value. -/
noncomputable def preimage {A B : Type} (f : A → B) (b : B) : Option A := by
  classical
  exact if h : ∃ a, f a = b then some h.choose else none

@[simp] theorem preimage_image {A B : Type} (f : A → B) (inj : Function.Injective f) (a : A) :
    preimage f (f a) = some a := by
  classical
  simp only [preimage, dite_eq_left (show ∃ a', f a' = f a from ⟨a, rfl⟩)]
  exact congrArg some (inj (Exists.choose_spec (show ∃ a', f a' = f a from ⟨a, rfl⟩)))

theorem preimage_sound {A B : Type} (f : A → B) {b : B} {a : A}
    (found : preimage f b = some a) : f a = b := by
  classical
  unfold preimage at found
  split at found
  next h =>
    have same := Option.some.inj found
    exact same ▸ h.choose_spec
  next h => contradiction

noncomputable def environment (g : G) (old : Environment (Payload s View)) :
    Environment (Payload (extended s G) (Sum View Unit)) where
  root := payload g old.root
  anchors key := match preimage (anchorKey g) key with
    | some oldKey => scopedValue g (old.anchors oldKey)
    | none => ⟨payload g old.root, ⟨[], 0⟩⟩
  publications key := (preimage (publicationId g) key).bind fun oldKey =>
    (old.publications oldKey).map (publicationRecord g)
  origin := old.origin
  eventPath := old.eventPath.map (step g)
  names := names g old.names
  frames := old.frames.map (frame g)
  replay := old.replay.map (List.map (frame g))
  initializers := old.initializers.map (initializer g)

theorem anchors_preserved (g : G) (old : Environment (Payload s View)) (key : AnchorKey (Payload s View)) :
    (environment g old).anchors (anchorKey g key) = scopedValue g (old.anchors key) := by
  simp only [environment, preimage_image _ (anchorKey_injective g)]

theorem publications_preserved (g : G) (old : Environment (Payload s View)) (key : PublicationId (Payload s View)) :
    (environment g old).publications (publicationId g key) =
      (old.publications key).map (publicationRecord g) := by
  simp only [environment, preimage_image _ (publicationId_injective g), Option.bind_some]

theorem extension_commutes (g : G) (old : Environment (Payload s View))
    (binder : Binder) (candidate : ScopedValue (Payload s View)) :
    environment g (old.extend binder candidate) =
      (environment g old).extend binder (scopedValue g candidate) := by
  cases binder with | mk site kind index =>
    cases kind <;> simp [environment, Environment.extend, ActualEvent.path,
      frame, scopedValue, actualEvent, step, Binder.isEvent, List.map_append]

def decoded (g : G) (d : Decoded s View) : Decoded (extended s G) (Sum View Unit) :=
  ⟨upAssignment d.assignment, fun e => .inl (d.interfaces e), d.carriers,
    views g d.viewMeaning, fun n => (d.installed n).map upInstalled,
    d.active.map upCall, d.activeRaw.map invocation, d.fixedFrames.map (frame g), d.callOwners⟩

noncomputable def readout (g : G) (old : RuntimeReadout s View) :
    RuntimeReadout (extended s G) (Sum View Unit) where
  eta fs e b d := match preimage (List.map (frame g)) fs, preimage runtime d with
    | some fs, some d => old.eta fs (downEvent e) b d
    | _, _ => e.eta
  witness fs e b d := match preimage (List.map (frame g)) fs, preimage runtime d with
    | some fs, some d => old.witness fs (downEvent e) b d
    | _, _ => e.witness
  scope fs e b d := match preimage (List.map (frame g)) fs, preimage runtime d with
    | some fs, some d => old.scope fs (downEvent e) b d
    | _, _ => e.scope
  authority fs e b d := match preimage (List.map (frame g)) fs, preimage runtime d with
    | some fs, some d => old.authority fs (downEvent e) b d
    | _, _ => e.authority
  incidence fs e b d := match preimage (List.map (frame g)) fs, preimage runtime d with
    | some fs, some d => old.incidence fs (downEvent e) b d
    | _, _ => e.incidence
  dictionary fs e b d := match preimage (List.map (frame g)) fs, preimage runtime d with
    | some fs, some d => old.dictionary fs (downEvent e) b d
    | _, _ => e.dictionary

@[simp] theorem runtime_after (d : Runtime s View) :
    (runtime (G := G) d).after = d.after.map upCurrent := by cases d <;> rfl

theorem event_commutes (g : G) (old : RuntimeReadout s View)
    (fs : List (Frame (Payload s View))) (e : Event s) (b : Binder) (d : Runtime s View) :
    (readout g old).event (fs.map (frame g)) (upEvent e) b (runtime d) =
      upEvent (old.event fs e b d) := by
  simp only [RuntimeReadout.event, readout,
    preimage_image _ (list_injective _ (frame_injective g)),
    preimage_image _ runtime_injective, down_up_event, runtime_after]
  cases d <;> rfl

theorem put_map {K A B : Type} [DecidableEq K] (f : A → B)
    (base : K → A) (entries : List (K × A)) :
    put (fun k => f (base k)) (entries.map (fun e => (e.1, f e.2))) =
      fun k => f (put base entries k) := by
  induction entries generalizing base with
  | nil => rfl
  | cons first rest ih =>
      change put (fun k => if k = first.1 then f first.2 else f (base k))
        (rest.map (fun e => (e.1, f e.2))) =
          fun k => f (put (fun k => if k = first.1 then first.2 else base k) rest k)
      have same : (fun k => if k = first.1 then f first.2 else f (base k)) =
          (fun k => f (if k = first.1 then first.2 else base k)) := by
        funext k
        split <;> rfl
      rw [same, ih]

theorem logical_commutes (g : G) (state : Decoded s View) (data : Logical s View) :
    decoded g (state.logical data) = (decoded g state).logical (logical g data) := by
  have interfaces := put_map (fun x : s.Interface => (Sum.inl x : Sum s.Interface G))
    state.interfaces data.interfaces
  simp only [decoded, Decoded.logical, logical, upAssignment, upEvent]
  congr 1
  exact interfaces.symm

theorem shared_commutes (g : G) (state : Decoded s View) (data : Shared s) :
    decoded g (state.shared data) = (decoded g state).shared (upShared data) := by
  simp only [decoded, Decoded.shared, upShared, upAssignment, List.map_map,
    Function.comp_def]
  have same := put_map (fun x : Option (Installed s) => x.map (upInstalled (G := G)))
    state.installed (data.installed.map (fun e => (e.1, some e.2)))
  simpa only [List.map_map, Function.comp_def, Option.map_some, upAssignment] using congrArg
    (fun inst => (⟨upAssignment {state.assignment with
        binding := put state.assignment.binding (data.bindings.map fun e => (e.1, some e.2))},
      fun e => Sum.inl (state.interfaces e), state.carriers, views g state.viewMeaning,
      inst, state.active.map upCall, state.activeRaw.map invocation,
      state.fixedFrames.map (frame g), state.callOwners⟩ : Decoded (extended s G) (Sum View Unit))) same.symm

theorem object_commutes (g : G) (state : Decoded s View) (entry : Endpoint × Object s) :
    decoded g (state.object entry) = (decoded g state).object (entry.1, upObject entry.2) := by
  rcases entry with ⟨e, object⟩
  cases object <;> rfl

theorem objects_commute (g : G) (state : Decoded s View) (entries : List (Endpoint × Object s)) :
    decoded g (entries.foldl Decoded.object state) =
      (entries.map (fun e => (e.1, upObject e.2))).foldl Decoded.object (decoded g state) := by
  induction entries generalizing state with
  | nil => rfl
  | cons first rest ih => rw [List.foldl_cons, List.map_cons, List.foldl_cons, ih, object_commutes]

theorem runtime_endpoints (data : Runtime s View) :
    (runtime (G := G) data).endpoints = data.endpoints.map (fun e => (e.1, upObject e.2)) := by
  cases data <;> rfl

theorem runtime_commutes (g : G) (old : RuntimeReadout s View)
    (state : Decoded s View) (binder : Binder) (data : Runtime s View) :
    decoded g (state.runtime old binder data) =
      (decoded g state).runtime (readout g old) binder (runtime data) := by
  have ev := event_commutes g old state.fixedFrames state.assignment.event binder data
  cases data <;>
    simp only [Decoded.runtime, runtime, Runtime.endpoints, Runtime.bindings,
      upOutcome, upRigid, response, receipt]
  all_goals try rw [← objects_commute]
  all_goals simp only [decoded, upAssignment]
  all_goals simp only [runtime, upOutcome, upRigid, response, receipt] at ev
  all_goals simp only [ev]
  all_goals simp only [Invocation.challenge, Invocation.decorate, invocation, views,
    upCall, upEvent, Challenge.input, Option.map_some, List.foldl_nil]
  all_goals simp only [invocation, upEvent] at ev
  all_goals simp only [ev]
  all_goals rfl

theorem retain_commutes (g : G) (state : Decoded s View) (entry : Frame (Payload s View)) :
    decoded g (state.retain entry) = (decoded g state).retain (frame g entry) := by
  simp only [Decoded.retain, decoded, List.map_append, List.map_cons, List.map_nil]

theorem frame_commutes (g : G) (old : RuntimeReadout s View)
    (state : Decoded s View) (entry : Frame (Payload s View)) :
    decoded g (decodeFrame old state entry) =
      decodeFrame (readout g old) (decoded g state) (frame g entry) := by
  cases data : entry.value.data with
  | root d => simp only [decodeFrame, frame, scopedValue, payload, data]
  | logical k d =>
      simp only [decodeFrame, frame, scopedValue, payload, data]
      exact logical_commutes g state d
  | shared d =>
      simpa only [decodeFrame, frame, scopedValue, payload, data] using
        (retain_commutes g (state.shared d) entry).trans
          (congrArg (fun st => st.retain (frame g entry)) (shared_commutes g state d))
  | runtime d =>
      simpa only [decodeFrame, frame, scopedValue, payload, data] using
        (retain_commutes g (state.runtime old entry.binder d) entry).trans
          (congrArg (fun st => st.retain (frame g entry)) (runtime_commutes g old state entry.binder d))

theorem frames_commute (g : G) (old : RuntimeReadout s View)
    (state : Decoded s View) (entries : List (Frame (Payload s View))) :
    decoded g (entries.foldl (decodeFrame old) state) =
      (entries.map (frame g)).foldl (decodeFrame (readout g old)) (decoded g state) := by
  induction entries generalizing state with
  | nil => rfl
  | cons first rest ih => rw [List.foldl_cons, List.map_cons, List.foldl_cons, ih, frame_commutes]

theorem decode_commutes (g : G) (old : RuntimeReadout s View)
    (env : Environment (Payload s View)) :
    decode (readout g old) (environment g env) = (decode old env).map (decoded g) := by
  cases data : env.root <;> simp only [decode, environment, payload, data, Option.map_none]
  case root d =>
    rw [Option.map_some]
    exact congrArg some (frames_commute g old d.decoded env.frames).symm

def callPreimage (d : CallInput (extended s G)) : Option (CallInput s) :=
  match d.carrierView with
  | .inl i => some (downCall d i)
  | .inr _ => none
@[simp] theorem call_roundtrip (d : CallInput s) : callPreimage (upCall (G := G) d) = some d := rfl

theorem call_injective : Function.Injective (upCall (s := s) (G := G)) := by
  intro a b h
  exact Option.some.inj (congrArg callPreimage h)

theorem decoded_injective (g : G) : Function.Injective (decoded (s := s) (View := View) g) := by
  intro a b h
  cases a; cases b
  dsimp only [decoded] at h
  injection h with assignment interfaces carriers meaning installed active raw fixed owners
  have := assignment_injective assignment
  have := post_injective Sum.inl (fun _ _ h => Sum.inl.inj h) interfaces
  have := views_injective g meaning
  have := post_injective _ (option_injective upInstalled installed_injective) installed
  have := option_injective _ call_injective active
  have := option_injective _ invocation_injective raw
  have := list_injective _ (frame_injective g) fixed
  simp_all

/-- Each local source relation is pulled back on its exact original image.
This conservative instance does not grant admission to nonimage data. It is
not a proof that native/source owner laws select this extended instance. -/
noncomputable def admissions (g : G) (old : LocalAdmissions s View) :
    LocalAdmissions (extended s G) (Sum View Unit) where
  logical state b k data := ∃ a d, decoded g a = state ∧ logical g d = data ∧ old.logical a b k d
  shared state b data := ∃ a d, decoded g a = state ∧ upShared d = data ∧ old.shared a b d
  receipt state b data := ∃ a d, decoded g a = state ∧ receipt d = data ∧ old.receipt a b d
  returnRebind state b data := ∃ a d, decoded g a = state ∧ upOutcome d = data ∧ old.returnRebind a b d
  response state b data := ∃ a d, decoded g a = state ∧ response d = data ∧ old.response a b d
  rigidOperation state b data := ∃ a d, decoded g a = state ∧ upRigid d = data ∧ old.rigidOperation a b d
  oneShot state b data := ∃ a d, decoded g a = state ∧ upOutcome d = data ∧ old.oneShot a b d

theorem image_relation {A B C D : Type} (f : A → B) (fi : Function.Injective f)
    (g : C → D) (gi : Function.Injective g) (R : A → C → Prop) (a : A) (c : C) :
    (∃ a' c', f a' = f a ∧ g c' = g c ∧ R a' c') ↔ R a c := by
  constructor
  · rintro ⟨a', c', ha, hc, valid⟩
    exact fi ha ▸ gi hc ▸ valid
  · intro valid
    exact ⟨a, c, rfl, rfl, valid⟩

theorem logical_admission_preserved (g : G) (old : LocalAdmissions s View)
    (state : Decoded s View) (b : Binder) (k : LogicalKind) (d : Logical s View) :
    (admissions g old).logical (decoded g state) b k (logical g d) ↔ old.logical state b k d :=
  image_relation _ (decoded_injective g) _ (logical_injective g) _ _ _

theorem data_admission_preserved (g : G) (base : Inputs s) (gen : Generated s G)
    (oldReadout : RuntimeReadout s View) (old : LocalAdmissions s View)
    (state : Decoded s View) (b : Binder) (data : Payload s View) :
    DataAdmitted (inputs base gen) (readout g oldReadout) (admissions g old)
      (decoded g state) b (payload g data) ↔
        DataAdmitted base oldReadout old state b data := by
  cases data with
  | root d => rfl
  | logical k d => exact and_congr Iff.rfl (logical_admission_preserved g old state b k d)
  | shared d => exact and_congr Iff.rfl (image_relation _ (decoded_injective g) _ shared_injective _ _ _)
  | runtime d =>
      cases d with
      | invocation call =>
          simp only [payload, runtime, DataAdmitted]
          have evt := event_commutes g oldReadout state.fixedFrames state.assignment.event b (.invocation call)
          change _ ∧ _ ∧ _ ∧ CheckedDomain (inputs base gen)
            ((invocation call).challenge
              ((readout g oldReadout).event (state.fixedFrames.map (frame g)) (upEvent state.assignment.event) b (runtime (.invocation call)))
              (state.callRow b).descriptor (views g state.viewMeaning)) ↔ _
          rw [evt]
          exact Iff.rfl
      | receipt d => exact and_congr Iff.rfl (image_relation _ (decoded_injective g) _ receipt_injective _ _ _)
      | returnRebind d => exact and_congr Iff.rfl (image_relation _ (decoded_injective g) _ outcome_injective _ _ _)
      | response d => exact and_congr Iff.rfl (image_relation _ (decoded_injective g) _ response_injective _ _ _)
      | rigidOperation d => exact and_congr Iff.rfl (image_relation _ (decoded_injective g) _ rigid_injective _ _ _)
      | oneShot d => exact and_congr Iff.rfl (image_relation _ (decoded_injective g) _ outcome_injective _ _ _)

theorem admission_preserved (g : G) (base : Inputs s) (gen : Generated s G)
    (oldReadout : RuntimeReadout s View) (old : LocalAdmissions s View)
    (env : Environment (Payload s View)) (b : Binder) (candidate : ScopedValue (Payload s View)) :
    Admitted (inputs base gen) (readout g oldReadout) (admissions g old)
      (environment g env) b (scopedValue g candidate) ↔
        Admitted base oldReadout old env b candidate := by
  unfold Admitted
  rw [decode_commutes]
  change (candidate.event.parents.map (step g) = env.eventPath.map (step g) ∧ _) ↔ _
  constructor
  · rintro ⟨parents, state, found, valid⟩
    obtain ⟨before, decodedBefore, rfl⟩ := Option.map_eq_some_iff.mp found
    exact ⟨list_injective _ (step_injective g) parents, before, decodedBefore,
      (data_admission_preserved g base gen oldReadout old before b candidate.data).mp valid⟩
  · rintro ⟨parents, state, found, valid⟩
    refine ⟨congrArg (List.map (step g)) parents, decoded g state, ?_, ?_⟩
    · rw [found]; rfl
    · exact (data_admission_preserved g base gen oldReadout old state b candidate.data).mpr valid

theorem decode_image_iff (g : G) (old : RuntimeReadout s View)
    (env : Environment (Payload s View)) (state : Decoded s View) :
    decode (readout g old) (environment g env) = some (decoded g state) ↔
      decode old env = some state := by
  rw [decode_commutes]
  constructor
  · intro found
    obtain ⟨before, original, same⟩ := Option.map_eq_some_iff.mp found
    exact decoded_injective g same ▸ original
  · intro found
    rw [found]
    rfl

theorem choose_preserved (g : G) (env : Environment (Payload s View))
    (b : Binder) (c : ScopedValue (Payload s View)) :
    (environment g env).choose b (scopedValue g c) = scopedValue g (env.choose b c) := rfl

theorem anchorValue_preserved (g : G) (env : Environment (Payload s View)) (b : Binder) :
    (environment g env).anchorValue b = scopedValue g (env.anchorValue b) :=
  anchors_preserved g env (env.anchorKey b)

theorem initializer_commutes (g : G) (env : Environment (Payload s View)) (site : Site) :
    environment g (env.enterInitializer site) = (environment g env).enterInitializer site := by
  simp only [environment, Environment.enterInitializer, initializer, List.map_cons,
    List.filter_map, Function.comp_def, frame]

theorem restore_commutes (g : G) (env : Environment (Payload s View))
    (record : PublicationRecord (Payload s View)) :
    environment g (env.restore record) =
      (environment g env).restore (publicationRecord g record) := by
  simp only [environment, Environment.restore, publicationRecord, List.map_append,
    List.filter_map, Function.comp_def, frame, publicationId, Option.map_some]

/-- Every candidate is still independently admitted at its own original
predecessor environment. No strategy lookup substitutes for a candidate. -/
def PrefixAdmitted (base : Inputs s) (ro : RuntimeReadout s View)
    (adm : LocalAdmissions s View) : Environment (Payload s View) →
      List (Binder × ScopedValue (Payload s View)) → Prop
  | _, [] => True
  | env, (b,c) :: rest => Admitted base ro adm env b c ∧
      PrefixAdmitted base ro adm (env.extend b c) rest

def runPrefix (env : Environment V) (steps : List (Binder × ScopedValue V)) : Environment V :=
  steps.foldl (fun e bc => e.extend bc.1 bc.2) env

def prefixImage (g : G) (steps : List (Binder × ScopedValue (Payload s View))) :=
  steps.map (fun bc => (bc.1, scopedValue g bc.2))

theorem prefix_commutes (g : G) (env : Environment (Payload s View))
    (steps : List (Binder × ScopedValue (Payload s View))) :
    environment g (runPrefix env steps) = runPrefix (environment g env) (prefixImage g steps) := by
  induction steps generalizing env with
  | nil => rfl
  | cons first rest ih =>
      change environment g (runPrefix (env.extend first.1 first.2) rest) = _
      rw [ih, extension_commutes]
      rfl

theorem prefix_admission_preserved (g : G) (base : Inputs s) (gen : Generated s G)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (env : Environment (Payload s View)) (steps : List (Binder × ScopedValue (Payload s View))) :
    PrefixAdmitted (inputs base gen) (readout g ro) (admissions g adm)
      (environment g env) (prefixImage g steps) ↔ PrefixAdmitted base ro adm env steps := by
  induction steps generalizing env with
  | nil => rfl
  | cons first rest ih =>
      simp only [prefixImage, List.map_cons, PrefixAdmitted]
      rw [← extension_commutes]
      exact and_congr (admission_preserved g base gen ro adm env first.1 first.2) (ih _)

/-- The seven binders actually enclosing R330's selected owner. The source
allocator, rather than an arbitrary owner-position premise, supplies this list. -/
def selectedBinders : List Binder :=
  [⟨98,.description,0⟩, ⟨0,.viewLogic,0⟩, ⟨0,.invocation,0⟩,
   ⟨98,.receipt,0⟩, ⟨98,.returnRebind,0⟩, ⟨98,.shared,0⟩, ⟨1,.eventProof,0⟩]

theorem selected_source_telescope (origin : Declaration) :
    (owner origin).position.telescope =
      [.existsE (selectedBinders[0]'(by decide)), .existsE (selectedBinders[1]'(by decide)),
       .forallE (selectedBinders[2]'(by decide)), .existsE (selectedBinders[3]'(by decide)),
       .executionE (selectedBinders[4]'(by decide)), .sharedE (selectedBinders[5]'(by decide)),
       .existsE (selectedBinders[6]'(by decide))] := by rfl

theorem prefix_decodes (ro : RuntimeReadout s View)
    (env : Environment (Payload s View)) (state : Decoded s View)
    (found : decode ro env = some state)
    (steps : List (Binder × ScopedValue (Payload s View))) :
    ∃ after, decode ro (runPrefix env steps) = some after := by
  induction steps generalizing env state with
  | nil => exact ⟨state, found⟩
  | cons first rest ih =>
      exact ih (env.extend first.1 first.2) _ (decode_extend ro env first.1 first.2 state found)

/-- Apply the original decoder along the full original selected prefix and
then R330's actual registration. Every runPrefix admission is transported as an
iff. This lemma does not extract a reachable runPrefix from a vacuous source
forall, nor establish the generated logical admission or any target Checking. -/
theorem selected_prefix_registration {origin : Declaration} {declared : ComputedCallTypedFormationR310.Key → Prop}
    (definition : Definition origin declared) (base : Inputs s)
    (gen : Generated s Code) (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (env : Environment (Payload s View)) (state : Decoded s View)
    (found : decode ro env = some state)
    (steps : List (Binder × ScopedValue (Payload s View)))
    (actualBinders : steps.map Prod.fst = selectedBinders)
    (accepted : PrefixAdmitted base ro adm env steps)
    (data : Logical s View) (occurrence : Nat) :
    (prefixImage definition.code steps).map Prod.fst = selectedBinders ∧
    PrefixAdmitted (inputs base gen) (readout definition.code ro) (admissions definition.code adm)
      (environment definition.code env) (prefixImage definition.code steps) ∧
    (owner origin).position.telescope =
      [.existsE (selectedBinders[0]'(by decide)), .existsE (selectedBinders[1]'(by decide)),
       .forallE (selectedBinders[2]'(by decide)), .existsE (selectedBinders[3]'(by decide)),
       .executionE (selectedBinders[4]'(by decide)), .sharedE (selectedBinders[5]'(by decide)),
       .existsE (selectedBinders[6]'(by decide))] ∧
    (decode (readout definition.code ro)
      ((runPrefix (environment definition.code env) (prefixImage definition.code steps)).extend
        (owner origin).binder
        (scopeCandidate (runPrefix (environment definition.code env) (prefixImage definition.code steps))
          occurrence (definedPayload data definition)))).map
            (fun after => after.viewMeaning (.inr ())) = some (.inr definition.code) := by
  obtain ⟨after, afterFound⟩ := prefix_decodes ro env state found steps
  have mapped : decode (readout definition.code ro)
      (runPrefix (environment definition.code env) (prefixImage definition.code steps)) =
        some (decoded definition.code after) := by
    rw [← prefix_commutes, decode_commutes, afterFound]
    rfl
  refine ⟨?_, (prefix_admission_preserved definition.code base gen ro adm env steps).mpr accepted,
    selected_source_telescope origin,
    actual_decoder_generated_view (readout definition.code ro) _ _ mapped data definition occurrence⟩
  simpa only [prefixImage, List.map_map, Function.comp_def] using actualBinders

abbrev selectedContext := OriginalScopedSourceEventMapR314.Fixture.localContext
  OriginalModuleContextBindingR315.externalContext
abbrev selectedSource := OriginalScopedSourceEventMapR314.Fixture.selected

def SelectedContinuation (kernel : Kernel V) (env : Environment V) : Prop :=
  let b : Binder := ⟨98,.shared,0⟩
  let shared := env.anchorValue b
  let after := env.extend b shared
  kernel.admitted env b shared ∧ ∃ eventProof,
    kernel.admitted after ⟨1,.eventProof,0⟩ eventProof ∧
    SourceJudgment kernel (after.extend ⟨1,.eventProof,0⟩ eventProof) selectedContext selectedSource

def ReturnContinuations (kernel : Kernel V) (env : Environment V) : Prop :=
  let b : Binder := ⟨98,.returnRebind,0⟩
  match env.replay with
  | none => ∀ returned, kernel.admitted env b returned →
      SelectedContinuation kernel (env.extend b returned)
  | some _ => ∃ returned, env.executionValue b = some returned ∧
      kernel.admitted env b returned ∧ SelectedContinuation kernel (env.extend b returned)

/-- Invert the ACTUAL accepted root source rule. Universal invocation and
open-return domains are unchanged; fixed replay keeps its genuine lookup.
Vacuous invocation admission yields a universal continuation, not a fictitious
reachable selected environment. Every returned source proof is original. -/
theorem original_source_prefix_alternatives (kernel : Kernel V) (env : Environment V)
    (sourceProof : SourceJudgment kernel env OriginalModuleContextBindingR315.externalContext
      OriginalScopedSourceEventMapR314.Fixture.root) :
    ∃ description outerView,
      kernel.admitted env ⟨98,.description,0⟩ description ∧
      let afterDescription := env.extend ⟨98,.description,0⟩ description
      kernel.admitted afterDescription ⟨0,.viewLogic,0⟩ outerView ∧
      let afterView := afterDescription.extend ⟨0,.viewLogic,0⟩ outerView
      ∀ call, kernel.admitted afterView ⟨0,.invocation,0⟩ call →
        let afterCall := afterView.extend ⟨0,.invocation,0⟩ call
        ∃ received, kernel.admitted afterCall ⟨98,.receipt,0⟩ received ∧
          ReturnContinuations kernel (afterCall.extend ⟨98,.receipt,0⟩ received) := by
  simp only [SourceJudgment, OriginalScopedSourceEventMapR314.Fixture.root, sourceRules] at sourceProof
  cases sourceProof with
  | existsE description admittedDescription descriptionProof =>
    cases descriptionProof with
    | existsE outerView admittedView viewProof =>
      refine ⟨description, outerView, admittedDescription, admittedView, ?_⟩
      cases viewProof with
      | rule _ children =>
        cases children with
        | cons invocationProof _ =>
          cases invocationProof with
          | forallE alternatives =>
            dsimp only
            intro call admittedCall
            have callProof := alternatives call admittedCall
            cases callProof with
            | existsE received admittedReceipt receiptProof =>
              refine ⟨received, admittedReceipt, ?_⟩
              cases receiptProof with
              | rule _ children =>
                cases children with
                | cons executionProof _ =>
                  cases executionProof with
                  | executionOpen openHistory alternatives =>
                    simp only [ReturnContinuations, openHistory]
                    intro returned admittedReturn
                    have sharedProof := alternatives returned admittedReturn
                    cases sharedProof with
                    | sharedE admittedShared sharedBody =>
                      refine ⟨admittedShared, ?_⟩
                      cases sharedBody with
                      | rule _ children =>
                        cases children with
                        | cons _ rest =>
                          cases rest with
                          | cons eventProof _ =>
                            cases eventProof with
                            | existsE eventData admittedEvent eventBody =>
                              refine ⟨eventData, admittedEvent, ?_⟩
                              cases eventBody with
                              | rule _ children =>
                                cases children with
                                | cons selectedProof _ => exact selectedProof
                  | executionFixed history fixedHistory returned lookup admittedReturn sharedProof =>
                    simp only [ReturnContinuations, fixedHistory]
                    refine ⟨returned, lookup, admittedReturn, ?_⟩
                    cases sharedProof with
                    | sharedE admittedShared sharedBody =>
                      refine ⟨admittedShared, ?_⟩
                      cases sharedBody with
                      | rule _ children =>
                        cases children with
                        | cons _ rest =>
                          cases rest with
                          | cons eventProof _ =>
                            cases eventProof with
                            | existsE eventData admittedEvent eventBody =>
                              refine ⟨eventData, admittedEvent, ?_⟩
                              cases eventBody with
                              | rule _ children =>
                                cases children with
                                | cons selectedProof _ => exact selectedProof

theorem publicationName_preserved (g : G) (env : Environment (Payload s View)) (name : Name) :
    (environment g env).publicationName name = (env.publicationName name).map (publicationId g) := by
  simp only [Environment.publicationName, environment, names, List.find?_map,
    Option.map_map, Function.comp_def]

theorem alias_commutes (g : G) (env next : Environment (Payload s View)) (a b : Name)
    (aliased : env.aliasPublication a b = some next) :
    (environment g env).aliasPublication a b = some (environment g next) := by
  cases named : env.publicationName a with
  | none => simp only [Environment.aliasPublication, named] at aliased; contradiction
  | some identity =>
    simp only [Environment.aliasPublication, named, Option.pure_def] at aliased
    cases aliased
    rw [Environment.aliasPublication, publicationName_preserved, named]
    rfl

attribute [local instance] Classical.propDecidable

theorem execution_find_preserved (g : G) (env : Environment (Payload s View))
    (saved : List (Frame (Payload s View))) (b : Binder) :
    (saved.map (frame g)).find? (fun f => decide (f.binder = b ∧
        f.entryPath = (env.eventPath.map (step g)))) =
      (saved.find? (fun f => decide (f.binder = b ∧ f.entryPath = env.eventPath))).map (frame g) := by
  classical
  rw [List.find?_map]
  congr 2
  funext f
  change decide (f.binder = b ∧ f.entryPath.map (step g) = env.eventPath.map (step g)) = _
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]

  exact and_congr Iff.rfl ⟨fun h => list_injective _ (step_injective g) h, congrArg (List.map (step g))⟩

theorem executionValue_preserved (g : G) (env : Environment (Payload s View)) (b : Binder) :
    (environment g env).executionValue b = (env.executionValue b).map (scopedValue g) := by
  classical
  cases saved : env.replay with
  | none => simp only [Environment.executionValue, environment, saved, Option.map_none, Option.bind_eq_bind, Option.bind_none]
  | some history =>
    simp only [Environment.executionValue, environment, saved, Option.map_some, Option.bind_eq_bind, Option.bind_some,
      execution_find_preserved]
    cases history.find? (fun f => decide (f.binder = b ∧ f.entryPath = env.eventPath)) <;> rfl

/-- Apply R330's own original-admission boundary after the decoded ORIGINAL
prefix. The transported instance reflects precisely the independent old
logical law; this is not a concrete proof of that law or native instance. -/
theorem original_parent_admission {origin : Declaration} {declared : ComputedCallTypedFormationR310.Key → Prop}
    (definition : Definition origin declared) (base : Inputs s) (gen : Generated s Code)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (env : Environment (Payload s View)) (state : Decoded s View)
    (found : decode ro env = some state) (data : Logical s View) (occurrence : Nat) :
    Admitted (inputs base gen) (readout definition.code ro) (admissions definition.code adm)
      (environment definition.code env) (owner origin).binder
      (scopeCandidate (environment definition.code env) occurrence (definedPayload data definition)) ↔
      adm.logical state (owner origin).binder .viewLogic data := by
  have mapped : decode (readout definition.code ro) (environment definition.code env) =
      some (decoded definition.code state) := by rw [decode_commutes, found]; rfl
  rw [parent_admission_obligation (inputs base gen) (readout definition.code ro)
    (admissions definition.code adm) (environment definition.code env)
    (decoded definition.code state) mapped data definition occurrence]
  exact logical_admission_preserved definition.code adm state (owner origin).binder .viewLogic data

/-- Apply the named existing R315/R159 consumer to the original environment
image. All original locals, descriptor formation, target checks and both
source children remain explicit at the same candidate extension. -/
theorem original_parent_residual {origin : Declaration} {declared : ComputedCallTypedFormationR310.Key → Prop}
    (definition : Definition origin declared) (base : Inputs s) (gen : Generated s Code)
    (ro : RuntimeReadout s View) (adm : LocalAdmissions s View)
    (original : Kernel (Payload (extended s Code) (Sum View Unit)))
    (env : Environment (Payload s View)) :
    let context := selectedContext
    let mark : Mark := ⟨1, none⟩
    let callee := OriginalScopedSourceEventMapR314.Fixture.callee
    let argument := OriginalScopedSourceEventMapR314.Fixture.argument
    let kernel := admissionKernel (inputs base gen) (readout definition.code ro)
      (admissions definition.code adm) original
    let before := environment definition.code env
    SourceJudgment kernel before context (.app mark callee argument) ↔
      (∀ premise ∈ SourceAppAdmissionR159.annotationPremises context mark,
        Local kernel before premise) ∧
      ∃ occurrence data state,
        decode (readout definition.code ro) before = some state ∧
        (admissions definition.code adm).logical state ⟨mark.site,.viewLogic,0⟩ .viewLogic data ∧
        let candidate := scopeCandidate before occurrence (.logical .viewLogic data)
        let after := before.extend ⟨mark.site,.viewLogic,0⟩ candidate
        original.atom after (atom .descriptorFormation mark.site context [callee.site,argument.site]) ∧
        (∀ premise ∈ OriginalSourceContractResolutionR311.remainingPremises context mark callee argument,
          Local kernel after premise) ∧
        SourceJudgment kernel after context callee ∧ SourceJudgment kernel after context argument :=
  OriginalModuleContextBindingR315.original_parent_formation_iff
    (inputs base gen) (readout definition.code ro) (admissions definition.code adm)
    original (environment definition.code env)

end YulangClosure.OriginalSourceEnvironmentTransportR331
