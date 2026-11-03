import YulangClosure.OriginalModuleContextBindingR315
import YulangClosure.ComputedCallUnionClausesR308

/-!
R328. Conservative addition of computation-interface handles. Old interface
interpretations, independent challenge domains, execution, Force, compatible
worlds and the original four-component greatest fixed point are retained.
The generated case is not an inlet: no new carrier-view challenge enters an
old Function domain. No inhabitant of the old Interface sort is selected.
Authority: computed-call-result-constructor §§2–6; generated-computed-result-
correspondence GR1–GR5. Source laws and endpoint incidence remain separate.
-/
namespace YulangClosure.OriginalInterfacePreservationR328
open OriginalSourceInterpretation
variable {s : Sorts} {G : Type}

def extended (s : Sorts) (G : Type) : Sorts := { s with Interface := Sum s.Interface G }

def upFiber (x : Fiber (s)) : Fiber (extended s G) :=
  ⟨x.nu, x.K, x.D, x.source, x.binders⟩
def downFiber (x : Fiber (extended s G)) : Fiber (s) :=
  ⟨x.nu, x.K, x.D, x.source, x.binders⟩
@[simp] theorem down_up_fiber (x : Fiber s) : downFiber (upFiber (G := G) x) = x := rfl
@[simp] theorem up_down_fiber (x : Fiber (extended s G)) : upFiber (downFiber x) = x := rfl

def upEvent (x : Event (s)) : Event (extended s G) :=
  ⟨upFiber x.fiber, x.eta0, x.eta, x.history, x.current, x.witness, x.scope, x.authority, x.incidence, x.dictionary⟩
def downEvent (x : Event (extended s G)) : Event (s) :=
  ⟨downFiber x.fiber, x.eta0, x.eta, x.history, x.current, x.witness, x.scope, x.authority, x.incidence, x.dictionary⟩
@[simp] theorem down_up_event (x : Event s) : downEvent (upEvent (G := G) x) = x := rfl
@[simp] theorem up_down_event (x : Event (extended s G)) : upEvent (downEvent x) = x := rfl

def upValue (x : ValueRow (s)) : ValueRow (extended s G) :=
  ⟨x.descriptor, x.value, x.root, upEvent x.event⟩
def downValue (x : ValueRow (extended s G)) : ValueRow (s) :=
  ⟨x.descriptor, x.value, x.root, downEvent x.event⟩
@[simp] theorem down_up_value (x : ValueRow s) : downValue (upValue (G := G) x) = x := rfl
@[simp] theorem up_down_value (x : ValueRow (extended s G)) : upValue (downValue x) = x := rfl

def upRaw (x : RawObservation (s)) : RawObservation (extended s G) :=
  ⟨x.observation, upEvent x.event⟩
def downRaw (x : RawObservation (extended s G)) : RawObservation (s) :=
  ⟨x.observation, downEvent x.event⟩
@[simp] theorem down_up_raw (x : RawObservation s) : downRaw (upRaw (G := G) x) = x := rfl
@[simp] theorem up_down_raw (x : RawObservation (extended s G)) : upRaw (downRaw x) = x := rfl

def upInput (x : CarrierInput (s)) : CarrierInput (extended s G) :=
  ⟨x.carrier, x.root, upEvent x.event⟩
def downInput (x : CarrierInput (extended s G)) : CarrierInput (s) :=
  ⟨x.carrier, x.root, downEvent x.event⟩
@[simp] theorem down_up_input (x : CarrierInput s) : downInput (upInput (G := G) x) = x := rfl
@[simp] theorem up_down_input (x : CarrierInput (extended s G)) : upInput (downInput x) = x := rfl

def upTrace (x : TraceRow s) : TraceRow (extended s G) :=
  ⟨.inl x.interface, x.observation, upEvent x.event⟩
def downTrace (x : TraceRow (extended s G)) (i : s.Interface) : TraceRow s :=
  ⟨i, x.observation, downEvent x.event⟩
def upCarrier (x : CarrierRow s) : CarrierRow (extended s G) :=
  ⟨.inl x.interface, x.carrier, x.root, upEvent x.event⟩
def downCarrier (x : CarrierRow (extended s G)) (i : s.Interface) : CarrierRow s :=
  ⟨i, x.carrier, x.root, downEvent x.event⟩
def upCall (x : CallInput s) : CallInput (extended s G) :=
  ⟨x.value, x.valueRoot, upEvent x.event, x.context, x.continuation,
    x.carrier, x.carrierRoot, .inl x.carrierView, x.receipt, x.path, x.consumer, x.incidence⟩
def downCall (x : CallInput (extended s G)) (i : s.Interface) : CallInput s :=
  ⟨x.value, x.valueRoot, downEvent x.event, x.context, x.continuation,
    x.carrier, x.carrierRoot, i, x.receipt, x.path, x.consumer, x.incidence⟩
def upChallenge {row : ValueRow s} (x : Challenge row) : Challenge (upValue (G := G) row) :=
  ⟨x.context, x.continuation, x.carrier, x.carrierRoot, .inl x.carrierView,
    x.receipt, x.path, x.consumer, x.incidence⟩
def downChallenge {row : ValueRow (extended s G)} (x : Challenge row) (i : s.Interface) :
    Challenge (downValue row) :=
  ⟨x.context, x.continuation, x.carrier, x.carrierRoot, i,
    x.receipt, x.path, x.consumer, x.incidence⟩
def upInstalled : Installed s → Installed (extended s G)
  | .value d v r => .value d v r
  | .carrier i c r => .carrier (.inl i) c r

def upQuery : Query s → Query (extended s G)
  | .value row => .value (upValue row)
  | .world row => .world (upEvent row)
  | .trace row => .trace (upTrace row)
  | .carrier row => .carrier (upCarrier row)

def upPositive : Positive s → Positive (extended s G)
  | .guard fact => .guard fact
  | .field q => .field (upQuery q)
  | .both a b => .both (upPositive a) (upPositive b)
  | .either a b => .either (upPositive a) (upPositive b)
  | .all D body => .all D (fun d => upPositive (body d))
  | .existsE D body => .existsE D (fun d => upPositive (body d))

def pull (Z : Family (extended s G)) : Family s := fun q => Z (upQuery q)

theorem positive_correspondence (body : Positive s) (Z : Family (extended s G)) :
    (upPositive body).Holds Z ↔ body.Holds (pull Z) := by
  induction body with
  | guard fact => rfl
  | field q => rfl
  | both a b iha ihb => exact and_congr iha ihb
  | either a b iha ihb => exact or_congr iha ihb
  | all D body ih => exact forall_congr' ih
  | existsE D body ih => exact exists_congr ih

/-- Arbitrary independent generated computation data; old preservation does
not require any generated membership or a distinguished old interface.
An EI instance must construct these fields from its original typed contracts.
Generated interfaces never serve as new inlets/carrier contracts. -/
structure Generated (s : Sorts) (G : Type) where
  guards : G → RawObservation s → ObservationGuards
  form : G → RawObservation s → TraceForm s
  fields : G → RawObservation s → Positive (extended s G)

def upForm : TraceForm s → TraceForm (extended s G)
  | .pureReturn v => .pureReturn (upValue v)
  | .unfinished => .unfinished

def inputs (base : Inputs s) (generated : Generated s G) : Inputs (extended s G) where
  compatible a b := base.compatible (downEvent a) (downEvent b)
  eventCoherent e := base.eventCoherent (downEvent e)
  valueForm := base.valueForm
  ground row := base.ground (downValue row)
  fixedExternal row := base.fixedExternal (downValue row)
  structuralGuard row := base.structuralGuard (downValue row)
  structuralFields row := upPositive (base.structuralFields (downValue row))
  actual := base.actual
  functionGuards row p := base.functionGuards (downValue row) p
  capturedFields row p := upPositive (base.capturedFields (downValue row) p)
  checkedInlet d := .inl (base.checkedInlet d)
  actualInlet p := .inl (base.actualInlet p)
  carrierAccepted row := match row.interface with
    | .inl i => base.carrierAccepted (downCarrier row i)
    | .inr _ => False
  puncturedContext d := match d.carrierView with
    | .inl i => base.puncturedContext (downChallenge d i)
    | .inr _ => False
  otherValues d := match d.carrierView with
    | .inl i => base.otherValues (downChallenge d i)
    | .inr _ => False
  registeredHoles d := match d.carrierView with
    | .inl i => base.registeredHoles (downChallenge d i)
    | .inr _ => False
  checkedIncidences d := match d.carrierView with
    | .inl i => base.checkedIncidences (downChallenge d i)
    | .inr _ => False
  receiptPrecondition p call := match call.carrierView with
    | .inl i => base.receiptPrecondition p (downCall call i)
    | .inr _ => False
  actualTypedPath p call := match call.carrierView with
    | .inl i => base.actualTypedPath p (downCall call i)
    | .inr _ => False
  actualContext p call := match call.carrierView with
    | .inl i => base.actualContext p (downCall call i)
    | .inr _ => False
  execute p call raw := match call.carrierView with
    | .inl i => base.execute p (downCall call i) (downRaw raw)
    | .inr _ => False
  observationGuards row := match row.interface with
    | .inl i => base.observationGuards (downTrace row i)
    | .inr g => generated.guards g (downRaw row.raw)
  traceForm row := match row.interface with
    | .inl i => upForm (base.traceForm (downTrace row i))
    | .inr g => upForm (generated.form g (downRaw row.raw))
  observationFields row := match row.interface with
    | .inl i => upPositive (base.observationFields (downTrace row i))
    | .inr g => generated.fields g (downRaw row.raw)
  checkedObservation d raw := match d.carrierView with
    | .inl i => upPositive (base.checkedObservation (downChallenge d i) (downRaw raw))
    | .inr _ => .guard False
  worldGuards e := base.worldGuards (downEvent e)
  installedCount e := base.installedCount (downEvent e)
  installed e n := (base.installed (downEvent e) n).map upInstalled
  alias e := base.alias (downEvent e)
  capture e := base.capture (downEvent e)
  captureValue e p n := (base.captureValue (downEvent e) p n).map upInstalled
  sharedPosition e := base.sharedPosition (downEvent e)
  witnessAt e := base.witnessAt (downEvent e)
  carrierGuards row := match row.interface with
    | .inl i => base.carrierGuards (downCarrier row i)
    | .inr _ => ⟨False, False, False, False, False⟩
  carrierCaptures row := match row.interface with
    | .inl i => upPositive (base.carrierCaptures (downCarrier row i))
    | .inr _ => .guard False
  demand row e := match row.interface with
    | .inl i => base.demand (downCarrier row i) (downEvent e)
    | .inr _ => False
  force call e raw := base.force (downInput call) (downEvent e) (downRaw raw)
  forceIncidence row e raw := match row.interface with
    | .inl i => base.forceIncidence (downCarrier row i) (downEvent e) (downRaw raw)
    | .inr _ => False

@[simp] theorem down_up_trace (row : TraceRow s) :
    downTrace (upTrace (G := G) row) row.interface = row := rfl
@[simp] theorem down_up_carrier (row : CarrierRow s) :
    downCarrier (upCarrier (G := G) row) row.interface = row := rfl
@[simp] theorem down_up_call (call : CallInput s) :
    downCall (upCall (G := G) call) call.carrierView = call := rfl
@[simp] theorem down_up_challenge {row : ValueRow s} (d : Challenge row) :
    downChallenge (upChallenge (G := G) d) d.carrierView = d := rfl

@[simp] theorem up_value_event (row : ValueRow s) (e : Event s) :
    upValue (G := G) (row.atEvent e) = (upValue row).atEvent (upEvent e) := rfl
@[simp] theorem up_carrier_event (row : CarrierRow s) (e : Event s) :
    upCarrier (G := G) (row.atEvent e) = (upCarrier row).atEvent (upEvent e) := rfl
@[simp] theorem up_raw_interface (raw : RawObservation s) (i : s.Interface) :
    upTrace (G := G) (raw.atInterface i) = (upRaw raw).atInterface (.inl i) := rfl
@[simp] theorem up_challenge_input {row : ValueRow s} (d : Challenge row) :
    (upChallenge (G := G) d).input = upCall d.input := rfl
@[simp] theorem up_carrier_input (row : CarrierRow s) :
    (upCarrier (G := G) row).input = upInput row.input := rfl

 theorem all_event (P : Event (extended s G) → Prop) :
    (∀ e, P e) ↔ ∀ e : Event s, P (upEvent e) :=
  ⟨fun h e => h (upEvent e), fun h e => by simpa using h (downEvent e)⟩
 theorem all_raw (P : RawObservation (extended s G) → Prop) :
    (∀ raw, P raw) ↔ ∀ raw : RawObservation s, P (upRaw raw) :=
  ⟨fun h raw => h (upRaw raw), fun h raw => by simpa using h (downRaw raw)⟩

def downInstalled : Installed (extended s G) → Option (Installed s)
  | .value d v r => some (.value d v r)
  | .carrier (.inl i) c r => some (.carrier i c r)
  | .carrier (.inr _) _ _ => none
@[simp] theorem down_up_installed (binding : Installed s) :
    downInstalled (upInstalled (G := G) binding) = some binding := by cases binding <;> rfl

def downQuery : Query (extended s G) → Option (Query s)
  | .value row => some (.value (downValue row))
  | .world row => some (.world (downEvent row))
  | .trace row => match row.interface with
    | .inl i => some (.trace (downTrace row i))
    | .inr _ => none
  | .carrier row => match row.interface with
    | .inl i => some (.carrier (downCarrier row i))
    | .inr _ => none
@[simp] theorem down_up_query (q : Query s) :
    downQuery (upQuery (G := G) q) = some q := by cases q <;> rfl

 theorem installed_injective : Function.Injective (upInstalled (s := s) (G := G)) := by
  intro a b same
  exact Option.some.inj (by simpa only [down_up_installed] using congrArg downInstalled same)

 theorem query_injective : Function.Injective (upQuery (s := s) (G := G)) := by
  intro a b same
  exact Option.some.inj (by simpa only [down_up_query] using congrArg downQuery same)

 theorem option_shared {A B : Type} (f : A → B) (inj : Function.Injective f)
    (a b : Option A) :
    (∃ z, a.map f = some z ∧ b.map f = some z) ↔
      ∃ z, a = some z ∧ b = some z := by
  cases a <;> cases b <;> simp [inj.eq_iff]

 theorem installed_correspondence (binding : Installed s) (event : Event s)
    (Z : Family (extended s G)) :
    (upInstalled binding).Valid Z (upEvent event) ↔ binding.Valid (pull Z) event := by
  cases binding <;> rfl

 theorem aliases_correspondence (base : Inputs s) (gen : Generated s G) (e : Event s) :
    AliasesAgree (inputs base gen) (upEvent e) ↔ AliasesAgree base e := by
  simp only [AliasesAgree, inputs, down_up_event]
  exact forall_congr' fun a => forall_congr' fun b =>
    imp_congr_right fun _ => option_shared upInstalled installed_injective _ _

 theorem captures_correspondence (base : Inputs s) (gen : Generated s G) (e : Event s) :
    CapturesAgree (inputs base gen) (upEvent e) ↔ CapturesAgree base e := by
  simp only [CapturesAgree, inputs, down_up_event]
  exact forall_congr' fun p => forall_congr' fun n => forall_congr' fun a =>
    imp_congr_right fun _ => and_congr_right fun _ =>
      option_shared upInstalled installed_injective _ _

 theorem world_correspondence (base : Inputs s) (gen : Generated s G)
    (e : Event s) (Z : Family (extended s G)) :
    PhiW (inputs base gen) Z (upEvent e) ↔ PhiW base (pull Z) e := by
  unfold PhiW
  rw [aliases_correspondence, captures_correspondence]
  change (base.eventCoherent e ∧ (base.worldGuards e).Valid ∧
    AliasesAgree base e ∧ CapturesAgree base e ∧ WitnessesAgree base e ∧ _) ↔ _
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  apply forall_congr'; intro n
  change (∀ binding, (base.installed e n).map upInstalled = some binding →
    binding.Valid Z (upEvent e)) ↔ _
  cases found : base.installed e n with
  | none => simp
  | some binding => simp [installed_correspondence]

 theorem checked_domain_correspondence (base : Inputs s) (gen : Generated s G)
    {row : ValueRow s} (d : Challenge row) :
    CheckedDomain (inputs base gen) (upChallenge d) ↔ CheckedDomain base d := Iff.rfl

 theorem admission_correspondence (base : Inputs s) (gen : Generated s G)
    {row : ValueRow s} (p : s.Provider) (d : Challenge row) :
    ActualAdm (inputs base gen) p (upChallenge d) ↔ ActualAdm base p d := Iff.rfl

 theorem execution_correspondence (base : Inputs s) (gen : Generated s G)
    (p : s.Provider) (call : CallInput s) (raw : RawObservation s) :
    (inputs base gen).execute p (upCall call) (upRaw raw) ↔ base.execute p call raw := Iff.rfl

 theorem force_correspondence (base : Inputs s) (gen : Generated s G)
    (call : CarrierInput s) (event : Event s) (raw : RawObservation s) :
    (inputs base gen).force (upInput call) (upEvent event) (upRaw raw) ↔
      base.force call event raw := Iff.rfl

 theorem compatible_correspondence (base : Inputs s) (gen : Generated s G)
    (a b : Event s) :
    (inputs base gen).compatible (upEvent a) (upEvent b) ↔ base.compatible a b := Iff.rfl

 theorem new_challenge_excluded (base : Inputs s) (gen : Generated s G)
    {row : ValueRow (extended s G)} (d : Challenge row) (g : G)
    (newView : d.carrierView = .inr g) : ¬ CheckedDomain (inputs base gen) d := by
  intro checked
  have no := checked.2.1
  simp only [inputs, newView] at no

 theorem function_correspondence (base : Inputs s) (gen : Generated s G)
    (row : ValueRow s) (Z : Family (extended s G)) :
    FunctionAt (inputs base gen) Z (upValue row) ↔ FunctionAt base (pull Z) row := by
  simp only [FunctionAt, inputs, upValue, downValue, down_up_event,
    positive_correspondence]
  apply and_congr_right; intro _
  apply forall_congr'; intro provider
  apply imp_congr_right; intro _
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  constructor
  · intro h d checked
    have got := h (upChallenge d) checked
    refine ⟨got.1, ?_⟩
    intro raw executed
    exact (positive_correspondence _ Z).mp (got.2 (upRaw raw) executed)
  · intro h d checked
    rcases d with ⟨context, continuation, carrier, root, view, receipt, path, consumer, incidence⟩
    cases view with
    | inl i =>
      let old : Challenge row := ⟨context, continuation, carrier, root, i, receipt, path, consumer, incidence⟩
      have got := h old checked
      refine ⟨got.1, ?_⟩
      intro raw executed
      exact (positive_correspondence _ Z).mpr (got.2 (downRaw raw) executed)
    | inr g => exact False.elim checked.2.1

 theorem value_correspondence (base : Inputs s) (gen : Generated s G)
    (row : ValueRow s) (Z : Family (extended s G)) :
    PhiV (inputs base gen) Z (upValue row) ↔ PhiV base (pull Z) row := by
  unfold PhiV
  apply and_congr
  · cases form : base.valueForm row.descriptor <;>
      simp only [show (inputs base gen).valueForm (upValue row).descriptor =
        base.valueForm row.descriptor from rfl, form]
    · rfl
    · rfl
    · exact and_congr Iff.rfl (positive_correspondence _ Z)
    · exact function_correspondence base gen row Z
  · rw [all_event]
    rfl

 theorem up_event_eq (a b : Event s) : upEvent (G := G) a = upEvent b ↔ a = b :=
  ⟨fun h => congrArg downEvent h, fun h => congrArg upEvent h⟩

 theorem trace_correspondence (base : Inputs s) (gen : Generated s G)
    (row : TraceRow s) (Z : Family (extended s G)) :
    PhiT (inputs base gen) Z (upTrace row) ↔ PhiT base (pull Z) row := by
  cases form : base.traceForm row <;>
    simp only [PhiT, inputs, upTrace, downTrace, down_up_event, form, upForm,
      positive_correspondence, upValue, pull, upQuery]
  exact and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => and_congr
      (and_congr ⟨fun h => congrArg downEvent h, fun h => congrArg upEvent h⟩ Iff.rfl) Iff.rfl

 theorem carrier_correspondence (base : Inputs s) (gen : Generated s G)
    (row : CarrierRow s) (Z : Family (extended s G)) :
    PhiCar (inputs base gen) Z (upCarrier row) ↔ PhiCar base (pull Z) row := by
  simp only [PhiCar, inputs, upCarrier, downCarrier, down_up_event,
    positive_correspondence]
  simp only [all_event (s := s) (G := G), all_raw (s := s) (G := G),
    down_up_event, down_up_raw]
  rfl

 theorem phi_correspondence (base : Inputs s) (gen : Generated s G)
    (q : Query s) (Z : Family (extended s G)) :
    Phi (inputs base gen) Z (upQuery q) ↔ Phi base (pull Z) q := by
  cases q with
  | value row => exact value_correspondence base gen row Z
  | world row => exact world_correspondence base gen row Z
  | trace row => exact trace_correspondence base gen row Z
  | carrier row => exact carrier_correspondence base gen row Z

/-- Direct image keeps exactly the old queries, with the SAME old witness. -/
def image (Z : Family s) : Family (extended s G) :=
  fun q => ∃ old, upQuery old = q ∧ Z old

 theorem pull_image (Z : Family s) : pull (image (G := G) Z) = Z := by
  funext q
  apply propext
  constructor
  · rintro ⟨old, same, valid⟩
    exact query_injective same ▸ valid
  · intro valid
    exact ⟨q, rfl, valid⟩

/-- Reflection uses the original four-component operator and its original
Greatest, with no assumption about generated rows being meaningful. -/
 theorem meaning_reflect (base : Inputs s) (gen : Generated s G) (q : Query s)
    (valid : Meaning (inputs base gen) (upQuery q)) : Meaning base q := by
  apply greatest_coinduct (Phi base) (pull (Meaning (inputs base gen))) _ q valid
  intro old member
  exact (phi_correspondence base gen old _).mp
    ((meaning_iff (inputs base gen) (upQuery old)).mp member)

/-- Extension uses the direct image of the actual original greatest fixed
point. It does not change any old endpoint or add a premise about its meaning. -/
 theorem meaning_preserve (base : Inputs s) (gen : Generated s G) (q : Query s)
    (valid : Meaning base q) : Meaning (inputs base gen) (upQuery q) := by
  apply greatest_coinduct (Phi (inputs base gen)) (image (Meaning base)) _ _ ⟨q, rfl, valid⟩
  rintro _ ⟨old, rfl, member⟩
  apply (phi_correspondence base gen old _).mpr
  rw [pull_image]
  exact (meaning_iff base old).mp member

 theorem old_meaning_iff (base : Inputs s) (gen : Generated s G) (q : Query s) :
    Meaning (inputs base gen) (upQuery q) ↔ Meaning base q :=
  ⟨meaning_reflect base gen q, meaning_preserve base gen q⟩

/-- The generated clause retains the independent outer coherence and world,
plus the genuine optional result at its actual event. No arbitrary body B is
identified with PhiT without these fields. -/
def generatedClause (base : Inputs s) (gen : Generated s G) (g : G)
    (raw : RawObservation s) : Positive (extended s G) :=
  .both (.guard (base.eventCoherent raw.event ∧ (gen.guards g raw).Valid))
    (.both (.field (.world (upEvent raw.event)))
      (.both (match gen.form g raw with
        | .pureReturn v => .both (.guard (v.event = raw.event)) (.field (.value (upValue v)))
        | .unfinished => .guard True)
        (gen.fields g raw)))

 theorem generated_phi_iff (base : Inputs s) (gen : Generated s G) (g : G)
    (raw : RawObservation s) (Z : Family (extended s G)) :
    PhiT (inputs base gen) Z ((upRaw raw).atInterface (.inr g)) ↔
      (generatedClause base gen g raw).Holds Z := by
  have guards : (inputs base gen).observationGuards
      ((upRaw raw).atInterface (.inr g)) = gen.guards g raw := rfl
  have trace : (inputs base gen).traceForm
      ((upRaw raw).atInterface (.inr g)) = upForm (gen.form g raw) := rfl
  have fields : (inputs base gen).observationFields
      ((upRaw raw).atInterface (.inr g)) = gen.fields g raw := rfl
  have coherent : (inputs base gen).eventCoherent (upEvent raw.event) =
      base.eventCoherent raw.event := rfl
  simp only [PhiT, guards, trace, fields]
  cases form : gen.form g raw <;>
    simp only [upForm, generatedClause, Positive.Holds, form, upValue,
      RawObservation.atInterface, upRaw, coherent, up_event_eq, and_assoc]

 theorem generated_meaning_iff (base : Inputs s) (gen : Generated s G) (g : G)
    (raw : RawObservation s) :
    Meaning (inputs base gen) (.trace ((upRaw raw).atInterface (.inr g))) ↔
      (generatedClause base gen g raw).Holds (Meaning (inputs base gen)) :=
  (meaning_iff (inputs base gen) _).trans (generated_phi_iff base gen g raw _)

/-- Exact reflection of the full original negative challenge domain: every
extended checked challenge, not just every embedded challenge, comes from the
same original challenge. No generated carrier-view alternative is lost. -/
 theorem checked_domain_exact (base : Inputs s) (gen : Generated s G)
    {row : ValueRow s} (d : Challenge (upValue (G := G) row)) :
    CheckedDomain (inputs base gen) d ↔
      ∃ old : Challenge row, upChallenge old = d ∧ CheckedDomain base old := by
  rcases d with ⟨context, continuation, carrier, root, view, receipt, path, consumer, incidence⟩
  cases view with
  | inl i =>
    let old : Challenge row := ⟨context, continuation, carrier, root, i, receipt, path, consumer, incidence⟩
    constructor
    · intro checked
      exact ⟨old, rfl, checked⟩
    · rintro ⟨old, same, checked⟩
      exact same ▸ (checked_domain_correspondence base gen old).mpr checked
  | inr g =>
    constructor
    · intro checked
      exact False.elim checked.2.1
    · rintro ⟨old, same, _⟩
      have impossible := congrArg Challenge.carrierView same
      cases impossible

 theorem new_execution_excluded (base : Inputs s) (gen : Generated s G)
    (p : s.Provider) (call : CallInput (extended s G)) (g : G)
    (newView : call.carrierView = .inr g) (raw : RawObservation (extended s G)) :
    ¬ (inputs base gen).execute p call raw := by
  simp only [inputs, newView, not_false_eq_true]

open OriginalSource OriginalSourceEnvironment

/-- The source environment embedding retains every old endpoint and view;
its frame/event payloads are mapped structurally, including installed carriers.
This is not registration of the missing EI semantics. -/
def upAssignment (x : SourceAssignment s) : SourceAssignment (extended s G) :=
  ⟨upEvent x.event, x.descriptor, x.value, x.root, x.binding⟩
def upCurrent (x : Current s) : Current (extended s G) :=
  ⟨x.history, x.configuration⟩
def upObject : Object s → Object (extended s G)
  | .value v r => .value v r
  | .carrier c r => .carrier c r
def upInvocation (x : Invocation s View) : Invocation (extended s G) View :=
  ⟨upCurrent x.current, x.value, x.valueRoot, x.context, x.continuation, x.carrier, x.carrierRoot, x.view, x.receipt, x.path, x.consumer, x.incidence⟩
def upReceipt (x : ReceiptData s View) : ReceiptData (extended s G) View :=
  ⟨x.receipt, x.view, x.path, x.consumer, x.incidence, upCurrent x.after⟩
def upOutcome (x : Outcome s) : Outcome (extended s G) :=
  ⟨x.observation, x.result.map upObject, upCurrent x.after, x.endpoints.map (fun e => (e.1, upObject e.2)), x.bindings⟩
def upResponse (x : ResponseData s View) : ResponseData (extended s G) View :=
  ⟨x.observation, upReceipt x.receipt⟩
def upRigid (x : RigidData s) : RigidData (extended s G) :=
  ⟨x.declaration, x.arity, x.packet, upCurrent x.after⟩
def upRuntime : Runtime s View → Runtime (extended s G) View
  | .invocation d => .invocation (upInvocation d)
  | .receipt d => .receipt (upReceipt d)
  | .returnRebind d => .returnRebind (upOutcome d)
  | .response d => .response (upResponse d)
  | .rigidOperation d => .rigidOperation (upRigid d)
  | .oneShot d => .oneShot (upOutcome d)
def upRoot (x : Root s View) : Root (extended s G) View :=
  ⟨upAssignment x.assignment, fun e => .inl (x.interfaces e), x.carriers, fun v => .inl (x.viewMeaning v), fun n => (x.installed n).map upInstalled, x.callOwners⟩
def upLogical (x : Logical s View) : Logical (extended s G) View :=
  ⟨x.descriptors, x.interfaces.map (fun e => (e.1, .inl e.2)), fun v => .inl (x.viewMeaning v), x.eta, x.witness⟩
def upShared (x : Shared s) : Shared (extended s G) :=
  ⟨x.bindings, x.installed.map (fun e => (e.1, upInstalled e.2)), x.witness⟩
def upPayload : Payload s View → Payload (extended s G) View
  | .root d => .root (upRoot d)
  | .logical k d => .logical k (upLogical d)
  | .shared d => .shared (upShared d)
  | .runtime d => .runtime (upRuntime d)
def upStep (x : EventStep (Payload s View)) : EventStep (Payload (extended s G) View) :=
  ⟨x.source, x.kind, x.occurrence, upPayload x.data⟩
def upActualEvent (x : ActualEvent (Payload s View)) : ActualEvent (Payload (extended s G) View) :=
  ⟨x.parents.map upStep, x.occurrence⟩
def upScoped (x : ScopedValue (Payload s View)) : ScopedValue (Payload (extended s G) View) :=
  ⟨upPayload x.data, upActualEvent x.event⟩
def upFrame (x : Frame (Payload s View)) : Frame (Payload (extended s G) View) :=
  ⟨x.binder, upScoped x.value, x.entryPath.map upStep⟩
def upDecoded (x : Decoded s View) : Decoded (extended s G) View :=
  ⟨upAssignment x.assignment, (fun e => .inl (x.interfaces e)), x.carriers,
    (fun v => .inl (x.viewMeaning v)), (fun n => (x.installed n).map upInstalled),
    x.active.map upCall, x.activeRaw.map upInvocation, x.fixedFrames.map upFrame, x.callOwners⟩

 theorem decoded_old_endpoints (x : Decoded s View) (endpoint : Endpoint) :
    (upDecoded (G := G) x).interfaces endpoint = .inl (x.interfaces endpoint) := rfl

/-- Authentic existing R293 packets, when available, transport into the
existing R293 catalogue over the extended Inputs/Decoded. No catalogue/readback
equation or new source membership is supplied as a hypothesis. Classical
reification preserves all nested existential/universal field evidence. -/
noncomputable def upBranchPacket (base : Inputs s) (gen : Generated s G)
    (state : Decoded s View) (scope : List Binder) (endpoint : Endpoint)
    (raw : RawObservation s)
    (packet : SourceContributionConstruction.Packet
      (ComputedCallUnionRealizationR293.branchCatalogue base state scope endpoint) raw) :
    SourceContributionConstruction.Packet
      (ComputedCallUnionRealizationR293.branchCatalogue (inputs base gen)
        (upDecoded state) scope endpoint) (upRaw raw) := by
  have old := ComputedCallUnionRealizationR293.source_packet_meaning
    base state scope endpoint raw packet
  have member := meaning_preserve base gen _ old
  exact ⟨(), ComputedCallUnionClausesR308.evidenceOfHolds _ _
    ((OriginalSourceChecking.meaning_clause (inputs base gen) _).mp member)⟩

 theorem transported_packet_meaning (base : Inputs s) (gen : Generated s G)
    (state : Decoded s View) (scope : List Binder) (endpoint : Endpoint)
    (raw : RawObservation s)
    (packet : SourceContributionConstruction.Packet
      (ComputedCallUnionRealizationR293.branchCatalogue base state scope endpoint) raw) :
    Meaning (inputs base gen) (.trace ((upRaw raw).atInterface
      ((upDecoded state).interfaces endpoint))) :=
  ComputedCallUnionRealizationR293.source_packet_meaning (inputs base gen)
    (upDecoded state) scope endpoint (upRaw raw)
    (upBranchPacket base gen state scope endpoint raw packet)

namespace Selected
open ComputedCallTypedFormationR310 OriginalScopedClosure

/-- Source-owned typed generated labels: the complete scoped constructor
expression is retained, rather than a guessed original interface inhabitant. -/
abbrev Code := (scope : List LocalBinder) × Computation scope

def request (origin : Declaration) : Request :=
  prepare (OriginalModuleContextBindingR315.selectedCall origin
    OriginalModuleContextBindingR315.externalContext)
def sourceCode (origin : Declaration) : Code := ⟨[], (request origin).sourceExpression⟩
def resultCode (origin : Declaration) (arms : List (Arm [])) : Code :=
  ⟨[], resultExpression (request origin) arms⟩
def sourceInterface (s : Sorts) (origin : Declaration) : (extended s Code).Interface :=
  .inr (sourceCode origin)
def resultInterface (s : Sorts) (origin : Declaration) (arms : List (Arm [])) :
    (extended s Code).Interface := .inr (resultCode origin arms)

 theorem actual_request (origin : Declaration) :
    ((SourceGraphRegistrationR297.sourceInventory origin
      OriginalModuleContextBindingR315.externalContext
      OriginalScopedSourceEventMapR314.Fixture.root)[13]?).bind callRecord =
      some (request origin).original :=
  OriginalModuleContextBindingR315.selected_request_computed origin _

 theorem all_scoped_arms_retained (origin : Declaration) (arms : List (Arm [])) :
    (resultCode origin arms).2 = .allArms
      (.evalInvoke (request origin).original.position (request origin).operands) arms := rfl

 theorem source_result_check_retained (origin : Declaration) :
    (request origin).original = OriginalModuleContextBindingR315.selectedCall origin
      OriginalModuleContextBindingR315.externalContext ∧
    (request origin).originalResult = ⟨1, .synthesis⟩ ∧
    (request origin).originalCheck = ⟨1, .callableImage⟩ ∧
    (request origin).operands.argument.reference.key.scope =
      [.calRet (request origin).original.position] := ⟨rfl, rfl, rfl, rfl⟩

/-- Applied to the ACTUAL R315 source construction and full caller-supplied
original scoped arm family. The independent generated data remains explicit:
this theorem proves conservative formation, not EI-Intro or its interpretation.
No empty-arm default, final membership or selected solution is assumed. -/
 theorem conservative_formation (base : Inputs s) (gen : Generated s Code)
    (origin : Declaration) (arms : List (Arm [])) (declared : Key → Prop)
    (operands : StaticFormation declared (request origin).operands)
    (armFormation : ∀ arm ∈ arms, declared arm.descriptor.key) :
    Formed declared (resultCode origin arms).2 ∧
      ∀ q : Query s, Meaning (inputs base gen) (upQuery q) ↔ Meaning base q :=
  ⟨form declared (request origin) arms operands armFormation, old_meaning_iff base gen⟩

/-- Existing genuine source-check packets at this actual occurrence retain
all their original fields in R293's extended catalogue. The original packet
remains an OPEN premise; no EI child is fabricated from the new label. -/
 theorem original_r293_source_transport (base : Inputs s) (gen : Generated s Code)
    (origin : Declaration) (state : Decoded s View) (scope : List Binder)
    (raw : RawObservation s)
    (packet : SourceContributionConstruction.Packet
      (ComputedCallUnionRealizationR293.branchCatalogue base state scope
        (request origin).originalCheck) raw) :
    Meaning (inputs base gen) (.trace ((upRaw raw).atInterface
      ((upDecoded state).interfaces (request origin).originalCheck))) :=
  transported_packet_meaning base gen state scope (request origin).originalCheck raw packet

end Selected
end YulangClosure.OriginalInterfacePreservationR328
