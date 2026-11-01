import Lean.Elab.Command
import Lean.Util.CollectAxioms
import YulangClosure.OriginalSourceEnvironment
import YulangClosure.SourceLogicalOccurrencesR104

/-!
R159: exact App interface separation, not a source-semantic counterexample.

SG §§3.1--3.3, 5.2 supplies the original scoped rule grammar relative to
independently established L1--L5. Source-call generation §§5--7 leaves original
profile completion P and initial admission A open. No interpretation of either
is selected here. In particular the interface model below is not an original
WF_Dec/profile law, a native implementation or production authority.

R157's import build fails in the frozen R105 dependency. This module uses only
the already buildable original environment and exact R104 App syntax. It does
not repair, import or claim kernel acceptance for R105/R112/R114/R157.
-/
namespace YulangClosure.SourceAppAdmissionR159

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment

variable {s : Sorts} {View Value : Type}

/-- Every original App local, including the conditional singleton-formal
origin and both finite checks. This is definitionally R104's actual list. -/
def appPremises (context : Context) (mark : Mark)
    (callee argument : Source .expression) : List Premise :=
  ((([.descriptorFormation, .wholeArgumentCompatibility, .completeCallCertificate,
      .sourceCallIncidence, .callableImage] : List AtomKind) ++
      (if singletonFormalCall context callee argument then
        [AtomKind.roleAndInitialCallOrigin] else [])).map
      (fun kind => Premise.atom (atom kind mark.site context [callee.site, argument.site]))) ++
    [.checking ⟨.value, mark.site, context, ⟨callee.site, .returnedValue⟩, ⟨mark.site, .descriptor⟩⟩,
     .checking ⟨.computation, mark.site, context, ⟨mark.site, .callableImage⟩, ⟨mark.site, .synthesis⟩⟩]

/-- Exact original outer annotation premises, at the incoming environment. -/
def annotationPremises (context : Context) (mark : Mark) : List Premise :=
  match mark.annotation with
  | none => []
  | some target =>
      [.atom { (atom .finalAnnotationFormation mark.site context) with annotation := some target },
       .boundary mark.site context ⟨mark.site, .synthesis⟩ ⟨mark.site, .writtenTarget⟩]

theorem app_continuation_iff (kernel : Kernel Value) (environment : Environment Value)
    (context : Context) (mark : Mark) (callee argument : Source .expression) :
    Judgment kernel environment (LogicalOccurrencesR104.appRule context mark callee argument) ↔
      (∀ premise ∈ appPremises context mark callee argument, Local kernel environment premise) ∧
      SourceJudgment kernel environment context callee ∧
      SourceJudgment kernel environment context argument := by
  constructor
  · intro proof
    cases proof with
    | rule locals children =>
        cases children with
        | cons first rest =>
            cases rest with
            | cons second _ => exact ⟨locals, first, second⟩
  · rintro ⟨locals, first, second⟩
    exact .rule locals (.cons first (.cons second .nil))

/-- Inversion and reconstruction retain BOTH annotation alternatives and all
their actual local proofs. No transport to a different Environment occurs. -/
theorem app_source_iff (kernel : Kernel Value) (environment : Environment Value)
    (context : Context) (mark : Mark) (callee argument : Source .expression) :
    SourceJudgment kernel environment context (.app mark callee argument) ↔
      (∀ premise ∈ annotationPremises context mark, Local kernel environment premise) ∧
      ∃ candidate, kernel.admitted environment ⟨mark.site, .viewLogic, 0⟩ candidate ∧
        Judgment kernel (environment.extend ⟨mark.site, .viewLogic, 0⟩ candidate)
          (LogicalOccurrencesR104.appRule context mark callee argument) := by
  rcases mark with ⟨site, annotation⟩
  cases annotation with
  | none =>
      simp only [SourceJudgment, sourceRules]
      constructor
      · intro source
        cases source with
        | existsE candidate accepted body =>
            refine ⟨?_, candidate, accepted, body⟩
            intro premise absent
            cases absent
      · rintro ⟨_, candidate, accepted, body⟩
        exact Judgment.existsE candidate accepted body
  | some target =>
      simp only [SourceJudgment, sourceRules]
      constructor
      · intro source
        cases source with
        | rule locals children =>
            cases children with
            | cons first _ =>
                cases first with
                | existsE candidate accepted body => exact ⟨locals, candidate, accepted, body⟩
      · rintro ⟨locals, candidate, accepted, body⟩
        exact Judgment.rule locals (.cons (.existsE candidate accepted body) .nil)

/-- Admission classifies the actual ViewLogic payload without replacing its
descriptor/interface writes, eta, witness, occurrence or scope. -/
theorem admitted_view_iff (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (environment : Environment (Payload s View))
    (site : Site) (candidate : ScopedValue (Payload s View)) :
    Admitted inputs readout admissions environment ⟨site, .viewLogic, 0⟩ candidate ↔
      ∃ occurrence data state,
        candidate = scopeCandidate environment occurrence (.logical .viewLogic data) ∧
        decode readout environment = some state ∧
        admissions.logical state ⟨site, .viewLogic, 0⟩ .viewLogic data := by
  constructor
  · rintro ⟨parents, state, decoded, valid⟩
    rcases candidate with ⟨payload, ⟨path, occurrence⟩⟩
    change path = environment.eventPath at parents
    subst path
    cases payload with
    | root data => exact False.elim valid
    | shared data => simp [DataAdmitted] at valid
    | runtime data => cases data <;> simp [DataAdmitted] at valid
    | logical kind data =>
        cases kind <;>
          simp only [DataAdmitted, LogicalKind.binderKind, reduceCtorEq, false_and] at valid
        exact ⟨occurrence, data, state, rfl, decoded, valid.2⟩
  · rintro ⟨occurrence, data, state, rfl, decoded, admitted⟩
    exact ⟨rfl, state, decoded, rfl, admitted⟩

/-- This exact parent decomposition exposes the genuinely independent local
admission as a remaining conjunct; it does not establish its concrete instance.
All Local clauses, both finite checks and both arbitrary source children use
the SAME original candidate extension. -/
theorem app_admission_iff (inputs : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (original : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (context : Context) (mark : Mark)
    (callee argument : Source .expression) :
    let kernel := admissionKernel inputs readout admissions original
    SourceJudgment kernel environment context (.app mark callee argument) ↔
      (∀ premise ∈ annotationPremises context mark, Local kernel environment premise) ∧
      ∃ occurrence data state,
        decode readout environment = some state ∧
        admissions.logical state ⟨mark.site, .viewLogic, 0⟩ .viewLogic data ∧
        let candidate := scopeCandidate environment occurrence (.logical .viewLogic data)
        let after := environment.extend ⟨mark.site, .viewLogic, 0⟩ candidate
        (∀ premise ∈ appPremises context mark callee argument, Local kernel after premise) ∧
        SourceJudgment kernel after context callee ∧
        SourceJudgment kernel after context argument := by
  dsimp only
  rw [app_source_iff]
  constructor
  · rintro ⟨annotations, candidate, admitted, body⟩
    obtain ⟨occurrence, data, state, rfl, decoded, accepted⟩ :=
      (admitted_view_iff inputs readout admissions environment mark.site candidate).mp admitted
    exact ⟨annotations, occurrence, data, state, decoded, accepted,
      (app_continuation_iff _ _ context mark callee argument).mp body⟩
  · rintro ⟨annotations, occurrence, data, state, decoded, accepted, body⟩
    refine ⟨annotations, scopeCandidate environment occurrence (.logical .viewLogic data), ?_, ?_⟩
    · exact (admitted_view_iff inputs readout admissions environment mark.site _).mpr
        ⟨occurrence, data, state, rfl, decoded, accepted⟩
    · exact (app_continuation_iff _ _ context mark callee argument).mpr body

/-- Interface experiment only: block precisely this existing App binder while
retaining every other LocalAdmissions field and every other logical binder.
This is not a proposed source law. -/
def rejectApp (base : LocalAdmissions s View) (site : Site) : LocalAdmissions s View :=
  {base with logical := fun state binder kind data =>
    binder ≠ ⟨site, .viewLogic, 0⟩ ∧ base.logical state binder kind data}

theorem rejectApp_elsewhere (base : LocalAdmissions s View) (site : Site)
    (state : Decoded s View) (binder : Binder) (kind : LogicalKind) (data : Logical s View)
    (other : binder ≠ ⟨site, .viewLogic, 0⟩) :
    (rejectApp base site).logical state binder kind data ↔ base.logical state binder kind data :=
  ⟨And.right, fun accepted => ⟨other, accepted⟩⟩

theorem rejectApp_no_source (inputs : Inputs s) (readout : RuntimeReadout s View)
    (base : LocalAdmissions s View) (original : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (context : Context) (mark : Mark)
    (callee argument : Source .expression) :
    ¬ SourceJudgment (admissionKernel inputs readout (rejectApp base mark.site) original)
      environment context (.app mark callee argument) := by
  intro source
  obtain ⟨_, occurrence, data, state, _, accepted, _⟩ :=
    (app_admission_iff inputs readout (rejectApp base mark.site) original
      environment context mark callee argument).mp source
  exact accepted.1 rfl

namespace InterfaceModel

/-- Explicit arbitrary local-kernel model. These True relations are not
authenticated source semantics and supply no original L1--L5 instance. -/
def kernel (inputs : Inputs s) (readout : RuntimeReadout s View)
    (base : LocalAdmissions s View) (site : Site) : Kernel (Payload s View) where
  atom := fun _ _ => True
  admitted := Admitted inputs readout (rejectApp base site)
  primitiveCheck := fun _ _ _ => True
  structuralShape := fun _ _ _ _ => False
  functionShape := fun _ _ _ _ _ => False
  boundaryTag := fun _ _ _ _ _ _ => True
  conversion := fun _ _ _ _ _ _ => True

theorem every_local (inputs : Inputs s) (readout : RuntimeReadout s View)
    (base : LocalAdmissions s View) (site : Site)
    (environment : Environment (Payload s View)) (premise : Premise) :
    Local (kernel inputs readout base site) environment premise := by
  cases premise with
  | atom atom => exact .atom True.intro
  | checking goal => exact .checking (.primitive goal 0 True.intro)
  | boundary site context lower upper =>
      exact .boundary (.actual site context lower upper 0 True.intro)

/-- Arbitrary operands retain their actual derivations at this SAME extension.
The model has every original local clause (including the conditional origin),
both finite checks and the exact continuation, yet no outer App admission.
This refutes only a universal implication of the parametric interface. -/
theorem separation (inputs : Inputs s) (readout : RuntimeReadout s View)
    (base : LocalAdmissions s View) (environment : Environment (Payload s View))
    (context : Context) (mark : Mark) (callee argument : Source .expression)
    (occurrence : Nat) (data : Logical s View)
    (state : Decoded s View) (decoded : decode readout environment = some state)
    (calleeProof : SourceJudgment (kernel inputs readout base mark.site)
      (environment.extend ⟨mark.site, .viewLogic, 0⟩
        (scopeCandidate environment occurrence (.logical .viewLogic data))) context callee)
    (argumentProof : SourceJudgment (kernel inputs readout base mark.site)
      (environment.extend ⟨mark.site, .viewLogic, 0⟩
        (scopeCandidate environment occurrence (.logical .viewLogic data))) context argument) :
    let selected := kernel inputs readout base mark.site
    let after := environment.extend ⟨mark.site, .viewLogic, 0⟩
      (scopeCandidate environment occurrence (.logical .viewLogic data))
    decode readout after = some (state.logical data) ∧
    (state.logical data).assignment.descriptor = put state.assignment.descriptor data.descriptors ∧
    (state.logical data).interfaces = put state.interfaces data.interfaces ∧
    ¬ (rejectApp base mark.site).logical state ⟨mark.site, .viewLogic, 0⟩ .viewLogic data ∧
    (∀ premise ∈ annotationPremises context mark, Local selected environment premise) ∧
    (∀ premise ∈ appPremises context mark callee argument, Local selected after premise) ∧
    Checking selected after
      ⟨.value, mark.site, context, ⟨callee.site, .returnedValue⟩, ⟨mark.site, .descriptor⟩⟩ ∧
    Checking selected after
      ⟨.computation, mark.site, context, ⟨mark.site, .callableImage⟩, ⟨mark.site, .synthesis⟩⟩ ∧
    SourceJudgment selected after context callee ∧
    SourceJudgment selected after context argument ∧
    Judgment selected after (LogicalOccurrencesR104.appRule context mark callee argument) ∧
    ¬ SourceJudgment selected environment context (.app mark callee argument) := by
  dsimp only
  refine ⟨decode_extend readout environment ⟨mark.site, .viewLogic, 0⟩ _ state decoded,
    rfl, rfl, fun rejected => rejected.1 rfl,
    fun premise _ => every_local inputs readout base mark.site environment premise,
    fun premise _ => every_local inputs readout base mark.site _ premise,
    .primitive _ 0 True.intro, .primitive _ 0 True.intro, calleeProof, argumentProof,
    (app_continuation_iff _ _ context mark callee argument).mpr
      ⟨fun premise _ => every_local inputs readout base mark.site _ premise, calleeProof, argumentProof⟩, ?_⟩
  intro source
  obtain ⟨_, candidate, accepted, _⟩ := (app_source_iff _ _ context mark callee argument).mp source
  obtain ⟨_, _, _, _, _, rejected⟩ :=
    (admitted_view_iff inputs readout (rejectApp base mark.site) environment mark.site candidate).mp accepted
  exact rejected.1 rfl

/-- Concrete inhabitation of both operand premises, for either operand
annotation alternative. The source domain of `separation` stays arbitrary. -/
theorem literal_operand (inputs : Inputs s) (readout : RuntimeReadout s View)
    (base : LocalAdmissions s View) (site : Site)
    (environment : Environment (Payload s View)) (context : Context)
    (mark : Mark) (value : Literal) :
    SourceJudgment (kernel inputs readout base site) environment context (.literal mark value) := by
  rcases mark with ⟨literalSite, annotation⟩
  cases annotation with
  | none =>
      simp only [SourceJudgment, sourceRules]
      exact .rule (fun premise _ => every_local inputs readout base site environment premise) .nil
  | some target =>
      simp only [SourceJudgment, sourceRules]
      exact .rule (fun premise _ => every_local inputs readout base site environment premise)
        (.cons (.rule (fun premise _ => every_local inputs readout base site environment premise) .nil) .nil)

/-- A genuinely decoded incoming state exists in the interface model. -/
def rootEnvironment (root : Root s View) : Environment (Payload s View) where
  root := .root root
  anchors := fun _ => ⟨.root root, ⟨[], 0⟩⟩
  publications := fun _ => none
  origin := 0

theorem root_decoded (readout : RuntimeReadout s View) (root : Root s View) :
    decode readout (rootEnvironment root) = some root.decoded := rfl

def formalContext : Context :=
  [{name := 0, owner := 10, kind := .formal, annotation := none,
    entry := some .value, singleUse := true},
   {name := 1, owner := 11, kind := .formal, annotation := none,
    entry := some .value, singleUse := false}]

def formalCallee : Source .expression := .name ⟨20, none⟩ 0
def formalArgument : Source .expression := .name ⟨21, none⟩ 1

/-- Nonvacuous input to `separation` for the conditional-origin TRUE branch.
The outer App mark, data, interfaces and occurrence remain arbitrary. -/
theorem formal_operands (inputs : Inputs s) (readout : RuntimeReadout s View)
    (base : LocalAdmissions s View) (site : Site)
    (environment : Environment (Payload s View)) :
    singletonFormalCall formalContext formalCallee formalArgument = true ∧
    SourceJudgment (kernel inputs readout base site) environment formalContext formalCallee ∧
    SourceJudgment (kernel inputs readout base site) environment formalContext formalArgument := by
  refine ⟨rfl, ?_, ?_⟩
  · simp only [formalCallee, SourceJudgment, sourceRules]
    exact .rule (fun premise _ => every_local inputs readout base site environment premise) .nil
  · simp only [formalArgument, SourceJudgment, sourceRules]
    exact .rule (fun premise _ => every_local inputs readout base site environment premise) .nil

end InterfaceModel

set_option pp.fullNames true
set_option pp.universes false
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.SourceAppAdmissionR159.app_continuation_iff with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.SourceAppAdmissionR159.app_continuation_iff is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.SourceAppAdmissionR159.app_continuation_iff"
#check @YulangClosure.SourceAppAdmissionR159.app_continuation_iff
#print axioms YulangClosure.SourceAppAdmissionR159.app_continuation_iff
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.SourceAppAdmissionR159.app_continuation_iff
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.SourceAppAdmissionR159.app_continuation_iff"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.SourceAppAdmissionR159.app_source_iff with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.SourceAppAdmissionR159.app_source_iff is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.SourceAppAdmissionR159.app_source_iff"
#check @YulangClosure.SourceAppAdmissionR159.app_source_iff
#print axioms YulangClosure.SourceAppAdmissionR159.app_source_iff
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.SourceAppAdmissionR159.app_source_iff
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.SourceAppAdmissionR159.app_source_iff"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.SourceAppAdmissionR159.admitted_view_iff with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.SourceAppAdmissionR159.admitted_view_iff is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.SourceAppAdmissionR159.admitted_view_iff"
#check @YulangClosure.SourceAppAdmissionR159.admitted_view_iff
#print axioms YulangClosure.SourceAppAdmissionR159.admitted_view_iff
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.SourceAppAdmissionR159.admitted_view_iff
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.SourceAppAdmissionR159.admitted_view_iff"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.SourceAppAdmissionR159.app_admission_iff with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.SourceAppAdmissionR159.app_admission_iff is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.SourceAppAdmissionR159.app_admission_iff"
#check @YulangClosure.SourceAppAdmissionR159.app_admission_iff
#print axioms YulangClosure.SourceAppAdmissionR159.app_admission_iff
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.SourceAppAdmissionR159.app_admission_iff
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.SourceAppAdmissionR159.app_admission_iff"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.SourceAppAdmissionR159.rejectApp_elsewhere with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.SourceAppAdmissionR159.rejectApp_elsewhere is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.SourceAppAdmissionR159.rejectApp_elsewhere"
#check @YulangClosure.SourceAppAdmissionR159.rejectApp_elsewhere
#print axioms YulangClosure.SourceAppAdmissionR159.rejectApp_elsewhere
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.SourceAppAdmissionR159.rejectApp_elsewhere
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.SourceAppAdmissionR159.rejectApp_elsewhere"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.SourceAppAdmissionR159.rejectApp_no_source with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.SourceAppAdmissionR159.rejectApp_no_source is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.SourceAppAdmissionR159.rejectApp_no_source"
#check @YulangClosure.SourceAppAdmissionR159.rejectApp_no_source
#print axioms YulangClosure.SourceAppAdmissionR159.rejectApp_no_source
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.SourceAppAdmissionR159.rejectApp_no_source
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.SourceAppAdmissionR159.rejectApp_no_source"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.SourceAppAdmissionR159.InterfaceModel.every_local with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.SourceAppAdmissionR159.InterfaceModel.every_local is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.SourceAppAdmissionR159.InterfaceModel.every_local"
#check @YulangClosure.SourceAppAdmissionR159.InterfaceModel.every_local
#print axioms YulangClosure.SourceAppAdmissionR159.InterfaceModel.every_local
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.SourceAppAdmissionR159.InterfaceModel.every_local
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.SourceAppAdmissionR159.InterfaceModel.every_local"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.SourceAppAdmissionR159.InterfaceModel.separation with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.SourceAppAdmissionR159.InterfaceModel.separation is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.SourceAppAdmissionR159.InterfaceModel.separation"
#check @YulangClosure.SourceAppAdmissionR159.InterfaceModel.separation
#print axioms YulangClosure.SourceAppAdmissionR159.InterfaceModel.separation
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.SourceAppAdmissionR159.InterfaceModel.separation
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.SourceAppAdmissionR159.InterfaceModel.separation"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.SourceAppAdmissionR159.InterfaceModel.literal_operand with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.SourceAppAdmissionR159.InterfaceModel.literal_operand is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.SourceAppAdmissionR159.InterfaceModel.literal_operand"
#check @YulangClosure.SourceAppAdmissionR159.InterfaceModel.literal_operand
#print axioms YulangClosure.SourceAppAdmissionR159.InterfaceModel.literal_operand
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.SourceAppAdmissionR159.InterfaceModel.literal_operand
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.SourceAppAdmissionR159.InterfaceModel.literal_operand"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.SourceAppAdmissionR159.InterfaceModel.root_decoded with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.SourceAppAdmissionR159.InterfaceModel.root_decoded is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.SourceAppAdmissionR159.InterfaceModel.root_decoded"
#check @YulangClosure.SourceAppAdmissionR159.InterfaceModel.root_decoded
#print axioms YulangClosure.SourceAppAdmissionR159.InterfaceModel.root_decoded
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.SourceAppAdmissionR159.InterfaceModel.root_decoded
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.SourceAppAdmissionR159.InterfaceModel.root_decoded"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.SourceAppAdmissionR159.InterfaceModel.formal_operands with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.SourceAppAdmissionR159.InterfaceModel.formal_operands is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.SourceAppAdmissionR159.InterfaceModel.formal_operands"
#check @YulangClosure.SourceAppAdmissionR159.InterfaceModel.formal_operands
#print axioms YulangClosure.SourceAppAdmissionR159.InterfaceModel.formal_operands
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.SourceAppAdmissionR159.InterfaceModel.formal_operands
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.SourceAppAdmissionR159.InterfaceModel.formal_operands"

end YulangClosure.SourceAppAdmissionR159
