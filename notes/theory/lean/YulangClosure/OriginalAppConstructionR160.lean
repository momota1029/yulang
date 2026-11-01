import YulangClosure.SourceAppAdmissionR159

/-!
R160 source consumer audit. The selected native signature-formation definition
already supplies native support, licensing/incidence, and profile projections
within its scope. This module does not prove their witness-preserving
interpretation into the original App's descriptorFormation atom,
FunctionGuards, annotation/port evidence, or Logical payload at the same
ViewLogic occurrence. It also does not construct the independent original
initial-context admission A. The two theorems below reduce existing consumers
to the supplied relations; they are audit facts, not P/A scaffolding. The
unchanged full parent is SourceAppAdmissionR159.app_admission_iff.
-/
namespace YulangClosure.OriginalAppConstructionR160

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment

variable {s : Sorts} {View : Type}

/-- At the same original ViewLogic occurrence/extension, descriptor formation
is consumed from original.atom. The selected native profile still needs a
witness-preserving bridge to this exact consumer. All descriptor/interface
writes and arbitrary operands remain explicit; this is not that bridge. -/
theorem formation_consumer_iff (inputs : Inputs s)
    (readout : RuntimeReadout s View) (admissions : LocalAdmissions s View)
    (original : Kernel (Payload s View)) (environment : Environment (Payload s View))
    (context : Context) (mark : Mark) (callee argument : Source .expression)
    (occurrence : Nat) (data : Logical s View) :
    let after := environment.extend ⟨mark.site, .viewLogic, 0⟩
      (scopeCandidate environment occurrence (.logical .viewLogic data))
    Local (admissionKernel inputs readout admissions original) after
      (.atom (atom .descriptorFormation mark.site context [callee.site, argument.site])) ↔
    original.atom after
      (atom .descriptorFormation mark.site context [callee.site, argument.site]) := by
  dsimp only
  constructor
  · intro proof
    cases proof with
    | atom valid => exact valid
  · intro valid
    exact .atom valid

/-- The original App logical-data admission branch checks its kind and the
independent supplied relation. It contains no context-typing constructor. -/
theorem logical_admission_consumer_iff (inputs : Inputs s)
    (readout : RuntimeReadout s View) (admissions : LocalAdmissions s View)
    (state : Decoded s View) (mark : Mark) (data : Logical s View) :
    DataAdmitted inputs readout admissions state ⟨mark.site, .viewLogic, 0⟩
      (.logical .viewLogic data) ↔
    admissions.logical state ⟨mark.site, .viewLogic, 0⟩ .viewLogic data := by
  constructor
  · intro accepted
    exact accepted.2
  · intro accepted
    exact ⟨rfl, accepted⟩

end YulangClosure.OriginalAppConstructionR160

set_option pp.fullNames true
set_option pp.universes false
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalAppConstructionR160.formation_consumer_iff with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalAppConstructionR160.formation_consumer_iff is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalAppConstructionR160.formation_consumer_iff"
#check @YulangClosure.OriginalAppConstructionR160.formation_consumer_iff
#print axioms YulangClosure.OriginalAppConstructionR160.formation_consumer_iff
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalAppConstructionR160.formation_consumer_iff
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalAppConstructionR160.formation_consumer_iff"
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.OriginalAppConstructionR160.logical_admission_consumer_iff with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.OriginalAppConstructionR160.logical_admission_consumer_iff is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.OriginalAppConstructionR160.logical_admission_consumer_iff"
#check @YulangClosure.OriginalAppConstructionR160.logical_admission_consumer_iff
#print axioms YulangClosure.OriginalAppConstructionR160.logical_admission_consumer_iff
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.OriginalAppConstructionR160.logical_admission_consumer_iff
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.OriginalAppConstructionR160.logical_admission_consumer_iff"
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
