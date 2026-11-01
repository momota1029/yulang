import YulangClosure.OriginalAppConstructionR160

/-!
R161: locate the original App consumer at its one admitted logical witness.

The selected native L/DeclContribution/profile construction remains the paper
construction selected by native-signature-formation-definition §§2–5. The
existing SourceSignatureConstruction.LeafLicensedField is explicitly only a
primitive/local leaf, not a licensed projection of composite DeclContribution.
This module neither reconstructs that grammar nor interprets opaque Descriptor
and Interface sorts or supplied Kernel.atom/FunctionGuards predicates.

The theorem is a necessary consequence of the unchanged R159 App judgment.
It retains the complete parent continuation and identifies descriptorFormation
at that very witness, together with its actual logical decode. It does not
derive P or independent A from native support, a leaf license, or a profile.
-/
namespace YulangClosure.SelectedNativeAppBridgeR161

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment
open SourceAppAdmissionR159

variable {s : Sorts} {View : Type}

/-- The original App must consume descriptor formation at the SAME occurrence,
payload and extension as independent logical admission and every continuation
premise. The two arbitrary operand derivations, finite Checking judgments,
conditional origin and both annotation alternatives remain in their full lists.
This implication is a consumer audit, not a native-to-original bridge. -/
theorem app_same_witness_consumers (inputs : Inputs s)
    (readout : RuntimeReadout s View) (admissions : LocalAdmissions s View)
    (original : Kernel (Payload s View)) (environment : Environment (Payload s View))
    (context : Context) (mark : Mark) (callee argument : Source .expression)
    (source : SourceJudgment (admissionKernel inputs readout admissions original)
      environment context (.app mark callee argument)) :
    let kernel := admissionKernel inputs readout admissions original
    (∀ premise ∈ annotationPremises context mark, Local kernel environment premise) ∧
    ∃ occurrence data state,
      decode readout environment = some state ∧
      admissions.logical state ⟨mark.site, .viewLogic, 0⟩ .viewLogic data ∧
      let after := environment.extend ⟨mark.site, .viewLogic, 0⟩
        (scopeCandidate environment occurrence (.logical .viewLogic data))
      decode readout after = some (state.logical data) ∧
      original.atom after
        (atom .descriptorFormation mark.site context [callee.site, argument.site]) ∧
      (state.logical data).assignment.event.eta = data.eta ∧
      (state.logical data).assignment.event.witness = data.witness ∧
      (state.logical data).viewMeaning = data.viewMeaning ∧
      (∀ premise ∈ appPremises context mark callee argument, Local kernel after premise) ∧
      SourceJudgment kernel after context callee ∧
      SourceJudgment kernel after context argument := by
  dsimp only
  obtain ⟨annotations, occurrence, data, state, decoded, admitted,
    locals, calleeProof, argumentProof⟩ :=
    (app_admission_iff inputs readout admissions original environment context mark callee argument).mp source
  have member : Premise.atom (atom .descriptorFormation mark.site context
      [callee.site, argument.site]) ∈ appPremises context mark callee argument := by
    simp [appPremises]
  have formation := (OriginalAppConstructionR160.formation_consumer_iff inputs readout
    admissions original environment context mark callee argument occurrence data).mp
      (locals _ member)
  exact ⟨annotations, occurrence, data, state, decoded, admitted,
    decode_extend readout environment ⟨mark.site, .viewLogic, 0⟩ _ state decoded,
    formation, rfl, rfl, rfl, locals, calleeProof, argumentProof⟩

end YulangClosure.SelectedNativeAppBridgeR161

set_option pp.fullNames true
set_option pp.universes false
run_cmd do
  match (← Lean.getEnv).find? `YulangClosure.SelectedNativeAppBridgeR161.app_same_witness_consumers with
  | some (.thmInfo _) => pure ()
  | _ => throwError "YulangClosure.SelectedNativeAppBridgeR161.app_same_witness_consumers is not a theorem declaration"
  Lean.logInfo "YULANG_AUDIT_BEGIN YulangClosure.SelectedNativeAppBridgeR161.app_same_witness_consumers"
#check @YulangClosure.SelectedNativeAppBridgeR161.app_same_witness_consumers
#print axioms YulangClosure.SelectedNativeAppBridgeR161.app_same_witness_consumers
run_cmd do
  let axioms ← Lean.collectAxioms `YulangClosure.SelectedNativeAppBridgeR161.app_same_witness_consumers
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "unapproved axiom: {ax}"
  Lean.logInfo "YULANG_AUDIT_END YulangClosure.SelectedNativeAppBridgeR161.app_same_witness_consumers"
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
