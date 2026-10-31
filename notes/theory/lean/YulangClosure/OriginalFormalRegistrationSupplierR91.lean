import YulangClosure.OriginalFormalAdmission
import YulangClosure.SourceRegistrationAppBridgeR90

/-!
R91: original declaration, actual Shared continuation, and App/Name seam.

Source-Generalize (2026-10-08) §§2–3 selects construction §§3–5, especially
§3.3's pre-invocation Desc / ViewLogic / Shared distinction. The original
intrusion parent (2026-10-13) §§1,3,5,7 remains open under the birth-level
correction (2026-10-24) §§2–6. Complete Call definition §§2–3 retains every
dependent source field; no opaque descriptor/interface is projected here.

`actual_build_shared_supplier` constructs the selected contract at the SAME
anchor used by the actual original Lambda rule, for both entry modes. It
stops at checkedBody. `app_formal_name_seam` inverts an actual App and its
resolved formal Name, including both annotations and the same App witness.
These are deliberately separate: neither a declaration-to-use equation nor
complete Gen-Call-0 follows from the current unrestricted logical admissions.
`event_proof_replacement_admitted` exhibits that precise interface gap. Its
permissive local interpretation is a discriminator, never adopted semantics.

No compiler/native correspondence, parent A/B, principality, termination or
production closure is claimed. Audit commands request types and full axioms;
only the primary's bounded direct runs can supply execution receipts.
-/
namespace YulangClosure.OriginalFormalRegistrationSupplierR91

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment
open OriginalParameterWorld OriginalFormalShared OriginalFormalAdmission

variable {s : Sorts} {View : Type}

/-- Exact result of the original Shared rule at this incoming environment.
This proposition is used only as the conclusion of the construction below. -/
def SharedSupply (kernel : Kernel (Payload s View)) (readout : RuntimeReadout s View)
    (parameter : Parameter) (environment : Environment (Payload s View))
    (contract : Contract s parameter.formal.entry) : Prop :=
  let delivered := environment.extend (sharedBinder parameter)
    (environment.anchorValue (sharedBinder parameter))
  ∃ after, decode readout delivered = some after ∧
    formalContract after parameter = contract ∧
    Judgment kernel delivered (checkedBody parameter)

/-- Value entry quantifies over its original actual Return domain;
Computation entry introduces no Force or returned Value. -/
def EntrySupply (kernel : Kernel (Payload s View)) (readout : RuntimeReadout s View)
    (parameter : Parameter) (environment : Environment (Payload s View))
    (contract : Contract s parameter.formal.entry) : Prop :=
  match parameter.formal.entry with
  | .value => ∀ returned, kernel.admitted environment (returnBinder parameter) returned →
      SharedSupply kernel readout parameter (environment.extend (returnBinder parameter) returned) contract
  | .computation => SharedSupply kernel readout parameter environment contract

/-- Applying actual Build inversion to the complete typed prior telescope
supplies the SAME generated Shared continuation. Assignment depends only on
the original declaration, occurrence route and pre-invocation ScopeValues.
No later invocation, body proof, return or App witness selects the contract. -/
theorem actual_build_shared_supplier (intro : Introduction s View)
    (assignment : FormalAssignment s View) (inputs : Inputs s)
    (readout : RuntimeReadout s View) (base : LocalAdmissions s View)
    (original : Kernel (Payload s View)) (prior : Prior s View)
    (annotation : Option Declaration)
    (solves : Satisfies (localKernel intro assignment inputs readout base original)
      (priorEnvironment intro prior)
      (Build intro.parameter.context (.lambda ⟨intro.parameter.lambdaSite, annotation⟩
        intro.parameter.formal intro.parameter.pattern intro.parameter.body))) :
    let environment := priorEnvironment intro prior
    let state := OriginalParameterSemantics.replayTelescope readout prior.root.decoded intro.telescope
    let kernel := localKernel intro assignment inputs readout base original
    ∃ description view packet,
      description.data = .logical .description (intro.description assignment state) ∧
      view.data = .logical .viewLogic (ViewPacket.encode (intro := intro) packet) ∧
      kernel.admitted environment (descriptionBinder intro.parameter) description ∧
      kernel.admitted (environment.extend (descriptionBinder intro.parameter) description)
        (viewBinder intro.parameter) view ∧
      ∀ invocation, kernel.admitted
        ((environment.extend (descriptionBinder intro.parameter) description).extend
          (viewBinder intro.parameter) view) (invocationBinder intro.parameter) invocation →
      ∃ receipt,
        kernel.admitted
          (((environment.extend (descriptionBinder intro.parameter) description).extend
            (viewBinder intro.parameter) view).extend (invocationBinder intro.parameter) invocation)
          (receiptBinder intro.parameter) receipt ∧
        EntrySupply kernel readout intro.parameter
          ((((environment.extend (descriptionBinder intro.parameter) description).extend
            (viewBinder intro.parameter) view).extend (invocationBinder intro.parameter) invocation).extend
            (receiptBinder intro.parameter) receipt)
          (intro.selection assignment).contract := by
  obtain ⟨description, view, packet, descPayload, viewPayload, descValid, viewValid, every⟩ :=
    actual_build_from_whole_telescope intro assignment inputs readout base original prior annotation solves
  refine ⟨description, view, packet, descPayload, viewPayload, descValid, viewValid, ?_⟩
  intro invocation invocationValid
  obtain ⟨receipt, state, receiptValid, decoded, selected, entry⟩ := every invocation invocationValid
  refine ⟨receipt, receiptValid, ?_⟩
  cases mode : intro.parameter.formal.entry with
  | value =>
    simp only [EntrySupply, mode]
    intro returned returnedValid
    obtain ⟨after, afterDecoded, kept, body⟩ :=
      value_entry_body_keeps_contract inputs readout intro assignment base original
        intro.parameter mode _ (invocation_receipt_open _ intro.parameter invocation receipt)
        state decoded entry returned returnedValid
    exact ⟨after, afterDecoded, kept.trans selected, body⟩
  | computation =>
    simp only [EntrySupply, mode]
    obtain ⟨after, afterDecoded, kept, body⟩ :=
      computation_entry_body_keeps_contract inputs readout intro assignment base original
        intro.parameter mode _ state decoded entry
    exact ⟨after, afterDecoded, kept.trans selected, body⟩

/-- The complete resolved Binding is retained in both original Name atoms.
In particular annotation, entry mode, owner and single-use data are not erased. -/
def namePremises (site : Site) (context : Context) (name : Name) (binding : Binding) :
    List Premise :=
  [.atom {(atom .resolvedSameBinding site context) with names := [name], binding := some binding},
   .atom {(atom .computedFetchOnce site context) with names := [name], binding := some binding}]

def nameCore (site : Site) (context : Context) (name : Name) (binding : Binding) : RuleTree :=
  .rule .name site context (namePremises site context name binding) .nil

/-- Constructor equation for arbitrary formal modes and source annotations.
Resolution is a lexical lookup premise, never an assumed contract readout. -/
theorem resolved_formal_name_rule (mark : Mark) (context : Context) (name : Name)
    (binding : Binding) (resolved : lookupBinding context name = some binding)
    (formal : binding.kind = .formal) :
    sourceRules context (.name mark name) =
      match mark.annotation with
      | none => nameCore mark.site context name binding
      | some target => .rule .annotation mark.site context
          (SourceRegistrationAppBridgeR90.annotationPremises mark.site context target)
          (.one (nameCore mark.site context name binding)) := by
  rcases mark with ⟨site, annotation⟩
  cases annotation <;> simp only [sourceRules, resolved, Option.map_some, formal] <;> rfl

/-- Both annotated and unannotated resolved formal Names expose the exact
original local atoms at their incoming environment, without a fresh witness. -/
theorem resolved_formal_name_iff {Value : Type} (kernel : Kernel Value)
    (environment : Environment Value) (mark : Mark) (context : Context) (name : Name)
    (binding : Binding) (resolved : lookupBinding context name = some binding)
    (formal : binding.kind = .formal) :
    SourceJudgment kernel environment context (.name mark name) ↔
      (match mark.annotation with
       | none => True
       | some target => ∀ premise ∈ SourceRegistrationAppBridgeR90.annotationPremises
           mark.site context target, Local kernel environment premise) ∧
      ∀ premise ∈ namePremises mark.site context name binding,
        Local kernel environment premise := by
  unfold SourceJudgment
  rw [resolved_formal_name_rule mark context name binding resolved formal]
  cases mark.annotation with
  | none =>
    constructor
    · intro derivation
      cases derivation with
      | rule locals children => exact ⟨True.intro, locals⟩
    · rintro ⟨_, locals⟩
      exact .rule locals .nil
  | some target =>
    constructor
    · intro derivation
      cases derivation with
      | rule annotations children =>
        cases children with
        | cons child tail =>
          cases child with
          | rule locals children => exact ⟨annotations, locals⟩
    · rintro ⟨annotations, locals⟩
      exact .rule annotations (.cons (.rule locals .nil) .nil)

/-- Actual R90 App application. The outer annotation, App binder, complete
local Call/checking premises and argument tree retain the original witness.
The callee's annotation and two resolved Name atoms use that same environment.
This theorem exposes, but does not replace, the missing semantic readout. -/
theorem app_formal_name_seam {Value : Type} (kernel : Kernel Value)
    (environment : Environment Value) (appMark nameMark : Mark) (context : Context)
    (name : Name) (binding : Binding) (argument : Source .expression)
    (resolved : lookupBinding context name = some binding) (formal : binding.kind = .formal)
    (derivation : SourceJudgment kernel environment context
      (.app appMark (.name nameMark name) argument)) :
    (match appMark.annotation with
     | none => True
     | some target => ∀ premise ∈ SourceRegistrationAppBridgeR90.annotationPremises
         appMark.site context target, Local kernel environment premise) ∧
    ∃ witness : ScopedValue Value,
      kernel.admitted environment ⟨appMark.site, .viewLogic, 0⟩ witness ∧
      (∀ premise ∈ SourceRegistrationAppBridgeR90.appPremises appMark.site context
          (.name nameMark name) argument,
        Local kernel (environment.extend ⟨appMark.site, .viewLogic, 0⟩ witness) premise) ∧
      (match nameMark.annotation with
       | none => True
       | some target => ∀ premise ∈ SourceRegistrationAppBridgeR90.annotationPremises
           nameMark.site context target,
           Local kernel (environment.extend ⟨appMark.site, .viewLogic, 0⟩ witness) premise) ∧
      (∀ premise ∈ namePremises nameMark.site context name binding,
        Local kernel (environment.extend ⟨appMark.site, .viewLogic, 0⟩ witness) premise) ∧
      SourceJudgment kernel (environment.extend ⟨appMark.site, .viewLogic, 0⟩ witness)
        context argument := by
  obtain ⟨annotation, witness, admitted, locals, callee, argumentProof⟩ :=
    (SourceRegistrationAppBridgeR90.app_derivation_iff kernel environment appMark context
      (.name nameMark name) argument).mp derivation
  obtain ⟨nameAnnotation, nameLocals⟩ :=
    (resolved_formal_name_iff kernel _ nameMark context name binding resolved formal).mp callee
  exact ⟨annotation, witness, admitted, locals, nameAnnotation, nameLocals, argumentProof⟩

/-- Interface discriminator, not an adopted original source law. With an
unrestricted base logical relation, the actual checkedBody EventProof binder
admits replacement of the selected contract in either mode. The replacement
is a concrete declaration payload, not a premise asserting a desired readout.
Thus a universal declaration-to-Name preservation claim needs an additional
source-owned logical admission/readout law before it can be constructed. -/
theorem event_proof_replacement_admitted (intro : Introduction s View)
    (assignment : FormalAssignment s View) (inputs : Inputs s)
    (readout : RuntimeReadout s View) (base : LocalAdmissions s View)
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state) (occurrence : Nat)
    (replacement : Contract s intro.parameter.formal.entry) :
    let binder : Binder := ⟨intro.parameter.body.site, .eventProof, 0⟩
    let data := declaration state intro.parameter replacement
    let candidate := scopeCandidate environment occurrence (.logical .eventProof data)
    let admissions := localAdmissions intro assignment
      {base with logical := fun _ _ _ _ => True}
    Admitted inputs readout admissions environment binder candidate ∧
      ∃ after, decode readout (environment.extend binder candidate) = some after ∧
        formalContract after intro.parameter = replacement := by
  dsimp only
  constructor
  · apply (admitted_scoped_iff inputs readout _ environment _ state decoded occurrence _).mpr
    exact ⟨rfl, True.intro⟩
  · refine ⟨_, decode_extend readout environment _ _ state decoded, ?_⟩
    exact declaration_selects state intro.parameter replacement

end YulangClosure.OriginalFormalRegistrationSupplierR91

#print YulangClosure.OriginalFormalRegistrationSupplierR91.SharedSupply
#print YulangClosure.OriginalFormalRegistrationSupplierR91.EntrySupply
#check @YulangClosure.OriginalFormalRegistrationSupplierR91.actual_build_shared_supplier
#print axioms YulangClosure.OriginalFormalRegistrationSupplierR91.actual_build_shared_supplier
#check @YulangClosure.OriginalFormalRegistrationSupplierR91.resolved_formal_name_rule
#print axioms YulangClosure.OriginalFormalRegistrationSupplierR91.resolved_formal_name_rule
#check @YulangClosure.OriginalFormalRegistrationSupplierR91.resolved_formal_name_iff
#print axioms YulangClosure.OriginalFormalRegistrationSupplierR91.resolved_formal_name_iff
#check @YulangClosure.OriginalFormalRegistrationSupplierR91.app_formal_name_seam
#print axioms YulangClosure.OriginalFormalRegistrationSupplierR91.app_formal_name_seam
#check @YulangClosure.OriginalFormalRegistrationSupplierR91.event_proof_replacement_admitted
#print axioms YulangClosure.OriginalFormalRegistrationSupplierR91.event_proof_replacement_admitted
