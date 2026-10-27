import YulangClosure.OriginalIdentityRealization
import YulangClosure.OriginalCalleeDelayProvenance

/-!
Original identity source-constructor provenance, before the frontend join.
All equations below use OriginalIdentityRealization.Identity itself. No runtime
program table, selected Closure, receipt payload or admission is manufactured.
The Lambda/Apply/Name-to-HIR and label interpretation remains an open owner
equation; consequently the Callee Delay prefix is not instantiated here.
-/
namespace YulangClosure.OriginalIdentityEntryOrigin

open OriginalSource OriginalSourceEnvironment OriginalSourceEvents
open OriginalParameterWorld OriginalFormalShared OriginalIdentityRealization

theorem identity_source (source : Identity) :
    source.parameter.source =
      .lambda ⟨source.lambdaSite, none⟩ ⟨source.formalSite, source.name, none, false⟩
        (.wild source.patternSite) (.name ⟨source.nameSite, none⟩ source.name) := rfl

theorem identity_registration (source : Identity) :
    (sourceEntries source.context source.parameter.source).head? =
      some source.parameter.registration :=
  parameter_registered source.parameter

theorem identity_registration_operands (source : Identity) :
    source.parameter.registration.site = source.formalSite ∧
    source.parameter.registration.entry = .value ∧
    source.parameter.registration.role.annotation = none ∧
    source.parameter.registration.role.entry = some .value ∧
    source.parameter.registration.receipt.operands =
      [source.lambdaSite, source.patternSite, source.nameSite] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem identity_closure_owner (source : Identity) :
    (sourceCallOwners source.context source.parameter.source).head? =
      some (.closure source.lambdaSite source.context source.formalSite
        source.patternSite source.nameSite) :=
  source_lambda_call_owner source.context source.lambdaSite source.parameter.formal
    source.parameter.pattern source.parameter.body

/-- The argument is the arbitrary original whole source expression. Its
syntax is retained under the same App; no Delay/body execution is asserted. -/
theorem identity_application_owners (source : Identity) (callSite : Site)
    (argument : Source .expression) :
    sourceCallOwners source.context
      (.app ⟨callSite, none⟩ source.parameter.source argument) =
      .application callSite source.context source.lambdaSite argument.site ::
        (sourceCallOwners source.context source.parameter.source ++
          sourceCallOwners source.context argument) :=
  source_app_call_owner source.context callSite source.parameter.source argument

theorem identity_application_ports (source : Identity) (callSite : Site)
    (argument : Source .expression) :
    ∃ atoms, sourceRules source.context
        (.app ⟨callSite, none⟩ source.parameter.source argument) =
      .existsE ⟨callSite, .viewLogic, 0⟩
        (.rule .app callSite source.context
          (atoms ++
            [.checking ⟨.value, callSite, source.context,
              ⟨source.lambdaSite, .returnedValue⟩, ⟨callSite, .descriptor⟩⟩,
             .checking ⟨.computation, callSite, source.context,
              ⟨callSite, .callableImage⟩, ⟨callSite, .synthesis⟩⟩])
          (.two (sourceRules source.context source.parameter.source)
            (sourceRules source.context argument))) :=
  OriginalSourceChecking.generated_application_ports source.context callSite
    source.parameter.source argument

theorem identity_invocation_owner (source : Identity) :
    (sourceOwners source.context source.parameter.source).head? =
      some (lambdaInvocationOwner source.lambdaSite source.parameter.formal) :=
  source_lambda_invocation source.context source.lambdaSite source.parameter.formal
    source.parameter.pattern source.parameter.body

theorem identity_receipt_owner (source : Identity) :
    ((sourceOwners source.context source.parameter.source).drop 1).head? =
      some (owner [0, 0, 0, 0]
        [⟨[], ⟨source.formalSite, .description, 0⟩⟩,
         ⟨[0], ⟨source.lambdaSite, .viewLogic, 0⟩⟩,
         ⟨[0, 0, 0], ⟨source.lambdaSite, .invocation, 0⟩⟩]
        ⟨source.formalSite, .receipt, 0⟩ .actualEvent) :=
  source_lambda_receipt source.context source.lambdaSite source.parameter.formal
    source.parameter.pattern source.parameter.body

theorem identity_value_entry_sequence (source : Identity) :
    enteredBody source.parameter =
      .executionE ⟨source.formalSite, .returnRebind, 0⟩
        (.sharedE ⟨source.formalSite, .shared, 0⟩ (checkedBody source.parameter)) := rfl

theorem identity_name_binding (source : Identity) :
    lookupBinding (bodyContext source.parameter) source.name =
      some {name := source.name, owner := source.formalSite, kind := .formal,
            entry := some .value, singleUse := true} :=
  identity_body_resolves_formal source

/-- The original Name's generated fetch observes the same resolved binding.
This does not claim a native Observe instruction or environment lookup. -/
theorem identity_name_rule (source : Identity) :
    sourceRules (bodyContext source.parameter) source.parameter.body =
      .rule .name source.nameSite (bodyContext source.parameter)
        [.atom {(atom .resolvedSameBinding source.nameSite (bodyContext source.parameter)) with
          names := [source.name], binding := lookupBinding (bodyContext source.parameter) source.name},
         .atom {(atom .computedFetchOnce source.nameSite (bodyContext source.parameter)) with
          names := [source.name], binding := lookupBinding (bodyContext source.parameter) source.name}]
        .nil := by
  change sourceRules (bodyContext source.parameter)
    (.name ⟨source.nameSite, none⟩ source.name) = _
  simp only [sourceRules, identity_name_binding]
  rfl

end YulangClosure.OriginalIdentityEntryOrigin
