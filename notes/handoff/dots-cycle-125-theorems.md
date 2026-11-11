# Cycle125: exact checked theorem signatures

All39 public theorem signatures, including implicit parameters (`#check @...`).
These are13 general component results and26 concrete regression results, not
completed B4 fields. General B4Bridges V3 remains12/12 unfilled.

Command: `lake env lean --trust=0 -j1 ../cache/yulang125/FinalSignatures.lean`, exit0.

```text
Yulang.GeneralDictionaryOutputBinderTerms.lookup_exact : ∀ (roles : Yulang.Roles.RoleDecls)
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture),
  List.Nodup.{0} (List.map.{0, 0} Yulang.GeneralDeclarations.Equation.name declaration.associated) →
    ∀ (name : Nat) (term : Yulang.Core.PresenceGeneration.TyTerm Nat),
      Eq.{1} (Yulang.GeneralDictionaryOutputBinderTerms.lookup roles declaration capture name) (some.{0} term) ↔
        Yulang.GeneralDictionaryOutputBinderTerms.Denotes roles declaration capture name term
Yulang.GeneralDictionaryOutputBinderTerms.denotes_functional : ∀ (roles : Yulang.Roles.RoleDecls)
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture),
  List.Nodup.{0} (List.map.{0, 0} Yulang.GeneralDeclarations.Equation.name declaration.associated) →
    ∀ (name : Nat) (first last : Yulang.Core.PresenceGeneration.TyTerm Nat),
      Yulang.GeneralDictionaryOutputBinderTerms.Denotes roles declaration capture name first →
        Yulang.GeneralDictionaryOutputBinderTerms.Denotes roles declaration capture name last → Eq.{1} first last
@Yulang.GeneralDictionaryOutputBinderTerms.denotes_has_producer : ∀ {roles : Yulang.Roles.RoleDecls}
  {constructors : Yulang.GeneralDeclarationPatterns.Constructors} {declaration : Yulang.GeneralDeclarations.Declaration}
  (checked : Yulang.GeneralDeclarations.DeclarationChecked constructors roles declaration)
  (capture : Yulang.GeneralDeclarationDemands.Capture) (name : Nat) (term : Yulang.Core.PresenceGeneration.TyTerm Nat),
  Yulang.GeneralDictionaryOutputBinderTerms.Denotes roles declaration capture name term →
    ∀
      (allocate :
        (clause : Yulang.GeneralDeclarations.Clause) → Yulang.GeneralDeclarationDemands.Allocation roles clause),
      Exists.{1} fun clause =>
        Exists.{0} fun present =>
          Exists.{1} fun equation =>
            Membership.mem.{0, 0} clause.outputs equation ∧
              Eq.{1} term
                  (Yulang.Core.PresenceGeneration.TyTerm.var
                    (Yulang.GeneralDeclarationDemands.outputTarget declaration capture (allocate clause).outputs
                      equation)) ∧
                Membership.mem.{0, 0}
                  (Yulang.GeneralDeclarationDemands.childDemand declaration clause ⋯ capture (allocate clause)).outputs
                  { name := equation.name,
                    target :=
                      Yulang.GeneralDeclarationDemands.outputTarget declaration capture (allocate clause).outputs
                        equation }
Yulang.GeneralDictionaryOutputBinderTerms.outputs_sources : ∀ (roles : Yulang.Roles.RoleDecls)
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (demand : Yulang.GeneralSourceState.Demand roles),
  Eq.{1}
    (List.map.{0, 0} Prod.fst.{0, 0}
      (Yulang.GeneralDictionaryOutputBinderTerms.outputs roles declaration capture demand))
    demand.outputs
@Yulang.GeneralDictionaryOutputBinderTerms.recorded_output_denotes : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} {demand : Yulang.GeneralSourceState.Demand roles}
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture),
  List.Nodup.{0} (List.map.{0, 0} Yulang.GeneralDeclarations.Equation.name declaration.associated) →
    ∀ (located : Yulang.GeneralDictionaryStateEquations.Located state demand),
      Yulang.GeneralDictionaryOutputBinderTerms.Interpreted declaration capture located →
        ∀ (assignment : Yulang.GeneralSourceState.Assignment),
          Yulang.GeneralSourceState.Models (Yulang.GeneralDictionaryEquationRecording.record located) assignment →
            ∀ (index : Fin (List.length.{0} demand.outputs)),
              Yulang.GeneralDictionaryOutputBinderTerms.Denotes roles declaration capture
                  (getElem.{0, 0, 0} demand.outputs index ⋯).name (located.equations.output index) ∧
                Yulang.Common.Equivalent
                  (Prod.fst.{0, 0} (assignment (getElem.{0, 0, 0} demand.outputs index ⋯).target))
                  (Yulang.Core.PresenceGeneration.TyTerm.eval.{0, 0} Yulang.Common.model assignment
                    (located.equations.output index))
@Yulang.GeneralDictionaryOutputBinderTerms.recorded_output_producer : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} {demand : Yulang.GeneralSourceState.Demand roles}
  {constructors : Yulang.GeneralDeclarationPatterns.Constructors} {declaration : Yulang.GeneralDeclarations.Declaration}
  (checked : Yulang.GeneralDeclarations.DeclarationChecked constructors roles declaration)
  (capture : Yulang.GeneralDeclarationDemands.Capture)
  (located : Yulang.GeneralDictionaryStateEquations.Located state demand),
  Yulang.GeneralDictionaryOutputBinderTerms.Interpreted declaration capture located →
    ∀
      (allocate :
        (clause : Yulang.GeneralDeclarations.Clause) → Yulang.GeneralDeclarationDemands.Allocation roles clause)
      (assignment : Yulang.GeneralSourceState.Assignment),
      Yulang.GeneralSourceState.Models (Yulang.GeneralDictionaryEquationRecording.record located) assignment →
        ∀ (index : Fin (List.length.{0} demand.outputs)),
          Exists.{1} fun clause =>
            Exists.{0} fun present =>
              Exists.{1} fun equation =>
                Membership.mem.{0, 0} clause.outputs equation ∧
                  Membership.mem.{0, 0}
                      (Yulang.GeneralDeclarationDemands.childDemand declaration clause ⋯ capture
                          (allocate clause)).outputs
                      { name := equation.name,
                        target :=
                          Yulang.GeneralDeclarationDemands.outputTarget declaration capture (allocate clause).outputs
                            equation } ∧
                    Yulang.Common.Equivalent
                      (Prod.fst.{0, 0} (assignment (getElem.{0, 0, 0} demand.outputs index ⋯).target))
                      (Prod.fst.{0, 0}
                        (assignment
                          (Yulang.GeneralDeclarationDemands.outputTarget declaration capture (allocate clause).outputs
                            equation)))
Yulang.GeneralDictionaryBinderLocations.sourceSlot_exact : ∀ (state : Yulang.GeneralSourceState.State) (source : Nat)
  (slot : Fin state.slots),
  Eq.{1} (Yulang.GeneralDictionaryBinderLocations.sourceSlot state source) (some.{0} slot) ↔
    Eq.{1} (state.source slot) source
Yulang.GeneralDictionaryBinderLocations.locateTerm_lifts : ∀ (state : Yulang.GeneralSourceState.State)
  (source : Yulang.Core.PresenceGeneration.TyTerm Nat)
  (localTerm : Yulang.Core.PresenceGeneration.TyTerm (Fin state.slots)),
  Eq.{1} (Yulang.GeneralDictionaryBinderLocations.locateTerm state source) (some.{0} localTerm) →
    Eq.{1} (Yulang.GeneralDictionaryStateEquations.liftType state localTerm) source
Yulang.GeneralDictionaryBinderLocations.compile_interpreted : ∀ (state : Yulang.GeneralSourceState.State)
  (roles : Yulang.Roles.RoleDecls) (declaration : Yulang.GeneralDeclarations.Declaration)
  (capture : Yulang.GeneralDeclarationDemands.Capture) (name : Nat)
  (term : Yulang.Core.PresenceGeneration.TyTerm (Fin state.slots)),
  Eq.{1} (Yulang.GeneralDictionaryBinderLocations.compile state roles declaration capture name) (some.{0} term) →
    Eq.{1} (Yulang.GeneralDictionaryOutputBinderTerms.lookup roles declaration capture name)
      (some.{0} (Yulang.GeneralDictionaryStateEquations.liftType state term))
Yulang.GeneralDictionaryBinderLocations.compile_source_complete : ∀ (state : Yulang.GeneralSourceState.State)
  (roles : Yulang.Roles.RoleDecls) (declaration : Yulang.GeneralDeclarations.Declaration)
  (capture : Yulang.GeneralDeclarationDemands.Capture) (name : Nat) (slot : Fin state.slots),
  Eq.{1} (Yulang.GeneralDictionaryOutputBinderTerms.lookup roles declaration capture name)
      (some.{0} (Yulang.Core.PresenceGeneration.TyTerm.var (state.source slot))) →
    Eq.{1} (Yulang.GeneralDictionaryBinderLocations.compile state roles declaration capture name)
      (some.{0} (Yulang.Core.PresenceGeneration.TyTerm.var slot))
Yulang.GeneralDictionaryBinderLocations.compile_slot_exact : ∀ (state : Yulang.GeneralSourceState.State)
  (roles : Yulang.Roles.RoleDecls) (declaration : Yulang.GeneralDeclarations.Declaration)
  (capture : Yulang.GeneralDeclarationDemands.Capture),
  List.Nodup.{0} (List.map.{0, 0} Yulang.GeneralDeclarations.Equation.name declaration.associated) →
    ∀ (name : Nat) (slot : Fin state.slots),
      Eq.{1} (Yulang.GeneralDictionaryBinderLocations.compile state roles declaration capture name)
          (some.{0} (Yulang.Core.PresenceGeneration.TyTerm.var slot)) ↔
        Yulang.GeneralDictionaryOutputBinderTerms.Denotes roles declaration capture name
          (Yulang.Core.PresenceGeneration.TyTerm.var (state.source slot))
@Yulang.GeneralDictionaryBinderLocations.build_interpreted : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} {demand : Yulang.GeneralSourceState.Demand roles}
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture)
  (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state demand)
  (located : Yulang.GeneralDictionaryStateEquations.Located state demand),
  Eq.{1} (Yulang.GeneralDictionaryBinderLocations.build declaration capture inputs) (some.{0} located) →
    Yulang.GeneralDictionaryOutputBinderTerms.Interpreted declaration capture located
@Yulang.GeneralDictionaryBinderLocations.built_output_denotes : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} {demand : Yulang.GeneralSourceState.Demand roles}
  (declaration : Yulang.GeneralDeclarations.Declaration) (capture : Yulang.GeneralDeclarationDemands.Capture),
  List.Nodup.{0} (List.map.{0, 0} Yulang.GeneralDeclarations.Equation.name declaration.associated) →
    ∀ (inputs : Yulang.GeneralDictionaryBinderLocations.Inputs state demand)
      (located : Yulang.GeneralDictionaryStateEquations.Located state demand),
      Eq.{1} (Yulang.GeneralDictionaryBinderLocations.build declaration capture inputs) (some.{0} located) →
        ∀ (assignment : Yulang.GeneralSourceState.Assignment),
          Yulang.GeneralSourceState.Models (Yulang.GeneralDictionaryEquationRecording.record located) assignment →
            ∀ (index : Fin (List.length.{0} demand.outputs)),
              Yulang.GeneralDictionaryOutputBinderTerms.Denotes roles declaration capture
                  (getElem.{0, 0, 0} demand.outputs index ⋯).name (located.equations.output index) ∧
                Yulang.Common.Equivalent
                  (Prod.fst.{0, 0} (assignment (getElem.{0, 0, 0} demand.outputs index ⋯).target))
                  (Yulang.Core.PresenceGeneration.TyTerm.eval.{0, 0} Yulang.Common.model assignment
                    (located.equations.output index))
Yulang.GeneralDictionaryOutputBinderExamples.binderWrap_checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDeclarationExamples.roles
  Yulang.GeneralDictionaryOutputBinderExamples.binderWrap
Yulang.GeneralDictionaryOutputBinderExamples.actual_rhs_lookup : Eq.{1}
  (Yulang.GeneralDictionaryOutputBinderTerms.lookup Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryOutputBinderExamples.binderWrap Yulang.GeneralDictionaryOutputBinderExamples.capture 0)
  (some.{0} (Yulang.Core.PresenceGeneration.TyTerm.var 2))
Yulang.GeneralDictionaryOutputBinderExamples.actual_rhs_denotes : Yulang.GeneralDictionaryOutputBinderTerms.Denotes
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryOutputBinderExamples.binderWrap
  Yulang.GeneralDictionaryOutputBinderExamples.capture 0 (Yulang.Core.PresenceGeneration.TyTerm.var 2)
Yulang.GeneralDictionaryOutputBinderExamples.child_producer_target : Eq.{1}
  (Yulang.GeneralDeclarationDemands.childDemand Yulang.GeneralDictionaryOutputBinderExamples.binderWrap
      Yulang.GeneralDeclarationExamples.containerChild ⋯ Yulang.GeneralDictionaryOutputBinderExamples.capture
      Yulang.GeneralDictionaryOutputBinderExamples.allocation).outputs
  (List.cons.{0} { name := 1, target := 2 } List.nil.{0})
Yulang.GeneralDictionaryOutputBinderExamples.compound_deferred : Eq.{1}
  (Yulang.GeneralDictionaryOutputBinderTerms.lookup Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDeclarationExamples.wrap Yulang.GeneralDictionaryOutputBinderExamples.capture 0)
  none.{0}
Yulang.GeneralDictionaryOutputBinderExamples.input_deferred : Eq.{1}
  (Yulang.GeneralDictionaryOutputBinderTerms.lookup Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryOutputBinderExamples.inputWrap Yulang.GeneralDictionaryOutputBinderExamples.capture 0)
  none.{0}
Yulang.GeneralDictionaryOutputBinderExamples.positional_default_retained : Eq.{1}
  (Yulang.GeneralDictionaryAssociatedProvenance.lookup Yulang.GeneralDictionaryOutputBinderExamples.defaultRoles
    Yulang.GeneralDictionaryOutputBinderExamples.defaultWrap 0)
  (some.{0} (Yulang.GeneralDictionaryAssociatedProvenance.Body.default 1 0 (Yulang.Roles.Term.var 0)))
Yulang.GeneralDictionaryOutputBinderExamples.default_deferred : Eq.{1}
  (Yulang.GeneralDictionaryOutputBinderTerms.lookup Yulang.GeneralDictionaryOutputBinderExamples.defaultRoles
    Yulang.GeneralDictionaryOutputBinderExamples.defaultWrap Yulang.GeneralDictionaryOutputBinderExamples.capture 0)
  none.{0}
Yulang.GeneralDictionaryOutputBinderExamples.repeated_root_targets : Eq.{1}
  (Yulang.GeneralDictionaryOutputBinderTerms.outputs Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryOutputBinderExamples.binderWrap Yulang.GeneralDictionaryOutputBinderExamples.capture
    Yulang.GeneralDictionaryOutputBinderExamples.demand)
  (List.cons.{0} (Prod.mk.{0, 0} { name := 0, target := 3 } (some.{0} (Yulang.Core.PresenceGeneration.TyTerm.var 2)))
    (List.cons.{0} (Prod.mk.{0, 0} { name := 0, target := 4 } (some.{0} (Yulang.Core.PresenceGeneration.TyTerm.var 2)))
      List.nil.{0}))
Yulang.GeneralDictionaryOutputBinderExamples.located_interpreted : Yulang.GeneralDictionaryOutputBinderTerms.Interpreted
  Yulang.GeneralDictionaryOutputBinderExamples.binderWrap Yulang.GeneralDictionaryOutputBinderExamples.capture
  Yulang.GeneralDictionaryOutputBinderExamples.located
Yulang.GeneralDictionaryOutputBinderExamples.recording_has_model : Yulang.GeneralSourceState.Models
  (Yulang.GeneralDictionaryEquationRecording.record Yulang.GeneralDictionaryOutputBinderExamples.located)
  Yulang.GeneralDictionaryOutputBinderExamples.assignment
Yulang.GeneralDictionaryOutputBinderExamples.all_model_binder_output : ∀ (model : Yulang.GeneralSourceState.Assignment),
  Yulang.GeneralSourceState.Models
      (Yulang.GeneralDictionaryEquationRecording.record Yulang.GeneralDictionaryOutputBinderExamples.located) model →
    ∀ (index : Fin (List.length.{0} Yulang.GeneralDictionaryOutputBinderExamples.demand.outputs)),
      Yulang.Common.Equivalent
        (Prod.fst.{0, 0}
          (model (getElem.{0, 0, 0} Yulang.GeneralDictionaryOutputBinderExamples.demand.outputs index ⋯).target))
        (Prod.fst.{0, 0} (model 2))
Yulang.GeneralDictionaryOutputBinderExamples.all_model_child_output : ∀ (model : Yulang.GeneralSourceState.Assignment),
  Yulang.GeneralSourceState.Models
      (Yulang.GeneralDictionaryEquationRecording.record Yulang.GeneralDictionaryOutputBinderExamples.located) model →
    ∀ (index : Fin (List.length.{0} Yulang.GeneralDictionaryOutputBinderExamples.demand.outputs)),
      Yulang.Common.Equivalent
        (Prod.fst.{0, 0}
          (model (getElem.{0, 0, 0} Yulang.GeneralDictionaryOutputBinderExamples.demand.outputs index ⋯).target))
        (Prod.fst.{0, 0}
          (model
            (Yulang.GeneralDeclarationDemands.outputTarget Yulang.GeneralDictionaryOutputBinderExamples.binderWrap
              Yulang.GeneralDictionaryOutputBinderExamples.capture
              Yulang.GeneralDictionaryOutputBinderExamples.allocation.outputs
              Yulang.GeneralDeclarationExamples.itemEquation)))
Yulang.GeneralDictionaryOutputBinderExamples.all_model_actual_producer : ∀
  (model : Yulang.GeneralSourceState.Assignment),
  Yulang.GeneralSourceState.Models
      (Yulang.GeneralDictionaryEquationRecording.record Yulang.GeneralDictionaryOutputBinderExamples.located) model →
    ∀ (index : Fin (List.length.{0} Yulang.GeneralDictionaryOutputBinderExamples.demand.outputs)),
      Exists.{1} fun clause =>
        Exists.{0} fun present =>
          Exists.{1} fun equation =>
            Membership.mem.{0, 0} clause.outputs equation ∧
              Membership.mem.{0, 0}
                  (Yulang.GeneralDeclarationDemands.childDemand Yulang.GeneralDictionaryOutputBinderExamples.binderWrap
                      clause ⋯ Yulang.GeneralDictionaryOutputBinderExamples.capture
                      (Yulang.GeneralDictionaryOutputBinderExamples.allocations clause)).outputs
                  { name := equation.name,
                    target :=
                      Yulang.GeneralDeclarationDemands.outputTarget
                        Yulang.GeneralDictionaryOutputBinderExamples.binderWrap
                        Yulang.GeneralDictionaryOutputBinderExamples.capture
                        (Yulang.GeneralDictionaryOutputBinderExamples.allocations clause).outputs equation } ∧
                Yulang.Common.Equivalent
                  (Prod.fst.{0, 0}
                    (model
                      (getElem.{0, 0, 0} Yulang.GeneralDictionaryOutputBinderExamples.demand.outputs index ⋯).target))
                  (Prod.fst.{0, 0}
                    (model
                      (Yulang.GeneralDeclarationDemands.outputTarget
                        Yulang.GeneralDictionaryOutputBinderExamples.binderWrap
                        Yulang.GeneralDictionaryOutputBinderExamples.capture
                        (Yulang.GeneralDictionaryOutputBinderExamples.allocations clause).outputs equation)))
Yulang.GeneralDictionaryOutputBinderExamples.repeated_equations_recorded : Eq.{1}
    (List.length.{0} Yulang.GeneralDictionaryOutputBinderExamples.demand.outputs) 2 ∧
  Eq.{1}
    (List.length.{0}
      (Yulang.GeneralDictionaryEquationRecording.atoms Yulang.GeneralDictionaryOutputBinderExamples.located))
    6
Yulang.GeneralDictionaryBinderLocationExamples.prior_source_lookup : Eq.{1}
  (Yulang.GeneralDictionaryBinderLocations.sourceSlot Yulang.GeneralDictionaryOutputBinderExamples.state 2) (some.{0} 2)
Yulang.GeneralDictionaryBinderLocationExamples.prior_rhs_compiles : Eq.{1}
  (Yulang.GeneralDictionaryBinderLocations.compile Yulang.GeneralDictionaryOutputBinderExamples.state
    Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryOutputBinderExamples.binderWrap
    Yulang.GeneralDictionaryOutputBinderExamples.capture 0)
  (some.{0} (Yulang.Core.PresenceGeneration.TyTerm.var 2))
Yulang.GeneralDictionaryBinderLocationExamples.reconstructs_prior_located : Eq.{1}
  (Yulang.GeneralDictionaryBinderLocations.build Yulang.GeneralDictionaryOutputBinderExamples.binderWrap
    Yulang.GeneralDictionaryOutputBinderExamples.capture Yulang.GeneralDictionaryBinderLocationExamples.inputs)
  (some.{0} Yulang.GeneralDictionaryOutputBinderExamples.located)
Yulang.GeneralDictionaryBinderLocationExamples.nonidentity_source_lookup : Eq.{1}
    (Yulang.GeneralDictionaryBinderLocations.sourceSlot Yulang.GeneralDictionaryBinderLocationExamples.shiftedState 12)
    (some.{0} 2) ∧
  Eq.{1}
    (Yulang.GeneralDictionaryBinderLocations.sourceSlot Yulang.GeneralDictionaryBinderLocationExamples.shiftedState 2)
    none.{0}
Yulang.GeneralDictionaryBinderLocationExamples.nonidentity_rhs_compiles : Eq.{1}
  (Yulang.GeneralDictionaryBinderLocations.compile Yulang.GeneralDictionaryBinderLocationExamples.shiftedState
    Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryOutputBinderExamples.binderWrap
    Yulang.GeneralDictionaryBinderLocationExamples.shiftedCapture 0)
  (some.{0} (Yulang.Core.PresenceGeneration.TyTerm.var 2))
Yulang.GeneralDictionaryBinderLocationExamples.nonidentity_lift_returns_actual_source : Eq.{1}
  (Yulang.GeneralDictionaryStateEquations.liftType Yulang.GeneralDictionaryBinderLocationExamples.shiftedState
    (Yulang.Core.PresenceGeneration.TyTerm.var 2))
  (Yulang.Core.PresenceGeneration.TyTerm.var 12)
Yulang.GeneralDictionaryBinderLocationExamples.builds_nonidentity_locations : Eq.{1}
  (Yulang.GeneralDictionaryBinderLocations.build Yulang.GeneralDictionaryOutputBinderExamples.binderWrap
    Yulang.GeneralDictionaryBinderLocationExamples.shiftedCapture
    Yulang.GeneralDictionaryBinderLocationExamples.shiftedInputs)
  (some.{0} Yulang.GeneralDictionaryBinderLocationExamples.shiftedLocated)
Yulang.GeneralDictionaryBinderLocationExamples.success_preserves_repeated_targets : Eq.{1}
  (Option.map.{0, 0}
    (fun result =>
      List.cons.{0} (Yulang.GeneralDictionaryBinderLocationExamples.shiftedState.source (result.target ⟨0, ⋯⟩))
        (List.cons.{0} (Yulang.GeneralDictionaryBinderLocationExamples.shiftedState.source (result.target ⟨1, ⋯⟩))
          List.nil.{0}))
    (Yulang.GeneralDictionaryBinderLocations.build Yulang.GeneralDictionaryOutputBinderExamples.binderWrap
      Yulang.GeneralDictionaryBinderLocationExamples.shiftedCapture
      Yulang.GeneralDictionaryBinderLocationExamples.shiftedInputs))
  (some.{0} (List.cons.{0} 13 (List.cons.{0} 14 List.nil.{0})))
Yulang.GeneralDictionaryBinderLocationExamples.missing_binder_source_defers : Eq.{1}
  (Yulang.GeneralDictionaryBinderLocations.build Yulang.GeneralDictionaryOutputBinderExamples.binderWrap
    Yulang.GeneralDictionaryBinderLocationExamples.absentCapture
    Yulang.GeneralDictionaryBinderLocationExamples.shiftedInputs)
  none.{0}
Yulang.GeneralDictionaryBinderLocationExamples.compound_defers_entire_build : Eq.{1}
  (Yulang.GeneralDictionaryBinderLocations.build Yulang.GeneralDeclarationExamples.wrap
    Yulang.GeneralDictionaryOutputBinderExamples.capture Yulang.GeneralDictionaryBinderLocationExamples.inputs)
  none.{0}
Yulang.GeneralDictionaryBinderLocationExamples.input_defers_entire_build : Eq.{1}
  (Yulang.GeneralDictionaryBinderLocations.build Yulang.GeneralDictionaryOutputBinderExamples.inputWrap
    Yulang.GeneralDictionaryOutputBinderExamples.capture Yulang.GeneralDictionaryBinderLocationExamples.inputs)
  none.{0}
```
