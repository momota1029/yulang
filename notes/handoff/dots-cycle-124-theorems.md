# Cycle124: exact checked theorem signatures

All79 audited theorem/certificate signatures, including every implicit parameter.
Frame, term, package and refinement premises remain visible. These are not79
completed B4 fields; general B4Bridges V3 is still12/12 unfilled.

Command: `lean --trust=0 -j1 cache/yulang124/FinalSignatures.lean`, exit0.

```text
Yulang.GeneralDictionaryEquationRecording.append_models : ∀ (state : Yulang.GeneralSourceState.State)
  (atoms : List.{0} (Yulang.PresenceNormalForm.Atom (Fin state.slots)))
  (assignment : Yulang.GeneralSourceState.Assignment),
  Iff (Yulang.GeneralSourceState.Models (Yulang.GeneralDictionaryEquationRecording.append state atoms) assignment)
    (And (Yulang.GeneralSourceState.Models state assignment)
      (@Yulang.PresenceNormalForm.All.{0, 0} (Fin state.slots) Yulang.Common.model (state.assignment assignment) atoms))
@Yulang.GeneralDictionaryEquationRecording.atoms_exact : ∀ {state : Yulang.GeneralSourceState.State}
  {roles : Yulang.Roles.RoleDecls} {demand : Yulang.GeneralSourceState.Demand roles}
  (located : @Yulang.GeneralDictionaryStateEquations.Located roles state demand)
  (assignment : Yulang.GeneralSourceState.Assignment),
  Iff
    (@Yulang.PresenceNormalForm.All.{0, 0} (Fin state.slots) Yulang.Common.model (state.assignment assignment)
      (@Yulang.GeneralDictionaryEquationRecording.atoms state roles demand located))
    (@Yulang.GeneralSourceDictionaryEquations.InstanceEquations.Holds roles demand
      (@Yulang.GeneralDictionaryStateEquations.Located.equations state roles demand located) assignment)
@Yulang.GeneralDictionaryEquationRecording.record_recorded : ∀ {state : Yulang.GeneralSourceState.State}
  {roles : Yulang.Roles.RoleDecls} {demand : Yulang.GeneralSourceState.Demand roles}
  (located : @Yulang.GeneralDictionaryStateEquations.Located roles state demand),
  @Yulang.GeneralDictionaryStateEquations.Recorded
    (@Yulang.GeneralDictionaryEquationRecording.record state roles demand located) roles demand
    (@Yulang.GeneralDictionaryEquationRecording.relocation state roles demand located)
@Yulang.GeneralDictionaryEquationRecording.record_models : ∀ {state : Yulang.GeneralSourceState.State}
  {roles : Yulang.Roles.RoleDecls} {demand : Yulang.GeneralSourceState.Demand roles}
  (located : @Yulang.GeneralDictionaryStateEquations.Located roles state demand)
  (assignment : Yulang.GeneralSourceState.Assignment),
  Iff
    (Yulang.GeneralSourceState.Models (@Yulang.GeneralDictionaryEquationRecording.record state roles demand located)
      assignment)
    (And (Yulang.GeneralSourceState.Models state assignment)
      (@Yulang.GeneralSourceDictionaryEquations.InstanceEquations.Holds roles demand
        (@Yulang.GeneralDictionaryStateEquations.Located.equations state roles demand located) assignment))
@Yulang.GeneralDictionaryEquationRecording.record_satisfiable : ∀ {state : Yulang.GeneralSourceState.State}
  {roles : Yulang.Roles.RoleDecls} {demand : Yulang.GeneralSourceState.Demand roles}
  (located : @Yulang.GeneralDictionaryStateEquations.Located roles state demand),
  Iff
    (@Exists.{1} Yulang.GeneralSourceState.Assignment fun assignment =>
      Yulang.GeneralSourceState.Models (@Yulang.GeneralDictionaryEquationRecording.record state roles demand located)
        assignment)
    (@Exists.{1} Yulang.GeneralSourceState.Assignment fun assignment =>
      And (Yulang.GeneralSourceState.Models state assignment)
        (@Yulang.GeneralSourceDictionaryEquations.InstanceEquations.Holds roles demand
          (@Yulang.GeneralDictionaryStateEquations.Located.equations state roles demand located) assignment))
@Yulang.GeneralDictionaryEquationRecording.record_conservative : ∀ {state : Yulang.GeneralSourceState.State}
  {roles : Yulang.Roles.RoleDecls} {demand : Yulang.GeneralSourceState.Demand roles}
  (located : @Yulang.GeneralDictionaryStateEquations.Located roles state demand),
  (∀ (assignment : Yulang.GeneralSourceState.Assignment),
      Yulang.GeneralSourceState.Models state assignment →
        @Yulang.GeneralSourceDictionaryEquations.InstanceEquations.Holds roles demand
          (@Yulang.GeneralDictionaryStateEquations.Located.equations state roles demand located) assignment) →
    ∀ (assignment : Yulang.GeneralSourceState.Assignment),
      Iff
        (Yulang.GeneralSourceState.Models (@Yulang.GeneralDictionaryEquationRecording.record state roles demand located)
          assignment)
        (Yulang.GeneralSourceState.Models state assignment)
@Yulang.GeneralDictionaryEquationRecording.relocation_equations : ∀ {state : Yulang.GeneralSourceState.State}
  {roles : Yulang.Roles.RoleDecls} {demand : Yulang.GeneralSourceState.Demand roles}
  (located : @Yulang.GeneralDictionaryStateEquations.Located roles state demand),
  @Eq.{1} (@Yulang.GeneralSourceDictionaryEquations.InstanceEquations roles demand)
    (@Yulang.GeneralDictionaryStateEquations.Located.equations
      (@Yulang.GeneralDictionaryEquationRecording.record state roles demand located) roles demand
      (@Yulang.GeneralDictionaryEquationRecording.relocation state roles demand located))
    (@Yulang.GeneralDictionaryStateEquations.Located.equations state roles demand located)
@Yulang.GeneralDictionaryBatchRecording.batch_models : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} (items : List.{0} (Yulang.GeneralDictionaryBatchRecording.Item roles state))
  (assignment : Yulang.GeneralSourceState.Assignment),
  Iff (Yulang.GeneralSourceState.Models (@Yulang.GeneralDictionaryBatchRecording.record roles state items) assignment)
    (And (Yulang.GeneralSourceState.Models state assignment)
      (∀ (item : Yulang.GeneralDictionaryBatchRecording.Item roles state),
        @Membership.mem.{0, 0} (Yulang.GeneralDictionaryBatchRecording.Item roles state)
            (List.{0} (Yulang.GeneralDictionaryBatchRecording.Item roles state))
            (@List.instMembership.{0} (Yulang.GeneralDictionaryBatchRecording.Item roles state)) items item →
          @Yulang.GeneralSourceDictionaryEquations.InstanceEquations.Holds roles
            (@Yulang.GeneralDictionaryBatchRecording.Item.demand roles state item)
            (@Yulang.GeneralDictionaryStateEquations.Located.equations state roles
              (@Yulang.GeneralDictionaryBatchRecording.Item.demand roles state item)
              (@Yulang.GeneralDictionaryBatchRecording.Item.located roles state item))
            assignment))
@Yulang.GeneralDictionaryBatchRecording.relocate_equations : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} {roles_1 : Yulang.Roles.RoleDecls}
  {demand : Yulang.GeneralSourceState.Demand roles_1}
  (items : List.{0} (Yulang.GeneralDictionaryBatchRecording.Item roles state))
  (located : @Yulang.GeneralDictionaryStateEquations.Located roles_1 state demand),
  @Eq.{1} (@Yulang.GeneralSourceDictionaryEquations.InstanceEquations roles_1 demand)
    (@Yulang.GeneralDictionaryStateEquations.Located.equations
      (@Yulang.GeneralDictionaryBatchRecording.record roles state items) roles_1 demand
      (@Yulang.GeneralDictionaryBatchRecording.relocate roles state roles_1 demand items located))
    (@Yulang.GeneralDictionaryStateEquations.Located.equations state roles_1 demand located)
@Yulang.GeneralDictionaryBatchRecording.batch_recorded : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} (items : List.{0} (Yulang.GeneralDictionaryBatchRecording.Item roles state))
  (item : Yulang.GeneralDictionaryBatchRecording.Item roles state),
  @Membership.mem.{0, 0} (Yulang.GeneralDictionaryBatchRecording.Item roles state)
      (List.{0} (Yulang.GeneralDictionaryBatchRecording.Item roles state))
      (@List.instMembership.{0} (Yulang.GeneralDictionaryBatchRecording.Item roles state)) items item →
    @Yulang.GeneralDictionaryStateEquations.Recorded (@Yulang.GeneralDictionaryBatchRecording.record roles state items)
      roles (@Yulang.GeneralDictionaryBatchRecording.Item.demand roles state item)
      (@Yulang.GeneralDictionaryBatchRecording.relocate roles state roles
        (@Yulang.GeneralDictionaryBatchRecording.Item.demand roles state item) items
        (@Yulang.GeneralDictionaryBatchRecording.Item.located roles state item))
@Yulang.GeneralDictionaryBatchRecording.batch_order_models : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State}
  (first last : List.{0} (Yulang.GeneralDictionaryBatchRecording.Item roles state)),
  @List.Perm.{0} (Yulang.GeneralDictionaryBatchRecording.Item roles state) first last →
    ∀ (assignment : Yulang.GeneralSourceState.Assignment),
      Iff
        (Yulang.GeneralSourceState.Models (@Yulang.GeneralDictionaryBatchRecording.record roles state first) assignment)
        (Yulang.GeneralSourceState.Models (@Yulang.GeneralDictionaryBatchRecording.record roles state last) assignment)
@Yulang.GeneralDictionaryBatchRecording.batch_satisfiable : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State}
  (items : List.{0} (Yulang.GeneralDictionaryBatchRecording.Item roles state)),
  Iff
    (@Exists.{1} Yulang.GeneralSourceState.Assignment fun assignment =>
      Yulang.GeneralSourceState.Models (@Yulang.GeneralDictionaryBatchRecording.record roles state items) assignment)
    (@Exists.{1} Yulang.GeneralSourceState.Assignment fun assignment =>
      And (Yulang.GeneralSourceState.Models state assignment)
        (∀ (item : Yulang.GeneralDictionaryBatchRecording.Item roles state),
          @Membership.mem.{0, 0} (Yulang.GeneralDictionaryBatchRecording.Item roles state)
              (List.{0} (Yulang.GeneralDictionaryBatchRecording.Item roles state))
              (@List.instMembership.{0} (Yulang.GeneralDictionaryBatchRecording.Item roles state)) items item →
            @Yulang.GeneralSourceDictionaryEquations.InstanceEquations.Holds roles
              (@Yulang.GeneralDictionaryBatchRecording.Item.demand roles state item)
              (@Yulang.GeneralDictionaryStateEquations.Located.equations state roles
                (@Yulang.GeneralDictionaryBatchRecording.Item.demand roles state item)
                (@Yulang.GeneralDictionaryBatchRecording.Item.located roles state item))
              assignment))
@Yulang.GeneralDictionaryBatchRecording.batch_conservative : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State}
  (items : List.{0} (Yulang.GeneralDictionaryBatchRecording.Item roles state)),
  (∀ (assignment : Yulang.GeneralSourceState.Assignment),
      Yulang.GeneralSourceState.Models state assignment →
        ∀ (item : Yulang.GeneralDictionaryBatchRecording.Item roles state),
          @Membership.mem.{0, 0} (Yulang.GeneralDictionaryBatchRecording.Item roles state)
              (List.{0} (Yulang.GeneralDictionaryBatchRecording.Item roles state))
              (@List.instMembership.{0} (Yulang.GeneralDictionaryBatchRecording.Item roles state)) items item →
            @Yulang.GeneralSourceDictionaryEquations.InstanceEquations.Holds roles
              (@Yulang.GeneralDictionaryBatchRecording.Item.demand roles state item)
              (@Yulang.GeneralDictionaryStateEquations.Located.equations state roles
                (@Yulang.GeneralDictionaryBatchRecording.Item.demand roles state item)
                (@Yulang.GeneralDictionaryBatchRecording.Item.located roles state item))
              assignment) →
    ∀ (assignment : Yulang.GeneralSourceState.Assignment),
      Iff
        (Yulang.GeneralSourceState.Models (@Yulang.GeneralDictionaryBatchRecording.record roles state items) assignment)
        (Yulang.GeneralSourceState.Models state assignment)
@Yulang.GeneralDictionaryBatchRecording.batch_append_models : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State}
  (first last : List.{0} (Yulang.GeneralDictionaryBatchRecording.Item roles state))
  (assignment : Yulang.GeneralSourceState.Assignment),
  Iff
    (Yulang.GeneralSourceState.Models
      (@Yulang.GeneralDictionaryBatchRecording.record roles state
        (@HAppend.hAppend.{0, 0, 0} (List.{0} (Yulang.GeneralDictionaryBatchRecording.Item roles state))
          (List.{0} (Yulang.GeneralDictionaryBatchRecording.Item roles state))
          (List.{0} (Yulang.GeneralDictionaryBatchRecording.Item roles state))
          (@instHAppendOfAppend.{0} (List.{0} (Yulang.GeneralDictionaryBatchRecording.Item roles state))
            (@List.instAppend.{0} (Yulang.GeneralDictionaryBatchRecording.Item roles state)))
          first last))
      assignment)
    (And
      (Yulang.GeneralSourceState.Models (@Yulang.GeneralDictionaryBatchRecording.record roles state first) assignment)
      (Yulang.GeneralSourceState.Models (@Yulang.GeneralDictionaryBatchRecording.record roles state last) assignment))
@Yulang.GeneralDictionaryTransactions.plannedAt_children_functional : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (terms : Yulang.GeneralDictionaryPlannedEvidence.TermInstances registry.roles state),
  @Yulang.GeneralDictionaryReadback.ChildrenFunctional registry.roles
    (@Yulang.GeneralDictionaryModelEvidence.StoredInstance registry.roles state
      (@Yulang.GeneralDictionaryTransactions.PlannedAt state registry checked frames terms))
@Yulang.GeneralDictionaryTransactions.dictionary_root : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} (tree : Yulang.GeneralDictionaryTransactions.Prepared roles state),
  @Eq.{1} (Yulang.GeneralSourceDictionaries.Occurrence roles)
    (@Yulang.GeneralSourceDictionaries.Dictionary.root roles
      (@Yulang.GeneralDictionaryTransactions.Prepared.dictionary roles state tree))
    (@Yulang.GeneralDictionaryTransactions.Prepared.root roles state tree)
@Yulang.GeneralDictionaryTransactions.dictionaries_map : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State}
  (children : List.{0} (Yulang.GeneralDictionaryTransactions.Prepared roles state)),
  @Eq.{1} (List.{0} (Yulang.GeneralSourceDictionaries.Dictionary roles))
    (@Yulang.GeneralDictionaryTransactions.dictionaries roles state children)
    (@List.map.{0, 0} (Yulang.GeneralDictionaryTransactions.Prepared roles state)
      (Yulang.GeneralSourceDictionaries.Dictionary roles)
      (@Yulang.GeneralDictionaryTransactions.Prepared.dictionary roles state) children)
@Yulang.GeneralDictionaryTransactions.dictionaries_roots : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State}
  (children : List.{0} (Yulang.GeneralDictionaryTransactions.Prepared roles state)),
  @Eq.{1} (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles))
    (@List.map.{0, 0} (Yulang.GeneralSourceDictionaries.Dictionary roles)
      (Yulang.GeneralSourceDictionaries.Occurrence roles) (@Yulang.GeneralSourceDictionaries.Dictionary.root roles)
      (@Yulang.GeneralDictionaryTransactions.dictionaries roles state children))
    (@List.map.{0, 0} (Yulang.GeneralDictionaryTransactions.Prepared roles state)
      (Yulang.GeneralSourceDictionaries.Occurrence roles)
      (@Yulang.GeneralDictionaryTransactions.Prepared.root roles state) children)
@Yulang.GeneralDictionaryTransactions.childItems_member : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State}
  (children : List.{0} (Yulang.GeneralDictionaryTransactions.Prepared roles state))
  (child : Yulang.GeneralDictionaryTransactions.Prepared roles state),
  @Membership.mem.{0, 0} (Yulang.GeneralDictionaryTransactions.Prepared roles state)
      (List.{0} (Yulang.GeneralDictionaryTransactions.Prepared roles state))
      (@List.instMembership.{0} (Yulang.GeneralDictionaryTransactions.Prepared roles state)) children child →
    ∀ (item : Yulang.GeneralDictionaryBatchRecording.Item roles state),
      @Membership.mem.{0, 0} (Yulang.GeneralDictionaryBatchRecording.Item roles state)
          (List.{0} (Yulang.GeneralDictionaryBatchRecording.Item roles state))
          (@List.instMembership.{0} (Yulang.GeneralDictionaryBatchRecording.Item roles state))
          (@Yulang.GeneralDictionaryTransactions.Prepared.items roles state child) item →
        @Membership.mem.{0, 0} (Yulang.GeneralDictionaryBatchRecording.Item roles state)
          (List.{0} (Yulang.GeneralDictionaryBatchRecording.Item roles state))
          (@List.instMembership.{0} (Yulang.GeneralDictionaryBatchRecording.Item roles state))
          (@Yulang.GeneralDictionaryTransactions.childItems roles state children) item
@Yulang.GeneralDictionaryTransactions.valid_stored_in : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (terms : Yulang.GeneralDictionaryPlannedEvidence.TermInstances registry.roles state)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  @Yulang.GeneralDictionaryTransactions.Valid state registry checked frames terms tree →
    ∀ (items : List.{0} (Yulang.GeneralDictionaryBatchRecording.Item registry.roles state)),
      (∀ (item : Yulang.GeneralDictionaryBatchRecording.Item registry.roles state),
          @Membership.mem.{0, 0} (Yulang.GeneralDictionaryBatchRecording.Item registry.roles state)
              (List.{0} (Yulang.GeneralDictionaryBatchRecording.Item registry.roles state))
              (@List.instMembership.{0} (Yulang.GeneralDictionaryBatchRecording.Item registry.roles state))
              (@Yulang.GeneralDictionaryTransactions.Prepared.items registry.roles state tree) item →
            @Membership.mem.{0, 0} (Yulang.GeneralDictionaryBatchRecording.Item registry.roles state)
              (List.{0} (Yulang.GeneralDictionaryBatchRecording.Item registry.roles state))
              (@List.instMembership.{0} (Yulang.GeneralDictionaryBatchRecording.Item registry.roles state)) items
              item) →
        @Yulang.GeneralSourceDictionaries.Evidence registry.roles
          (@Yulang.GeneralDictionaryModelEvidence.StoredInstance registry.roles
            (@Yulang.GeneralDictionaryBatchRecording.record registry.roles state items)
            (@Yulang.GeneralDictionaryTransactions.PlannedAt
              (@Yulang.GeneralDictionaryBatchRecording.record registry.roles state items) registry checked frames
              (@Yulang.GeneralDictionaryTransactions.LiftedTerms registry.roles state items terms)))
          (@Yulang.GeneralDictionaryTransactions.Prepared.dictionary registry.roles state tree)
@Yulang.GeneralDictionaryTransactions.transaction_stored : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (terms : Yulang.GeneralDictionaryPlannedEvidence.TermInstances registry.roles state)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  @Yulang.GeneralDictionaryTransactions.Valid state registry checked frames terms tree →
    @Yulang.GeneralSourceDictionaries.Evidence registry.roles
      (@Yulang.GeneralDictionaryModelEvidence.StoredInstance registry.roles
        (@Yulang.GeneralDictionaryBatchRecording.record registry.roles state
          (@Yulang.GeneralDictionaryTransactions.Prepared.items registry.roles state tree))
        (@Yulang.GeneralDictionaryTransactions.PlannedAt
          (@Yulang.GeneralDictionaryBatchRecording.record registry.roles state
            (@Yulang.GeneralDictionaryTransactions.Prepared.items registry.roles state tree))
          registry checked frames
          (@Yulang.GeneralDictionaryTransactions.LiftedTerms registry.roles state
            (@Yulang.GeneralDictionaryTransactions.Prepared.items registry.roles state tree) terms)))
      (@Yulang.GeneralDictionaryTransactions.Prepared.dictionary registry.roles state tree)
@Yulang.GeneralDictionaryTransactions.transaction_uniform : ∀ {state : Yulang.GeneralSourceState.State}
  (registry : Yulang.GeneralDeclarations.Registry) (checked : Yulang.GeneralDeclarations.Checked registry)
  (frames : Yulang.GeneralDictionaryTransactions.Frames registry.roles)
  (terms : Yulang.GeneralDictionaryPlannedEvidence.TermInstances registry.roles state)
  (tree : Yulang.GeneralDictionaryTransactions.Prepared registry.roles state),
  @Yulang.GeneralDictionaryTransactions.Valid state registry checked frames terms tree →
    @Exists.{1} (Yulang.GeneralSourceDictionaries.Dictionary registry.roles) fun witness =>
      And
        (@Yulang.GeneralSourceDictionaries.Readback registry.roles
          (@Yulang.GeneralDictionaryTransactions.Prepared.root registry.roles state tree)
          (@Yulang.GeneralSourceDictionaries.erase registry.roles
            (@Yulang.GeneralDictionaryTransactions.Prepared.dictionary registry.roles state tree))
          witness)
        (∀ (assignment : Yulang.GeneralSourceState.Assignment),
          Yulang.GeneralSourceState.Models
              (@Yulang.GeneralDictionaryBatchRecording.record registry.roles state
                (@Yulang.GeneralDictionaryTransactions.Prepared.items registry.roles state tree))
              assignment →
            @Yulang.GeneralSourceDictionaries.Evidence registry.roles
              (@Yulang.GeneralDictionaryModelEvidence.ModelInstance registry.roles
                (@Yulang.GeneralDictionaryBatchRecording.record registry.roles state
                  (@Yulang.GeneralDictionaryTransactions.Prepared.items registry.roles state tree))
                (@Yulang.GeneralDictionaryTransactions.PlannedAt
                  (@Yulang.GeneralDictionaryBatchRecording.record registry.roles state
                    (@Yulang.GeneralDictionaryTransactions.Prepared.items registry.roles state tree))
                  registry checked frames
                  (@Yulang.GeneralDictionaryTransactions.LiftedTerms registry.roles state
                    (@Yulang.GeneralDictionaryTransactions.Prepared.items registry.roles state tree) terms))
                assignment)
              witness)
@Yulang.GeneralDictionaryTransactions.transaction_models : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralSourceState.State} (tree : Yulang.GeneralDictionaryTransactions.Prepared roles state)
  (assignment : Yulang.GeneralSourceState.Assignment),
  Iff
    (Yulang.GeneralSourceState.Models
      (@Yulang.GeneralDictionaryBatchRecording.record roles state
        (@Yulang.GeneralDictionaryTransactions.Prepared.items roles state tree))
      assignment)
    (And (Yulang.GeneralSourceState.Models state assignment)
      (∀ (item : Yulang.GeneralDictionaryBatchRecording.Item roles state),
        @Membership.mem.{0, 0} (Yulang.GeneralDictionaryBatchRecording.Item roles state)
            (List.{0} (Yulang.GeneralDictionaryBatchRecording.Item roles state))
            (@List.instMembership.{0} (Yulang.GeneralDictionaryBatchRecording.Item roles state))
            (@Yulang.GeneralDictionaryTransactions.Prepared.items roles state tree) item →
          @Yulang.GeneralSourceDictionaryEquations.InstanceEquations.Holds roles
            (@Yulang.GeneralDictionaryBatchRecording.Item.demand roles state item)
            (@Yulang.GeneralDictionaryStateEquations.Located.equations state roles
              (@Yulang.GeneralDictionaryBatchRecording.Item.demand roles state item)
              (@Yulang.GeneralDictionaryBatchRecording.Item.located roles state item))
            assignment))
Yulang.GeneralDictionaryRecordingExamples.automatically_stored : @Yulang.GeneralDictionaryStateEquations.Recorded
  (@Yulang.GeneralDictionaryEquationRecording.record Yulang.GeneralDictionaryEquationExamples.state
    Yulang.GeneralDictionaryEquationExamples.roles Yulang.GeneralDictionaryEquationExamples.demand
    Yulang.GeneralDictionaryEquationExamples.located)
  Yulang.GeneralDictionaryEquationExamples.roles Yulang.GeneralDictionaryEquationExamples.demand
  (@Yulang.GeneralDictionaryEquationRecording.relocation Yulang.GeneralDictionaryEquationExamples.state
    Yulang.GeneralDictionaryEquationExamples.roles Yulang.GeneralDictionaryEquationExamples.demand
    Yulang.GeneralDictionaryEquationExamples.located)
Yulang.GeneralDictionaryRecordingExamples.nonvacuous : Yulang.GeneralSourceState.Models
  Yulang.GeneralDictionaryRecordingExamples.next Yulang.GeneralDictionaryEquationExamples.assignment
Yulang.GeneralDictionaryRecordingExamples.same_models : ∀ (model : Yulang.GeneralSourceState.Assignment),
  Iff (Yulang.GeneralSourceState.Models Yulang.GeneralDictionaryRecordingExamples.next model)
    (Yulang.GeneralSourceState.Models Yulang.GeneralDictionaryEquationExamples.state model)
Yulang.GeneralDictionaryRecordingExamples.source_ids_retained : And
  (@Eq.{1} Nat
    (Yulang.GeneralDictionaryRecordingExamples.next.source
      (@Fin.mk Yulang.GeneralDictionaryRecordingExamples.next.slots
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) ⋯))
    (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))
  (@Eq.{1} Nat
    (Yulang.GeneralDictionaryRecordingExamples.next.rowSource
      (@Fin.mk Yulang.GeneralDictionaryRecordingExamples.next.slots
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) ⋯))
    (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
Yulang.GeneralDictionaryRecordingExamples.repeated_outputs_retained : And
  (@Eq.{1} Nat
    (@List.length.{0} Yulang.GeneralSourceState.Output
      (@Yulang.GeneralSourceState.Demand.outputs Yulang.GeneralDictionaryEquationExamples.roles
        Yulang.GeneralDictionaryEquationExamples.demand))
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (@Eq.{1} Nat
    (@List.length.{0} (Yulang.PresenceNormalForm.Atom (Fin Yulang.GeneralDictionaryEquationExamples.state.slots))
      (@Yulang.GeneralDictionaryEquationRecording.atoms Yulang.GeneralDictionaryEquationExamples.state
        Yulang.GeneralDictionaryEquationExamples.roles Yulang.GeneralDictionaryEquationExamples.demand
        Yulang.GeneralDictionaryEquationExamples.located))
    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
Yulang.GeneralDictionaryRecordingExamples.incompatible_no_model : Not
  (@Exists.{1} Yulang.GeneralSourceState.Assignment fun model =>
    Yulang.GeneralSourceState.Models
      (@Yulang.GeneralDictionaryEquationRecording.record Yulang.GeneralDictionaryEquationExamples.state
        Yulang.GeneralDictionaryEquationExamples.roles Yulang.GeneralDictionaryEquationExamples.demand
        Yulang.GeneralDictionaryRecordingExamples.incompatible)
      model)
Yulang.GeneralDictionaryAssociatedProvenance.lookup_exact : ∀ (roles : Yulang.Roles.RoleDecls)
  (declaration : Yulang.GeneralDeclarations.Declaration),
  @List.Nodup.{0} Nat
      (@List.map.{0, 0} Yulang.GeneralDeclarations.Equation Nat Yulang.GeneralDeclarations.Equation.name
        declaration.associated) →
    ∀ (name : Nat) (body : Yulang.GeneralDictionaryAssociatedProvenance.Body),
      Iff
        (@Eq.{1} (Option.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body)
          (Yulang.GeneralDictionaryAssociatedProvenance.lookup roles declaration name)
          (@some.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body body))
        (Yulang.GeneralDictionaryAssociatedProvenance.Supplies roles declaration name body)
Yulang.GeneralDictionaryAssociatedProvenance.declared_covered : ∀ (roles : Yulang.Roles.RoleDecls)
  (declaration : Yulang.GeneralDeclarations.Declaration),
  Yulang.GeneralDeclarations.Declaration.Signature roles declaration →
    ∀ (name : Nat),
      (@Exists.{1} (Option.{0} Yulang.Roles.Term) fun value =>
          @Eq.{1} (Option.{0} (Option.{0} Yulang.Roles.Term)) ((roles declaration.role).assoc name)
            (@some.{0} (Option.{0} Yulang.Roles.Term) value)) →
        @Exists.{1} Yulang.GeneralDictionaryAssociatedProvenance.Body fun body =>
          Yulang.GeneralDictionaryAssociatedProvenance.Supplies roles declaration name body
Yulang.GeneralDictionaryAssociatedProvenance.supplies_unique : ∀ (roles : Yulang.Roles.RoleDecls)
  (declaration : Yulang.GeneralDeclarations.Declaration),
  @List.Nodup.{0} Nat
      (@List.map.{0, 0} Yulang.GeneralDeclarations.Equation Nat Yulang.GeneralDeclarations.Equation.name
        declaration.associated) →
    ∀ (name : Nat) (first last : Yulang.GeneralDictionaryAssociatedProvenance.Body),
      Yulang.GeneralDictionaryAssociatedProvenance.Supplies roles declaration name first →
        Yulang.GeneralDictionaryAssociatedProvenance.Supplies roles declaration name last →
          @Eq.{1} Yulang.GeneralDictionaryAssociatedProvenance.Body first last
@Yulang.GeneralDictionaryAssociatedProvenance.lookup_reorders : ∀ {first last : Yulang.GeneralDeclarations.Declaration}
  (roles : Yulang.Roles.RoleDecls),
  Yulang.GeneralRegistryReordering.DeclarationReorders first last →
    ∀ (name : Nat),
      @Eq.{1} (Option.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body)
        (Yulang.GeneralDictionaryAssociatedProvenance.lookup roles first name)
        (Yulang.GeneralDictionaryAssociatedProvenance.lookup roles last name)
@Yulang.GeneralDictionaryAssociatedProvenance.supplies_reorders : ∀
  {first last : Yulang.GeneralDeclarations.Declaration} (roles : Yulang.Roles.RoleDecls),
  Yulang.GeneralRegistryReordering.DeclarationReorders first last →
    ∀ (name : Nat) (body : Yulang.GeneralDictionaryAssociatedProvenance.Body),
      Iff (Yulang.GeneralDictionaryAssociatedProvenance.Supplies roles first name body)
        (Yulang.GeneralDictionaryAssociatedProvenance.Supplies roles last name body)
Yulang.GeneralDictionaryAssociatedProvenance.outputs_length : ∀ (roles : Yulang.Roles.RoleDecls)
  (declaration : Yulang.GeneralDeclarations.Declaration) (demand : Yulang.GeneralSourceState.Demand roles),
  @Eq.{1} Nat
    (@List.length.{0}
      (Prod.{0, 0} Yulang.GeneralSourceState.Output (Option.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body))
      (Yulang.GeneralDictionaryAssociatedProvenance.outputs roles declaration demand))
    (@List.length.{0} Yulang.GeneralSourceState.Output (@Yulang.GeneralSourceState.Demand.outputs roles demand))
Yulang.GeneralDictionaryAssociatedProvenance.outputs_sources : ∀ (roles : Yulang.Roles.RoleDecls)
  (declaration : Yulang.GeneralDeclarations.Declaration) (demand : Yulang.GeneralSourceState.Demand roles),
  @Eq.{1} (List.{0} Yulang.GeneralSourceState.Output)
    (@List.map.{0, 0}
      (Prod.{0, 0} Yulang.GeneralSourceState.Output (Option.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body))
      Yulang.GeneralSourceState.Output
      (@Prod.fst.{0, 0} Yulang.GeneralSourceState.Output (Option.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body))
      (Yulang.GeneralDictionaryAssociatedProvenance.outputs roles declaration demand))
    (@Yulang.GeneralSourceState.Demand.outputs roles demand)
Yulang.GeneralDictionaryAssociatedProvenance.outputs_at : ∀ (roles : Yulang.Roles.RoleDecls)
  (declaration : Yulang.GeneralDeclarations.Declaration) (demand : Yulang.GeneralSourceState.Demand roles)
  (index :
    Fin (@List.length.{0} Yulang.GeneralSourceState.Output (@Yulang.GeneralSourceState.Demand.outputs roles demand))),
  @Eq.{1} (Prod.{0, 0} Yulang.GeneralSourceState.Output (Option.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body))
    (@getElem.{0, 0, 0}
      (List.{0}
        (Prod.{0, 0} Yulang.GeneralSourceState.Output (Option.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body)))
      Nat (Prod.{0, 0} Yulang.GeneralSourceState.Output (Option.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body))
      (fun as i =>
        @LT.lt.{0} Nat instLTNat i
          (@List.length.{0}
            (Prod.{0, 0} Yulang.GeneralSourceState.Output
              (Option.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body))
            as))
      (@List.instGetElemNatLtLength.{0}
        (Prod.{0, 0} Yulang.GeneralSourceState.Output (Option.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body)))
      (Yulang.GeneralDictionaryAssociatedProvenance.outputs roles declaration demand)
      (@Fin.val
        (@List.length.{0} Yulang.GeneralSourceState.Output (@Yulang.GeneralSourceState.Demand.outputs roles demand))
        index)
      ⋯)
    (@Prod.mk.{0, 0} Yulang.GeneralSourceState.Output (Option.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body)
      (@getElem.{0, 0, 0} (List.{0} Yulang.GeneralSourceState.Output) Nat Yulang.GeneralSourceState.Output
        (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Yulang.GeneralSourceState.Output as))
        (@List.instGetElemNatLtLength.{0} Yulang.GeneralSourceState.Output)
        (@Yulang.GeneralSourceState.Demand.outputs roles demand)
        (@Fin.val
          (@List.length.{0} Yulang.GeneralSourceState.Output (@Yulang.GeneralSourceState.Demand.outputs roles demand))
          index)
        ⋯)
      (Yulang.GeneralDictionaryAssociatedProvenance.lookup roles declaration
        (@getElem.{0, 0, 0} (List.{0} Yulang.GeneralSourceState.Output) Nat Yulang.GeneralSourceState.Output
            (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Yulang.GeneralSourceState.Output as))
            (@List.instGetElemNatLtLength.{0} Yulang.GeneralSourceState.Output)
            (@Yulang.GeneralSourceState.Demand.outputs roles demand)
            (@Fin.val
              (@List.length.{0} Yulang.GeneralSourceState.Output
                (@Yulang.GeneralSourceState.Demand.outputs roles demand))
              index)
            ⋯).name))
Yulang.GeneralDictionaryAssociatedProvenance.outputs_complete : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (declaration : Yulang.GeneralDeclarations.Declaration),
  Yulang.GeneralDeclarations.DeclarationChecked registry.constructors registry.roles declaration →
    ∀ (demand : Yulang.GeneralSourceState.Demand registry.roles),
      @Eq.{1} Nat declaration.role (@Yulang.GeneralSourceState.Demand.role registry.roles demand) →
        ∀ (output : Yulang.GeneralSourceState.Output),
          @Membership.mem.{0, 0} Yulang.GeneralSourceState.Output (List.{0} Yulang.GeneralSourceState.Output)
              (@List.instMembership.{0} Yulang.GeneralSourceState.Output)
              (@Yulang.GeneralSourceState.Demand.outputs registry.roles demand) output →
            @Exists.{1} Yulang.GeneralDictionaryAssociatedProvenance.Body fun body =>
              And
                (@Membership.mem.{0, 0}
                  (Prod.{0, 0} Yulang.GeneralSourceState.Output
                    (Option.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body))
                  (List.{0}
                    (Prod.{0, 0} Yulang.GeneralSourceState.Output
                      (Option.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body)))
                  (@List.instMembership.{0}
                    (Prod.{0, 0} Yulang.GeneralSourceState.Output
                      (Option.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body)))
                  (Yulang.GeneralDictionaryAssociatedProvenance.outputs registry.roles declaration demand)
                  (@Prod.mk.{0, 0} Yulang.GeneralSourceState.Output
                    (Option.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body) output
                    (@some.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body body)))
                (Yulang.GeneralDictionaryAssociatedProvenance.Supplies registry.roles declaration output.name body)
@Yulang.GeneralDictionaryAssociatedProvenance.outputs_reorders : ∀ {first last : Yulang.GeneralDeclarations.Declaration}
  (roles : Yulang.Roles.RoleDecls),
  Yulang.GeneralRegistryReordering.DeclarationReorders first last →
    ∀ (demand : Yulang.GeneralSourceState.Demand roles),
      @Eq.{1}
        (List.{0}
          (Prod.{0, 0} Yulang.GeneralSourceState.Output (Option.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body)))
        (Yulang.GeneralDictionaryAssociatedProvenance.outputs roles first demand)
        (Yulang.GeneralDictionaryAssociatedProvenance.outputs roles last demand)
Yulang.GeneralDictionaryAssociatedProvenanceExamples.explicit_wins : @Eq.{1}
  (Option.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body)
  (Yulang.GeneralDictionaryAssociatedProvenance.lookup Yulang.GeneralDictionaryAssociatedProvenanceExamples.roles✝
    Yulang.GeneralDictionaryAssociatedProvenanceExamples.explicit✝
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@some.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body
    (Yulang.GeneralDictionaryAssociatedProvenance.Body.explicit
      Yulang.GeneralDictionaryAssociatedProvenanceExamples.equation✝))
Yulang.GeneralDictionaryAssociatedProvenanceExamples.positional_default : @Eq.{1}
  (Option.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body)
  (Yulang.GeneralDictionaryAssociatedProvenance.lookup Yulang.GeneralDictionaryAssociatedProvenanceExamples.roles✝
    Yulang.GeneralDictionaryAssociatedProvenanceExamples.fallback✝
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (@some.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body
    (Yulang.GeneralDictionaryAssociatedProvenance.Body.default
      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (Yulang.Roles.Term.var (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
Yulang.GeneralDictionaryAssociatedProvenanceExamples.undeclared_absent : @Eq.{1}
  (Option.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body)
  (Yulang.GeneralDictionaryAssociatedProvenance.lookup Yulang.GeneralDictionaryAssociatedProvenanceExamples.roles✝
    Yulang.GeneralDictionaryAssociatedProvenanceExamples.fallback✝
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
  (@none.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body)
Yulang.GeneralDictionaryAssociatedProvenanceExamples.repeated_name_distinct_targets : @Eq.{1}
  (List.{0}
    (Prod.{0, 0} Yulang.GeneralSourceState.Output (Option.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body)))
  (Yulang.GeneralDictionaryAssociatedProvenance.outputs Yulang.GeneralDictionaryAssociatedProvenanceExamples.roles✝
    Yulang.GeneralDictionaryAssociatedProvenanceExamples.fallback✝
    Yulang.GeneralDictionaryAssociatedProvenanceExamples.demand✝)
  (@List.cons.{0}
    (Prod.{0, 0} Yulang.GeneralSourceState.Output (Option.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body))
    (@Prod.mk.{0, 0} Yulang.GeneralSourceState.Output (Option.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body)
      { name := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)),
        target := @OfNat.ofNat.{0} Nat (nat_lit 21) (instOfNatNat (nat_lit 21)) }
      (@some.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body
        (Yulang.GeneralDictionaryAssociatedProvenance.Body.default
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (Yulang.Roles.Term.var (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
    (@List.cons.{0}
      (Prod.{0, 0} Yulang.GeneralSourceState.Output (Option.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body))
      (@Prod.mk.{0, 0} Yulang.GeneralSourceState.Output (Option.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body)
        { name := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)),
          target := @OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)) }
        (@some.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body
          (Yulang.GeneralDictionaryAssociatedProvenance.Body.default
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (Yulang.Roles.Term.var (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
      (@List.nil.{0}
        (Prod.{0, 0} Yulang.GeneralSourceState.Output (Option.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body)))))
Yulang.GeneralDictionaryPlannedOutputs.output_plan_functional : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (first last : Yulang.GeneralDictionaryPlannedOutputs.Result registry.roles),
  Yulang.GeneralDictionaryPlannedOutputs.OutputPlan registry checked frame root key first →
    Yulang.GeneralDictionaryPlannedOutputs.OutputPlan registry checked frame root key last →
      @Eq.{1} (Yulang.GeneralDictionaryPlannedOutputs.Result registry.roles) first last
Yulang.GeneralDictionaryPlannedOutputs.lookup_exact : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (result : Yulang.GeneralDictionaryPlannedOutputs.Result registry.roles),
  Iff
    (@Eq.{1} (Option.{0} (Yulang.GeneralDictionaryPlannedOutputs.Result registry.roles))
      (Yulang.GeneralDictionaryPlannedOutputs.lookup registry checked frame root key)
      (@some.{0} (Yulang.GeneralDictionaryPlannedOutputs.Result registry.roles) result))
    (Yulang.GeneralDictionaryPlannedOutputs.OutputPlan registry checked frame root key result)
Yulang.GeneralDictionaryPlannedOutputs.output_plan_children : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (result : Yulang.GeneralDictionaryPlannedOutputs.Result registry.roles),
  Yulang.GeneralDictionaryPlannedOutputs.OutputPlan registry checked frame root key result →
    Yulang.GeneralDictionaryEmissionPlans.Plan registry checked frame root key
      (@Prod.fst.{0, 0} (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence registry.roles))
        (List.{0}
          (Prod.{0, 0} Yulang.GeneralSourceState.Output (Option.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body)))
        result)
Yulang.GeneralDictionaryPlannedOutputs.output_plan_sources : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (result : Yulang.GeneralDictionaryPlannedOutputs.Result registry.roles),
  Yulang.GeneralDictionaryPlannedOutputs.OutputPlan registry checked frame root key result →
    @Eq.{1} (List.{0} Yulang.GeneralSourceState.Output)
      (@List.map.{0, 0}
        (Prod.{0, 0} Yulang.GeneralSourceState.Output (Option.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body))
        Yulang.GeneralSourceState.Output
        (@Prod.fst.{0, 0} Yulang.GeneralSourceState.Output
          (Option.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body))
        (@Prod.snd.{0, 0} (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence registry.roles))
          (List.{0}
            (Prod.{0, 0} Yulang.GeneralSourceState.Output
              (Option.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body)))
          result))
      (@Yulang.GeneralSourceState.Demand.outputs registry.roles
        (@Yulang.GeneralSourceDictionaries.Occurrence.demand registry.roles root))
Yulang.GeneralDictionaryPlannedOutputs.output_plan_covered : ∀ (registry : Yulang.GeneralDeclarations.Registry)
  (checked : Yulang.GeneralDeclarations.Checked registry)
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame registry.roles)
  (root : Yulang.GeneralSourceDictionaries.Occurrence registry.roles) (key : Nat)
  (result : Yulang.GeneralDictionaryPlannedOutputs.Result registry.roles),
  Yulang.GeneralDictionaryPlannedOutputs.OutputPlan registry checked frame root key result →
    ∀ (output : Yulang.GeneralSourceState.Output),
      @Membership.mem.{0, 0} Yulang.GeneralSourceState.Output (List.{0} Yulang.GeneralSourceState.Output)
          (@List.instMembership.{0} Yulang.GeneralSourceState.Output)
          (@Yulang.GeneralSourceState.Demand.outputs registry.roles
            (@Yulang.GeneralSourceDictionaries.Occurrence.demand registry.roles root))
          output →
        @Exists.{1} Yulang.GeneralDictionaryAssociatedProvenance.Body fun body =>
          @Membership.mem.{0, 0}
            (Prod.{0, 0} Yulang.GeneralSourceState.Output
              (Option.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body))
            (List.{0}
              (Prod.{0, 0} Yulang.GeneralSourceState.Output
                (Option.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body)))
            (@List.instMembership.{0}
              (Prod.{0, 0} Yulang.GeneralSourceState.Output
                (Option.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body)))
            (@Prod.snd.{0, 0} (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence registry.roles))
              (List.{0}
                (Prod.{0, 0} Yulang.GeneralSourceState.Output
                  (Option.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body)))
              result)
            (@Prod.mk.{0, 0} Yulang.GeneralSourceState.Output
              (Option.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body) output
              (@some.{0} Yulang.GeneralDictionaryAssociatedProvenance.Body body))
Yulang.GeneralDictionaryInvocationExamples.first_children : @Eq.{1}
  (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
  (@Yulang.GeneralDictionaryEmissionPlans.children Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDeclarationExamples.constructors
    (Yulang.GeneralDictionaryInvocationExamples.frames Yulang.GeneralDictionaryInvocationExamples.first)
    Yulang.GeneralDictionaryInvocationExamples.first Yulang.GeneralDeclarationExamples.wrap
    Yulang.GeneralDeclarationExamples.wrap_checked)
  (@List.cons.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
    (@Yulang.GeneralSourceDictionaries.Occurrence.mk Yulang.GeneralDeclarationExamples.roles
      (@OfNat.ofNat.{0} Nat (nat_lit 920) (instOfNatNat (nat_lit 920)))
      Yulang.GeneralDictionaryInvocationExamples.firstDemand)
    (@List.nil.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)))
Yulang.GeneralDictionaryInvocationExamples.second_children : @Eq.{1}
  (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
  (@Yulang.GeneralDictionaryEmissionPlans.children Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDeclarationExamples.constructors
    (Yulang.GeneralDictionaryInvocationExamples.frames Yulang.GeneralDictionaryInvocationExamples.second)
    Yulang.GeneralDictionaryInvocationExamples.second Yulang.GeneralDeclarationExamples.wrap
    Yulang.GeneralDeclarationExamples.wrap_checked)
  (@List.cons.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
    (@Yulang.GeneralSourceDictionaries.Occurrence.mk Yulang.GeneralDeclarationExamples.roles
      (@OfNat.ofNat.{0} Nat (nat_lit 1020) (instOfNatNat (nat_lit 1020)))
      Yulang.GeneralDictionaryInvocationExamples.secondDemand)
    (@List.nil.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)))
Yulang.GeneralDictionaryInvocationExamples.actual_distinct_source_demands : And
  (@Eq.{1} Yulang.GeneralSourceState.Interval
    (@Yulang.GeneralSourceState.Demand.arguments Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryInvocationExamples.firstDemand
      (@Fin.mk
        (Yulang.GeneralDeclarationExamples.roles
            (@Yulang.GeneralSourceState.Demand.role Yulang.GeneralDeclarationExamples.roles
              Yulang.GeneralDictionaryInvocationExamples.firstDemand)).arity
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) ⋯))
    (@Prod.mk.{0, 0} Nat Nat (@OfNat.ofNat.{0} Nat (nat_lit 100) (instOfNatNat (nat_lit 100)))
      (@OfNat.ofNat.{0} Nat (nat_lit 101) (instOfNatNat (nat_lit 101)))))
  (And
    (@Eq.{1} (List.{0} Yulang.GeneralSourceState.Output)
      (@Yulang.GeneralSourceState.Demand.outputs Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryInvocationExamples.firstDemand)
      (@List.cons.{0} Yulang.GeneralSourceState.Output
        { name := @OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)),
          target := @OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200)) }
        (@List.nil.{0} Yulang.GeneralSourceState.Output)))
    (And
      (@Eq.{1} Yulang.GeneralSourceState.Interval
        (@Yulang.GeneralSourceState.Demand.arguments Yulang.GeneralDeclarationExamples.roles
          Yulang.GeneralDictionaryInvocationExamples.secondDemand
          (@Fin.mk
            (Yulang.GeneralDeclarationExamples.roles
                (@Yulang.GeneralSourceState.Demand.role Yulang.GeneralDeclarationExamples.roles
                  Yulang.GeneralDictionaryInvocationExamples.secondDemand)).arity
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) ⋯))
        (@Prod.mk.{0, 0} Nat Nat (@OfNat.ofNat.{0} Nat (nat_lit 500) (instOfNatNat (nat_lit 500)))
          (@OfNat.ofNat.{0} Nat (nat_lit 501) (instOfNatNat (nat_lit 501)))))
      (@Eq.{1} (List.{0} Yulang.GeneralSourceState.Output)
        (@Yulang.GeneralSourceState.Demand.outputs Yulang.GeneralDeclarationExamples.roles
          Yulang.GeneralDictionaryInvocationExamples.secondDemand)
        (@List.cons.{0} Yulang.GeneralSourceState.Output
          { name := @OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)),
            target := @OfNat.ofNat.{0} Nat (nat_lit 600) (instOfNatNat (nat_lit 600)) }
          (@List.nil.{0} Yulang.GeneralSourceState.Output)))))
Yulang.GeneralDictionaryInvocationExamples.first_lookup : @Eq.{1}
  (Option.{0} (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.registry.roles)))
  (Yulang.GeneralDictionaryPlanLookup.lookup Yulang.GeneralDeclarationExamples.registry
    Yulang.GeneralDeclarationExamples.registry_checked
    (Yulang.GeneralDictionaryInvocationExamples.frames Yulang.GeneralDictionaryInvocationExamples.first)
    Yulang.GeneralDictionaryInvocationExamples.first (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (@some.{0} (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.registry.roles))
    (@List.cons.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.registry.roles)
      (@Yulang.GeneralSourceDictionaries.Occurrence.mk Yulang.GeneralDeclarationExamples.registry.roles
        (@OfNat.ofNat.{0} Nat (nat_lit 920) (instOfNatNat (nat_lit 920)))
        Yulang.GeneralDictionaryInvocationExamples.firstDemand)
      (@List.nil.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.registry.roles))))
Yulang.GeneralDictionaryInvocationExamples.second_lookup : @Eq.{1}
  (Option.{0} (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.registry.roles)))
  (Yulang.GeneralDictionaryPlanLookup.lookup Yulang.GeneralDeclarationExamples.registry
    Yulang.GeneralDeclarationExamples.registry_checked
    (Yulang.GeneralDictionaryInvocationExamples.frames Yulang.GeneralDictionaryInvocationExamples.second)
    Yulang.GeneralDictionaryInvocationExamples.second (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (@some.{0} (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.registry.roles))
    (@List.cons.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.registry.roles)
      (@Yulang.GeneralSourceDictionaries.Occurrence.mk Yulang.GeneralDeclarationExamples.registry.roles
        (@OfNat.ofNat.{0} Nat (nat_lit 1020) (instOfNatNat (nat_lit 1020)))
        Yulang.GeneralDictionaryInvocationExamples.secondDemand)
      (@List.nil.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.registry.roles))))
Yulang.GeneralDictionaryInvocationExamples.fixed_frame_outputs : ∀
  (frame : Yulang.GeneralDictionaryEmissionPlans.Frame Yulang.GeneralDeclarationExamples.roles)
  (one two : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles),
  @Eq.{1} (List.{0} (List.{0} Yulang.GeneralSourceState.Output))
    (@List.map.{0, 0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
      (List.{0} Yulang.GeneralSourceState.Output)
      (fun child =>
        @Yulang.GeneralSourceState.Demand.outputs Yulang.GeneralDeclarationExamples.roles
          (@Yulang.GeneralSourceDictionaries.Occurrence.demand Yulang.GeneralDeclarationExamples.roles child))
      (@Yulang.GeneralDictionaryEmissionPlans.children Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDeclarationExamples.constructors frame one Yulang.GeneralDeclarationExamples.wrap
        Yulang.GeneralDeclarationExamples.wrap_checked))
    (@List.map.{0, 0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
      (List.{0} Yulang.GeneralSourceState.Output)
      (fun child =>
        @Yulang.GeneralSourceState.Demand.outputs Yulang.GeneralDeclarationExamples.roles
          (@Yulang.GeneralSourceDictionaries.Occurrence.demand Yulang.GeneralDeclarationExamples.roles child))
      (@Yulang.GeneralDictionaryEmissionPlans.children Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDeclarationExamples.constructors frame two Yulang.GeneralDeclarationExamples.wrap
        Yulang.GeneralDeclarationExamples.wrap_checked))
Yulang.GeneralDictionaryInvocationExamples.fixed_frame_cannot_represent_both : Not
  (@Exists.{1} (Yulang.GeneralDictionaryEmissionPlans.Frame Yulang.GeneralDeclarationExamples.roles) fun frame =>
    And
      (@Eq.{1} (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
        (@Yulang.GeneralDictionaryEmissionPlans.children Yulang.GeneralDeclarationExamples.roles
          Yulang.GeneralDeclarationExamples.constructors frame Yulang.GeneralDictionaryInvocationExamples.first
          Yulang.GeneralDeclarationExamples.wrap Yulang.GeneralDeclarationExamples.wrap_checked)
        (@List.cons.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
          (@Yulang.GeneralSourceDictionaries.Occurrence.mk Yulang.GeneralDeclarationExamples.roles
            (@OfNat.ofNat.{0} Nat (nat_lit 920) (instOfNatNat (nat_lit 920)))
            Yulang.GeneralDictionaryInvocationExamples.firstDemand)
          (@List.nil.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))))
      (@Eq.{1} (List.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
        (@Yulang.GeneralDictionaryEmissionPlans.children Yulang.GeneralDeclarationExamples.roles
          Yulang.GeneralDeclarationExamples.constructors frame Yulang.GeneralDictionaryInvocationExamples.second
          Yulang.GeneralDeclarationExamples.wrap Yulang.GeneralDeclarationExamples.wrap_checked)
        (@List.cons.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
          (@Yulang.GeneralSourceDictionaries.Occurrence.mk Yulang.GeneralDeclarationExamples.roles
            (@OfNat.ofNat.{0} Nat (nat_lit 1020) (instOfNatNat (nat_lit 1020)))
            Yulang.GeneralDictionaryInvocationExamples.secondDemand)
          (@List.nil.{0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)))))
Yulang.GeneralDictionaryInvocationExamples.both_reordered_lookups : And
  (@Eq.{1}
    (Option.{0}
      (List.{0}
        (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDictionaryEmissionPlanExamples.reversed.roles)))
    (Yulang.GeneralDictionaryPlanLookup.lookup Yulang.GeneralDictionaryEmissionPlanExamples.reversed
      Yulang.GeneralDictionaryEmissionPlanExamples.reversed_checked
      (Yulang.GeneralDictionaryInvocationExamples.frames Yulang.GeneralDictionaryInvocationExamples.first)
      Yulang.GeneralDictionaryInvocationExamples.first (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@some.{0}
      (List.{0}
        (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDictionaryEmissionPlanExamples.reversed.roles))
      (@List.cons.{0}
        (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDictionaryEmissionPlanExamples.reversed.roles)
        (@Yulang.GeneralSourceDictionaries.Occurrence.mk Yulang.GeneralDictionaryEmissionPlanExamples.reversed.roles
          (@OfNat.ofNat.{0} Nat (nat_lit 920) (instOfNatNat (nat_lit 920)))
          Yulang.GeneralDictionaryInvocationExamples.firstDemand)
        (@List.nil.{0}
          (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDictionaryEmissionPlanExamples.reversed.roles)))))
  (@Eq.{1}
    (Option.{0}
      (List.{0}
        (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDictionaryEmissionPlanExamples.reversed.roles)))
    (Yulang.GeneralDictionaryPlanLookup.lookup Yulang.GeneralDictionaryEmissionPlanExamples.reversed
      Yulang.GeneralDictionaryEmissionPlanExamples.reversed_checked
      (Yulang.GeneralDictionaryInvocationExamples.frames Yulang.GeneralDictionaryInvocationExamples.second)
      Yulang.GeneralDictionaryInvocationExamples.second (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@some.{0}
      (List.{0}
        (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDictionaryEmissionPlanExamples.reversed.roles))
      (@List.cons.{0}
        (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDictionaryEmissionPlanExamples.reversed.roles)
        (@Yulang.GeneralSourceDictionaries.Occurrence.mk Yulang.GeneralDictionaryEmissionPlanExamples.reversed.roles
          (@OfNat.ofNat.{0} Nat (nat_lit 1020) (instOfNatNat (nat_lit 1020)))
          Yulang.GeneralDictionaryInvocationExamples.secondDemand)
        (@List.nil.{0}
          (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDictionaryEmissionPlanExamples.reversed.roles)))))
@Yulang.GeneralDictionaryRefinementEvidence.transport_recorded : ∀ {before after : Yulang.GeneralSourceState.State}
  {roles : Yulang.Roles.RoleDecls} {demand : Yulang.GeneralSourceState.Demand roles}
  (refinement : Yulang.GeneralSourceState.Refines before after)
  (located : @Yulang.GeneralDictionaryStateEquations.Located roles before demand),
  @Yulang.GeneralDictionaryStateEquations.Recorded before roles demand located →
    @Yulang.GeneralDictionaryStateEquations.Recorded after roles demand
      (@Yulang.GeneralDictionaryRefinementEvidence.transport before after roles demand refinement located)
@Yulang.GeneralDictionaryRefinementEvidence.assignment_comp_embed : ∀ {before after : Yulang.GeneralSourceState.State}
  (refinement : Yulang.GeneralSourceState.Refines before after) (assignment : Yulang.GeneralSourceState.Assignment),
  @Eq.{1} (Fin before.slots → Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model)
    (@Function.comp.{1, 1, 1} (Fin before.slots) (Fin after.slots)
      (Yulang.Core.PresenceGeneration.Comp.{0, 0} Yulang.Common.model) (after.assignment assignment)
      (@Yulang.GeneralSourceState.Refines.embed before after refinement))
    (before.assignment assignment)
@Yulang.GeneralDictionaryRefinementEvidence.liftType_transport_eval : ∀ {before after : Yulang.GeneralSourceState.State}
  (refinement : Yulang.GeneralSourceState.Refines before after)
  (term : Yulang.Core.PresenceGeneration.TyTerm (Fin before.slots)) (assignment : Yulang.GeneralSourceState.Assignment),
  @Eq.{1} Yulang.Common.model.Ty
    (@Yulang.Core.PresenceGeneration.TyTerm.eval.{0, 0} Nat Yulang.Common.model assignment
      (Yulang.GeneralDictionaryStateEquations.liftType after
        (@Yulang.Core.PresenceGeneration.TyTerm.rename (Fin before.slots) (Fin after.slots)
          (@Yulang.GeneralSourceState.Refines.embed before after refinement) term)))
    (@Yulang.Core.PresenceGeneration.TyTerm.eval.{0, 0} Nat Yulang.Common.model assignment
      (Yulang.GeneralDictionaryStateEquations.liftType before term))
@Yulang.GeneralDictionaryRefinementEvidence.transport_holds_iff : ∀ {before after : Yulang.GeneralSourceState.State}
  {roles : Yulang.Roles.RoleDecls} {demand : Yulang.GeneralSourceState.Demand roles}
  (refinement : Yulang.GeneralSourceState.Refines before after)
  (located : @Yulang.GeneralDictionaryStateEquations.Located roles before demand)
  (assignment : Yulang.GeneralSourceState.Assignment),
  Iff
    (@Yulang.GeneralSourceDictionaryEquations.InstanceEquations.Holds roles demand
      (@Yulang.GeneralDictionaryStateEquations.Located.equations after roles demand
        (@Yulang.GeneralDictionaryRefinementEvidence.transport before after roles demand refinement located))
      assignment)
    (@Yulang.GeneralSourceDictionaryEquations.InstanceEquations.Holds roles demand
      (@Yulang.GeneralDictionaryStateEquations.Located.equations before roles demand located) assignment)
@Yulang.GeneralDictionaryRefinementEvidence.stored_instance_transport : ∀
  {before after : Yulang.GeneralSourceState.State} {roles : Yulang.Roles.RoleDecls}
  (refinement : Yulang.GeneralSourceState.Refines before after)
  (packages : Yulang.GeneralDictionaryModelEvidence.Packages roles before)
  (occurrence : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
  (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles)),
  @Yulang.GeneralDictionaryModelEvidence.StoredInstance roles before packages occurrence key children →
    @Yulang.GeneralDictionaryModelEvidence.StoredInstance roles after
      (@Yulang.GeneralDictionaryRefinementEvidence.liftPackages before after roles refinement packages) occurrence key
      children
@Yulang.GeneralDictionaryRefinementEvidence.model_instance_transport_iff : ∀
  {before after : Yulang.GeneralSourceState.State} {roles : Yulang.Roles.RoleDecls}
  (refinement : Yulang.GeneralSourceState.Refines before after)
  (packages : Yulang.GeneralDictionaryModelEvidence.Packages roles before)
  (assignment : Yulang.GeneralSourceState.Assignment) (occurrence : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (key : Nat) (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles)),
  Iff
    (@Yulang.GeneralDictionaryModelEvidence.ModelInstance roles after
      (@Yulang.GeneralDictionaryRefinementEvidence.liftPackages before after roles refinement packages) assignment
      occurrence key children)
    (@Yulang.GeneralDictionaryModelEvidence.ModelInstance roles before packages assignment occurrence key children)
@Yulang.GeneralDictionaryRefinementEvidence.indexed_transport : ∀ {before after : Yulang.GeneralSourceState.State}
  {roles : Yulang.Roles.RoleDecls} (refinement : Yulang.GeneralSourceState.Refines before after)
  (packages : Yulang.GeneralDictionaryModelEvidence.Packages roles before)
  (tree : Yulang.GeneralSourceDictionaries.Dictionary roles),
  @Yulang.GeneralSourceDictionaries.Evidence roles
      (@Yulang.GeneralDictionaryModelEvidence.StoredInstance roles before packages) tree →
    @Yulang.GeneralSourceDictionaries.Evidence roles
      (@Yulang.GeneralDictionaryModelEvidence.StoredInstance roles after
        (@Yulang.GeneralDictionaryRefinementEvidence.liftPackages before after roles refinement packages))
      tree
@Yulang.GeneralDictionaryRefinementEvidence.indexed_transport_all_models : ∀
  {before after : Yulang.GeneralSourceState.State} {roles : Yulang.Roles.RoleDecls}
  (refinement : Yulang.GeneralSourceState.Refines before after)
  (packages : Yulang.GeneralDictionaryModelEvidence.Packages roles before)
  (tree : Yulang.GeneralSourceDictionaries.Dictionary roles),
  @Yulang.GeneralSourceDictionaries.Evidence roles
      (@Yulang.GeneralDictionaryModelEvidence.StoredInstance roles before packages) tree →
    ∀ (assignment : Yulang.GeneralSourceState.Assignment),
      Yulang.GeneralSourceState.Models after assignment →
        @Yulang.GeneralSourceDictionaries.Evidence roles
          (@Yulang.GeneralDictionaryModelEvidence.ModelInstance roles after
            (@Yulang.GeneralDictionaryRefinementEvidence.liftPackages before after roles refinement packages)
            assignment)
          tree
@Yulang.GeneralDictionaryRefinementEvidence.erased_transport_uniform_witness : ∀
  {before after : Yulang.GeneralSourceState.State} {roles : Yulang.Roles.RoleDecls}
  (refinement : Yulang.GeneralSourceState.Refines before after)
  (packages : Yulang.GeneralDictionaryModelEvidence.Packages roles before)
  (occurrence : Yulang.GeneralSourceDictionaries.Occurrence roles) (payload : Yulang.GeneralDictionaryReadback.Payload),
  @Yulang.GeneralSourceDictionaries.ErasedEvidence roles
      (@Yulang.GeneralDictionaryModelEvidence.StoredInstance roles before packages) occurrence payload →
    @Exists.{1} (Yulang.GeneralSourceDictionaries.Dictionary roles) fun tree =>
      And (@Yulang.GeneralSourceDictionaries.Readback roles occurrence payload tree)
        (And
          (@Yulang.GeneralSourceDictionaries.Evidence roles
            (@Yulang.GeneralDictionaryModelEvidence.StoredInstance roles after
              (@Yulang.GeneralDictionaryRefinementEvidence.liftPackages before after roles refinement packages))
            tree)
          (∀ (assignment : Yulang.GeneralSourceState.Assignment),
            Yulang.GeneralSourceState.Models after assignment →
              @Yulang.GeneralSourceDictionaries.Evidence roles
                (@Yulang.GeneralDictionaryModelEvidence.ModelInstance roles after
                  (@Yulang.GeneralDictionaryRefinementEvidence.liftPackages before after roles refinement packages)
                  assignment)
                tree))
Yulang.GeneralDictionaryRefinementExamples.proper_growth_and_reindex : And
  (@LT.lt.{0} Nat instLTNat Yulang.GeneralDictionaryEquationExamples.state.slots
    Yulang.GeneralDictionaryRefinementExamples.grown.slots)
  (And
    (@Eq.{1} (Fin Yulang.GeneralDictionaryRefinementExamples.grown.slots)
      (@Yulang.GeneralSourceState.Refines.embed Yulang.GeneralDictionaryEquationExamples.state
        Yulang.GeneralDictionaryRefinementExamples.grown Yulang.GeneralDictionaryRefinementExamples.refinement
        (@OfNat.ofNat.{0} (Fin Yulang.GeneralDictionaryEquationExamples.state.slots) (nat_lit 0)
          (@Fin.instOfNat Yulang.GeneralDictionaryEquationExamples.state.slots ⋯ (nat_lit 0))))
      (@OfNat.ofNat.{0} (Fin Yulang.GeneralDictionaryRefinementExamples.grown.slots) (nat_lit 1)
        (@Fin.instOfNat Yulang.GeneralDictionaryRefinementExamples.grown.slots ⋯ (nat_lit 1))))
    (And
      (@Eq.{1} Nat
        (Yulang.GeneralDictionaryRefinementExamples.grown.source
          (@OfNat.ofNat.{0} (Fin Yulang.GeneralDictionaryRefinementExamples.grown.slots) (nat_lit 0)
            (@Fin.instOfNat Yulang.GeneralDictionaryRefinementExamples.grown.slots ⋯ (nat_lit 0))))
        (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
      (And
        (@Eq.{1} Nat
          (Yulang.GeneralDictionaryRefinementExamples.grown.source
            (@Yulang.GeneralSourceState.Refines.embed Yulang.GeneralDictionaryEquationExamples.state
              Yulang.GeneralDictionaryRefinementExamples.grown Yulang.GeneralDictionaryRefinementExamples.refinement
              (@OfNat.ofNat.{0} (Fin Yulang.GeneralDictionaryEquationExamples.state.slots) (nat_lit 0)
                (@Fin.instOfNat Yulang.GeneralDictionaryEquationExamples.state.slots ⋯ (nat_lit 0)))))
          (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))
        (@Eq.{1} Nat
          (Yulang.GeneralDictionaryRefinementExamples.grown.rowSource
            (@Yulang.GeneralSourceState.Refines.embed Yulang.GeneralDictionaryEquationExamples.state
              Yulang.GeneralDictionaryRefinementExamples.grown Yulang.GeneralDictionaryRefinementExamples.refinement
              (@OfNat.ofNat.{0} (Fin Yulang.GeneralDictionaryEquationExamples.state.slots) (nat_lit 0)
                (@Fin.instOfNat Yulang.GeneralDictionaryEquationExamples.state.slots ⋯ (nat_lit 0)))))
          (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))))
Yulang.GeneralDictionaryRefinementExamples.grown_models : Yulang.GeneralSourceState.Models
  Yulang.GeneralDictionaryRefinementExamples.grown Yulang.GeneralDictionaryEquationExamples.assignment
Yulang.GeneralDictionaryRefinementExamples.transported_recorded : @Yulang.GeneralDictionaryStateEquations.Recorded
  Yulang.GeneralDictionaryRefinementExamples.grown Yulang.GeneralDictionaryEquationExamples.roles
  Yulang.GeneralDictionaryEquationExamples.demand
  (@Yulang.GeneralDictionaryRefinementEvidence.transport Yulang.GeneralDictionaryEquationExamples.state
    Yulang.GeneralDictionaryRefinementExamples.grown Yulang.GeneralDictionaryEquationExamples.roles
    Yulang.GeneralDictionaryEquationExamples.demand Yulang.GeneralDictionaryRefinementExamples.refinement
    Yulang.GeneralDictionaryEquationExamples.located)
Yulang.GeneralDictionaryRefinementExamples.reindexed_arrow_sources : @Eq.{1} (Yulang.Core.PresenceGeneration.TyTerm Nat)
  (Yulang.GeneralDictionaryStateEquations.liftType Yulang.GeneralDictionaryRefinementExamples.grown
    (@Yulang.Core.PresenceGeneration.TyTerm.rename (Fin Yulang.GeneralDictionaryEquationExamples.state.slots)
      (Fin Yulang.GeneralDictionaryRefinementExamples.grown.slots)
      (@Yulang.GeneralSourceState.Refines.embed Yulang.GeneralDictionaryEquationExamples.state
        Yulang.GeneralDictionaryRefinementExamples.grown Yulang.GeneralDictionaryRefinementExamples.refinement)
      (@Yulang.Core.PresenceGeneration.TyTerm.arrow (Fin Yulang.GeneralDictionaryEquationExamples.state.slots)
        (@Yulang.Core.PresenceGeneration.TyTerm.var (Fin Yulang.GeneralDictionaryEquationExamples.state.slots)
          (@OfNat.ofNat.{0} (Fin Yulang.GeneralDictionaryEquationExamples.state.slots) (nat_lit 0)
            (@Fin.instOfNat Yulang.GeneralDictionaryEquationExamples.state.slots ⋯ (nat_lit 0))))
        (@Yulang.Core.PresenceGeneration.RowTerm.var (Fin Yulang.GeneralDictionaryEquationExamples.state.slots)
          (@OfNat.ofNat.{0} (Fin Yulang.GeneralDictionaryEquationExamples.state.slots) (nat_lit 0)
            (@Fin.instOfNat Yulang.GeneralDictionaryEquationExamples.state.slots ⋯ (nat_lit 0))))
        (@Yulang.Core.PresenceGeneration.TyTerm.var (Fin Yulang.GeneralDictionaryEquationExamples.state.slots)
          (@OfNat.ofNat.{0} (Fin Yulang.GeneralDictionaryEquationExamples.state.slots) (nat_lit 0)
            (@Fin.instOfNat Yulang.GeneralDictionaryEquationExamples.state.slots ⋯ (nat_lit 0))))
        (@Yulang.Core.PresenceGeneration.RowTerm.var (Fin Yulang.GeneralDictionaryEquationExamples.state.slots)
          (@OfNat.ofNat.{0} (Fin Yulang.GeneralDictionaryEquationExamples.state.slots) (nat_lit 0)
            (@Fin.instOfNat Yulang.GeneralDictionaryEquationExamples.state.slots ⋯ (nat_lit 0)))))))
  (@Yulang.Core.PresenceGeneration.TyTerm.arrow Nat
    (@Yulang.Core.PresenceGeneration.TyTerm.var Nat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))
    (@Yulang.Core.PresenceGeneration.RowTerm.var Nat (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
    (@Yulang.Core.PresenceGeneration.TyTerm.var Nat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))
    (@Yulang.Core.PresenceGeneration.RowTerm.var Nat (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
Yulang.GeneralDictionaryRefinementExamples.unchanged_three_node_tree : And
  (@Yulang.GeneralSourceDictionaries.Evidence Yulang.GeneralDictionaryEquationExamples.roles
    (@Yulang.GeneralDictionaryModelEvidence.StoredInstance Yulang.GeneralDictionaryEquationExamples.roles
      Yulang.GeneralDictionaryRefinementExamples.grown
      (@Yulang.GeneralDictionaryRefinementEvidence.liftPackages Yulang.GeneralDictionaryEquationExamples.state
        Yulang.GeneralDictionaryRefinementExamples.grown Yulang.GeneralDictionaryEquationExamples.roles
        Yulang.GeneralDictionaryRefinementExamples.refinement Yulang.GeneralDictionaryReadbackExamples.Package))
    Yulang.GeneralDictionaryReadbackExamples.tree)
  (@Eq.{1} (List.{0} Nat)
    (@List.map.{0, 0}
      (Prod.{0, 0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDictionaryEquationExamples.roles) Nat) Nat
      (fun event =>
        @Yulang.GeneralSourceDictionaries.Occurrence.identity Yulang.GeneralDictionaryEquationExamples.roles
          (@Prod.fst.{0, 0} (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDictionaryEquationExamples.roles)
            Nat event))
      (@Yulang.GeneralSourceDictionaries.observations Yulang.GeneralDictionaryEquationExamples.roles
        Yulang.GeneralDictionaryReadbackExamples.tree))
    (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 100) (instOfNatNat (nat_lit 100)))
      (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 101) (instOfNatNat (nat_lit 101)))
        (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 102) (instOfNatNat (nat_lit 102))) (@List.nil.{0} Nat)))))
Yulang.GeneralDictionaryRefinementExamples.all_refined_models : ∀ (model : Yulang.GeneralSourceState.Assignment),
  Yulang.GeneralSourceState.Models Yulang.GeneralDictionaryRefinementExamples.grown model →
    @Yulang.GeneralSourceDictionaries.Evidence Yulang.GeneralDictionaryEquationExamples.roles
      (@Yulang.GeneralDictionaryModelEvidence.ModelInstance Yulang.GeneralDictionaryEquationExamples.roles
        Yulang.GeneralDictionaryRefinementExamples.grown
        (@Yulang.GeneralDictionaryRefinementEvidence.liftPackages Yulang.GeneralDictionaryEquationExamples.state
          Yulang.GeneralDictionaryRefinementExamples.grown Yulang.GeneralDictionaryEquationExamples.roles
          Yulang.GeneralDictionaryRefinementExamples.refinement Yulang.GeneralDictionaryReadbackExamples.Package)
        model)
      Yulang.GeneralDictionaryReadbackExamples.tree
Yulang.GeneralDictionaryRefinementExamples.nonvacuous_refined_tree : And
  (Yulang.GeneralSourceState.Models Yulang.GeneralDictionaryRefinementExamples.grown
    Yulang.GeneralDictionaryEquationExamples.assignment)
  (@Yulang.GeneralSourceDictionaries.Evidence Yulang.GeneralDictionaryEquationExamples.roles
    (@Yulang.GeneralDictionaryModelEvidence.ModelInstance Yulang.GeneralDictionaryEquationExamples.roles
      Yulang.GeneralDictionaryRefinementExamples.grown
      (@Yulang.GeneralDictionaryRefinementEvidence.liftPackages Yulang.GeneralDictionaryEquationExamples.state
        Yulang.GeneralDictionaryRefinementExamples.grown Yulang.GeneralDictionaryEquationExamples.roles
        Yulang.GeneralDictionaryRefinementExamples.refinement Yulang.GeneralDictionaryReadbackExamples.Package)
      Yulang.GeneralDictionaryEquationExamples.assignment)
    Yulang.GeneralDictionaryReadbackExamples.tree)
Yulang.GeneralDictionaryBatchExamples.free_models : ∀ (assignment : Yulang.GeneralSourceState.Assignment),
  Yulang.GeneralSourceState.Models Yulang.GeneralDictionaryBatchExamples.free assignment
Yulang.GeneralDictionaryBatchExamples.package_holds : ∀ (base : Yulang.Inference.Base),
  @Yulang.GeneralSourceDictionaryEquations.InstanceEquations.Holds Yulang.GeneralDictionaryEquationExamples.roles
    (@Yulang.GeneralDictionaryBatchRecording.Item.demand Yulang.GeneralDictionaryEquationExamples.roles
      Yulang.GeneralDictionaryBatchExamples.free (Yulang.GeneralDictionaryBatchExamples.package base))
    (@Yulang.GeneralDictionaryStateEquations.Located.equations Yulang.GeneralDictionaryBatchExamples.free
      Yulang.GeneralDictionaryEquationExamples.roles
      (@Yulang.GeneralDictionaryBatchRecording.Item.demand Yulang.GeneralDictionaryEquationExamples.roles
        Yulang.GeneralDictionaryBatchExamples.free (Yulang.GeneralDictionaryBatchExamples.package base))
      (@Yulang.GeneralDictionaryBatchRecording.Item.located Yulang.GeneralDictionaryEquationExamples.roles
        Yulang.GeneralDictionaryBatchExamples.free (Yulang.GeneralDictionaryBatchExamples.package base)))
    (Yulang.GeneralDictionaryBatchExamples.valuation base)
Yulang.GeneralDictionaryBatchExamples.separately_satisfiable : ∀ (base : Yulang.Inference.Base),
  Yulang.GeneralSourceState.Models
    (@Yulang.GeneralDictionaryBatchRecording.record Yulang.GeneralDictionaryEquationExamples.roles
      Yulang.GeneralDictionaryBatchExamples.free
      (@List.cons.{0}
        (Yulang.GeneralDictionaryBatchRecording.Item Yulang.GeneralDictionaryEquationExamples.roles
          Yulang.GeneralDictionaryBatchExamples.free)
        (Yulang.GeneralDictionaryBatchExamples.package base)
        (@List.nil.{0}
          (Yulang.GeneralDictionaryBatchRecording.Item Yulang.GeneralDictionaryEquationExamples.roles
            Yulang.GeneralDictionaryBatchExamples.free))))
    (Yulang.GeneralDictionaryBatchExamples.valuation base)
Yulang.GeneralDictionaryBatchExamples.joint_inconsistent : Not
  (@Exists.{1} Yulang.GeneralSourceState.Assignment fun assignment =>
    Yulang.GeneralSourceState.Models
      (@Yulang.GeneralDictionaryBatchRecording.record Yulang.GeneralDictionaryEquationExamples.roles
        Yulang.GeneralDictionaryBatchExamples.free
        (@List.cons.{0}
          (Yulang.GeneralDictionaryBatchRecording.Item Yulang.GeneralDictionaryEquationExamples.roles
            Yulang.GeneralDictionaryBatchExamples.free)
          (Yulang.GeneralDictionaryBatchExamples.package Yulang.Inference.Base.int)
          (@List.cons.{0}
            (Yulang.GeneralDictionaryBatchRecording.Item Yulang.GeneralDictionaryEquationExamples.roles
              Yulang.GeneralDictionaryBatchExamples.free)
            (Yulang.GeneralDictionaryBatchExamples.package Yulang.Inference.Base.str)
            (@List.nil.{0}
              (Yulang.GeneralDictionaryBatchRecording.Item Yulang.GeneralDictionaryEquationExamples.roles
                Yulang.GeneralDictionaryBatchExamples.free)))))
      assignment)
Yulang.GeneralDictionaryBatchExamples.order_preserves_joint_failure : Not
  (@Exists.{1} Yulang.GeneralSourceState.Assignment fun assignment =>
    Yulang.GeneralSourceState.Models
      (@Yulang.GeneralDictionaryBatchRecording.record Yulang.GeneralDictionaryEquationExamples.roles
        Yulang.GeneralDictionaryBatchExamples.free
        (@List.cons.{0}
          (Yulang.GeneralDictionaryBatchRecording.Item Yulang.GeneralDictionaryEquationExamples.roles
            Yulang.GeneralDictionaryBatchExamples.free)
          (Yulang.GeneralDictionaryBatchExamples.package Yulang.Inference.Base.str)
          (@List.cons.{0}
            (Yulang.GeneralDictionaryBatchRecording.Item Yulang.GeneralDictionaryEquationExamples.roles
              Yulang.GeneralDictionaryBatchExamples.free)
            (Yulang.GeneralDictionaryBatchExamples.package Yulang.Inference.Base.int)
            (@List.nil.{0}
              (Yulang.GeneralDictionaryBatchRecording.Item Yulang.GeneralDictionaryEquationExamples.roles
                Yulang.GeneralDictionaryBatchExamples.free)))))
      assignment)
Yulang.GeneralDictionaryBatchExamples.repeated_package_atoms : @Eq.{1} Nat
  (@List.length.{0} (Yulang.PresenceNormalForm.Atom (Fin Yulang.GeneralDictionaryBatchExamples.free.slots))
    (@Yulang.GeneralDictionaryBatchRecording.batchAtoms Yulang.GeneralDictionaryEquationExamples.roles
      Yulang.GeneralDictionaryBatchExamples.free
      (@List.cons.{0}
        (Yulang.GeneralDictionaryBatchRecording.Item Yulang.GeneralDictionaryEquationExamples.roles
          Yulang.GeneralDictionaryBatchExamples.free)
        (Yulang.GeneralDictionaryBatchExamples.package Yulang.Inference.Base.int)
        (@List.cons.{0}
          (Yulang.GeneralDictionaryBatchRecording.Item Yulang.GeneralDictionaryEquationExamples.roles
            Yulang.GeneralDictionaryBatchExamples.free)
          (Yulang.GeneralDictionaryBatchExamples.package Yulang.Inference.Base.int)
          (@List.nil.{0}
            (Yulang.GeneralDictionaryBatchRecording.Item Yulang.GeneralDictionaryEquationExamples.roles
              Yulang.GeneralDictionaryBatchExamples.free))))))
  (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
Yulang.GeneralDictionaryEquationRecording.append_refines : (state : Yulang.GeneralSourceState.State) →
  (atoms : List.{0} (Yulang.PresenceNormalForm.Atom (Fin state.slots))) →
    Yulang.GeneralSourceState.Refines state (Yulang.GeneralDictionaryEquationRecording.append state atoms)
```
