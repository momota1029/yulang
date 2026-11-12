# Cycle138 exact declaration signatures

Lean4.35.0 #check with full names/universes: 99 declarations = 97 public theorems + 2 proof certificates. All dependent premises retained. This is not 99 completed B4 obligations.

```lean
Yulang.GeneralDictionarySourceChoiceVisibility.visible {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (formed : Yulang.GeneralNominalFeedbackSteps.SourceFormed registry root state)
  (packet : Yulang.GeneralNominalSaturationState.Packet roles) :
  Membership.mem.{0, 0} state.packets packet → Membership.mem.{0, 0} registry.declarations packet.declaration
Yulang.GeneralDictionarySourceChoiceVisibility.singleton_choice {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (formed : Yulang.GeneralNominalFeedbackSteps.SourceFormed registry root state)
  (declaration : Yulang.GeneralDeclarations.Declaration)
  (singleton : Eq.{1} registry.declarations (List.cons.{0} declaration List.nil.{0}))
  (packet : Yulang.GeneralNominalSaturationState.Packet roles) :
  Membership.mem.{0, 0} state.packets packet → Eq.{1} packet.declaration declaration
Yulang.GeneralDictionarySourceChoiceVisibility.singleton_key_coherence {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (formed : Yulang.GeneralNominalFeedbackSteps.SourceFormed registry root state)
  (declaration : Yulang.GeneralDeclarations.Declaration)
  (singleton : Eq.{1} registry.declarations (List.cons.{0} declaration List.nil.{0}))
  (focus : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (packet : Yulang.GeneralNominalSaturationState.Packet roles) :
  Membership.mem.{0, 0} state.packets packet →
    Yulang.GeneralNominalSaturationState.Alias state focus.identity packet.site.occurrence.identity →
      Eq.{1} packet.declaration.id declaration.id
Yulang.GeneralDictionarySourceChoiceVisibility.singleton_selected_coherence {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (formed : Yulang.GeneralNominalFeedbackSteps.SourceFormed registry root state)
  (declaration : Yulang.GeneralDeclarations.Declaration)
  (singleton : Eq.{1} registry.declarations (List.cons.{0} declaration List.nil.{0}))
  (focus : Yulang.GeneralSourceDictionaries.Occurrence roles) (key : Nat)
  (children : List.{0} (Yulang.GeneralSourceDictionaries.Occurrence roles))
  (selected :
    Yulang.GeneralNominalFeedbackK2.Local registry state focus
      (Yulang.CommonRoleOutermostResolver.Frontier.selected.{0} key children))
  (packet : Yulang.GeneralNominalSaturationState.Packet roles) :
  Membership.mem.{0, 0} state.packets packet →
    Yulang.GeneralNominalSaturationState.Alias state focus.identity packet.site.occurrence.identity →
      Eq.{1} packet.declaration.id key
Yulang.GeneralDictionaryJournalTreeFormation.initial_source :
  Yulang.GeneralNominalSourceFormation.InitialSource Yulang.GeneralDictionaryRecursiveObstruction.registry
    Yulang.GeneralDictionaryRecursiveObstruction.context Yulang.GeneralDictionaryRecursiveObstruction.root
Yulang.GeneralDictionaryJournalTreeFormation.formed_before :
  Yulang.GeneralNominalFeedbackSteps.SourceFormed Yulang.GeneralDictionaryRecursiveObstruction.registry
    Yulang.GeneralDictionaryRecursiveObstruction.root Yulang.GeneralDictionaryCommittedEvidenceExamples.before
Yulang.GeneralDictionaryJournalTreeFormation.formed_after :
  Yulang.GeneralNominalFeedbackSteps.SourceFormed Yulang.GeneralDictionaryRecursiveObstruction.registry
    Yulang.GeneralDictionaryRecursiveObstruction.root Yulang.GeneralDictionaryJournalTreeExamples.after
Yulang.GeneralDictionaryJournalTreeFormation.reachable_positive :
  Yulang.GeneralNominalFeedbackSteps.SourceFormed Yulang.GeneralDictionaryRecursiveObstruction.registry
      Yulang.GeneralDictionaryRecursiveObstruction.root Yulang.GeneralDictionaryJournalTreeExamples.after ∧
    Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryJournalTreeExamples.after
        Yulang.GeneralNominalExamples.model ∧
      ¬Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryJournalTreeExamples.after
          Yulang.GeneralDictionaryRecursiveObstruction.badModel
Yulang.GeneralDictionaryJournalTreeExamples.good_before :
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryCommittedEvidenceExamples.before
    Yulang.GeneralNominalExamples.model
Yulang.GeneralDictionaryJournalTreeExamples.edge_shape (first last : Nat)
  (edge : Yulang.GeneralNominalFeedbackK2.Edge Yulang.GeneralDictionaryCommittedEvidenceExamples.before first last) :
  Eq.{1} first 0 ∧ Eq.{1} last 1
Yulang.GeneralDictionaryJournalTreeExamples.acyclic (source : Nat) :
  ¬Yulang.GeneralNominalFeedbackK2.Cycle Yulang.GeneralDictionaryCommittedEvidenceExamples.before source
Yulang.GeneralDictionaryJournalTreeExamples.old_acyclic (slot : Fin 2) :
  ¬Yulang.GeneralNominalCycleK2.RecursAt Yulang.GeneralDictionaryRecursiveObstruction.context.state slot
Yulang.GeneralDictionaryJournalTreeExamples.selected :
  Yulang.GeneralNominalFeedbackK2.Local Yulang.GeneralDictionaryRecursiveObstruction.registry
    Yulang.GeneralDictionaryCommittedEvidenceExamples.before Yulang.GeneralDictionaryRecursiveObstruction.root
    (Yulang.CommonRoleOutermostResolver.Frontier.selected.{0} 40 List.nil.{0})
Yulang.GeneralDictionaryJournalTreeExamples.enabled :
  Yulang.GeneralNominalFeedbackSteps.Installable Yulang.GeneralDictionaryRecursiveObstruction.registry
    Yulang.GeneralDictionaryCommittedEvidenceExamples.before Yulang.GeneralDictionaryCommittedEvidenceExamples.packet
Yulang.GeneralDictionaryJournalTreeExamples.feedback_step :
  Yulang.GeneralNominalFeedbackSteps.Step Yulang.GeneralDictionaryRecursiveObstruction.registry
    Yulang.GeneralDictionaryRecursiveObstruction.root Yulang.GeneralDictionaryCommittedEvidenceExamples.before
    Yulang.GeneralDictionaryJournalTreeExamples.after
Yulang.GeneralDictionaryJournalTreeExamples.finished_step :
  Yulang.GeneralDictionaryFinishedTrace.Step Yulang.GeneralDictionaryRecursiveObstruction.registry
    Yulang.GeneralDictionaryRecursiveObstruction.root Yulang.GeneralDictionaryCommittedEvidenceExamples.before
    Yulang.GeneralDictionaryJournalTreeExamples.after
Yulang.GeneralDictionaryJournalTreeExamples.no_child
  (child parent : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles) :
  ¬Yulang.GeneralDictionaryJournalTree.Child Yulang.GeneralDictionaryJournalTreeExamples.after child parent
Yulang.GeneralDictionaryJournalTreeExamples.covered :
  Yulang.GeneralDictionaryJournalTree.Covered Yulang.GeneralDictionaryJournalTreeExamples.after
    Yulang.GeneralDictionaryRecursiveObstruction.root
Yulang.GeneralDictionaryJournalTreeExamples.accessible :
  Acc.{1} (Yulang.GeneralDictionaryJournalTree.Child Yulang.GeneralDictionaryJournalTreeExamples.after)
    Yulang.GeneralDictionaryRecursiveObstruction.root
Yulang.GeneralDictionaryJournalTreeExamples.good_after :
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryJournalTreeExamples.after
    Yulang.GeneralNominalExamples.model
Yulang.GeneralDictionaryJournalTreeExamples.bad_excluded :
  ¬Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryJournalTreeExamples.after
      Yulang.GeneralDictionaryRecursiveObstruction.badModel
Yulang.GeneralDictionaryJournalTreeExamples.uniform_dictionary :
  Exists.{1} fun tree =>
    Eq.{1} tree.root Yulang.GeneralDictionaryRecursiveObstruction.root ∧
      Yulang.GeneralSourceDictionaries.Evidence
          (Yulang.GeneralDictionaryJournalTree.Recorded Yulang.GeneralDictionaryJournalTreeExamples.after) tree ∧
        ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
          Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryJournalTreeExamples.after model →
            Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDictionaryRecursiveObstruction.registry
              Yulang.GeneralDictionaryJournalTreeExamples.after.context model
              Yulang.GeneralDictionaryRecursiveObstruction.root (Yulang.GeneralSourceDictionaries.erase tree)
Yulang.GeneralDictionaryCurrentJournal.initial_current {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (context : Yulang.GeneralNominalCandidates.Context)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) :
  Yulang.GeneralDictionaryCurrentJournal.Current registry (Yulang.GeneralNominalSaturationState.initial context root)
Yulang.GeneralDictionaryCurrentJournal.installed_current {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (before : Yulang.GeneralNominalSaturationState.State roles)
  (packet : Yulang.GeneralNominalSaturationState.Packet roles)
  (enabled : Yulang.GeneralNominalFeedbackSteps.Installable registry before packet)
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (valid :
    Yulang.GeneralNominalSaturationState.Models
      (Yulang.GeneralNominalFeedbackSites.install before packet (Yulang.GeneralNominalFeedbackSites.emitted packet))
      model) :
  Yulang.GeneralDictionaryRecursiveEvidence.Instance registry
    (Yulang.GeneralNominalFeedbackSites.install before packet
        (Yulang.GeneralNominalFeedbackSites.emitted packet)).context
    model packet.site.occurrence packet.declaration.id packet.children
Yulang.GeneralDictionaryCurrentJournal.step_current {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (before after : Yulang.GeneralNominalSaturationState.State roles)
  (step : Yulang.GeneralDictionaryFinishedTrace.Step registry root before after)
  (current : Yulang.GeneralDictionaryCurrentJournal.Current registry before) :
  Yulang.GeneralDictionaryCurrentJournal.Current registry after
Yulang.GeneralDictionaryCurrentJournal.trace_current {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (before after : Yulang.GeneralNominalSaturationState.State roles)
  (path : Yulang.B4Target.Steps.{1} (Yulang.GeneralDictionaryFinishedTrace.Step registry root) before after)
  (current : Yulang.GeneralDictionaryCurrentJournal.Current registry before) :
  Yulang.GeneralDictionaryCurrentJournal.Current registry after
Yulang.GeneralDictionaryCurrentJournal.initial_trace_current {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context) (after : Yulang.GeneralNominalSaturationState.State roles)
  (path :
    Yulang.B4Target.Steps.{1} (Yulang.GeneralDictionaryFinishedTrace.Step registry root)
      (Yulang.GeneralNominalSaturationState.initial context root) after) :
  Yulang.GeneralDictionaryCurrentJournal.Current registry after
Yulang.GeneralDictionaryCurrentJournal.recorded_node {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context) (after : Yulang.GeneralNominalSaturationState.State roles)
  (path :
    Yulang.B4Target.Steps.{1} (Yulang.GeneralDictionaryFinishedTrace.Step registry root)
      (Yulang.GeneralNominalSaturationState.initial context root) after)
  (packet : Yulang.GeneralNominalSaturationState.Packet roles) (recorded : Membership.mem.{0, 0} after.packets packet)
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (valid : Yulang.GeneralNominalSaturationState.Models after model)
  (dictionaries : List.{0} Yulang.GeneralDictionaryReadback.Payload)
  (children :
    Yulang.CommonRoleOutermostResolver.All₂.{0, 0}
      (Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry after.context model) packet.children dictionaries) :
  Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry after.context model packet.site.occurrence
    (Yulang.CommonRoleOutermostResolver.Dictionary.node packet.declaration.id dictionaries)
Yulang.GeneralDictionaryCurrentJournalExamples.actual_path :
  Yulang.B4Target.Steps.{1}
    (Yulang.GeneralDictionaryFinishedTrace.Step Yulang.GeneralNominalFeedbackObstruction.registry
      Yulang.GeneralNominalFeedbackObstruction.root)
    Yulang.GeneralNominalFeedbackObstruction.initialState Yulang.GeneralNominalFeedbackRefresh.refreshed
Yulang.GeneralDictionaryCurrentJournalExamples.recorded :
  Membership.mem.{0, 0} Yulang.GeneralNominalFeedbackRefresh.refreshed.packets
    Yulang.GeneralNominalFeedbackObstruction.packet
Yulang.GeneralDictionaryCurrentJournalExamples.current_parent (m : Yulang.GeneralNominalCommonBridge.Assignment)
  (valid : Yulang.GeneralNominalSaturationState.Models Yulang.GeneralNominalFeedbackRefresh.refreshed m) :
  Yulang.GeneralDictionaryRecursiveEvidence.Instance Yulang.GeneralNominalFeedbackObstruction.registry
    Yulang.GeneralNominalFeedbackRefresh.refreshed.context m Yulang.GeneralNominalFeedbackObstruction.root 2
    (List.cons.{0} Yulang.GeneralNominalFeedbackObstruction.child List.nil.{0})
Yulang.GeneralDictionaryCurrentJournalExamples.no_original_extension :
  ¬Yulang.GeneralDictionaryOrdinaryTrace.Extension Yulang.GeneralNominalFeedbackObstruction.packet.context
      Yulang.GeneralNominalFeedbackRefresh.refreshed.context
Yulang.GeneralDictionaryCurrentJournalExamples.nonvacuous_beyond_extension :
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralNominalFeedbackRefresh.refreshed
      Yulang.GeneralNominalFeedbackObstruction.model ∧
    Yulang.GeneralDictionaryRecursiveEvidence.Instance Yulang.GeneralNominalFeedbackObstruction.registry
        Yulang.GeneralNominalFeedbackRefresh.refreshed.context Yulang.GeneralNominalFeedbackObstruction.model
        Yulang.GeneralNominalFeedbackObstruction.root 2
        (List.cons.{0} Yulang.GeneralNominalFeedbackObstruction.child List.nil.{0}) ∧
      ¬Yulang.GeneralDictionaryOrdinaryTrace.Extension Yulang.GeneralNominalFeedbackObstruction.packet.context
          Yulang.GeneralNominalFeedbackRefresh.refreshed.context
Yulang.GeneralDictionaryCurrentJournalExamples.arbitrary_tail
  (after : Yulang.GeneralNominalSaturationState.State Yulang.GeneralDeclarationExamples.roles)
  (tail :
    Yulang.B4Target.Steps.{1}
      (Yulang.GeneralDictionaryFinishedTrace.Step Yulang.GeneralNominalFeedbackObstruction.registry
        Yulang.GeneralNominalFeedbackObstruction.root)
      Yulang.GeneralNominalFeedbackRefresh.refreshed after)
  (m : Yulang.GeneralNominalCommonBridge.Assignment) (valid : Yulang.GeneralNominalSaturationState.Models after m) :
  Yulang.GeneralDictionaryRecursiveEvidence.Instance Yulang.GeneralNominalFeedbackObstruction.registry after.context m
    Yulang.GeneralNominalFeedbackObstruction.root 2
    (List.cons.{0} Yulang.GeneralNominalFeedbackObstruction.child List.nil.{0})
Yulang.GeneralDictionaryTerminalRefresh.output_int (m : Yulang.GeneralNominalCommonBridge.Assignment)
  (valid : Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryJournalTreeExamples.after m) :
  Yulang.CommonNominalFullCarrier.Equivalent (Prod.fst.{0, 0} (m 1))
    (Yulang.CommonNominalSyntax.Layer.base.{0, 0} Yulang.Inference.Base.int)
Yulang.GeneralDictionaryTerminalRefresh.source_known :
  Yulang.GeneralNominalState.Known Yulang.GeneralDictionaryTerminalRefresh.nextState 1
Yulang.GeneralDictionaryTerminalRefresh.source_unknown :
  ¬Yulang.GeneralNominalState.Known Yulang.GeneralDictionaryJournalTreeExamples.after.context.state 1
Yulang.GeneralDictionaryTerminalRefresh.actual_refresh :
  Yulang.GeneralNominalFeedbackSteps.Step Yulang.GeneralDictionaryRecursiveObstruction.registry
    Yulang.GeneralDictionaryRecursiveObstruction.root Yulang.GeneralDictionaryJournalTreeExamples.after
    Yulang.GeneralDictionaryTerminalRefresh.refreshed
Yulang.GeneralDictionaryTerminalRefresh.exact_models (m : Yulang.GeneralNominalCommonBridge.Assignment) :
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryTerminalRefresh.refreshed m ↔
    Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryJournalTreeExamples.after m
Yulang.GeneralDictionaryTerminalRefresh.formed :
  Yulang.GeneralNominalFeedbackSteps.SourceFormed Yulang.GeneralDictionaryRecursiveObstruction.registry
    Yulang.GeneralDictionaryRecursiveObstruction.root Yulang.GeneralDictionaryTerminalRefresh.refreshed
Yulang.GeneralDictionaryTerminalRefresh.inhabited :
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryTerminalRefresh.refreshed
    Yulang.GeneralNominalExamples.model
Yulang.GeneralDictionaryTerminalRefresh.context_complete :
  Yulang.GeneralNominalSaturationState.ContextComplete Yulang.GeneralDictionaryTerminalRefresh.refreshed
Yulang.GeneralDictionaryTerminalRefresh.no_known_distinct (state : Yulang.GeneralNominalState.State)
  (first second : Yulang.GeneralNominalCommonBridge.Assignment) (sourceName : Nat)
  (firstAt :
    Eq.{1} (Prod.fst.{0, 0} (first sourceName))
      (Yulang.CommonNominalSyntax.Layer.base.{0, 0} Yulang.Inference.Base.int))
  (secondAt :
    Eq.{1} (Prod.fst.{0, 0} (second sourceName))
      (Yulang.CommonNominalSyntax.Layer.base.{0, 0} Yulang.Inference.Base.str))
  (one : Yulang.GeneralNominalState.Models state first) (two : Yulang.GeneralNominalState.Models state second) :
  ¬Yulang.GeneralNominalState.Known state sourceName
Yulang.GeneralDictionaryTerminalRefresh.varying_original (name : Nat) (large : LE.le.{0} 2 name) :
  Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryRecursiveObstruction.context.state
    (Yulang.GeneralDictionaryTerminalRefresh.varying name)
Yulang.GeneralDictionaryTerminalRefresh.varying_model (name : Nat) (large : LE.le.{0} 2 name) :
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryTerminalRefresh.refreshed
    (Yulang.GeneralDictionaryTerminalRefresh.varying name)
Yulang.GeneralDictionaryTerminalRefresh.refresh_large_unknown (next : Yulang.GeneralNominalCandidates.Context)
  (certificate : Yulang.GeneralNominalCycleSteps.Refresh Yulang.GeneralDictionaryTerminalRefresh.refreshed next)
  (source : Nat) (large : LE.le.{0} 2 source) : ¬Yulang.GeneralNominalState.Known next.state source
Yulang.GeneralDictionaryTerminalRefresh.current_query :
  Eq.{1}
    (Yulang.GeneralNominalInspection.queries Yulang.GeneralDictionaryTerminalRefresh.nextState
      Yulang.GeneralDictionaryRecursiveObstruction.context.interpretation
      Yulang.GeneralDictionaryRecursiveObstruction.declaration)
    (List.cons.{0}
      (Yulang.GeneralNominalInspection.Query.nominal 0
        (List.cons.{0} (Yulang.GeneralNominalInspection.Query.variables (List.cons.{0} 0 List.nil.{0})) List.nil.{0}))
      List.nil.{0})
Yulang.GeneralDictionaryTerminalRefresh.current_schema :
  Eq.{1}
    (Yulang.GeneralNominalRecursiveCandidates.generated Yulang.GeneralDictionaryRecursiveObstruction.registry
      Yulang.GeneralDictionaryTerminalRefresh.nextContext Yulang.GeneralDictionaryRecursiveObstruction.root
      Yulang.GeneralDictionaryRecursiveObstruction.declaration
      Yulang.GeneralDictionaryRecursiveObstruction.declaration_checked
      (List.cons.{0} (Prod.mk.{0, 0} 0 0) List.nil.{0}))
    {
      tests :=
        List.cons.{0}
          (Prod.mk.{0, 0} (Yulang.GeneralNominalRecursiveInspection.Origin.source 1)
            (Yulang.GeneralNominalRecursiveInspection.Test.scalar Yulang.Inference.Base.int))
          List.nil.{0} }
Yulang.GeneralDictionaryTerminalRefresh.every_current_branch (m : Yulang.GeneralNominalCommonBridge.Assignment)
  (valid : Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryTerminalRefresh.refreshed m) :
  Yulang.GeneralNominalRecursiveCandidates.BranchModels Yulang.GeneralDictionaryRecursiveObstruction.registry
    Yulang.GeneralDictionaryTerminalRefresh.nextContext Yulang.GeneralDictionaryRecursiveObstruction.root
    Yulang.GeneralDictionaryRecursiveObstruction.declaration
    Yulang.GeneralDictionaryRecursiveObstruction.declaration_checked (List.cons.{0} (Prod.mk.{0, 0} 0 0) List.nil.{0}) m
Yulang.GeneralDictionaryTerminalRefresh.installs_committed
  (p : Yulang.GeneralNominalSaturationState.Packet Yulang.GeneralDeclarationExamples.roles)
  (same : Eq.{1} p.site.occurrence Yulang.GeneralDictionaryRecursiveObstruction.root)
  (enabled :
    Yulang.GeneralNominalFeedbackSteps.Installable Yulang.GeneralDictionaryRecursiveObstruction.registry
      Yulang.GeneralDictionaryTerminalRefresh.refreshed p) :
  Yulang.GeneralNominalFeedbackSteps.Committed Yulang.GeneralDictionaryTerminalRefresh.refreshed p
Yulang.GeneralDictionaryTerminalRefresh.generated_only_root
  (child : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
  (generated :
    Yulang.GeneralNominalSaturationState.Generated Yulang.GeneralDictionaryTerminalRefresh.refreshed
      Yulang.GeneralDictionaryRecursiveObstruction.root child) :
  Eq.{1} child Yulang.GeneralDictionaryRecursiveObstruction.root
Yulang.GeneralDictionaryTerminalRefresh.stable :
  Yulang.GeneralNominalFeedbackSteps.Stable Yulang.GeneralDictionaryRecursiveObstruction.registry
    Yulang.GeneralDictionaryTerminalRefresh.refreshed Yulang.GeneralDictionaryRecursiveObstruction.root
Yulang.GeneralDictionaryTerminalRefresh.current_instance (m : Yulang.GeneralNominalCommonBridge.Assignment)
  (valid : Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryTerminalRefresh.refreshed m) :
  Yulang.GeneralDictionaryRecursiveEvidence.Instance Yulang.GeneralDictionaryRecursiveObstruction.registry
    Yulang.GeneralDictionaryTerminalRefresh.nextContext m Yulang.GeneralDictionaryRecursiveObstruction.root 40
    List.nil.{0}
Yulang.GeneralDictionaryTerminalRefresh.current_evidence (m : Yulang.GeneralNominalCommonBridge.Assignment)
  (valid : Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryTerminalRefresh.refreshed m) :
  Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDictionaryRecursiveObstruction.registry
    Yulang.GeneralDictionaryTerminalRefresh.refreshed.context m Yulang.GeneralDictionaryRecursiveObstruction.root
    (Yulang.CommonRoleOutermostResolver.Dictionary.node 40 List.nil.{0})
Yulang.GeneralDictionaryTerminalRefresh.completed :
  Yulang.GeneralNominalFeedbackSteps.SourceFormed Yulang.GeneralDictionaryRecursiveObstruction.registry
      Yulang.GeneralDictionaryRecursiveObstruction.root Yulang.GeneralDictionaryTerminalRefresh.refreshed ∧
    Yulang.GeneralNominalFeedbackSteps.Stable Yulang.GeneralDictionaryRecursiveObstruction.registry
        Yulang.GeneralDictionaryTerminalRefresh.refreshed Yulang.GeneralDictionaryRecursiveObstruction.root ∧
      Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryTerminalRefresh.refreshed
          Yulang.GeneralNominalExamples.model ∧
        ∀ (m : Yulang.GeneralNominalCommonBridge.Assignment),
          Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryTerminalRefresh.refreshed m →
            Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDictionaryRecursiveObstruction.registry
              Yulang.GeneralDictionaryTerminalRefresh.refreshed.context m
              Yulang.GeneralDictionaryRecursiveObstruction.root
              (Yulang.CommonRoleOutermostResolver.Dictionary.node 40 List.nil.{0})
Yulang.GeneralDictionaryTerminalRefresh.refines :
  Yulang.GeneralNominalRefinements.Refines Yulang.GeneralDictionaryJournalTreeExamples.after.context.state
    Yulang.GeneralDictionaryTerminalRefresh.nextState
Yulang.GeneralDictionaryTerminalRefresh.certificate :
  Yulang.GeneralNominalCycleSteps.Refresh Yulang.GeneralDictionaryJournalTreeExamples.after
    Yulang.GeneralDictionaryTerminalRefresh.nextContext
Yulang.GeneralDictionaryModeledJointGap.stale_checked :
  Yulang.GeneralDeclarations.DeclarationChecked Yulang.GeneralDeclarationExamples.constructors
    Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryModeledJointGap.stale
Yulang.GeneralDictionaryModeledJointGap.query (identity : Nat) :
  Eq.{1}
    (Yulang.GeneralNominalInspection.queries Yulang.GeneralDictionaryModeledJointGap.context.state
      Yulang.GeneralDictionaryModeledJointGap.context.interpretation
      (have __src := Yulang.GeneralNominalRecursiveExamples.len;
      { id := identity, role := __src.role, head := __src.head, requirements := __src.requirements,
        associated := __src.associated, outputBinders := __src.outputBinders }))
    (List.cons.{0}
      (Yulang.GeneralNominalInspection.Query.nominal 0
        (List.cons.{0} (Yulang.GeneralNominalInspection.Query.variables (List.cons.{0} 0 List.nil.{0})) List.nil.{0}))
      List.nil.{0})
Yulang.GeneralDictionaryModeledJointGap.schema (identity : Nat)
  (checked :
    Yulang.GeneralDeclarations.DeclarationChecked Yulang.GeneralDeclarationExamples.constructors
      Yulang.GeneralDeclarationExamples.roles
      (have __src := Yulang.GeneralNominalRecursiveExamples.len;
      { id := identity, role := __src.role, head := __src.head, requirements := __src.requirements,
        associated := __src.associated, outputBinders := __src.outputBinders })) :
  Eq.{1}
    (Yulang.GeneralNominalRecursiveCandidates.generated Yulang.GeneralNominalRecursiveExamples.lenRegistry
      Yulang.GeneralDictionaryModeledJointGap.context Yulang.GeneralDictionaryModeledJointGap.root
      (have __src := Yulang.GeneralNominalRecursiveExamples.len;
      { id := identity, role := __src.role, head := __src.head, requirements := __src.requirements,
        associated := __src.associated, outputBinders := __src.outputBinders })
      checked (List.cons.{0} (Prod.mk.{0, 0} 0 0) List.nil.{0}))
    { }
Yulang.GeneralDictionaryModeledJointGap.every_branch (identity : Nat)
  (checked :
    Yulang.GeneralDeclarations.DeclarationChecked Yulang.GeneralDeclarationExamples.constructors
      Yulang.GeneralDeclarationExamples.roles
      (have __src := Yulang.GeneralNominalRecursiveExamples.len;
      { id := identity, role := __src.role, head := __src.head, requirements := __src.requirements,
        associated := __src.associated, outputBinders := __src.outputBinders }))
  (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (valid : Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryModeledJointGap.context.state model) :
  Yulang.GeneralNominalRecursiveCandidates.BranchModels Yulang.GeneralNominalRecursiveExamples.lenRegistry
    Yulang.GeneralDictionaryModeledJointGap.context Yulang.GeneralDictionaryModeledJointGap.root
    (have __src := Yulang.GeneralNominalRecursiveExamples.len;
    { id := identity, role := __src.role, head := __src.head, requirements := __src.requirements,
      associated := __src.associated, outputBinders := __src.outputBinders })
    checked (List.cons.{0} (Prod.mk.{0, 0} 0 0) List.nil.{0}) model
Yulang.GeneralDictionaryModeledJointGap.models_iff (model : Yulang.GeneralNominalCommonBridge.Assignment) :
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryModeledJointGap.journal model ↔
    Yulang.GeneralNominalState.Models Yulang.GeneralDictionaryModeledJointGap.context.state model
Yulang.GeneralDictionaryModeledJointGap.journal_model :
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryModeledJointGap.journal
    Yulang.GeneralNominalExamples.model
Yulang.GeneralDictionaryModeledJointGap.known (source : Nat)
  (member :
    Membership.mem.{0, 0} (Yulang.GeneralNominalState.sources Yulang.GeneralDictionaryModeledJointGap.context.state)
      source) :
  Yulang.GeneralNominalState.Known Yulang.GeneralDictionaryModeledJointGap.context.state source
Yulang.GeneralDictionaryModeledJointGap.generated_only_root
  (child : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
  (generated :
    Yulang.GeneralNominalSaturationState.Generated Yulang.GeneralDictionaryModeledJointGap.journal
      Yulang.GeneralDictionaryModeledJointGap.root child) :
  Eq.{1} child Yulang.GeneralDictionaryModeledJointGap.root
Yulang.GeneralDictionaryModeledJointGap.no_install
  (p : Yulang.GeneralNominalSaturationState.Packet Yulang.GeneralDeclarationExamples.roles)
  (same : Eq.{1} p.site.occurrence Yulang.GeneralDictionaryModeledJointGap.root) :
  ¬Yulang.GeneralNominalFeedbackSteps.Installable Yulang.GeneralNominalRecursiveExamples.lenRegistry
      Yulang.GeneralDictionaryModeledJointGap.journal p
Yulang.GeneralDictionaryModeledJointGap.stable :
  Yulang.GeneralNominalFeedbackSteps.Stable Yulang.GeneralNominalRecursiveExamples.lenRegistry
    Yulang.GeneralDictionaryModeledJointGap.journal Yulang.GeneralDictionaryModeledJointGap.root
Yulang.GeneralDictionaryModeledJointGap.not_joint :
  ¬Yulang.GeneralNominalJointCandidates.Joint Yulang.GeneralNominalRecursiveExamples.lenRegistry
      Yulang.GeneralDictionaryModeledJointGap.journal Yulang.GeneralDictionaryModeledJointGap.root 30
Yulang.GeneralDictionaryModeledJointGap.edge_shape (first last : Nat)
  (edge : Yulang.GeneralNominalFeedbackK2.Edge Yulang.GeneralDictionaryModeledJointGap.journal first last) :
  Eq.{1} first 0 ∧ Eq.{1} last 1
Yulang.GeneralDictionaryModeledJointGap.acyclic (source : Nat) :
  ¬Yulang.GeneralNominalFeedbackK2.Cycle Yulang.GeneralDictionaryModeledJointGap.journal source
Yulang.GeneralDictionaryModeledJointGap.old_acyclic (slot : Fin 2) :
  ¬Yulang.GeneralNominalCycleK2.RecursAt Yulang.GeneralDictionaryModeledJointGap.context.state slot
Yulang.GeneralDictionaryModeledJointGap.report_calculated :
  Eq.{1}
    (Yulang.GeneralNominalRecursiveCandidates.report Yulang.GeneralDictionaryModeledJointGap.context
      Yulang.GeneralNominalRecursiveExamples.len (List.cons.{0} (Prod.mk.{0, 0} 0 0) List.nil.{0}))
    (Yulang.GeneralNominalUnaryCaptureFacts.captured Yulang.GeneralDictionaryModeledJointGap.context.state 0 0 0
      (Prod.mk.{0, 0} 1 1))
Yulang.GeneralDictionaryModeledJointGap.linked :
  Yulang.GeneralNominalState.Linked Yulang.GeneralDictionaryModeledJointGap.context.state
    Yulang.GeneralDictionaryModeledJointGap.root.demand
Yulang.GeneralDictionaryModeledJointGap.prepared :
  Yulang.GeneralNominalRecursiveCandidates.Prepared Yulang.GeneralNominalRecursiveExamples.lenRegistry
    Yulang.GeneralDictionaryModeledJointGap.context Yulang.GeneralDictionaryModeledJointGap.root
    Yulang.GeneralNominalRecursiveExamples.len Yulang.GeneralNominalRecursiveExamples.len_checked
Yulang.GeneralDictionaryModeledJointGap.ready :
  ¬Yulang.GeneralNominalState.RootPending Yulang.GeneralDictionaryModeledJointGap.context.state
      Yulang.GeneralDictionaryModeledJointGap.root.demand
Yulang.GeneralDictionaryModeledJointGap.survivor :
  Yulang.GeneralNominalRecursiveCandidates.Survivor Yulang.GeneralNominalRecursiveExamples.lenRegistry
    Yulang.GeneralDictionaryModeledJointGap.context Yulang.GeneralDictionaryModeledJointGap.root 30 List.nil.{0}
Yulang.GeneralDictionaryModeledJointGap.selected :
  Yulang.GeneralNominalFeedbackK2.Local Yulang.GeneralNominalRecursiveExamples.lenRegistry
    Yulang.GeneralDictionaryModeledJointGap.journal Yulang.GeneralDictionaryModeledJointGap.root
    (Yulang.CommonRoleOutermostResolver.Frontier.selected.{0} 30 List.nil.{0})
Yulang.GeneralDictionaryModeledJointGap.modeled_stable_selected_not_joint :
  Yulang.GeneralNominalFeedbackSteps.Stable Yulang.GeneralNominalRecursiveExamples.lenRegistry
      Yulang.GeneralDictionaryModeledJointGap.journal Yulang.GeneralDictionaryModeledJointGap.root ∧
    Yulang.GeneralNominalFeedbackK2.Local Yulang.GeneralNominalRecursiveExamples.lenRegistry
        Yulang.GeneralDictionaryModeledJointGap.journal Yulang.GeneralDictionaryModeledJointGap.root
        (Yulang.CommonRoleOutermostResolver.Frontier.selected.{0} 30 List.nil.{0}) ∧
      Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryModeledJointGap.journal
          Yulang.GeneralNominalExamples.model ∧
        ¬Yulang.GeneralNominalJointCandidates.Joint Yulang.GeneralNominalRecursiveExamples.lenRegistry
            Yulang.GeneralDictionaryModeledJointGap.journal Yulang.GeneralDictionaryModeledJointGap.root 30
Yulang.GeneralDictionaryModeledJointGap.registry_checked :
  Yulang.GeneralDeclarations.Checked Yulang.GeneralNominalRecursiveExamples.lenRegistry
Yulang.GeneralDictionaryModeledJointGap.no_modeledSelectedJoint :
  ¬Yulang.GeneralDictionaryFeedbackEvidence.ModeledSelectedJoint Yulang.GeneralDeclarationExamples.roles
Yulang.GeneralDictionaryModeledJointGap.current_instance (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (valid : Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryModeledJointGap.journal model) :
  Yulang.GeneralDictionaryRecursiveEvidence.Instance Yulang.GeneralNominalRecursiveExamples.lenRegistry
    Yulang.GeneralDictionaryModeledJointGap.context model Yulang.GeneralDictionaryModeledJointGap.root 30 List.nil.{0}
Yulang.GeneralDictionaryModeledJointGap.current_evidence (model : Yulang.GeneralNominalCommonBridge.Assignment)
  (valid : Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryModeledJointGap.journal model) :
  Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralNominalRecursiveExamples.lenRegistry
    Yulang.GeneralDictionaryModeledJointGap.context model Yulang.GeneralDictionaryModeledJointGap.root
    (Yulang.CommonRoleOutermostResolver.Dictionary.node 30 List.nil.{0})
Yulang.GeneralDictionaryModeledJointGap.not_sourceFormed :
  ¬Yulang.GeneralNominalFeedbackSteps.SourceFormed Yulang.GeneralNominalRecursiveExamples.lenRegistry
      Yulang.GeneralDictionaryModeledJointGap.root Yulang.GeneralDictionaryModeledJointGap.journal
Yulang.GeneralDictionaryJournalTree.recorded_tree {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (covered : Yulang.GeneralDictionaryJournalTree.Covered state root)
  (accessible : Acc.{1} (Yulang.GeneralDictionaryJournalTree.Child state) root) :
  Exists.{1} fun tree =>
    Eq.{1} tree.root root ∧
      Yulang.GeneralSourceDictionaries.Evidence (Yulang.GeneralDictionaryJournalTree.Recorded state) tree
Yulang.GeneralDictionaryJournalTree.uniform_dictionary {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context) (after : Yulang.GeneralNominalSaturationState.State roles)
  (path :
    Yulang.B4Target.Steps.{1} (Yulang.GeneralDictionaryFinishedTrace.Step registry root)
      (Yulang.GeneralNominalSaturationState.initial context root) after)
  (covered : Yulang.GeneralDictionaryJournalTree.Covered after root)
  (accessible : Acc.{1} (Yulang.GeneralDictionaryJournalTree.Child after) root) :
  Exists.{1} fun tree =>
    Eq.{1} tree.root root ∧
      Yulang.GeneralSourceDictionaries.Evidence (Yulang.GeneralDictionaryJournalTree.Recorded after) tree ∧
        ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
          Yulang.GeneralNominalSaturationState.Models after model →
            Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry after.context model root
              (Yulang.GeneralSourceDictionaries.erase tree)
Yulang.GeneralDictionaryJournalTree.missing_packet {roles : Yulang.Roles.RoleDecls}
  (state : Yulang.GeneralNominalSaturationState.State roles)
  (root site : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (reached : Yulang.GeneralDictionaryJournalTree.Reach state root site)
  (missing :
    ∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
      Membership.mem.{0, 0} state.packets packet → Ne.{1} packet.site.occurrence site) :
  ¬Yulang.GeneralDictionaryJournalTree.Covered state root
Yulang.GeneralDictionaryRefreshGap.no_known (state : Yulang.GeneralNominalState.State)
  (one : Yulang.GeneralNominalState.Models state Yulang.GeneralNominalExamples.model)
  (two : Yulang.GeneralNominalState.Models state Yulang.GeneralDictionaryRecursiveObstruction.badModel) :
  ¬Yulang.GeneralNominalState.Known state 1
Yulang.GeneralDictionaryRefreshGap.good_journal_model :
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionaryJournalObstruction.journal
    Yulang.GeneralNominalExamples.model
Yulang.GeneralDictionaryRefreshGap.refresh_unknown (after : Yulang.GeneralNominalCandidates.Context)
  (certificate : Yulang.GeneralNominalFeedbackSteps.Refresh Yulang.GeneralDictionaryJournalObstruction.journal after) :
  ¬Yulang.GeneralNominalState.Known after.state 1
Yulang.GeneralDictionaryRefreshGap.generated_only_root
  (child : Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
  (generated :
    Yulang.GeneralNominalSaturationState.Generated Yulang.GeneralDictionaryJournalObstruction.journal
      Yulang.GeneralDictionaryRecursiveObstruction.root child) :
  Eq.{1} child Yulang.GeneralDictionaryRecursiveObstruction.root
Yulang.GeneralDictionaryRefreshGap.no_install
  (p : Yulang.GeneralNominalSaturationState.Packet Yulang.GeneralDeclarationExamples.roles)
  (same : Eq.{1} p.site.occurrence Yulang.GeneralDictionaryRecursiveObstruction.root) :
  ¬Yulang.GeneralNominalFeedbackSteps.Installable Yulang.GeneralDictionaryRecursiveObstruction.registry
      Yulang.GeneralDictionaryJournalObstruction.journal p
Yulang.GeneralDictionaryRefreshGap.stable :
  Yulang.GeneralNominalFeedbackSteps.Stable Yulang.GeneralDictionaryRecursiveObstruction.registry
    Yulang.GeneralDictionaryJournalObstruction.journal Yulang.GeneralDictionaryRecursiveObstruction.root
Yulang.GeneralDictionaryRefreshGap.edge_shape (first last : Nat)
  (edge : Yulang.GeneralNominalFeedbackK2.Edge Yulang.GeneralDictionaryJournalObstruction.journal first last) :
  Eq.{1} first 0 ∧ Eq.{1} last 1
Yulang.GeneralDictionaryRefreshGap.acyclic (source : Nat) :
  ¬Yulang.GeneralNominalFeedbackK2.Cycle Yulang.GeneralDictionaryJournalObstruction.journal source
Yulang.GeneralDictionaryRefreshGap.old_acyclic (slot : Fin 2) :
  ¬Yulang.GeneralNominalCycleK2.RecursAt Yulang.GeneralDictionaryRecursiveObstruction.context.state slot
Yulang.GeneralDictionaryRefreshGap.selected :
  Yulang.GeneralNominalFeedbackK2.Local Yulang.GeneralDictionaryRecursiveObstruction.registry
    Yulang.GeneralDictionaryJournalObstruction.journal Yulang.GeneralDictionaryRecursiveObstruction.root
    (Yulang.CommonRoleOutermostResolver.Frontier.selected.{0} 40 List.nil.{0})
Yulang.GeneralDictionaryRefreshGap.no_evidenceNode :
  ¬Yulang.B4SkeletonV4.EvidenceNode.{0}
      (Yulang.GeneralDictionaryFeedbackEvidence.boundary Yulang.GeneralDeclarationExamples.roles)
Yulang.GeneralDictionaryRefreshGap.not_sourceFormed :
  ¬Yulang.GeneralNominalFeedbackSteps.SourceFormed Yulang.GeneralDictionaryRecursiveObstruction.registry
      Yulang.GeneralDictionaryRecursiveObstruction.root Yulang.GeneralDictionaryJournalObstruction.journal
Yulang.GeneralDictionaryRefreshGap.no_bridges
  (executor :
    Yulang.B4TargetV3.Executor.{0}
      (Yulang.GeneralNominalFeedbackBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles))
  (frontiers :
    Yulang.B4SkeletonV4.Frontiers.{0}
      (Yulang.GeneralNominalFeedbackBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles)) :
  ¬Yulang.B4SkeletonV4.B4Bridges.{0}
      (Yulang.GeneralDictionaryFeedbackEvidence.boundary Yulang.GeneralDeclarationExamples.roles) executor frontiers
```
