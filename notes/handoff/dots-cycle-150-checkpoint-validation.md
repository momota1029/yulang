# Cycle150 first checkpoint verification

4modules,21theorem checks,34scoped declarations. Exact source checkpoint local ce868aac4 plus aggregate/audit registration.

## fixture-build
exit0
```text
✔ [720/720] Built Yulang.GeneralDictionaryFiniteJournalJointExample (2.7s)
Build completed successfully (720 jobs).

```

## coverage-build
exit0
```text
✔ [708/708] Built Yulang.GeneralDictionaryBranchOrdinaryCoverage (2.4s)
Build completed successfully (708 jobs).

```

## locality-build
exit0
```text
✔ [720/721] Built Yulang.GeneralDictionaryNamedLocality (3.1s)
✔ [721/721] Built Yulang.GeneralDictionaryNamedLocalityExample (1.7s)
Build completed successfully (721 jobs).

```

## audit150
exit0
```text
'Yulang.GeneralDictionaryFiniteJournalJointExample.alias_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryFiniteJournalJointExample.root_locality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteJournalJointExample.root_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryFiniteJournalJointExample.actual_stable_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryBranchOrdinaryCoverage.coverage_from_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryBranchOrdinaryCoverage.dictionary_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryBranchOrdinaryCoverage.forget_growth' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryBranchOrdinaryCoverage.covered_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryBranchOrdinaryCoverage.recursive_fixture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.GeneralDictionaryNamedLocality.at_ordinary' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryNamedLocality.steps_ordinary' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryNamedLocality.at_aliases' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryNamedLocality.at_named' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryNamedLocality.initial_invariants' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryNamedLocality.alias_eq' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNamedLocality.related_locality' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNamedLocality.initial_joint' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryNamedLocalityExample.root_named' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNamedLocalityExample.child_named' depends on axioms: [propext, Quot.sound]
'Yulang.GeneralDictionaryNamedLocalityExample.actual_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.GeneralDictionaryNamedLocalityExample.every_model_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

```

## types
exit0
```text
@Yulang.GeneralDictionaryFiniteJournalJointExample.alias_eq : ∀ {first last : Nat},
  Yulang.GeneralNominalSaturationState.Alias Yulang.GeneralDictionarySupportRecursiveExample.finish.current first last →
    first = last
Yulang.GeneralDictionaryFiniteJournalJointExample.root_locality : ∀
  (site : Yulang.GeneralNominalDemandMerging.Site Yulang.GeneralDeclarationExamples.roles),
  Yulang.GeneralNominalJointCandidates.Related Yulang.GeneralDictionarySupportRecursiveExample.finish.current
      Yulang.GeneralNominalExamples.displayRoot site →
    site.occurrence = Yulang.GeneralNominalExamples.displayRoot
Yulang.GeneralDictionaryFiniteJournalJointExample.root_joint : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionarySupportRecursiveExample.finish.current
      assignment →
    Yulang.GeneralNominalJointCandidates.Joint Yulang.GeneralNominalExamples.registry
      Yulang.GeneralDictionarySupportRecursiveExample.finish.current Yulang.GeneralNominalExamples.displayRoot 1
Yulang.GeneralDictionaryFiniteJournalJointExample.actual_stable_joint : Yulang.B4TargetV5.Reachable
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralNominalExamples.registry Yulang.GeneralNominalExamples.displayRoot
    Yulang.GeneralDictionarySupportRecursiveExample.finish ∧
  Yulang.GeneralNominalSupportSteps.Stable Yulang.GeneralNominalExamples.registry
      Yulang.GeneralDictionarySupportRecursiveExample.finish Yulang.GeneralNominalExamples.displayRoot ∧
    Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionarySupportRecursiveExample.finish.current
        Yulang.GeneralNominalExamples.model ∧
      Yulang.GeneralNominalJointCandidates.Joint Yulang.GeneralNominalExamples.registry
        Yulang.GeneralDictionarySupportRecursiveExample.finish.current Yulang.GeneralNominalExamples.displayRoot 1
@Yulang.GeneralDictionaryBranchOrdinaryCoverage.coverage_from_trace : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context) (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4Target.Steps (Yulang.GeneralDictionarySupportOrdinaryExecution.Step registry root)
      (Yulang.GeneralNominalSupport.initial context root) state →
    Yulang.GeneralDictionaryBranchOrdinaryCoverage.Covered registry state root →
      Yulang.GeneralDictionarySpineCoverage.Covered registry state root
@Yulang.GeneralDictionaryBranchOrdinaryCoverage.dictionary_evidence : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context),
  Yulang.GeneralNominalSourceFormation.InitialSource registry context root →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles),
      Yulang.B4Target.Steps (Yulang.GeneralDictionarySupportOrdinaryExecution.Step registry root)
          (Yulang.GeneralNominalSupport.initial context root) state →
        Yulang.GeneralDictionaryBranchOrdinaryCoverage.Covered registry state root →
          ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
            Yulang.GeneralNominalSaturationState.Models state.current model →
              ∀ (dictionary : Yulang.GeneralDictionaryReadback.Payload),
                Yulang.B4TargetV3.Classify (Yulang.GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
                    registry state root (Yulang.CommonRoleOutermostResolver.Result.selected dictionary) →
                  Yulang.GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model root
                    dictionary
@Yulang.GeneralDictionaryBranchOrdinaryCoverage.forget_growth : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.GeneralDictionarySpineCoverage.Covered registry state root →
    Yulang.GeneralDictionaryBranchOrdinaryCoverage.Covered registry state root
@Yulang.GeneralDictionaryBranchOrdinaryCoverage.covered_iff : ∀ {roles : Yulang.Roles.RoleDecls}
  (registry : Yulang.GeneralDeclarations.Registry) (root : Yulang.GeneralSourceDictionaries.Occurrence roles)
  (context : Yulang.GeneralNominalCandidates.Context) (state : Yulang.GeneralNominalSupport.Tracked roles),
  Yulang.B4Target.Steps (Yulang.GeneralDictionarySupportOrdinaryExecution.Step registry root)
      (Yulang.GeneralNominalSupport.initial context root) state →
    (Yulang.GeneralDictionaryBranchOrdinaryCoverage.Covered registry state root ↔
      Yulang.GeneralDictionarySpineCoverage.Covered registry state root)
Yulang.GeneralDictionaryBranchOrdinaryCoverage.recursive_fixture : ∀
  (model : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionarySupportRecursiveExample.finish.current model →
    Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralNominalExamples.registry
      Yulang.GeneralDictionarySupportRecursiveExample.finish.current.context model
      Yulang.GeneralNominalExamples.displayRoot
      (Yulang.CommonRoleOutermostResolver.Dictionary.node 1 [Yulang.CommonRoleOutermostResolver.Dictionary.node 3 []])
@Yulang.GeneralDictionaryNamedLocality.at_ordinary : ∀ {roles : Yulang.Roles.RoleDecls}
  {names : Nat → Yulang.GeneralSourceDictionaries.Occurrence roles} {registry : Yulang.GeneralDeclarations.Registry}
  {before after : Yulang.GeneralNominalSupport.Tracked roles}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralDictionaryNamedLocality.At names registry before focus after →
    Yulang.GeneralDictionarySupportOrdinaryExecution.At registry before focus after
@Yulang.GeneralDictionaryNamedLocality.steps_ordinary : ∀ {roles : Yulang.Roles.RoleDecls}
  {names : Nat → Yulang.GeneralSourceDictionaries.Occurrence roles} {registry : Yulang.GeneralDeclarations.Registry}
  {root : Yulang.GeneralSourceDictionaries.Occurrence roles}
  {before after : Yulang.GeneralNominalSupport.Tracked roles},
  Yulang.B4Target.Steps (Yulang.GeneralDictionaryNamedLocality.Step names registry root) before after →
    Yulang.B4Target.Steps (Yulang.GeneralDictionarySupportOrdinaryExecution.Step registry root) before after
@Yulang.GeneralDictionaryNamedLocality.at_aliases : ∀ {roles : Yulang.Roles.RoleDecls}
  {names : Nat → Yulang.GeneralSourceDictionaries.Occurrence roles} {registry : Yulang.GeneralDeclarations.Registry}
  {before after : Yulang.GeneralNominalSupport.Tracked roles}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralDictionaryNamedLocality.At names registry before focus after →
    after.current.aliases = before.current.aliases
@Yulang.GeneralDictionaryNamedLocality.at_named : ∀ {roles : Yulang.Roles.RoleDecls}
  {names : Nat → Yulang.GeneralSourceDictionaries.Occurrence roles} {registry : Yulang.GeneralDeclarations.Registry}
  {before after : Yulang.GeneralNominalSupport.Tracked roles}
  {focus : Yulang.GeneralSourceDictionaries.Occurrence roles},
  Yulang.GeneralDictionaryNamedLocality.At names registry before focus after →
    Yulang.GeneralDictionaryNamedLocality.Named names before.current →
      Yulang.GeneralDictionaryNamedLocality.Named names after.current
@Yulang.GeneralDictionaryNamedLocality.initial_invariants : ∀ {roles : Yulang.Roles.RoleDecls}
  (names : Nat → Yulang.GeneralSourceDictionaries.Occurrence roles) (registry : Yulang.GeneralDeclarations.Registry)
  (root : Yulang.GeneralSourceDictionaries.Occurrence roles) (context : Yulang.GeneralNominalCandidates.Context),
  names root.identity = root →
    ∀ (state : Yulang.GeneralNominalSupport.Tracked roles),
      Yulang.B4Target.Steps (Yulang.GeneralDictionaryNamedLocality.Step names registry root)
          (Yulang.GeneralNominalSupport.initial context root) state →
        Yulang.GeneralDictionaryNamedLocality.Named names state.current ∧ state.current.aliases = []
@Yulang.GeneralDictionaryNamedLocality.alias_eq : ∀ {roles : Yulang.Roles.RoleDecls}
  {state : Yulang.GeneralNominalSaturationState.State roles},
  state.aliases = [] → ∀ {first last : Nat}, Yulang.GeneralNominalSaturationState.Alias state first last → first = last
@Yulang.GeneralDictionaryNamedLocality.related_locality : ∀ {roles : Yulang.Roles.RoleDecls}
  (names : Nat → Yulang.GeneralSourceDictionaries.Occurrence roles)
  (state : Yulang.GeneralNominalSaturationState.State roles),
  Yulang.GeneralDictionaryNamedLocality.Named names state →
    state.aliases = [] →
      ∀ (focus : Yulang.GeneralSourceDictionaries.Occurrence roles),
        names focus.identity = focus →
          ∀ (site : Yulang.GeneralNominalDemandMerging.Site roles),
            Yulang.GeneralNominalJointCandidates.Related state focus site → site.occurrence = focus
@Yulang.GeneralDictionaryNamedLocality.initial_joint : ∀ {roles : Yulang.Roles.RoleDecls}
  (names : Nat → Yulang.GeneralSourceDictionaries.Occurrence roles) (registry : Yulang.GeneralDeclarations.Registry)
  (root focus : Yulang.GeneralSourceDictionaries.Occurrence roles) (context : Yulang.GeneralNominalCandidates.Context),
  Yulang.GeneralNominalSourceFormation.InitialSource registry context root →
    names root.identity = root →
      ∀ (state : Yulang.GeneralNominalSupport.Tracked roles),
        Yulang.B4Target.Steps (Yulang.GeneralDictionaryNamedLocality.Step names registry root)
            (Yulang.GeneralNominalSupport.initial context root) state →
          ∀ (packet : Yulang.GeneralNominalSaturationState.Packet roles),
            packet ∈ state.current.packets →
              packet.site.occurrence = focus →
                ∀ (key : Nat) (children : List (Yulang.GeneralSourceDictionaries.Occurrence roles)),
                  Yulang.GeneralNominalSupportBoundary.Local registry state focus
                      (Yulang.CommonRoleOutermostResolver.Frontier.selected key children) →
                    ∀ (model : Yulang.GeneralNominalCommonBridge.Assignment),
                      Yulang.GeneralNominalSaturationState.Models state.current model →
                        Yulang.GeneralNominalJointCandidates.Joint registry state.current focus key
Yulang.GeneralDictionaryNamedLocalityExample.root_named : Yulang.GeneralDictionaryNamedLocalityExample.names
    Yulang.GeneralNominalExamples.displayRoot.identity =
  Yulang.GeneralNominalExamples.displayRoot
Yulang.GeneralDictionaryNamedLocalityExample.child_named : Yulang.GeneralDictionaryNamedLocalityExample.names
    Yulang.GeneralNominalExamples.displayChild.identity =
  Yulang.GeneralNominalExamples.displayChild
Yulang.GeneralDictionaryNamedLocalityExample.actual_trace : Yulang.B4Target.Steps
  (Yulang.GeneralDictionaryNamedLocality.Step Yulang.GeneralDictionaryNamedLocalityExample.names
    Yulang.GeneralNominalExamples.registry Yulang.GeneralNominalExamples.displayRoot)
  Yulang.GeneralDictionarySupportRecursiveExample.start Yulang.GeneralDictionarySupportRecursiveExample.finish
Yulang.GeneralDictionaryNamedLocalityExample.every_model_joint : ∀
  (assignment : Yulang.GeneralNominalCommonBridge.Assignment),
  Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDictionarySupportRecursiveExample.finish.current
      assignment →
    Yulang.GeneralNominalJointCandidates.Joint Yulang.GeneralNominalExamples.registry
      Yulang.GeneralDictionarySupportRecursiveExample.finish.current Yulang.GeneralNominalExamples.displayRoot 1

```

## scoped
exit0
```text
FOCUSED-AXIOM-PASS: 34 declarations in cycle150 modules

```

The first type-print run used unsupported pp.width and exited1; removing the display-only option produced the successful run above. No theorem statement was changed.
