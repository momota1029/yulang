# Cycle151 exact quantified theorem types

```text
                      (@Yulang.GeneralNominalSaturationState.State.context roles
                        (@Yulang.GeneralNominalSupport.Tracked.current roles state))
                      model root dictionary
Yulang.GeneralDictionaryVariableTreeCycles.edge_shape : ∀ (first last : Nat),
  @Yulang.GeneralNominalFeedbackK2.Edge Yulang.GeneralDeclarationExamples.roles
      (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryVariableTreeExample.start)
      first last →
    And (@Eq Nat first (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@Ne Nat last (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
Yulang.GeneralDictionaryVariableTreeCycles.acyclic : ∀ (source : Nat),
  Not
    (@Yulang.GeneralNominalFeedbackK2.Cycle Yulang.GeneralDeclarationExamples.roles
      (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryVariableTreeExample.start)
      source)
Yulang.GeneralDictionaryVariableTreeCycles.old_acyclic : ∀
  (slot : Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))),
  Not (Yulang.GeneralNominalCycleK2.RecursAt Yulang.GeneralNominalBranchExample.state slot)
Yulang.GeneralDictionaryVariableTreeEvidence.children_exact : @Eq
  (List (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
  Yulang.GeneralDictionaryVariableTreeExample.children
  (@List.cons (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralDictionaryVariableTreeEvidence.child
    (@List.nil (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)))
Yulang.GeneralDictionaryVariableTreeEvidence.captures_exact : @Eq Yulang.GeneralNominalAllocation.Bindings
  Yulang.GeneralDictionaryVariableTreeEvidence.captures
  (@List.cons (Prod Nat (Prod Nat Nat))
    (@Prod.mk Nat (Prod Nat Nat) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@Prod.mk Nat Nat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@List.cons (Prod Nat (Prod Nat Nat))
      (@Prod.mk Nat (Prod Nat Nat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@Prod.mk Nat Nat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@List.nil (Prod Nat (Prod Nat Nat)))))
Yulang.GeneralDictionaryVariableTreeEvidence.child_arguments : @Eq
  (Option (List (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralNominalBranchExample.context.state)))
  (@Yulang.GeneralNominalRecursiveCandidates.arguments Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralNominalBranchExample.context Yulang.GeneralDictionaryVariableTreeEvidence.child)
  (@some
    (List
      (Prod (Fin Yulang.GeneralNominalBranchExample.context.state.base.slots)
        (Fin Yulang.GeneralNominalBranchExample.context.state.base.slots)))
    (@List.cons
      (Prod (Fin Yulang.GeneralNominalBranchExample.context.state.base.slots)
        (Fin Yulang.GeneralNominalBranchExample.context.state.base.slots))
      (@Prod.mk (Fin Yulang.GeneralNominalBranchExample.context.state.base.slots)
        (Fin Yulang.GeneralNominalBranchExample.context.state.base.slots)
        (@OfNat.ofNat (Fin Yulang.GeneralNominalBranchExample.context.state.base.slots) (nat_lit 1)
          (@Fin.instOfNat Yulang.GeneralNominalBranchExample.context.state.base.slots ⋯ (nat_lit 1)))
        (@OfNat.ofNat (Fin Yulang.GeneralNominalBranchExample.context.state.base.slots) (nat_lit 1)
          (@Fin.instOfNat Yulang.GeneralNominalBranchExample.context.state.base.slots ⋯ (nat_lit 1))))
      (@List.nil
        (Prod (Fin Yulang.GeneralNominalBranchExample.context.state.base.slots)
          (Fin Yulang.GeneralNominalBranchExample.context.state.base.slots)))))
Yulang.GeneralDictionaryVariableTreeEvidence.leaf_checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDeclarationExamples.roles
  Yulang.GeneralDictionaryVariableTreeExample.leafDeclaration
Yulang.GeneralDictionaryVariableTreeEvidence.child_instance : @Yulang.GeneralDictionaryRecursiveEvidence.Instance
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryVariableTreeExample.registry
  Yulang.GeneralNominalBranchExample.context Yulang.GeneralNominalBranchExample.model
  Yulang.GeneralDictionaryVariableTreeEvidence.child Yulang.GeneralDictionaryVariableTreeExample.leafDeclaration.id
  (@List.nil (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
Yulang.GeneralDictionaryVariableTreeEvidence.child_evidence : @Yulang.GeneralDictionaryRecursiveEvidence.Evidence
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryVariableTreeExample.registry
  Yulang.GeneralNominalBranchExample.context Yulang.GeneralNominalBranchExample.model
  Yulang.GeneralDictionaryVariableTreeEvidence.child
  (Yulang.CommonRoleOutermostResolver.Dictionary.node Yulang.GeneralDictionaryVariableTreeExample.leafDeclaration.id
    (@List.nil Yulang.CommonRoleOutermostResolver.Dictionary))
Yulang.GeneralDictionaryVariableTreeEvidence.full_evidence : @Yulang.GeneralDictionaryRecursiveEvidence.Evidence
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryVariableTreeExample.registry
  Yulang.GeneralNominalBranchExample.context Yulang.GeneralNominalBranchExample.model
  Yulang.GeneralNominalBranchExample.root
  (Yulang.CommonRoleOutermostResolver.Dictionary.node Yulang.GeneralDictionaryVariableTreeExample.declaration.id
    (@List.cons Yulang.CommonRoleOutermostResolver.Dictionary
      (Yulang.CommonRoleOutermostResolver.Dictionary.node Yulang.GeneralDictionaryVariableTreeExample.leafDeclaration.id
        (@List.nil Yulang.CommonRoleOutermostResolver.Dictionary))
      (@List.nil Yulang.CommonRoleOutermostResolver.Dictionary)))
Yulang.GeneralDictionaryVariableTreeEvidence.reachable_inhabited_full_evidence : And
  (@Yulang.B4TargetV5.Reachable
    (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles)
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralDictionaryVariableTreeExample.registry Yulang.GeneralNominalBranchExample.root
    Yulang.GeneralDictionaryVariableTreeExample.start)
  (And
    (@Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDeclarationExamples.roles
      (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryVariableTreeExample.start)
      Yulang.GeneralNominalBranchExample.model)
    (And
      (@Yulang.GeneralDictionaryRecursiveEvidence.Evidence Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryVariableTreeExample.registry
        (@Yulang.GeneralNominalSaturationState.State.context Yulang.GeneralDeclarationExamples.roles
          (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
            Yulang.GeneralDictionaryVariableTreeExample.start))
        Yulang.GeneralNominalBranchExample.model Yulang.GeneralNominalBranchExample.root
        (Yulang.CommonRoleOutermostResolver.Dictionary.node Yulang.GeneralDictionaryVariableTreeExample.declaration.id
          (@List.cons Yulang.CommonRoleOutermostResolver.Dictionary
            (Yulang.CommonRoleOutermostResolver.Dictionary.node
              Yulang.GeneralDictionaryVariableTreeExample.leafDeclaration.id
              (@List.nil Yulang.CommonRoleOutermostResolver.Dictionary))
            (@List.nil Yulang.CommonRoleOutermostResolver.Dictionary))))
      (@Ne (List (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
        Yulang.GeneralDictionaryVariableTreeExample.children
        (@List.nil (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)))))
Yulang.GeneralDictionaryVariableTreeExample.checked : Yulang.GeneralDeclarations.DeclarationChecked
  Yulang.GeneralDeclarationExamples.constructors Yulang.GeneralDeclarationExamples.roles
  Yulang.GeneralDictionaryVariableTreeExample.declaration
Yulang.GeneralDictionaryVariableTreeExample.metadata : Yulang.GeneralNominalRecursiveCandidates.Metadata
  Yulang.GeneralDictionaryVariableTreeExample.registry Yulang.GeneralNominalBranchExample.context
Yulang.GeneralDictionaryVariableTreeExample.nonterminal : @Ne (List Yulang.GeneralDeclarations.Clause)
  Yulang.GeneralDictionaryVariableTreeExample.declaration.requirements (@List.nil Yulang.GeneralDeclarations.Clause)
Yulang.GeneralDictionaryVariableTreeExample.actual_children_count : @Eq Nat
  (@List.length (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralDictionaryVariableTreeExample.children)
  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
Yulang.GeneralDictionaryVariableTreeExample.actual_instance : @Yulang.GeneralDictionaryRecursiveEvidence.Instance
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryVariableTreeExample.registry
  Yulang.GeneralNominalBranchExample.context Yulang.GeneralNominalBranchExample.model
  Yulang.GeneralNominalBranchExample.root Yulang.GeneralDictionaryVariableTreeExample.declaration.id
  Yulang.GeneralDictionaryVariableTreeExample.children
Yulang.GeneralDictionaryVariableTreeExample.inhabited_nonterminal : And
  (Yulang.GeneralNominalState.Models Yulang.GeneralNominalBranchExample.state Yulang.GeneralNominalBranchExample.model)
  (And
    (@Yulang.GeneralDictionaryRecursiveEvidence.Instance Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryVariableTreeExample.registry Yulang.GeneralNominalBranchExample.context
      Yulang.GeneralNominalBranchExample.model Yulang.GeneralNominalBranchExample.root
      Yulang.GeneralDictionaryVariableTreeExample.declaration.id Yulang.GeneralDictionaryVariableTreeExample.children)
    (@Ne (List (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
      Yulang.GeneralDictionaryVariableTreeExample.children
      (@List.nil (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))))
Yulang.GeneralDictionaryVariableTreeExample.initial_source : @Yulang.GeneralNominalSourceFormation.InitialSource
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryVariableTreeExample.registry
  Yulang.GeneralNominalBranchExample.context Yulang.GeneralNominalBranchExample.root
Yulang.GeneralDictionaryVariableTreeExample.initial_models : @Yulang.GeneralNominalSaturationState.Models
  Yulang.GeneralDeclarationExamples.roles
  (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryVariableTreeExample.start)
  Yulang.GeneralNominalBranchExample.model
Yulang.GeneralDictionaryVariableTreeExample.actual_reachable : @Yulang.B4TargetV5.Reachable
  (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles)
  (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
  Yulang.GeneralDictionaryVariableTreeExample.registry Yulang.GeneralNominalBranchExample.root
  Yulang.GeneralDictionaryVariableTreeExample.start
Yulang.GeneralDictionaryVariableTreeInitialJoint.root_ready : Not
  (@Yulang.GeneralNominalState.RootPending Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralNominalBranchExample.state
    (@Yulang.GeneralSourceDictionaries.Occurrence.demand Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralNominalBranchExample.root))
Yulang.GeneralDictionaryVariableTreeInitialJoint.prepared : @Yulang.GeneralNominalRecursiveCandidates.Prepared
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryVariableTreeExample.registry
  Yulang.GeneralNominalBranchExample.context Yulang.GeneralNominalBranchExample.root
  Yulang.GeneralDictionaryVariableTreeExample.declaration Yulang.GeneralDictionaryVariableTreeExample.checked
Yulang.GeneralDictionaryVariableTreeInitialJoint.survivor : @Yulang.GeneralNominalRecursiveCandidates.Survivor
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryVariableTreeExample.registry
  Yulang.GeneralNominalBranchExample.context Yulang.GeneralNominalBranchExample.root
  Yulang.GeneralDictionaryVariableTreeExample.declaration.id Yulang.GeneralDictionaryVariableTreeExample.children
Yulang.GeneralDictionaryVariableTreeInitialJoint.initial_joint : @Yulang.GeneralNominalJointCandidates.Joint
  Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryVariableTreeExample.registry
  (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryVariableTreeExample.start)
  Yulang.GeneralNominalBranchExample.root Yulang.GeneralDictionaryVariableTreeExample.declaration.id
Yulang.GeneralDictionaryVariableTreeInitialJoint.unrecorded : @Eq
  (List (Yulang.GeneralNominalSaturationState.Packet Yulang.GeneralDeclarationExamples.roles))
  (@Yulang.GeneralNominalSaturationState.State.packets Yulang.GeneralDeclarationExamples.roles
    (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryVariableTreeExample.start))
  (@List.nil (Yulang.GeneralNominalSaturationState.Packet Yulang.GeneralDeclarationExamples.roles))
Yulang.GeneralDictionaryVariableTreeInitialJoint.reachable_unrecorded_nonterminal_joint : And
  (@Yulang.B4TargetV5.Reachable
    (Yulang.GeneralNominalSupportBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles)
    (Yulang.GeneralNominalSupportBoundary.boundary Yulang.GeneralDeclarationExamples.roles)
    Yulang.GeneralDictionaryVariableTreeExample.registry Yulang.GeneralNominalBranchExample.root
    Yulang.GeneralDictionaryVariableTreeExample.start)
  (And
    (@Yulang.GeneralNominalSaturationState.Models Yulang.GeneralDeclarationExamples.roles
      (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryVariableTreeExample.start)
      Yulang.GeneralNominalBranchExample.model)
    (And
      (@Yulang.GeneralNominalJointCandidates.Joint Yulang.GeneralDeclarationExamples.roles
        Yulang.GeneralDictionaryVariableTreeExample.registry
        (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
          Yulang.GeneralDictionaryVariableTreeExample.start)
        Yulang.GeneralNominalBranchExample.root Yulang.GeneralDictionaryVariableTreeExample.declaration.id)
      (And
        (@Eq (List (Yulang.GeneralNominalSaturationState.Packet Yulang.GeneralDeclarationExamples.roles))
          (@Yulang.GeneralNominalSaturationState.State.packets Yulang.GeneralDeclarationExamples.roles
            (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
              Yulang.GeneralDictionaryVariableTreeExample.start))
          (@List.nil (Yulang.GeneralNominalSaturationState.Packet Yulang.GeneralDeclarationExamples.roles)))
        (@Ne (List (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))
          Yulang.GeneralDictionaryVariableTreeExample.children
          (@List.nil (Yulang.GeneralSourceDictionaries.Occurrence Yulang.GeneralDeclarationExamples.roles))))))
Yulang.GeneralDictionaryVariableTreeInitialJoint.other_conflict : @Ne
  (List (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralNominalBranchExample.context.state))
  (@Yulang.GeneralNominalRecursiveInspection.Report.conflicts Yulang.GeneralNominalBranchExample.context.state
    (Yulang.GeneralNominalRecursiveCandidates.report Yulang.GeneralNominalBranchExample.context
      Yulang.GeneralDictionaryVariableTreeExample.leafDeclaration
      (@List.cons (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralNominalBranchExample.context.state)
        (@Prod.mk (Fin Yulang.GeneralNominalBranchExample.context.state.base.slots)
          (Fin Yulang.GeneralNominalBranchExample.context.state.base.slots)
          (@OfNat.ofNat (Fin Yulang.GeneralNominalBranchExample.context.state.base.slots) (nat_lit 0)
            (@Fin.instOfNat Yulang.GeneralNominalBranchExample.context.state.base.slots ⋯ (nat_lit 0)))
          (@OfNat.ofNat (Fin Yulang.GeneralNominalBranchExample.context.state.base.slots) (nat_lit 0)
            (@Fin.instOfNat Yulang.GeneralNominalBranchExample.context.state.base.slots ⋯ (nat_lit 0))))
        (@List.nil (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralNominalBranchExample.context.state)))))
  (@List.nil (Yulang.GeneralNominalInspection.Bounds Yulang.GeneralNominalBranchExample.context.state))
Yulang.GeneralDictionaryVariableTreeInitialJoint.other_not_prepared : ∀
  (check :
    Yulang.GeneralDeclarations.DeclarationChecked Yulang.GeneralDictionaryVariableTreeExample.registry.constructors
      Yulang.GeneralDeclarationExamples.roles Yulang.GeneralDictionaryVariableTreeExample.leafDeclaration),
  Not
    (@Yulang.GeneralNominalRecursiveCandidates.Prepared Yulang.GeneralDeclarationExamples.roles
      Yulang.GeneralDictionaryVariableTreeExample.registry Yulang.GeneralNominalBranchExample.context
      Yulang.GeneralNominalBranchExample.root Yulang.GeneralDictionaryVariableTreeExample.leafDeclaration check)
Yulang.GeneralDictionaryVariableTreeInitialJoint.unique : @Yulang.GeneralNominalLocalBoundary.Unique
  (Yulang.GeneralNominalCycleBoundary.vocabulary Yulang.GeneralDeclarationExamples.roles)
  (Yulang.GeneralNominalFeedbackK2.fields Yulang.GeneralDeclarationExamples.roles)
  Yulang.GeneralDictionaryVariableTreeExample.registry
  (@Yulang.GeneralNominalSupport.Tracked.current Yulang.GeneralDeclarationExamples.roles
    Yulang.GeneralDictionaryVariableTreeExample.start)
  Yulang.GeneralNominalBranchExample.root Yulang.GeneralDictionaryVariableTreeExample.declaration.id

```
